(** * CapacityCoherence.v -- Segment capacity bookkeeping is coherent.

    =========================================================================
    LAYER: 4 - APPLICATION (resource accounting invariant)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Proves that the seg_used field faithfully tracks the total size of
    objects on the segment.  The key invariant:

      seg_used s = sum_sizes (seg_objects s)

    This holds initially (trivially for empty segments) and is preserved
    by every operation in the enriched LTS:
    - Place: adds om_size to both seg_used and the objects list
    - Remove/Evict: subtracts freed from seg_used, removes from objects
    - BeginRead/EndRead: inc/dec_refcnt preserves om_size
    - BeginDrain/CompleteDrain/Unmount: status-only, no size change

    The partition identity (sum = kept + freed) is the core arithmetic
    lemma.  Combined with segment_wf (used ≤ capacity) and has_room
    checks before placement, this guarantees no space overflows.

    @source mooncake-store/src/store.cpp (allocation path)
    @source mooncake-store/include/allocator.h (capacity tracking)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.Diamond (inc/dec_preserves_size)

    PROVIDES:
    - sum_sizes (total object size on a segment)
    - capacity_coherent (seg_used = sum_sizes)
    - sum_sizes_cons, sum_sizes_app (structural lemmas)
    - sum_sizes_partition (CORE: total = kept + freed)
    - freed_eq_sum_matching (freed computation = sum of matching)
    - place_preserves_coherence (Place preserves capacity_coherent)
    - remove_preserves_coherence (Remove preserves capacity_coherent)
    - update_preserves_coherence (metadata updates preserve coherence)
    - step_preserves_coherence (HEADLINE: every step preserves coherence)
    - place_preserves_wf (has_room → place preserves used ≤ capacity)
    - store_well_formed (combined: consistent ∧ coherent ∧ NoDup)
    - step_preserves_well_formed (HEADLINE: well_formed is invariant)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Diamond.
Require Import MooncakeFormal.LTS.NoDupPreservation.
Require Import MooncakeFormal.LTS.TraceEquivalence.
Require Import MooncakeFormal.LTS.RichConsistency.

(** =====================================================================
    Section 1: SIZE SUMMATION
    ===================================================================== *)

(** Total size of all objects on a segment. *)
Fixpoint sum_sizes (objs : list ObjectMeta) : nat :=
  match objs with
  | [] => 0
  | m :: rest => om_size m + sum_sizes rest
  end.

Lemma sum_sizes_cons : forall m rest,
  sum_sizes (m :: rest) = om_size m + sum_sizes rest.
Proof. reflexivity. Qed.

Lemma sum_sizes_app : forall l1 l2,
  sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof.
  induction l1 as [| m rest IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** =====================================================================
    Section 2: FOLD_LEFT AND SUM_SIZES EQUIVALENCE
    ===================================================================== *)

(** The fold_left accumulator property for addition. *)
Lemma fold_left_add_acc : forall (objs : list ObjectMeta)
    (f : ObjectMeta -> nat) (a : nat),
  fold_left (fun acc m => acc + f m) objs a =
  a + fold_left (fun acc m => acc + f m) objs 0.
Proof.
  induction objs as [| m rest IH]; intros f a; simpl.
  - lia.
  - rewrite (IH f (a + f m)). rewrite (IH f (f m)). lia.
Qed.

(** Selective fold_left accumulator property. *)
Lemma fold_left_selective_acc : forall (objs : list ObjectMeta)
    (p : ObjectMeta -> bool) (f : ObjectMeta -> nat) (a : nat),
  fold_left (fun acc m => if p m then acc + f m else acc) objs a =
  a + fold_left (fun acc m => if p m then acc + f m else acc) objs 0.
Proof.
  induction objs as [| m rest IH]; intros p f a; simpl.
  - lia.
  - destruct (p m).
    + rewrite (IH p f (a + f m)). rewrite (IH p f (f m)). lia.
    + rewrite (IH p f a). rewrite (IH p f 0). lia.
Qed.

(** fold_left with addition equals sum_sizes. *)
Lemma fold_left_eq_sum_sizes : forall objs,
  fold_left (fun acc m => acc + om_size m) objs 0 = sum_sizes objs.
Proof.
  induction objs as [| m rest IH]; simpl.
  - reflexivity.
  - rewrite fold_left_add_acc. rewrite IH. lia.
Qed.

(** =====================================================================
    Section 3: PARTITION IDENTITY
    ===================================================================== *)

(** CORE: total size partitions into kept + freed by any predicate. *)
Lemma sum_sizes_partition : forall objs (p : ObjectMeta -> bool),
  sum_sizes objs =
  sum_sizes (filter p objs) + sum_sizes (filter (fun m => negb (p m)) objs).
Proof.
  induction objs as [| m rest IH]; intros p; simpl.
  - reflexivity.
  - destruct (p m) eqn:Hp; simpl.
    + rewrite (IH p). lia.
    + rewrite (IH p). lia.
Qed.

(** freed_space in remove_object equals sum of matching elements. *)
Lemma freed_eq_sum_matching : forall objs oid,
  fold_left (fun acc m =>
    if Nat.eqb (om_id m) oid then acc + om_size m else acc) objs 0 =
  sum_sizes (filter (fun m => Nat.eqb (om_id m) oid) objs).
Proof.
  induction objs as [| m rest IH]; intros oid; simpl.
  - reflexivity.
  - destruct (Nat.eqb (om_id m) oid) eqn:Heq; simpl.
    + rewrite fold_left_selective_acc. rewrite IH. lia.
    + exact (IH oid).
Qed.

(** Freed space is at most the total size. *)
Lemma freed_le_sum : forall objs oid,
  sum_sizes (filter (fun m => Nat.eqb (om_id m) oid) objs) <=
  sum_sizes objs.
Proof.
  intros objs oid.
  rewrite (sum_sizes_partition objs (fun m => negb (Nat.eqb (om_id m) oid))).
  (* sum = kept + matching, so matching ≤ sum *)
  simpl.
  assert (H: forall m, negb (negb (Nat.eqb (om_id m) oid)) = Nat.eqb (om_id m) oid).
  { intros m. rewrite negb_involutive. reflexivity. }
  (* Need to show filter (negb ∘ negb ∘ ...) = filter (...) *)
  enough (Hfilt: filter (fun m => negb (negb (Nat.eqb (om_id m) oid))) objs =
                 filter (fun m => Nat.eqb (om_id m) oid) objs).
  { rewrite Hfilt. lia. }
  apply filter_ext. exact H.
Qed.

(** =====================================================================
    Section 4: CAPACITY COHERENCE DEFINITION AND PRESERVATION
    ===================================================================== *)

(** The capacity coherence invariant: seg_used faithfully tracks
    the total size of all objects on the segment. *)
Definition capacity_coherent (s : Segment) : Prop :=
  seg_used s = sum_sizes (seg_objects s).

(** Place preserves capacity coherence. *)
Lemma place_preserves_coherence : forall s m,
  capacity_coherent s ->
  capacity_coherent (place_object s m).
Proof.
  intros s m Hc. unfold capacity_coherent in *. simpl. lia.
Qed.

(** Remove preserves capacity coherence. *)
Lemma remove_preserves_coherence : forall s oid,
  capacity_coherent s ->
  capacity_coherent (remove_object s oid).
Proof.
  intros s oid Hc. unfold capacity_coherent in *. simpl.
  rewrite freed_eq_sum_matching. rewrite Hc.
  pose proof (sum_sizes_partition (seg_objects s)
    (fun m => Nat.eqb (om_id m) oid)) as Hpart.
  simpl in Hpart. lia.
Qed.

(** Status operations preserve capacity coherence. *)
Lemma set_status_preserves_coherence : forall s st,
  capacity_coherent s ->
  capacity_coherent (set_segment_status s st).
Proof.
  intros s st Hc. unfold capacity_coherent in *. simpl. exact Hc.
Qed.

(** update_object_meta preserves coherence when f preserves om_size. *)
Lemma update_preserves_coherence : forall s oid f,
  (forall m, om_size (f m) = om_size m) ->
  capacity_coherent s ->
  capacity_coherent (update_object_meta s oid f).
Proof.
  intros s oid f Hsize Hc. unfold capacity_coherent in *. simpl.
  rewrite Hc. clear Hc.
  induction (seg_objects s) as [| m rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb (om_id m) oid).
    + rewrite Hsize. rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

(** inc_refcnt preserves om_size. *)
(* Already in Diamond.v: inc_preserves_size, dec_preserves_size *)

(** =====================================================================
    Section 5: ENRICHED STEP PRESERVES COHERENCE
    ===================================================================== *)

(** Store-level capacity coherence. *)
Definition store_capacity_coherent (st : StoreState) : Prop :=
  capacity_coherent (ss_segment st).

(** HEADLINE: Every operation in the enriched LTS preserves
    capacity coherence.

    Place: adds om_size to both seg_used and objects
    Remove/Evict: subtracts freed from both
    BeginRead/EndRead: inc/dec_refcnt preserves om_size
    Status ops: no change to used or objects *)
Theorem step_preserves_coherence : forall st l st',
  store_capacity_coherent st ->
  rich_store_step st l st' ->
  store_capacity_coherent st'.
Proof.
  intros st l st' Hc Hstep. unfold store_capacity_coherent in *.
  inversion Hstep; subst; simpl in *.
  - (* rstep_place *)
    exact (place_preserves_coherence _ _ Hc).
  - (* rstep_remove *)
    exact (remove_preserves_coherence _ _ Hc).
  - (* rstep_begin_drain *)
    exact (set_status_preserves_coherence _ _ Hc).
  - (* rstep_complete_drain *)
    exact (set_status_preserves_coherence _ _ Hc).
  - (* rstep_unmount *)
    exact (set_status_preserves_coherence _ _ Hc).
  - (* rstep_begin_read — inc_refcnt preserves om_size *)
    unfold inc_segment_refcnt.
    exact (update_preserves_coherence _ _ _ inc_preserves_size Hc).
  - (* rstep_end_read — dec_refcnt preserves om_size *)
    unfold dec_segment_refcnt.
    exact (update_preserves_coherence _ _ _ dec_preserves_size Hc).
  - (* rstep_evict — same as remove *)
    exact (remove_preserves_coherence _ _ Hc).
Qed.

(** =====================================================================
    Section 6: SEGMENT WELL-FORMEDNESS
    ===================================================================== *)

(** Place preserves segment_wf when has_room was checked. *)
Lemma place_preserves_wf : forall s m,
  segment_wf s ->
  segment_has_room s (om_size m) = true ->
  segment_wf (place_object s m).
Proof.
  intros s m Hwf Hroom.
  unfold segment_wf, segment_has_room in *. simpl.
  apply Nat.leb_le in Hroom. exact Hroom.
Qed.

(** Remove preserves segment_wf when capacity is coherent. *)
Lemma remove_preserves_wf : forall s oid,
  segment_wf s ->
  capacity_coherent s ->
  segment_wf (remove_object s oid).
Proof.
  intros s oid Hwf Hc. unfold segment_wf, capacity_coherent in *. simpl.
  rewrite freed_eq_sum_matching.
  rewrite Hc.
  assert (Hle : sum_sizes (filter (fun m => Nat.eqb (om_id m) oid) (seg_objects s)) <=
                sum_sizes (seg_objects s))
    by exact (freed_le_sum (seg_objects s) oid).
  lia.
Qed.

(** Status operations preserve segment_wf. *)
Lemma set_status_preserves_wf : forall s st,
  segment_wf s ->
  segment_wf (set_segment_status s st).
Proof.
  intros s st Hwf. unfold segment_wf in *. simpl. exact Hwf.
Qed.

(** update_object_meta preserves segment_wf. *)
Lemma update_preserves_wf : forall s oid f,
  segment_wf s ->
  segment_wf (update_object_meta s oid f).
Proof.
  intros s oid f Hwf. unfold segment_wf in *. simpl. exact Hwf.
Qed.

(** =====================================================================
    Section 7: COMBINED WELL-FORMEDNESS INVARIANT
    ===================================================================== *)

(** The combined well-formedness predicate: every structural invariant
    the store should maintain. *)
Definition store_well_formed (st : StoreState) : Prop :=
  store_consistent st /\
  store_capacity_coherent st /\
  NoDup (map om_id (seg_objects (ss_segment st))).

(** HEADLINE: store_well_formed is preserved by every enriched step,
    provided that Place operations use fresh IDs. *)
Theorem step_preserves_well_formed : forall st l st',
  store_well_formed st ->
  place_fresh st l ->
  rich_store_step st l st' ->
  store_well_formed st'.
Proof.
  intros st l st' [Hsc [Hcc Hnd]] Hfresh Hstep.
  split; [| split].
  - exact (rich_step_preserves_consistency st l st' Hsc Hstep).
  - exact (step_preserves_coherence st l st' Hcc Hstep).
  - exact (nodup_step_preserved st l st' Hstep Hfresh Hnd).
Qed.

(** HEADLINE: store_well_formed is preserved through traces without
    Place operations.  Covers drain, read, and eviction traces.
    For traces with placements, use step_preserves_well_formed
    inductively with freshness evidence at each step. *)
Theorem well_formed_exec : forall st ls st',
  store_well_formed st ->
  exec st ls st' ->
  Forall (fun l => match l with RLPlace _ => False | _ => True end) ls ->
  store_well_formed st'.
Proof.
  intros st ls st' Hwf Hexec Hall.
  induction Hexec as [s | s l ls s_mid s_final Hstep Hexec IH].
  - exact Hwf.
  - inversion Hall as [| ? ? Hl Hls]; subst.
    apply IH; [| exact Hls].
    apply (step_preserves_well_formed s l s_mid Hwf).
    + destruct l; simpl; try exact I. contradiction.
    + exact Hstep.
Qed.
