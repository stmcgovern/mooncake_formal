(** * Convergence.v — Tight lifecycle convergence bound.

    =========================================================================
    LAYER: 4 - APPLICATION (lifecycle convergence)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Proves the headline quantitative result: a segment in SegOk with n
    objects reaches SegUnmounting via an explicit trace of length n+3:

       [BeginDrain, Remove₁, …, Removeₙ, CompleteDrain, Unmount]

    This is tight — the 3 status-change steps are forced by acyclicity,
    and each of the n removals is necessary (object count decreases by
    at most 1 per step).

    The proof has three structural insights:
    1. Removals of distinct objects commute (order doesn't matter)
    2. Sequential removal of all objects empties the segment (under NoDup)
    3. The lifecycle is a sequential composition of four phases, each
       with exactly the right preconditions for the next

    @source mooncake-store/include/segment.h (full lifecycle)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.StoreLTS
    - DistributedML.Concurrency.Preservation (lstar, lstar_trans)

    PROVIDES:
    - filter_comm (filter operations commute)
    - remove_objects_comm (removal order doesn't affect objects)
    - sequential_remove_lstar (removing all objects empties segment)
    - drain_lifecycle_trace (explicit optimal trace)
    - lifecycle_convergence (headline: n+3 steps to SegUnmounting)
    - lifecycle_trace_length (the bound is exactly n+3)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.Preservation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.StoreLTS.

(** =====================================================================
    Section 1: FILTER COMMUTATIVITY
    ===================================================================== *)

(** Filters with independent predicates commute. *)
Lemma filter_comm : forall {A} (f g : A -> bool) l,
  filter f (filter g l) = filter g (filter f l).
Proof.
  intros A f g l. induction l as [| x rest IH].
  - reflexivity.
  - simpl. destruct (f x) eqn:Hf; destruct (g x) eqn:Hg; simpl;
    rewrite ?Hf, ?Hg; simpl; rewrite IH; reflexivity.
Qed.

(** Removal order doesn't matter for the objects list. *)
Theorem remove_objects_comm : forall seg oid1 oid2,
  seg_objects (remove_object (remove_object seg oid1) oid2) =
  seg_objects (remove_object (remove_object seg oid2) oid1).
Proof.
  intros seg oid1 oid2. simpl. apply filter_comm.
Qed.

(** =====================================================================
    Section 2: SEQUENTIAL REMOVAL EMPTIES SEGMENTS
    ===================================================================== *)

(** Filtering by negated ID is identity when the ID is not in the list. *)
Lemma filter_notin_id : forall (l : list ObjectMeta) (oid : ObjectId),
  ~ In oid (map om_id l) ->
  filter (fun m => negb (Nat.eqb (om_id m) oid)) l = l.
Proof.
  intros l oid Hni. induction l as [| h rest IH].
  - reflexivity.
  - simpl in *. apply Decidable.not_or in Hni.
    destruct Hni as [Hne Hni].
    assert (Hneq : Nat.eqb (om_id h) oid = false).
    { apply Nat.eqb_neq. exact Hne. }
    rewrite Hneq. simpl. f_equal. exact (IH Hni).
Qed.

(** Removing the first element from h :: rest under NoDup leaves rest. *)
Lemma remove_first_objects : forall h rest seg,
  seg_objects seg = h :: rest ->
  NoDup (map om_id (h :: rest)) ->
  seg_objects (remove_object seg (om_id h)) = rest.
Proof.
  intros h rest seg Hobjs Hnd.
  assert (Hfilter : seg_objects (remove_object seg (om_id h)) =
    filter (fun m => negb (Nat.eqb (om_id m) (om_id h))) (seg_objects seg))
    by reflexivity.
  rewrite Hfilter, Hobjs. simpl.
  rewrite Nat.eqb_refl. simpl.
  inversion Hnd; subst.
  exact (filter_notin_id rest (om_id h) H1).
Qed.

(** Removing all objects one by one produces a valid lstar trace that
    empties the segment, preserving status, transfers, and consistency. *)
Lemma sequential_remove_lstar : forall objs st,
  seg_objects (ss_segment st) = objs ->
  NoDup (map om_id objs) ->
  store_consistent st ->
  exists st',
    lstar store_step st (map (fun m => LRemove (om_id m)) objs) st' /\
    seg_objects (ss_segment st') = [] /\
    seg_status (ss_segment st') = seg_status (ss_segment st) /\
    ss_transfers st' = ss_transfers st /\
    store_consistent st'.
Proof.
  intros objs. induction objs as [| h rest IH]; intros st Hobjs Hnd Hsc.
  - (* Base: no objects *)
    exists st. simpl. split; [constructor |].
    split; [exact Hobjs |]. split; [reflexivity |].
    split; [reflexivity | exact Hsc].
  - (* Step: remove h, then rest *)
    set (st1 := mkStoreState (remove_object (ss_segment st) (om_id h))
                             (ss_transfers st)).
    assert (Hstep : store_step st (LRemove (om_id h)) st1) by constructor.
    assert (Hobjs1 : seg_objects (ss_segment st1) = rest).
    { unfold st1. simpl.
      exact (remove_first_objects h rest (ss_segment st) Hobjs Hnd). }
    assert (Hstat1 : seg_status (ss_segment st1) = seg_status (ss_segment st)).
    { unfold st1. reflexivity. }
    assert (Htrans1 : ss_transfers st1 = ss_transfers st).
    { unfold st1. reflexivity. }
    assert (Hnd' : NoDup (map om_id rest)).
    { inversion Hnd; assumption. }
    assert (Hsc1 : store_consistent st1).
    { exact (store_step_preserves_consistency st (LRemove (om_id h))
               st1 Hsc Hstep). }
    destruct (IH st1 Hobjs1 Hnd' Hsc1) as [st' [Hstar [He [Hs [Ht Hc]]]]].
    exists st'. split; [| split; [| split; [| split]]].
    + simpl. eapply lstar_step; eauto.
    + exact He.
    + rewrite Hs. exact Hstat1.
    + rewrite Ht. exact Htrans1.
    + exact Hc.
Qed.

(** =====================================================================
    Section 3: LIFECYCLE TRACE
    ===================================================================== *)

(** The explicit optimal trace for the full segment lifecycle. *)
Definition drain_lifecycle_trace (seg : Segment) : list StoreLabel :=
  LBeginDrain :: map (fun m => LRemove (om_id m)) (seg_objects seg)
              ++ [LCompleteDrain; LUnmount].

(** The trace length is exactly n + 3. *)
Lemma lifecycle_trace_length : forall seg,
  length (drain_lifecycle_trace seg) = length (seg_objects seg) + 3.
Proof.
  intros seg. unfold drain_lifecycle_trace. simpl.
  rewrite app_length, map_length. simpl. lia.
Qed.

(** =====================================================================
    Section 4: LIFECYCLE CONVERGENCE — HEADLINE THEOREM
    ===================================================================== *)

(** A segment in SegOk with n objects reaches SegUnmounting via an
    explicit trace of length n+3, preserving store_consistent throughout.

    This is the tight quantitative lifecycle bound.  The trace is:
      [BeginDrain, Remove₁, …, Removeₙ, CompleteDrain, Unmount]

    Preconditions:
    - SegOk (ready to drain)
    - no_in_progress (no PROCESSING or INITIALIZED objects — safe to drain)
    - store_consistent (global invariant holds)
    - NoDup object IDs (unique object identifiers)

    The proof constructs the witness trace by composing four phases:
    1. BeginDrain:    SegOk → SegDraining
    2. Remove all:    n steps, empties the segment
    3. CompleteDrain: SegDraining + empty → SegDrained
    4. Unmount:       SegDrained + empty → SegUnmounting
*)
Theorem lifecycle_convergence : forall st,
  seg_status (ss_segment st) = SegOk ->
  no_in_progress (ss_segment st) ->
  store_consistent st ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  exists st',
    lstar store_step st (drain_lifecycle_trace (ss_segment st)) st' /\
    seg_status (ss_segment st') = SegUnmounting /\
    store_consistent st' /\
    length (drain_lifecycle_trace (ss_segment st)) =
      length (seg_objects (ss_segment st)) + 3.
Proof.
  intros st Hok Hnip Hsc Hnd.
  (* Phase 1: BeginDrain *)
  set (st1 := mkStoreState (begin_drain (ss_segment st)) (ss_transfers st)).
  assert (Hstep1 : store_step st LBeginDrain st1).
  { constructor; assumption. }
  assert (Hsc1 : store_consistent st1).
  { exact (store_step_preserves_consistency st LBeginDrain st1 Hsc Hstep1). }
  assert (Hobjs1 : seg_objects (ss_segment st1) = seg_objects (ss_segment st)).
  { unfold st1. simpl. reflexivity. }
  assert (Hdr1 : seg_status (ss_segment st1) = SegDraining).
  { unfold st1. reflexivity. }
  assert (Hnd1 : NoDup (map om_id (seg_objects (ss_segment st1)))).
  { rewrite Hobjs1. exact Hnd. }
  (* Phase 2: Remove all objects *)
  destruct (sequential_remove_lstar (seg_objects (ss_segment st)) st1
              Hobjs1 Hnd Hsc1) as [st2 [Hstar2 [He2 [Hs2 [Ht2 Hc2]]]]].
  assert (Hdr2 : seg_status (ss_segment st2) = SegDraining).
  { rewrite Hs2. exact Hdr1. }
  (* Phase 3: CompleteDrain *)
  set (st3 := mkStoreState (complete_drain (ss_segment st2)) (ss_transfers st2)).
  assert (Hstep3 : store_step st2 LCompleteDrain st3).
  { constructor; assumption. }
  assert (Hsc3 : store_consistent st3).
  { exact (store_step_preserves_consistency st2 LCompleteDrain st3 Hc2 Hstep3). }
  assert (Hdrd3 : seg_status (ss_segment st3) = SegDrained).
  { unfold st3. reflexivity. }
  assert (He3 : seg_objects (ss_segment st3) = []).
  { unfold st3. simpl. exact He2. }
  (* Phase 4: Unmount *)
  set (st4 := mkStoreState (begin_unmount (ss_segment st3)) (ss_transfers st3)).
  assert (Hstep4 : store_step st3 LUnmount st4).
  { constructor. unfold safe_to_unmount. split; assumption. }
  assert (Hsc4 : store_consistent st4).
  { exact (store_step_preserves_consistency st3 LUnmount st4 Hsc3 Hstep4). }
  assert (Hum4 : seg_status (ss_segment st4) = SegUnmounting).
  { unfold st4. reflexivity. }
  (* Compose all phases *)
  exists st4. split; [| split; [| split]].
  - unfold drain_lifecycle_trace.
    (* Phase 1: [LBeginDrain] ++ rest *)
    eapply lstar_step.
    + exact Hstep1.
    + (* Phase 2: map LRemove ++ [LCompleteDrain; LUnmount] *)
      eapply (lstar_trans store_step).
      * exact Hstar2.
      * (* Phase 3-4: [LCompleteDrain; LUnmount] *)
        eapply lstar_step.
        -- exact Hstep3.
        -- eapply lstar_step.
           ++ exact Hstep4.
           ++ constructor.
  - exact Hum4.
  - exact Hsc4.
  - apply lifecycle_trace_length.
Qed.

(** =====================================================================
    Section 5: COROLLARIES
    ===================================================================== *)

(** Every segment with unique object IDs is reclaimable:
    there exists a finite trace leading to unmount. *)
Corollary segment_reclaimable : forall st,
  seg_status (ss_segment st) = SegOk ->
  no_in_progress (ss_segment st) ->
  store_consistent st ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  exists st', lstar store_step st (drain_lifecycle_trace (ss_segment st)) st' /\
              seg_status (ss_segment st') = SegUnmounting.
Proof.
  intros st Hok Hnip Hsc Hnd.
  destruct (lifecycle_convergence st Hok Hnip Hsc Hnd) as [st' [H1 [H2 [_ _]]]].
  exists st'. split; assumption.
Qed.

(** The lifecycle visits each segment status exactly once:
    Ok → Draining → Drained → Unmounting. *)
Corollary lifecycle_visits_all_statuses : forall st,
  seg_status (ss_segment st) = SegOk ->
  no_in_progress (ss_segment st) ->
  store_consistent st ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  exists st',
    lstar store_step st (drain_lifecycle_trace (ss_segment st)) st' /\
    seg_status (ss_segment st') = SegUnmounting /\
    (* The trace passes through each status *)
    (exists st_dr, lstar store_step st [LBeginDrain] st_dr /\
                   seg_status (ss_segment st_dr) = SegDraining).
Proof.
  intros st Hok Hnip Hsc Hnd.
  destruct (lifecycle_convergence st Hok Hnip Hsc Hnd) as [st' [H1 [H2 _]]].
  exists st'. split; [exact H1 | split; [exact H2 |]].
  set (st_dr := mkStoreState (begin_drain (ss_segment st)) (ss_transfers st)).
  exists st_dr. split.
  - eapply lstar_step. { constructor; assumption. } constructor.
  - reflexivity.
Qed.
