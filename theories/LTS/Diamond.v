(** * Diamond.v — Commutativity of independent operations.

    =========================================================================
    LAYER: 3-4 - DOMAIN/APPLICATION (confluent concurrency)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Proves the DIAMOND PROPERTY for independent operations in the
    enriched LTS: operations targeting different objects commute.
    Executing l1 then l2 reaches the same state as l2 then l1.

    This reveals that the Mooncake store has a partially commutative
    monoid of operations — scheduling order does not affect the final
    state for independent operations.

    The proof factors into three layers:
    1. List-level: filter and map on different IDs commute
    2. Accounting: freed-space computation is independent of non-matching ops
    3. Segment-level: segment operations on different IDs commute

    @source mooncake-store/src/master_service.cpp (concurrent operations)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.Convergence (filter_comm)

    PROVIDES:
    - filter_map_comm_neq (filter and map on different IDs commute)
    - map_map_comm_neq (maps on different IDs commute)
    - freed_filter_independent (freed-space unaffected by filtering other ID)
    - freed_map_independent (freed-space unaffected by mapping other ID)
    - remove_update_seg_comm (remove and update commute at segment level)
    - update_update_seg_comm (updates commute at segment level)
    - remove_remove_seg_comm (removes commute at segment level, full equality)
    - concurrent_reads_diamond (HEADLINE: concurrent reads commute)
    - evict_read_diamond (HEADLINE: eviction and read commute)
    - remove_remove_diamond (HEADLINE: concurrent removals commute)
    - evict_evict_diamond (HEADLINE: concurrent evictions commute)
    - remove_read_diamond (HEADLINE: removal and read commute)
    - end_read_end_read_diamond (HEADLINE: concurrent end-reads commute)
    - begin_read_end_read_diamond (HEADLINE: begin-read and end-read commute)
    - evict_end_read_diamond (HEADLINE: eviction and end-read commute)
    - remove_end_read_diamond (HEADLINE: removal and end-read commute)
    - general_object_diamond (HEADLINE: all object ops on different IDs commute)
    - drain_read_diamond, drain_evict_diamond (status-object diamonds)
    - read_session_transparent (HEADLINE: BeginRead;EndRead = identity)
    - read_session_store_transparent (HEADLINE: store-level read transparency)
*)

Require Import List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Convergence.

(** =====================================================================
    Section 1: LIST-LEVEL COMMUTATIVITY
    ===================================================================== *)

(** Filter by one ID commutes with map on a different ID. *)
Lemma filter_map_comm_neq :
  forall (objs : list ObjectMeta) oid_f oid_m (f : ObjectMeta -> ObjectMeta),
  oid_f <> oid_m ->
  (forall m, om_id (f m) = om_id m) ->
  filter (fun x => negb (Nat.eqb (om_id x) oid_f))
    (map (fun x => if Nat.eqb (om_id x) oid_m then f x else x) objs)
  = map (fun x => if Nat.eqb (om_id x) oid_m then f x else x)
      (filter (fun x => negb (Nat.eqb (om_id x) oid_f)) objs).
Proof.
  intros objs oid_f oid_m f Hneq Hpres.
  induction objs as [| h rest IH].
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (om_id h) oid_m) eqn:Hm;
    destruct (Nat.eqb (om_id h) oid_f) eqn:Hf; simpl.
    + (* om_id h = oid_m AND om_id h = oid_f: impossible *)
      apply Nat.eqb_eq in Hm. apply Nat.eqb_eq in Hf.
      exfalso. apply Hneq. congruence.
    + (* om_id h = oid_m, ≠ oid_f: map applies f, filter keeps *)
      rewrite Hpres. rewrite Hf. simpl. rewrite Hm. simpl. f_equal. exact IH.
    + (* om_id h = oid_f, ≠ oid_m: filter removes, map leaves *)
      exact IH.
    + (* om_id h ≠ oid_m, ≠ oid_f: both leave unchanged *)
      rewrite Hm. simpl. f_equal. exact IH.
Qed.

(** Maps on different IDs commute. *)
Lemma map_map_comm_neq :
  forall (objs : list ObjectMeta) oid1 oid2
    (f g : ObjectMeta -> ObjectMeta),
  oid1 <> oid2 ->
  (forall m, om_id (f m) = om_id m) ->
  (forall m, om_id (g m) = om_id m) ->
  map (fun x => if Nat.eqb (om_id x) oid1 then f x else x)
    (map (fun x => if Nat.eqb (om_id x) oid2 then g x else x) objs)
  = map (fun x => if Nat.eqb (om_id x) oid2 then g x else x)
      (map (fun x => if Nat.eqb (om_id x) oid1 then f x else x) objs).
Proof.
  intros objs oid1 oid2 f g Hneq Hpf Hpg.
  induction objs as [| h rest IH].
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (om_id h) oid1) eqn:H1;
    destruct (Nat.eqb (om_id h) oid2) eqn:H2; simpl.
    + (* Both match: impossible since oid1 ≠ oid2 *)
      apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
      exfalso. apply Hneq. congruence.
    + (* h matches oid1 only *)
      rewrite Hpf. rewrite H2. simpl. rewrite H1. f_equal. exact IH.
    + (* h matches oid2 only *)
      rewrite Hpg. rewrite H1. f_equal. exact IH.
    + (* h matches neither *)
      rewrite H1. f_equal. exact IH.
Qed.

(** =====================================================================
    Section 2: ACCOUNTING INDEPENDENCE
    ===================================================================== *)

(** Freed-space computation is unaffected by filtering a different ID. *)
Lemma freed_filter_independent :
  forall objs oid_freed oid_filter init,
  oid_freed <> oid_filter ->
  fold_left (fun acc m =>
    if Nat.eqb (om_id m) oid_freed then acc + om_size m else acc)
    (filter (fun m => negb (Nat.eqb (om_id m) oid_filter)) objs) init
  = fold_left (fun acc m =>
      if Nat.eqb (om_id m) oid_freed then acc + om_size m else acc)
      objs init.
Proof.
  intros objs oid_freed oid_filter.
  induction objs as [| h rest IH]; intros init Hneq.
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (om_id h) oid_filter) eqn:Hfilt; simpl.
    + (* h is filtered out — but fold also skips it *)
      destruct (Nat.eqb (om_id h) oid_freed) eqn:Hfreed.
      * apply Nat.eqb_eq in Hfreed. apply Nat.eqb_eq in Hfilt.
        exfalso. apply Hneq. congruence.
      * apply IH. exact Hneq.
    + (* h is kept by filter *)
      destruct (Nat.eqb (om_id h) oid_freed) eqn:Hfreed;
      apply IH; exact Hneq.
Qed.

(** Freed-space computation is unaffected by mapping a different ID
    (when the map preserves sizes). *)
Lemma freed_map_independent :
  forall objs oid_freed oid_map (f : ObjectMeta -> ObjectMeta) init,
  oid_freed <> oid_map ->
  (forall m, om_id (f m) = om_id m) ->
  (forall m, om_size (f m) = om_size m) ->
  fold_left (fun acc m =>
    if Nat.eqb (om_id m) oid_freed then acc + om_size m else acc)
    (map (fun x => if Nat.eqb (om_id x) oid_map then f x else x) objs) init
  = fold_left (fun acc m =>
      if Nat.eqb (om_id m) oid_freed then acc + om_size m else acc)
      objs init.
Proof.
  intros objs oid_freed oid_map f.
  induction objs as [| h rest IH]; intros init Hneq Hpid Hpsz.
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (om_id h) oid_map) eqn:Hmap; simpl.
    + (* h is mapped to f(h) *)
      rewrite Hpid.
      destruct (Nat.eqb (om_id h) oid_freed) eqn:Hfreed.
      * (* om_id h = oid_freed AND oid_map: impossible *)
        apply Nat.eqb_eq in Hfreed. apply Nat.eqb_eq in Hmap.
        exfalso. apply Hneq. congruence.
      * apply IH; assumption.
    + (* h is unchanged *)
      destruct (Nat.eqb (om_id h) oid_freed) eqn:Hfreed;
      apply IH; assumption.
Qed.

(** Auxiliary: inc_refcnt and dec_refcnt preserve om_size. *)
Lemma inc_preserves_size : forall m, om_size (inc_refcnt m) = om_size m.
Proof. reflexivity. Qed.

Lemma dec_preserves_size : forall m, om_size (dec_refcnt m) = om_size m.
Proof. reflexivity. Qed.

(** =====================================================================
    Section 3: SEGMENT-LEVEL COMMUTATIVITY
    ===================================================================== *)

(** update_object_meta on different IDs commute. *)
Theorem update_update_seg_comm :
  forall seg oid1 oid2 (f g : ObjectMeta -> ObjectMeta),
  oid1 <> oid2 ->
  (forall m, om_id (f m) = om_id m) ->
  (forall m, om_id (g m) = om_id m) ->
  update_object_meta (update_object_meta seg oid1 f) oid2 g =
  update_object_meta (update_object_meta seg oid2 g) oid1 f.
Proof.
  intros [id st cap used objs] oid1 oid2 f g Hneq Hpf Hpg.
  unfold update_object_meta. simpl. f_equal.
  apply map_map_comm_neq; auto using not_eq_sym.
Qed.

(** remove_object and update_object_meta on different IDs commute. *)
Theorem remove_update_seg_comm :
  forall seg oid_rm oid_up (f : ObjectMeta -> ObjectMeta),
  oid_rm <> oid_up ->
  (forall m, om_id (f m) = om_id m) ->
  (forall m, om_size (f m) = om_size m) ->
  remove_object (update_object_meta seg oid_up f) oid_rm =
  update_object_meta (remove_object seg oid_rm) oid_up f.
Proof.
  intros [id st cap used objs] oid_rm oid_up f Hneq Hpid Hpsz.
  unfold remove_object, update_object_meta. simpl. f_equal.
  - (* seg_used: freed is independent of the map *)
    f_equal. apply freed_map_independent; assumption.
  - (* seg_objects: filter and map commute *)
    apply filter_map_comm_neq; assumption.
Qed.

(** remove_object on different IDs commute (full segment equality).
    Extends Convergence.remove_objects_comm from seg_objects to full segment. *)
Theorem remove_remove_seg_comm : forall seg oid1 oid2,
  oid1 <> oid2 ->
  remove_object (remove_object seg oid1) oid2 =
  remove_object (remove_object seg oid2) oid1.
Proof.
  intros [id st cap used objs] oid1 oid2 Hneq.
  unfold remove_object. simpl. f_equal.
  - (* seg_used: freed accounting commutes *)
    rewrite (freed_filter_independent objs oid2 oid1 0
               (fun H => Hneq (eq_sym H))).
    rewrite (freed_filter_independent objs oid1 oid2 0 Hneq).
    lia.
  - (* seg_objects: filter commutes *)
    apply filter_comm.
Qed.

(** Status changes commute with update_object_meta. *)
Lemma status_update_comm :
  forall seg new_st oid (f : ObjectMeta -> ObjectMeta),
  set_segment_status (update_object_meta seg oid f) new_st =
  update_object_meta (set_segment_status seg new_st) oid f.
Proof.
  intros [id st cap used objs] new_st oid f.
  reflexivity.
Qed.

(** Status changes commute with remove_object. *)
Lemma status_remove_comm :
  forall seg new_st oid,
  set_segment_status (remove_object seg oid) new_st =
  remove_object (set_segment_status seg new_st) oid.
Proof.
  intros [id st cap used objs] new_st oid.
  reflexivity.
Qed.

(** =====================================================================
    Section 4: DIAMOND PROPERTY — HEADLINE THEOREMS
    ===================================================================== *)

(** Concurrent reads on different objects commute.
    BeginRead(A) then BeginRead(B) = BeginRead(B) then BeginRead(A). *)
Theorem concurrent_reads_diamond :
  forall st oid1 oid2 st1 st2 st12 st21,
  oid1 <> oid2 ->
  rich_store_step st (RLBeginRead oid1) st1 ->
  rich_store_step st1 (RLBeginRead oid2) st12 ->
  rich_store_step st (RLBeginRead oid2) st2 ->
  rich_store_step st2 (RLBeginRead oid1) st21 ->
  st12 = st21.
Proof.
  intros st oid1 oid2 st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold inc_segment_refcnt.
  apply update_update_seg_comm; try exact inc_preserves_id. exact Hneq.
Qed.

(** Eviction and reading on different objects commute.
    Evict(A) then BeginRead(B) = BeginRead(B) then Evict(A). *)
Theorem evict_read_diamond :
  forall st oid_e oid_r st1 st2 st12 st21,
  oid_e <> oid_r ->
  rich_store_step st (RLEvict oid_e) st1 ->
  rich_store_step st1 (RLBeginRead oid_r) st12 ->
  rich_store_step st (RLBeginRead oid_r) st2 ->
  rich_store_step st2 (RLEvict oid_e) st21 ->
  st12 = st21.
Proof.
  intros st oid_e oid_r st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold inc_segment_refcnt.
  symmetry. apply remove_update_seg_comm; try exact inc_preserves_id.
  exact Hneq. exact inc_preserves_size.
Qed.

(** Removals of different objects commute (during drain).
    Remove(A) then Remove(B) = Remove(B) then Remove(A). *)
Theorem remove_remove_diamond :
  forall st oid1 oid2 st1 st2 st12 st21,
  oid1 <> oid2 ->
  rich_store_step st (RLRemove oid1) st1 ->
  rich_store_step st1 (RLRemove oid2) st12 ->
  rich_store_step st (RLRemove oid2) st2 ->
  rich_store_step st2 (RLRemove oid1) st21 ->
  st12 = st21.
Proof.
  intros st oid1 oid2 st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  apply remove_remove_seg_comm. exact Hneq.
Qed.

(** Evictions of different objects commute.
    Evict(A) then Evict(B) = Evict(B) then Evict(A). *)
Theorem evict_evict_diamond :
  forall st oid1 oid2 st1 st2 st12 st21,
  oid1 <> oid2 ->
  rich_store_step st (RLEvict oid1) st1 ->
  rich_store_step st1 (RLEvict oid2) st12 ->
  rich_store_step st (RLEvict oid2) st2 ->
  rich_store_step st2 (RLEvict oid1) st21 ->
  st12 = st21.
Proof.
  intros st oid1 oid2 st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  apply remove_remove_seg_comm. exact Hneq.
Qed.

(** Removal and reading on different objects commute (drain + read).
    Remove(A) then BeginRead(B) = BeginRead(B) then Remove(A). *)
Theorem remove_read_diamond :
  forall st oid_rm oid_rd st1 st2 st12 st21,
  oid_rm <> oid_rd ->
  rich_store_step st (RLRemove oid_rm) st1 ->
  rich_store_step st1 (RLBeginRead oid_rd) st12 ->
  rich_store_step st (RLBeginRead oid_rd) st2 ->
  rich_store_step st2 (RLRemove oid_rm) st21 ->
  st12 = st21.
Proof.
  intros st oid_rm oid_rd st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold inc_segment_refcnt.
  symmetry. apply remove_update_seg_comm; try exact inc_preserves_id.
  exact Hneq. exact inc_preserves_size.
Qed.

(** EndRead operations on different objects commute.
    EndRead(A) then EndRead(B) = EndRead(B) then EndRead(A). *)
Theorem end_read_end_read_diamond :
  forall st oid1 oid2 st1 st2 st12 st21,
  oid1 <> oid2 ->
  rich_store_step st (RLEndRead oid1) st1 ->
  rich_store_step st1 (RLEndRead oid2) st12 ->
  rich_store_step st (RLEndRead oid2) st2 ->
  rich_store_step st2 (RLEndRead oid1) st21 ->
  st12 = st21.
Proof.
  intros st oid1 oid2 st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold dec_segment_refcnt.
  apply update_update_seg_comm; auto using dec_preserves_id, not_eq_sym.
Qed.

(** BeginRead and EndRead on different objects commute.
    BeginRead(A) then EndRead(B) = EndRead(B) then BeginRead(A). *)
Theorem begin_read_end_read_diamond :
  forall st oid_br oid_er st1 st2 st12 st21,
  oid_br <> oid_er ->
  rich_store_step st (RLBeginRead oid_br) st1 ->
  rich_store_step st1 (RLEndRead oid_er) st12 ->
  rich_store_step st (RLEndRead oid_er) st2 ->
  rich_store_step st2 (RLBeginRead oid_br) st21 ->
  st12 = st21.
Proof.
  intros st oid_br oid_er st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold inc_segment_refcnt, dec_segment_refcnt.
  apply update_update_seg_comm; auto using inc_preserves_id, dec_preserves_id.
Qed.

(** Eviction and EndRead on different objects commute.
    Evict(A) then EndRead(B) = EndRead(B) then Evict(A). *)
Theorem evict_end_read_diamond :
  forall st oid_e oid_er st1 st2 st12 st21,
  oid_e <> oid_er ->
  rich_store_step st (RLEvict oid_e) st1 ->
  rich_store_step st1 (RLEndRead oid_er) st12 ->
  rich_store_step st (RLEndRead oid_er) st2 ->
  rich_store_step st2 (RLEvict oid_e) st21 ->
  st12 = st21.
Proof.
  intros st oid_e oid_er st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold dec_segment_refcnt.
  symmetry. apply remove_update_seg_comm; try exact dec_preserves_id.
  exact Hneq. exact dec_preserves_size.
Qed.

(** Removal and EndRead on different objects commute.
    Remove(A) then EndRead(B) = EndRead(B) then Remove(A). *)
Theorem remove_end_read_diamond :
  forall st oid_rm oid_er st1 st2 st12 st21,
  oid_rm <> oid_er ->
  rich_store_step st (RLRemove oid_rm) st1 ->
  rich_store_step st1 (RLEndRead oid_er) st12 ->
  rich_store_step st (RLEndRead oid_er) st2 ->
  rich_store_step st2 (RLRemove oid_rm) st21 ->
  st12 = st21.
Proof.
  intros st oid_rm oid_er st1 st2 st12 st21 Hneq H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  simpl. f_equal.
  unfold dec_segment_refcnt.
  symmetry. apply remove_update_seg_comm; try exact dec_preserves_id.
  exact Hneq. exact dec_preserves_size.
Qed.

(** =====================================================================
    Section 5: STATUS-OBJECT DIAMONDS
    ===================================================================== *)

(** =====================================================================
    Section 6: GENERAL DIAMOND — CAPSTONE THEOREM
    ===================================================================== *)

(** Classifies labels that modify a specific object's metadata. *)
Inductive object_op : RichStoreLabel -> ObjectId -> Prop :=
  | oop_begin_read : forall oid, object_op (RLBeginRead oid) oid
  | oop_end_read : forall oid, object_op (RLEndRead oid) oid
  | oop_evict : forall oid, object_op (RLEvict oid) oid
  | oop_remove : forall oid, object_op (RLRemove oid) oid.

(** HEADLINE: All object operations on different objects commute.

    This is the general diamond property — the capstone of Diamond.v.
    Rather than proving each pair individually, this single theorem
    covers all 16 combinations of {BeginRead, EndRead, Evict, Remove}
    on different objects. *)
Theorem general_object_diamond :
  forall st l1 l2 oid1 oid2 st1 st2 st12 st21,
  object_op l1 oid1 ->
  object_op l2 oid2 ->
  oid1 <> oid2 ->
  rich_store_step st l1 st1 ->
  rich_store_step st1 l2 st12 ->
  rich_store_step st l2 st2 ->
  rich_store_step st2 l1 st21 ->
  st12 = st21.
Proof.
  intros st l1 l2 oid1 oid2 st1 st2 st12 st21 Hop1 Hop2 Hneq H1 H12 H2 H21.
  inversion Hop1; subst; inversion Hop2; subst;
  inversion H1; subst; inversion H12; subst;
  inversion H2; subst; inversion H21; subst;
  simpl; f_equal;
  unfold inc_segment_refcnt, dec_segment_refcnt;
  first
    [ apply remove_remove_seg_comm; exact Hneq
    | apply update_update_seg_comm;
      auto using inc_preserves_id, dec_preserves_id, not_eq_sym
    | symmetry; apply remove_update_seg_comm;
      auto using inc_preserves_id, dec_preserves_id,
                 inc_preserves_size, dec_preserves_size
    | apply remove_update_seg_comm;
      auto using inc_preserves_id, dec_preserves_id,
                 inc_preserves_size, dec_preserves_size
    ].
Qed.

(** =====================================================================
    Section 7: STATUS-OBJECT DIAMONDS
    ===================================================================== *)

(** BeginDrain commutes with BeginRead.
    Draining a segment while starting a read — order doesn't matter. *)
Theorem drain_read_diamond :
  forall st oid st1 st2 st12 st21,
  rich_store_step st RLBeginDrain st1 ->
  rich_store_step st1 (RLBeginRead oid) st12 ->
  rich_store_step st (RLBeginRead oid) st2 ->
  rich_store_step st2 RLBeginDrain st21 ->
  st12 = st21.
Proof.
  intros st oid st1 st2 st12 st21 H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  reflexivity.
Qed.

(** BeginDrain commutes with EndRead. *)
Theorem drain_end_read_diamond :
  forall st oid st1 st2 st12 st21,
  rich_store_step st RLBeginDrain st1 ->
  rich_store_step st1 (RLEndRead oid) st12 ->
  rich_store_step st (RLEndRead oid) st2 ->
  rich_store_step st2 RLBeginDrain st21 ->
  st12 = st21.
Proof.
  intros st oid st1 st2 st12 st21 H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  reflexivity.
Qed.

(** BeginDrain commutes with Evict. *)
Theorem drain_evict_diamond :
  forall st oid st1 st2 st12 st21,
  rich_store_step st RLBeginDrain st1 ->
  rich_store_step st1 (RLEvict oid) st12 ->
  rich_store_step st (RLEvict oid) st2 ->
  rich_store_step st2 RLBeginDrain st21 ->
  st12 = st21.
Proof.
  intros st oid st1 st2 st12 st21 H1 H12 H2 H21.
  inversion H1; subst. inversion H12; subst.
  inversion H2; subst. inversion H21; subst.
  reflexivity.
Qed.

(** BeginDrain commutes with Remove. *)
Theorem drain_remove_diamond :
  forall st oid st1 st2 st12 st21,
  rich_store_step st RLBeginDrain st1 ->
  rich_store_step st1 (RLRemove oid) st12 ->
  rich_store_step st (RLRemove oid) st2 ->
  rich_store_step st2 RLBeginDrain st21 ->
  st12 = st21.
Proof.
  intros st oid st1 st2 st12 st21 Hd Hr H2 H21.
  inversion Hd; subst. inversion Hr; subst.
  inversion H2; subst. inversion H21; subst.
  reflexivity.
Qed.

(** =====================================================================
    Section 8: READ SESSION TRANSPARENCY
    ===================================================================== *)

(** dec_refcnt is a left inverse of inc_refcnt.
    This is the object-level cancellation: incrementing then
    decrementing the refcount returns to the original metadata. *)
Lemma dec_refcnt_inc_refcnt : forall m : ObjectMeta,
  dec_refcnt (inc_refcnt m) = m.
Proof.
  intros [oid seg st pin rc sz]. unfold dec_refcnt, inc_refcnt. simpl.
  f_equal. lia.
Qed.

(** The composed update function (inc then dec on same ID) is pointwise
    the identity. *)
Lemma update_inc_dec_pointwise : forall x oid,
  (fun m => if Nat.eqb (om_id m) oid then dec_refcnt m else m)
    ((fun m => if Nat.eqb (om_id m) oid then inc_refcnt m else m) x)
  = x.
Proof.
  intros x oid. simpl.
  destruct (Nat.eqb (om_id x) oid) eqn:Heq.
  - rewrite inc_preserves_id. rewrite Heq.
    apply dec_refcnt_inc_refcnt.
  - rewrite Heq. reflexivity.
Qed.

(** HEADLINE: A read session (BeginRead then EndRead on the same object)
    is transparent — it returns the segment to its original state.

    This is the algebraic essence of read sessions in Mooncake:
    reads temporarily protect an object (via refcount) but leave no
    permanent trace.  The protocol is reversible by design. *)
Theorem read_session_transparent : forall seg oid,
  dec_segment_refcnt (inc_segment_refcnt seg oid) oid = seg.
Proof.
  intros [id st cap used objs] oid.
  unfold dec_segment_refcnt, inc_segment_refcnt, update_object_meta. simpl.
  f_equal. rewrite map_map.
  induction objs as [| h rest IH].
  - reflexivity.
  - simpl. rewrite (update_inc_dec_pointwise h oid).
    f_equal. exact IH.
Qed.

(** At the store level: BeginRead followed by EndRead on the same
    object returns to the exact starting state. *)
Theorem read_session_store_transparent : forall st oid st1 st2,
  rich_store_step st (RLBeginRead oid) st1 ->
  rich_store_step st1 (RLEndRead oid) st2 ->
  st = st2.
Proof.
  intros st oid st1 st2 Hbegin Hend.
  inversion Hbegin; subst. inversion Hend; subst. simpl.
  rewrite read_session_transparent. destruct st; reflexivity.
Qed.
