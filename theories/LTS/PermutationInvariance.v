(** * PermutationInvariance.v -- The one theorem they're all shadows of.

    =========================================================================
    LAYER: 4 - APPLICATION (algebraic capstone)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    We proved 40 diamond theorems, unified them into one
    (independent_diamond), and proved adjacent swaps preserve results
    (swap_preserves_result).  But these are all shadows of the real
    theorem:

      Any permutation of object operations on pairwise-different
      targets produces the same final state.

    This is the Cartier-Foata theorem (1969) for the Mooncake store:
    scheduling order is irrelevant for independent operations.

    The proof requires one genuinely new lemma: the BACKWARD FRAME.
    The forward frame says "non-targeting operations preserve
    find_object forward."  The backward frame says the reverse:
    "if an object is findable AFTER a non-targeting operation, it was
    findable BEFORE."  This enables executability transfer: if l1;l2
    is executable and they target different objects, then l2;l1 is
    also executable.

    @source mooncake-store/src/master_service.cpp (concurrent operations)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.Diamond
    - MooncakeFormal.LTS.ProtectionFrame
    - MooncakeFormal.LTS.TraceEquivalence

    PROVIDES:
    - find_backward_filter (backward frame for filter)
    - find_backward_map (backward frame for map)
    - non_targeting_preserves_find_backward (CORE: backward frame)
    - object_op_swap_executable (executability transfer for object ops)
    - permutation_invariance (HEADLINE: permutation of independent ops)
*)

Require Import List Arith Lia.
Import ListNotations.
Require Import Permutation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Diamond.
Require Import MooncakeFormal.LTS.ProtectionFrame.
Require Import MooncakeFormal.LTS.TraceEquivalence.

(** =====================================================================
    Section 1: BACKWARD FRAME — the new key lemma
    ===================================================================== *)

(** If an object is findable in a filtered list, it was findable
    in the original list (filter only removes elements). *)
Lemma find_backward_filter : forall objs oid oid' m,
  oid <> oid' ->
  find_object_in
    (filter (fun x => negb (Nat.eqb (om_id x) oid')) objs) oid = Some m ->
  find_object_in objs oid = Some m.
Proof.
  induction objs as [| h rest IH]; intros oid oid' m Hneq Hfind.
  - simpl in Hfind. discriminate.
  - simpl in *. destruct (Nat.eqb (om_id h) oid') eqn:Hmatch.
    + (* h matches oid' — filtered out, search continues in rest *)
      simpl in Hfind.
      destruct (Nat.eqb (om_id h) oid) eqn:Hid.
      * (* om_id h = oid but also om_id h = oid' — contradiction with oid ≠ oid' *)
        apply Nat.eqb_eq in Hmatch. apply Nat.eqb_eq in Hid.
        exfalso. apply Hneq. rewrite <- Hid. exact Hmatch.
      * exact (IH oid oid' m Hneq Hfind).
    + (* h doesn't match oid' — h is in filtered list *)
      simpl in Hfind. destruct (Nat.eqb (om_id h) oid) eqn:Hid.
      * exact Hfind.
      * exact (IH oid oid' m Hneq Hfind).
Qed.

(** For different IDs, conditional map is invisible to find_object_in.
    This gives both forward and backward frame in one lemma. *)
Lemma find_map_neq_eq : forall objs oid oid' f,
  oid <> oid' ->
  (forall x, om_id (f x) = om_id x) ->
  find_object_in
    (map (fun x => if Nat.eqb (om_id x) oid' then f x else x) objs) oid =
  find_object_in objs oid.
Proof.
  induction objs as [| h rest IH]; intros oid oid' f Hneq Hpres.
  - reflexivity.
  - simpl. destruct (Nat.eqb (om_id h) oid') eqn:Hmatch.
    + (* h matches oid' — mapped to f h *)
      rewrite (Hpres h).
      destruct (Nat.eqb (om_id h) oid) eqn:Hid.
      * (* om_id h = oid AND om_id h = oid' — contradiction *)
        apply Nat.eqb_eq in Hmatch. apply Nat.eqb_eq in Hid.
        exfalso. apply Hneq. rewrite <- Hid. exact Hmatch.
      * exact (IH oid oid' f Hneq Hpres).
    + (* h doesn't match oid' — unchanged *)
      destruct (Nat.eqb (om_id h) oid); [reflexivity |].
      exact (IH oid oid' f Hneq Hpres).
Qed.

(** CORE: The backward frame theorem.

    If a rich_store_step does not target oid, and find_object succeeds
    in the post-state, then find_object succeeded in the pre-state
    with the same metadata.

    This is the reverse direction of non_targeting_preserves_find. *)
Theorem non_targeting_preserves_find_backward : forall st l st' oid m,
  rich_store_step st l st' ->
  label_targets l oid = false ->
  find_object (ss_segment st') oid = Some m ->
  find_object (ss_segment st) oid = Some m.
Proof.
  intros st l st' oid m Hstep Hnt Hfind.
  inversion Hstep; subst; simpl in *.
  - (* rstep_place m0 — find in m0 :: objects *)
    unfold find_object in *. simpl in *.
    apply Nat.eqb_neq in Hnt.
    destruct (Nat.eqb (om_id m0) oid) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hnt. exact E.
    + exact Hfind.
  - (* rstep_remove oid0 *)
    unfold find_object in *. simpl in *.
    apply Nat.eqb_neq in Hnt.
    exact (find_backward_filter _ _ _ _ (not_eq_sym Hnt) Hfind).
  - (* rstep_begin_drain — set_segment_status preserves objects *)
    exact Hfind.
  - (* rstep_complete_drain *)
    exact Hfind.
  - (* rstep_unmount *)
    exact Hfind.
  - (* rstep_begin_read oid0 — inc_segment_refcnt *)
    unfold find_object, inc_segment_refcnt, update_object_meta in *. simpl in *.
    apply Nat.eqb_neq in Hnt.
    rewrite find_map_neq_eq in Hfind; [exact Hfind | exact (not_eq_sym Hnt) | exact inc_preserves_id].
  - (* rstep_end_read oid0 — dec_segment_refcnt *)
    unfold find_object, dec_segment_refcnt, update_object_meta in *. simpl in *.
    apply Nat.eqb_neq in Hnt.
    rewrite find_map_neq_eq in Hfind; [exact Hfind | exact (not_eq_sym Hnt) | exact dec_preserves_id].
  - (* rstep_evict oid0 — remove_object *)
    unfold find_object in *. simpl in *.
    apply Nat.eqb_neq in Hnt.
    exact (find_backward_filter _ _ _ _ (not_eq_sym Hnt) Hfind).
Qed.

(** =====================================================================
    Section 2: EXECUTABILITY TRANSFER FOR OBJECT OPERATIONS
    ===================================================================== *)

(** Extract the target object ID from an object_op. *)
Lemma object_op_target : forall l oid,
  object_op l oid ->
  label_targets l oid = true.
Proof.
  intros l oid Hop. inversion Hop; subst; simpl;
  apply Nat.eqb_refl.
Qed.

(** A non-targeting object operation preserves label_targets = false
    for other objects. *)
Lemma object_op_non_targeting : forall l oid1 oid2,
  object_op l oid1 ->
  oid1 <> oid2 ->
  label_targets l oid2 = false.
Proof.
  intros l oid1 oid2 Hop Hneq.
  inversion Hop; subst; simpl; apply Nat.eqb_neq; exact Hneq.
Qed.

(** Object operations don't change segment status. *)
Lemma object_op_preserves_seg_status : forall st l st',
  rich_store_step st l st' ->
  (exists oid, object_op l oid) ->
  seg_status (ss_segment st') = seg_status (ss_segment st).
Proof.
  intros st l st' Hstep [oid Hop].
  inversion Hop; subst; inversion Hstep; subst; simpl; reflexivity.
Qed.

(** Object operations don't change transfers. *)
Lemma object_op_preserves_transfers : forall st l st',
  rich_store_step st l st' ->
  (exists oid, object_op l oid) ->
  ss_transfers st' = ss_transfers st.
Proof.
  intros st l st' Hstep [oid Hop].
  inversion Hop; subst; inversion Hstep; subst; simpl; reflexivity.
Qed.

(** Executability transfer for object operations: if l1 and l2 target
    different objects and l1;l2 is executable from st, then l2 is
    executable from st (and l1 from the result of l2). *)
Theorem object_op_swap_executable : forall st l1 l2 oid1 oid2 s1 s12,
  object_op l1 oid1 ->
  object_op l2 oid2 ->
  oid1 <> oid2 ->
  rich_store_step st l1 s1 ->
  rich_store_step s1 l2 s12 ->
  exists s2 s21,
    rich_store_step st l2 s2 /\
    rich_store_step s2 l1 s21 /\
    s12 = s21.
Proof.
  intros st l1 l2 oid1 oid2 s1 s12 Hop1 Hop2 Hneq Hs1 Hs12.
  assert (Hnt1 : label_targets l1 oid2 = false)
    by exact (object_op_non_targeting l1 oid1 oid2 Hop1 Hneq).
  assert (Hnt2 : label_targets l2 oid1 = false)
    by exact (object_op_non_targeting l2 oid2 oid1 Hop2 (not_eq_sym Hneq)).
  (* Construct the step l2 from st *)
  inversion Hop2; subst; inversion Hs12; subst.
  - (* l2 = RLBeginRead oid2 *)
    assert (Hfind_st : find_object (ss_segment st) oid2 = Some m)
      by exact (non_targeting_preserves_find_backward st l1 s1 oid2 m Hs1 Hnt1 H0).
    assert (Hs2 : rich_store_step st (RLBeginRead oid2)
      (mkStoreState (inc_segment_refcnt (ss_segment st) oid2) (ss_transfers st)))
      by exact (rstep_begin_read st oid2 m Hfind_st H2).
    pose (s2 := mkStoreState (inc_segment_refcnt (ss_segment st) oid2) (ss_transfers st)).
    inversion Hop1; subst; inversion Hs1; subst; simpl in *.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl. unfold find_object in *.
        exact (find_after_update_neq (seg_objects (ss_segment st)) oid1 oid2 inc_refcnt
                 Hneq inc_preserves_id m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_begin_read s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold inc_segment_refcnt.
        apply update_update_seg_comm; auto using inc_preserves_id, not_eq_sym.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl. unfold find_object in *.
        exact (find_after_update_neq (seg_objects (ss_segment st)) oid1 oid2 inc_refcnt
                 Hneq inc_preserves_id m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_end_read s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold inc_segment_refcnt, dec_segment_refcnt.
        apply update_update_seg_comm; auto using inc_preserves_id, dec_preserves_id, not_eq_sym.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl. unfold find_object in *.
        exact (find_after_update_neq (seg_objects (ss_segment st)) oid1 oid2 inc_refcnt
                 Hneq inc_preserves_id m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_evict s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold inc_segment_refcnt.
        symmetry. apply remove_update_seg_comm;
        auto using inc_preserves_id, inc_preserves_size.
    + eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_remove s2 oid1).
      * simpl. f_equal. unfold inc_segment_refcnt.
        symmetry. apply remove_update_seg_comm;
        auto using inc_preserves_id, inc_preserves_size.
  - (* l2 = RLEndRead oid2 *)
    assert (Hfind_st : find_object (ss_segment st) oid2 = Some m)
      by exact (non_targeting_preserves_find_backward st l1 s1 oid2 m Hs1 Hnt1 H0).
    assert (Hs2 : rich_store_step st (RLEndRead oid2)
      (mkStoreState (dec_segment_refcnt (ss_segment st) oid2) (ss_transfers st)))
      by exact (rstep_end_read st oid2 m Hfind_st H2).
    pose (s2 := mkStoreState (dec_segment_refcnt (ss_segment st) oid2) (ss_transfers st)).
    inversion Hop1; subst; inversion Hs1; subst; simpl in *.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl. unfold find_object in *.
        exact (find_after_update_neq (seg_objects (ss_segment st)) oid1 oid2 dec_refcnt
                 Hneq dec_preserves_id m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_begin_read s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold inc_segment_refcnt, dec_segment_refcnt.
        apply update_update_seg_comm; auto using inc_preserves_id, dec_preserves_id, not_eq_sym.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl. unfold find_object in *.
        exact (find_after_update_neq (seg_objects (ss_segment st)) oid1 oid2 dec_refcnt
                 Hneq dec_preserves_id m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_end_read s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold dec_segment_refcnt.
        apply update_update_seg_comm; auto using dec_preserves_id, not_eq_sym.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl. unfold find_object in *.
        exact (find_after_update_neq (seg_objects (ss_segment st)) oid1 oid2 dec_refcnt
                 Hneq dec_preserves_id m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_evict s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold dec_segment_refcnt.
        symmetry. apply remove_update_seg_comm;
        auto using dec_preserves_id, dec_preserves_size.
    + eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_remove s2 oid1).
      * simpl. f_equal. unfold dec_segment_refcnt.
        symmetry. apply remove_update_seg_comm;
        auto using dec_preserves_id, dec_preserves_size.
  - (* l2 = RLEvict oid2 *)
    assert (Hfind_st : find_object (ss_segment st) oid2 = Some m)
      by exact (non_targeting_preserves_find_backward st l1 s1 oid2 m Hs1 Hnt1 H0).
    assert (Hs2 : rich_store_step st (RLEvict oid2)
      (mkStoreState (remove_object (ss_segment st) oid2) (ss_transfers st)))
      by exact (rstep_evict st oid2 m Hfind_st H2).
    pose (s2 := mkStoreState (remove_object (ss_segment st) oid2) (ss_transfers st)).
    inversion Hop1; subst; inversion Hs1; subst; simpl in *.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl.
        exact (remove_preserves_find_neq (ss_segment st) oid1 oid2
                 Hneq m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_begin_read s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold inc_segment_refcnt.
        apply remove_update_seg_comm;
        auto using inc_preserves_id, inc_preserves_size.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl.
        exact (remove_preserves_find_neq (ss_segment st) oid1 oid2
                 Hneq m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_end_read s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. unfold dec_segment_refcnt.
        apply remove_update_seg_comm;
        auto using dec_preserves_id, dec_preserves_size.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m0).
      { unfold s2. simpl.
        exact (remove_preserves_find_neq (ss_segment st) oid1 oid2
                 Hneq m0 H1). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_evict s2 oid1 m0 Hfind_s2 H4).
      * simpl. f_equal. apply remove_remove_seg_comm; exact Hneq.
    + eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_remove s2 oid1).
      * simpl. f_equal. apply remove_remove_seg_comm; exact Hneq.
  - (* l2 = RLRemove oid2 — always executable *)
    assert (Hs2 : rich_store_step st (RLRemove oid2)
      (mkStoreState (remove_object (ss_segment st) oid2) (ss_transfers st)))
      by exact (rstep_remove st oid2).
    pose (s2 := mkStoreState (remove_object (ss_segment st) oid2) (ss_transfers st)).
    inversion Hop1; subst; inversion Hs1; subst; simpl in *.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m).
      { unfold s2. simpl.
        exact (remove_preserves_find_neq (ss_segment st) oid1 oid2
                 Hneq m H0). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_begin_read s2 oid1 m Hfind_s2 H2).
      * simpl. f_equal. unfold inc_segment_refcnt.
        apply remove_update_seg_comm;
        auto using inc_preserves_id, inc_preserves_size.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m).
      { unfold s2. simpl.
        exact (remove_preserves_find_neq (ss_segment st) oid1 oid2
                 Hneq m H0). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_end_read s2 oid1 m Hfind_s2 H2).
      * simpl. f_equal. unfold dec_segment_refcnt.
        apply remove_update_seg_comm;
        auto using dec_preserves_id, dec_preserves_size.
    + assert (Hfind_s2 : find_object (ss_segment s2) oid1 = Some m).
      { unfold s2. simpl.
        exact (remove_preserves_find_neq (ss_segment st) oid1 oid2
                 Hneq m H0). }
      eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_evict s2 oid1 m Hfind_s2 H2).
      * simpl. f_equal. apply remove_remove_seg_comm; exact Hneq.
    + eexists. eexists. split; [exact Hs2 | split].
      * exact (rstep_remove s2 oid1).
      * simpl. f_equal. apply remove_remove_seg_comm; exact Hneq.
Qed.

(** =====================================================================
    Section 3: PERMUTATION INVARIANCE — HEADLINE
    ===================================================================== *)

(** All operations in a list are object operations. *)
Definition all_object_ops (ls : list RichStoreLabel) : Prop :=
  Forall (fun l => exists oid, object_op l oid) ls.

(** All pairs of operations in a list target different objects. *)
Definition pairwise_different (ls : list RichStoreLabel) : Prop :=
  forall i j li lj,
    i < length ls -> j < length ls -> i <> j ->
    nth_error ls i = Some li ->
    nth_error ls j = Some lj ->
    forall oid1 oid2, object_op li oid1 -> object_op lj oid2 -> oid1 <> oid2.

(** Object operations have deterministic targets: if object_op l oid1
    and object_op l oid2, then oid1 = oid2. *)
Lemma object_op_det : forall l oid1 oid2,
  object_op l oid1 -> object_op l oid2 -> oid1 = oid2.
Proof.
  intros l oid1 oid2 H1 H2.
  inversion H1; subst; inversion H2; subst; reflexivity.
Qed.

(** Pairwise different + all object ops implies NoDup.
    Key insight: if the same label appeared twice, object_op determinism
    gives oid1 = oid2, contradicting pairwise_different. *)
Lemma pd_ao_NoDup : forall ls,
  all_object_ops ls ->
  pairwise_different ls ->
  NoDup ls.
Proof.
  induction ls as [| a rest IH]; intros Hao Hpd.
  - exact (NoDup_nil RichStoreLabel).
  - apply NoDup_cons.
    + intro Hin.
      apply In_nth_error in Hin. destruct Hin as [j Hj].
      unfold all_object_ops in Hao. inversion Hao as [| ? ? Ha_op Hrest_ao]. subst.
      destruct Ha_op as [oid Hop].
      assert (Hneq_oid : oid <> oid).
      { assert (Hjlt : j < length rest)
          by (apply nth_error_Some; rewrite Hj; discriminate).
        eapply (Hpd 0 (S j) a a).
        - simpl; lia.
        - simpl; lia.
        - lia.
        - reflexivity.
        - simpl. exact Hj.
        - exact Hop.
        - exact Hop. }
      exact (Hneq_oid eq_refl).
    + apply IH.
      * inversion Hao; assumption.
      * unfold pairwise_different in *.
        intros i j li lj Hi Hj Hneq Hni Hnj.
        apply (Hpd (S i) (S j) li lj); simpl; try lia; assumption.
Qed.

(** Pairwise different + all object ops implies pairwise independent. *)
Lemma pairwise_different_independent : forall ls,
  all_object_ops ls ->
  pairwise_different ls ->
  forall l1 l2, In l1 ls -> In l2 ls -> l1 <> l2 ->
    independent l1 l2.
Proof.
  intros ls Hall Hpd l1 l2 Hin1 Hin2 Hneq.
  apply In_nth_error in Hin1. destruct Hin1 as [i Hi].
  apply In_nth_error in Hin2. destruct Hin2 as [j Hj].
  unfold all_object_ops in Hall. rewrite Forall_forall in Hall.
  assert (Hin1' : In l1 ls) by (eapply nth_error_In; eauto).
  assert (Hin2' : In l2 ls) by (eapply nth_error_In; eauto).
  destruct (Hall l1 Hin1') as [oid1 Hop1].
  destruct (Hall l2 Hin2') as [oid2 Hop2].
  left. exists oid1, oid2. repeat split; try assumption.
  destruct (Nat.eq_dec i j) as [Heq | Hneq'].
  - subst. rewrite Hi in Hj. inversion Hj. contradiction.
  - assert (Hi_lt : i < length ls).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    assert (Hj_lt : j < length ls).
    { apply nth_error_Some. rewrite Hj. discriminate. }
    exact (Hpd i j l1 l2 Hi_lt Hj_lt Hneq' Hi Hj oid1 oid2 Hop1 Hop2).
Qed.

(** HEADLINE: Any permutation of object operations on pairwise-different
    targets, from a state where the original order is executable,
    is itself executable and reaches the same final state.

    This is the Cartier-Foata theorem for the Mooncake store:
    for independent concurrent operations, scheduling order is
    completely irrelevant.  Not just "the result is the same if both
    orderings happen to work" (swap_preserves_result), but "if one
    ordering works, ALL orderings work and give the same result."

    The proof is by induction on the Permutation derivation.
    The key cases:
    - perm_swap: uses object_op_swap_executable (executability transfer)
      and the diamond (state equality)
    - perm_skip: trivial (same first operation)
    - perm_trans: compose the two IH results *)
Theorem permutation_invariance : forall ls1 ls2 st st1,
  Permutation ls1 ls2 ->
  all_object_ops ls1 ->
  pairwise_different ls1 ->
  exec st ls1 st1 ->
  exists st2, exec st ls2 st2 /\ st1 = st2.
Proof.
  intros ls1 ls2 st st1 Hperm.
  revert st st1.
  induction Hperm as [
    | a ls1 ls2 Hperm IH
    | a b ls
    | ls1 ls2 ls3 Hperm1 IH1 Hperm2 IH2
  ]; intros st st1 Hobj Hpd Hexec.
  - (* perm_nil *)
    exists st1. split; [exact Hexec | reflexivity].
  - (* perm_skip a *)
    destruct (exec_cons_inv _ _ _ _ Hexec) as [s1 [Ha Hrest]].
    assert (Hobj' : all_object_ops ls1).
    { inversion Hobj; assumption. }
    assert (Hpd' : pairwise_different ls1).
    { unfold pairwise_different in *. intros i j li lj Hi Hj Hneq Hni Hnj.
      apply (Hpd (S i) (S j) li lj); simpl; try lia; assumption. }
    destruct (IH s1 st1 Hobj' Hpd' Hrest) as [st2 [Hexec2 Heq]].
    exists st2. split.
    + exact (exec_cons st a ls2 s1 st2 Ha Hexec2).
    + exact Heq.
  - (* perm_swap a b *)
    destruct (exec_cons_inv _ _ _ _ Hexec) as [sa [Ha Hrest_ab]].
    destruct (exec_cons_inv _ _ _ _ Hrest_ab) as [sab [Hb Hrest]].
    (* Extract object_op witnesses *)
    inversion Hobj as [| ? ? Ha_obj Hobj']. subst.
    inversion Hobj' as [| ? ? Hb_obj _]. subst.
    destruct Ha_obj as [oid_a Hopa].
    destruct Hb_obj as [oid_b Hopb].
    (* Extract oid_a <> oid_b *)
    assert (Hneq : oid_a <> oid_b).
    { eapply (Hpd 0 1 b a); simpl;
      [lia | lia | lia | reflexivity | reflexivity | exact Hopa | exact Hopb]. }
    (* Use executability transfer *)
    destruct (object_op_swap_executable st b a oid_a oid_b sa sab
                Hopa Hopb Hneq Ha Hb)
      as [sb [sba [Hb' [Ha' Heq]]]].
    exists st1. split.
    + apply (exec_cons st a (b :: ls) sb st1 Hb').
      apply (exec_cons sb b ls sba st1 Ha').
      rewrite <- Heq. exact Hrest.
    + reflexivity.
  - (* perm_trans ls1 ls2 ls3 *)
    assert (Hobj2 : all_object_ops ls2).
    { unfold all_object_ops. rewrite Forall_forall.
      intros l Hin. unfold all_object_ops in Hobj. rewrite Forall_forall in Hobj.
      apply Hobj. eapply Permutation_in; [apply Permutation_sym; exact Hperm1 | exact Hin]. }
    assert (Hpd2 : pairwise_different ls2).
    { unfold pairwise_different. intros i j li lj Hi Hj Hneq Hni Hnj oid1 oid2 Hop1 Hop2.
      assert (Hin_li : In li ls2) by (eapply nth_error_In; eauto).
      assert (Hin_lj : In lj ls2) by (eapply nth_error_In; eauto).
      assert (Hin_li' : In li ls1) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm1 | exact Hin_li]).
      assert (Hin_lj' : In lj ls1) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm1 | exact Hin_lj]).
      apply In_nth_error in Hin_li'. destruct Hin_li' as [i' Hi'].
      apply In_nth_error in Hin_lj'. destruct Hin_lj' as [j' Hj'].
      destruct (Nat.eq_dec i' j') as [Heq_ij | Hneq_ij].
      - subst. rewrite Hi' in Hj'. inversion Hj'; subst.
        (* li = lj at positions i <> j in ls2 — contradicts NoDup ls2 *)
        exfalso. apply Hneq.
        apply (proj1 (NoDup_nth_error ls2)
                 (Permutation_NoDup Hperm1 (pd_ao_NoDup ls1 Hobj Hpd))
                 i j Hi).
        rewrite Hni. rewrite Hnj. reflexivity.
      - assert (Hi'lt : i' < length ls1).
        { apply nth_error_Some. rewrite Hi'. discriminate. }
        assert (Hj'lt : j' < length ls1).
        { apply nth_error_Some. rewrite Hj'. discriminate. }
        exact (Hpd i' j' li lj Hi'lt Hj'lt
                 Hneq_ij Hi' Hj' oid1 oid2 Hop1 Hop2). }
    destruct (IH1 st st1 Hobj Hpd Hexec) as [st2 [Hexec2 Heq1]].
    subst st2.
    destruct (IH2 st st1 Hobj2 Hpd2 Hexec2) as [st3 [Hexec3 Heq2]].
    exists st3. split; [exact Hexec3 | exact Heq2].
Qed.
