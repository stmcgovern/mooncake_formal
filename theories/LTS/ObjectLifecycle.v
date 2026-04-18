(** * ObjectLifecycle.v — Constructive lifecycle and operation effects.

    =========================================================================
    LAYER: 3-4 - DOMAIN/APPLICATION (operation completeness)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Complements EvictionSafety.v and ProtectionFrame.v by proving the
    COMPLETENESS direction: operations achieve their intended effects.

    EvictionSafety proves "reads block eviction" (soundness).
    ProtectionFrame proves "non-targeting operations don't interfere" (frame).
    This module proves "eviction removes the object" and "placement makes
    the object findable" (completeness).

    The headline theorem (read_or_evict): for any findable object, exactly
    one of two situations holds:
      1. The object is protected, and eviction is impossible.
      2. The object is unprotected, and eviction is possible.
    These cases are mutually exclusive and exhaustive.

    @source mooncake-store/src/master_service.cpp (BatchEvict, AddReplica)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety

    PROVIDES:
    - find_in_filter_self (filtering by ID removes that ID from results)
    - remove_makes_unfindable (remove_object makes object unfindable)
    - eviction_makes_unfindable (Evict step removes the object)
    - place_makes_findable (Place step makes new object findable)
    - eviction_possible (unprotected + findable → eviction step exists)
    - read_possible (COMPLETE + findable → BeginRead step exists)
    - read_or_evict (HEADLINE: protection dichotomy for findable objects)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.

(** =====================================================================
    Section 1: REMOVAL EFFECTS
    ===================================================================== *)

(** Filtering out an ID makes it unfindable in the result. *)
Lemma find_in_filter_self : forall objs oid,
  find_object_in
    (filter (fun x => negb (Nat.eqb (om_id x) oid)) objs) oid = None.
Proof.
  intros objs oid. induction objs as [| h rest IH].
  - reflexivity.
  - simpl. destruct (Nat.eqb (om_id h) oid) eqn:Heq.
    + (* h has the target ID, filter removes it *)
      simpl. exact IH.
    + (* h has a different ID, filter keeps it *)
      simpl. rewrite Heq. exact IH.
Qed.

(** remove_object makes the removed object unfindable. *)
Theorem remove_makes_unfindable : forall seg oid,
  find_object (remove_object seg oid) oid = None.
Proof.
  intros seg oid.
  unfold find_object, remove_object. simpl.
  apply find_in_filter_self.
Qed.

(** After an Evict step, the evicted object is no longer findable. *)
Theorem eviction_makes_unfindable : forall st oid st',
  rich_store_step st (RLEvict oid) st' ->
  find_object (ss_segment st') oid = None.
Proof.
  intros st oid st' Hstep.
  inversion Hstep; subst. simpl.
  apply remove_makes_unfindable.
Qed.

(** After a Remove step, the removed object is no longer findable. *)
Theorem remove_step_makes_unfindable : forall st oid st',
  rich_store_step st (RLRemove oid) st' ->
  find_object (ss_segment st') oid = None.
Proof.
  intros st oid st' Hstep.
  inversion Hstep; subst. simpl.
  apply remove_makes_unfindable.
Qed.

(** =====================================================================
    Section 2: PLACEMENT EFFECTS
    ===================================================================== *)

(** Placing an object makes it immediately findable by its ID. *)
Theorem place_makes_findable : forall st m st',
  rich_store_step st (RLPlace m) st' ->
  find_object (ss_segment st') (om_id m) = Some m.
Proof.
  intros st m st' Hstep.
  inversion Hstep; subst. simpl.
  unfold find_object, place_object. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** =====================================================================
    Section 3: OPERATION PRECONDITION SUFFICIENCY
    ===================================================================== *)

(** An unprotected findable object can be evicted. *)
Theorem eviction_possible : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  eviction_protected m = false ->
  exists st', rich_store_step st (RLEvict oid) st'.
Proof.
  intros st oid m Hfind Hprot.
  exists (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st)).
  exact (rstep_evict st oid m Hfind Hprot).
Qed.

(** A COMPLETE findable object can begin a read. *)
Theorem read_possible : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  om_status m = RsComplete ->
  exists st', rich_store_step st (RLBeginRead oid) st'.
Proof.
  intros st oid m Hfind Hcomp.
  exists (mkStoreState (inc_segment_refcnt (ss_segment st) oid) (ss_transfers st)).
  exact (rstep_begin_read st oid m Hfind Hcomp).
Qed.

(** An object with positive refcount can end a read. *)
Theorem end_read_possible : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  exists st', rich_store_step st (RLEndRead oid) st'.
Proof.
  intros st oid m Hfind Hrc.
  exists (mkStoreState (dec_segment_refcnt (ss_segment st) oid) (ss_transfers st)).
  exact (rstep_end_read st oid m Hfind Hrc).
Qed.

(** =====================================================================
    Section 4: PROTECTION DICHOTOMY — HEADLINE THEOREM
    ===================================================================== *)

(** For any findable object, exactly one of two situations holds:
    either the object is protected (eviction impossible) or
    unprotected (eviction possible).

    This is the completeness counterpart to read_eviction_safety:
    safety says "protected objects can't be evicted";
    this says "unprotected objects CAN be evicted". *)
Theorem read_or_evict : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  (* Protected: eviction is impossible *)
  (eviction_protected m = true /\
   ~ exists st', rich_store_step st (RLEvict oid) st') \/
  (* Unprotected: eviction is possible *)
  (eviction_protected m = false /\
   exists st', rich_store_step st (RLEvict oid) st').
Proof.
  intros st oid m Hfind.
  destruct (eviction_protected m) eqn:Hprot.
  - (* Protected *)
    left. split.
    + reflexivity.
    + intros [st' Hstep].
      inversion Hstep as [| | | | | | | ? ? m0 Hfind0 Hprot0]; subst.
      rewrite Hfind in Hfind0. inversion Hfind0; subst.
      rewrite Hprot in Hprot0. discriminate.
  - (* Unprotected *)
    right. split.
    + reflexivity.
    + exact (eviction_possible st oid m Hfind Hprot).
Qed.

(** Stronger version using active_readers_protected: active readers
    are one specific reason eviction is blocked. *)
Theorem active_readers_block_eviction : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  eviction_protected m = true /\
  ~ exists st', rich_store_step st (RLEvict oid) st'.
Proof.
  intros st oid m Hfind Hrc.
  assert (Hprot := active_readers_protected m Hrc).
  destruct (read_or_evict st oid m Hfind) as [[_ Hne] | [Habs _]].
  - split; assumption.
  - rewrite Hprot in Habs. discriminate.
Qed.

(** =====================================================================
    Section 5: EFFECT COMPLETENESS — OPERATIONS DO WHAT THEY SHOULD
    ===================================================================== *)

(** BeginRead makes an object protected that was previously unprotected.
    This is the constructive counterpart: not just "BeginRead makes
    eviction impossible" but "BeginRead changes protection status". *)
Theorem begin_read_protects : forall st oid m st',
  find_object (ss_segment st) oid = Some m ->
  om_status m = RsComplete ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  rich_store_step st (RLBeginRead oid) st' ->
  exists m',
    find_object (ss_segment st') oid = Some m' /\
    eviction_protected m' = true /\
    om_ref_count m' = S (om_ref_count m).
Proof.
  intros st oid m st' Hfind Hcomp Hnd Hstep.
  inversion Hstep; subst. simpl.
  destruct (inc_segment_refcnt_protects (ss_segment st) oid m Hfind Hnd)
    as [m' [Hf' [Hrc' Hp']]].
  exists m'. split; [| split].
  - exact Hf'.
  - exact Hp'.
  - (* Show om_ref_count m' = S (om_ref_count m) *)
    (* m' = inc_refcnt m by the definition of inc_segment_refcnt *)
    unfold find_object, inc_segment_refcnt, update_object_meta in Hf'. simpl in Hf'.
    assert (Hm' : m' = inc_refcnt m).
    { clear Hrc' Hp'.
      pose proof (find_after_update (seg_objects (ss_segment st)) oid inc_refcnt m
                    Hfind inc_preserves_id) as Hfu.
      unfold find_object in Hf'.
      rewrite Hfu in Hf'. inversion Hf'. reflexivity. }
    subst m'. simpl. reflexivity.
Qed.

(** Eviction and removal have the same effect: they make the object
    unfindable.  The difference is only in preconditions. *)
Theorem evict_and_remove_same_effect : forall st oid st1 st2,
  rich_store_step st (RLEvict oid) st1 ->
  rich_store_step st (RLRemove oid) st2 ->
  find_object (ss_segment st1) oid = find_object (ss_segment st2) oid.
Proof.
  intros st oid st1 st2 Hevict Hremove.
  inversion Hevict; subst. inversion Hremove; subst.
  reflexivity.
Qed.
