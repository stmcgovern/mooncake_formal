(** * ProtectionFrame.v — Frame properties for concurrent safety.

    =========================================================================
    LAYER: 3-4 - DOMAIN/APPLICATION (multi-object safety)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Proves that operations targeting one object do not affect another
    object's metadata, findability, or protection status.  These "frame
    properties" are the foundation for reasoning about concurrent reads
    and evictions in Mooncake's disaggregated KV cache.

    The central insight: Mooncake allows concurrent readers on different
    KV blocks and concurrent eviction of unprotected blocks.  Safety
    requires that these operations do not interfere — evicting block B
    must not affect block A's refcount-based protection.

    @source mooncake-store/src/master_service.cpp (BatchEvict, concurrent reads)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety

    PROVIDES:
    - find_in_filter_neq (lookup after filter on different ID)
    - find_after_update_neq (lookup after update on different ID)
    - find_after_cons_neq (lookup after cons with different ID)
    - remove_preserves_find_neq (remove_object frame property)
    - update_preserves_find_neq (update_object_meta frame property)
    - inc_refcnt_preserves_find_neq (inc_segment_refcnt frame property)
    - dec_refcnt_preserves_find_neq (dec_segment_refcnt frame property)
    - place_preserves_find_existing (place_object frame property)
    - label_targets (classifies which labels affect which object)
    - non_targeting_preserves_find (GENERAL: non-targeting steps preserve find)
    - concurrent_eviction_safe (HEADLINE: eviction respects other readers)
    - concurrent_reads_independent (HEADLINE: reads don't interfere)
    - drain_preserves_read_protection (HEADLINE: drain respects active reads)
    - trace_non_targeting_preserves_find (multi-step frame)
    - trace_read_protection (HEADLINE: protection through arbitrary traces)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.Preservation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.

(** =====================================================================
    Section 1: LIST-LEVEL FRAME LEMMAS
    ===================================================================== *)

(** Lookup is preserved after filtering out a different ID. *)
Lemma find_in_filter_neq : forall objs oid oid',
  oid <> oid' ->
  forall m,
  find_object_in objs oid = Some m ->
  find_object_in
    (filter (fun x => negb (Nat.eqb (om_id x) oid')) objs) oid = Some m.
Proof.
  intros objs oid oid' Hneq. induction objs as [| h rest IH]; intros m Hfind.
  - discriminate.
  - simpl in Hfind. simpl.
    destruct (Nat.eqb (om_id h) oid') eqn:Hoid'.
    + (* filter removes h *)
      simpl.
      destruct (Nat.eqb (om_id h) oid) eqn:Hoid.
      * apply Nat.eqb_eq in Hoid. apply Nat.eqb_eq in Hoid'.
        exfalso. apply Hneq. congruence.
      * exact (IH m Hfind).
    + (* filter keeps h *)
      simpl.
      destruct (Nat.eqb (om_id h) oid) eqn:Hoid.
      * exact Hfind.
      * exact (IH m Hfind).
Qed.

(** Lookup is preserved after updating a different ID in the list. *)
Lemma find_after_update_neq : forall objs oid oid' f,
  oid <> oid' ->
  (forall m, om_id (f m) = om_id m) ->
  forall m,
  find_object_in objs oid = Some m ->
  find_object_in
    (map (fun x => if Nat.eqb (om_id x) oid' then f x else x) objs) oid
    = Some m.
Proof.
  intros objs oid oid' f Hneq Hpres. induction objs as [| h rest IH]; intros m Hfind.
  - discriminate.
  - simpl in Hfind. simpl.
    destruct (Nat.eqb (om_id h) oid') eqn:Hoid'.
    + (* h matches oid', apply f *)
      rewrite Hpres.
      destruct (Nat.eqb (om_id h) oid) eqn:Hoid.
      * apply Nat.eqb_eq in Hoid. apply Nat.eqb_eq in Hoid'.
        exfalso. apply Hneq. congruence.
      * exact (IH m Hfind).
    + (* h doesn't match oid', unchanged *)
      destruct (Nat.eqb (om_id h) oid) eqn:Hoid.
      * exact Hfind.
      * exact (IH m Hfind).
Qed.

(** Lookup is preserved when a different-ID element is prepended. *)
Lemma find_after_cons_neq : forall objs m_new oid,
  om_id m_new <> oid ->
  forall m,
  find_object_in objs oid = Some m ->
  find_object_in (m_new :: objs) oid = Some m.
Proof.
  intros objs m_new oid Hneq m Hfind. simpl.
  destruct (Nat.eqb (om_id m_new) oid) eqn:Heq.
  - apply Nat.eqb_eq in Heq. exfalso. exact (Hneq Heq).
  - exact Hfind.
Qed.

(** =====================================================================
    Section 2: SEGMENT-LEVEL FRAME LEMMAS
    ===================================================================== *)

(** remove_object preserves find_object for a different ID. *)
Lemma remove_preserves_find_neq : forall seg oid oid',
  oid <> oid' ->
  forall m,
  find_object seg oid = Some m ->
  find_object (remove_object seg oid') oid = Some m.
Proof.
  intros seg oid oid' Hneq m Hfind.
  unfold find_object in *. unfold remove_object. simpl.
  apply find_in_filter_neq; assumption.
Qed.

(** update_object_meta on a different ID preserves find_object. *)
Lemma update_preserves_find_neq : forall seg oid oid' f,
  oid <> oid' ->
  (forall m, om_id (f m) = om_id m) ->
  forall m,
  find_object seg oid = Some m ->
  find_object (update_object_meta seg oid' f) oid = Some m.
Proof.
  intros seg oid oid' f Hneq Hpres m Hfind.
  unfold find_object in *. unfold update_object_meta. simpl.
  apply find_after_update_neq; assumption.
Qed.

(** inc_segment_refcnt on a different ID preserves find_object. *)
Lemma inc_refcnt_preserves_find_neq : forall seg oid oid',
  oid <> oid' ->
  forall m,
  find_object seg oid = Some m ->
  find_object (inc_segment_refcnt seg oid') oid = Some m.
Proof.
  intros seg oid oid' Hneq m Hfind.
  unfold inc_segment_refcnt.
  apply update_preserves_find_neq; try assumption.
  exact inc_preserves_id.
Qed.

(** dec_segment_refcnt on a different ID preserves find_object. *)
Lemma dec_refcnt_preserves_find_neq : forall seg oid oid',
  oid <> oid' ->
  forall m,
  find_object seg oid = Some m ->
  find_object (dec_segment_refcnt seg oid') oid = Some m.
Proof.
  intros seg oid oid' Hneq m Hfind.
  unfold dec_segment_refcnt.
  apply update_preserves_find_neq; try assumption.
  exact dec_preserves_id.
Qed.

(** place_object preserves find_object for existing objects with
    different IDs. *)
Lemma place_preserves_find_existing : forall seg m_new oid,
  om_id m_new <> oid ->
  forall m,
  find_object seg oid = Some m ->
  find_object (place_object seg m_new) oid = Some m.
Proof.
  intros seg m_new oid Hneq m Hfind.
  unfold find_object in *. unfold place_object. simpl.
  apply find_after_cons_neq; assumption.
Qed.

(** Status changes preserve find_object. *)
Lemma set_status_preserves_find : forall seg new_st oid,
  find_object (set_segment_status seg new_st) oid = find_object seg oid.
Proof. intros. reflexivity. Qed.

(** =====================================================================
    Section 3: LABEL TARGETING
    ===================================================================== *)

(** Classifies which enriched labels affect a specific object. *)
Definition label_targets (l : RichStoreLabel) (oid : ObjectId) : bool :=
  match l with
  | RLPlace m => Nat.eqb (om_id m) oid
  | RLRemove oid' => Nat.eqb oid' oid
  | RLBeginDrain => false
  | RLCompleteDrain => false
  | RLUnmount => false
  | RLBeginRead oid' => Nat.eqb oid' oid
  | RLEndRead oid' => Nat.eqb oid' oid
  | RLEvict oid' => Nat.eqb oid' oid
  end.

(** =====================================================================
    Section 4: GENERAL FRAME THEOREM
    ===================================================================== *)

(** Any enriched step that does not target a given object preserves
    that object's findability.  This is the master frame property. *)
Theorem non_targeting_preserves_find : forall st l st' oid m,
  rich_store_step st l st' ->
  label_targets l oid = false ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some m.
Proof.
  intros st l st' oid m Hstep Htarget Hfind.
  inversion Hstep; subst; simpl in Htarget |- *.
  - (* rstep_place *)
    apply place_preserves_find_existing; try assumption.
    intro Heq. rewrite Heq in Htarget.
    rewrite Nat.eqb_refl in Htarget. discriminate.
  - (* rstep_remove *)
    apply remove_preserves_find_neq; try assumption.
    intro Heq. rewrite Heq in Htarget.
    rewrite Nat.eqb_refl in Htarget. discriminate.
  - (* rstep_begin_drain *)
    unfold begin_drain, set_segment_status. simpl. exact Hfind.
  - (* rstep_complete_drain *)
    unfold complete_drain, set_segment_status. simpl. exact Hfind.
  - (* rstep_unmount *)
    unfold begin_unmount, set_segment_status. simpl. exact Hfind.
  - (* rstep_begin_read *)
    apply inc_refcnt_preserves_find_neq; try assumption.
    intro Heq. rewrite Heq in Htarget.
    rewrite Nat.eqb_refl in Htarget. discriminate.
  - (* rstep_end_read *)
    apply dec_refcnt_preserves_find_neq; try assumption.
    intro Heq. rewrite Heq in Htarget.
    rewrite Nat.eqb_refl in Htarget. discriminate.
  - (* rstep_evict *)
    apply remove_preserves_find_neq; try assumption.
    intro Heq. rewrite Heq in Htarget.
    rewrite Nat.eqb_refl in Htarget. discriminate.
Qed.

(** =====================================================================
    Section 5: CONCURRENT SAFETY — HEADLINE THEOREMS
    ===================================================================== *)

(** Evicting one object preserves read protection of a different object
    with active readers.  This is the concurrent eviction safety
    property: multiple objects can be independently protected. *)
Theorem concurrent_eviction_safe : forall st oid_a oid_b m_a st',
  oid_a <> oid_b ->
  find_object (ss_segment st) oid_a = Some m_a ->
  om_ref_count m_a > 0 ->
  rich_store_step st (RLEvict oid_b) st' ->
  ~ exists st'', rich_store_step st' (RLEvict oid_a) st''.
Proof.
  intros st oid_a oid_b m_a st' Hneq Hfind Hrc Hstep.
  assert (Hfind' : find_object (ss_segment st') oid_a = Some m_a).
  { apply (non_targeting_preserves_find st (RLEvict oid_b) st'); try assumption.
    simpl. apply Nat.eqb_neq. exact (fun H => Hneq (eq_sym H)). }
  exact (read_eviction_safety st' oid_a m_a Hfind' Hrc).
Qed.

(** Reading one object preserves findability and protection of
    another object with active readers. *)
Theorem concurrent_reads_independent : forall st oid_a oid_b m_a st',
  oid_a <> oid_b ->
  find_object (ss_segment st) oid_a = Some m_a ->
  om_ref_count m_a > 0 ->
  rich_store_step st (RLBeginRead oid_b) st' ->
  find_object (ss_segment st') oid_a = Some m_a /\
  ~ exists st'', rich_store_step st' (RLEvict oid_a) st''.
Proof.
  intros st oid_a oid_b m_a st' Hneq Hfind Hrc Hstep.
  assert (Hfind' : find_object (ss_segment st') oid_a = Some m_a).
  { apply (non_targeting_preserves_find st (RLBeginRead oid_b) st'); try assumption.
    simpl. apply Nat.eqb_neq. exact (fun H => Hneq (eq_sym H)). }
  split.
  - exact Hfind'.
  - exact (read_eviction_safety st' oid_a m_a Hfind' Hrc).
Qed.

(** Removing an object during drain preserves read protection of
    a different object with active readers.  This connects the drain
    lifecycle (Convergence.v) with eviction safety (EvictionSafety.v). *)
Theorem drain_preserves_read_protection : forall st oid_read oid_remove m st',
  oid_read <> oid_remove ->
  find_object (ss_segment st) oid_read = Some m ->
  om_ref_count m > 0 ->
  rich_store_step st (RLRemove oid_remove) st' ->
  find_object (ss_segment st') oid_read = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid_read) st''.
Proof.
  intros st oid_read oid_remove m st' Hneq Hfind Hrc Hstep.
  assert (Hfind' : find_object (ss_segment st') oid_read = Some m).
  { apply (non_targeting_preserves_find st (RLRemove oid_remove) st');
      try assumption.
    simpl. apply Nat.eqb_neq.
    exact (fun H => Hneq (eq_sym H)). }
  split.
  - exact Hfind'.
  - exact (read_eviction_safety st' oid_read m Hfind' Hrc).
Qed.

(** Ending a read on one object preserves protection of another
    object that still has active readers. *)
Theorem end_read_preserves_other_protection : forall st oid_a oid_b m_a st',
  oid_a <> oid_b ->
  find_object (ss_segment st) oid_a = Some m_a ->
  om_ref_count m_a > 0 ->
  rich_store_step st (RLEndRead oid_b) st' ->
  find_object (ss_segment st') oid_a = Some m_a /\
  ~ exists st'', rich_store_step st' (RLEvict oid_a) st''.
Proof.
  intros st oid_a oid_b m_a st' Hneq Hfind Hrc Hstep.
  assert (Hfind' : find_object (ss_segment st') oid_a = Some m_a).
  { apply (non_targeting_preserves_find st (RLEndRead oid_b) st'); try assumption.
    simpl. apply Nat.eqb_neq. exact (fun H => Hneq (eq_sym H)). }
  split.
  - exact Hfind'.
  - exact (read_eviction_safety st' oid_a m_a Hfind' Hrc).
Qed.

(** =====================================================================
    Section 6: MULTI-STEP FRAME — TRACE-LEVEL SAFETY
    ===================================================================== *)

(** Non-targeting operations preserve find_object through arbitrary
    multi-step traces.  Extends the single-step frame to sequences. *)
Theorem trace_non_targeting_preserves_find : forall st ls st' oid m,
  lstar rich_store_step st ls st' ->
  Forall (fun l => label_targets l oid = false) ls ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some m.
Proof.
  intros st ls st' oid m Hstar. revert m.
  induction Hstar as [| s1 l s2 ls s3 Hstep Hstar IH]; intros m Hall Hfind.
  - exact Hfind.
  - inversion Hall as [| ? ? Hl Hls]; subst.
    assert (Hfind2 : find_object (ss_segment s2) oid = Some m).
    { exact (non_targeting_preserves_find s1 l s2 oid m Hstep Hl Hfind). }
    exact (IH m Hls Hfind2).
Qed.

(** HEADLINE: An object with active readers remains protected through
    any trace of operations that do not target it.

    This is the trace-level concurrent safety theorem: as long as no
    operation in the trace directly affects object [oid], its metadata
    is preserved unchanged, and it remains protected from eviction
    throughout the entire execution. *)
Theorem trace_read_protection : forall st ls st' oid m,
  lstar rich_store_step st ls st' ->
  Forall (fun l => label_targets l oid = false) ls ->
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  intros st ls st' oid m Hstar Hall Hfind Hrc.
  assert (Hfind' := trace_non_targeting_preserves_find st ls st' oid m
                       Hstar Hall Hfind).
  split.
  - exact Hfind'.
  - exact (read_eviction_safety st' oid m Hfind' Hrc).
Qed.
