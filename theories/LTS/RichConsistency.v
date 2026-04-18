(** * RichConsistency.v -- Global invariant for the enriched LTS.

    =========================================================================
    LAYER: 4 - APPLICATION (invariant preservation)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Extends the consistency preservation theorem from the original 5-label
    LTS (StoreLTS.v) to the full enriched 8-label LTS (EvictionSafety.v).
    The three new operations (BeginRead, EndRead, Evict) all preserve
    store_consistent:

    - BeginRead (inc_refcnt): changes only refcount, preserves status
    - EndRead (dec_refcnt): changes only refcount, preserves status
    - Evict (remove_object): same as Remove, already proved

    The headline result: store_consistent is an invariant of the ENTIRE
    enriched system, not just the original store operations.  This means
    the global safety invariant (four gates hold simultaneously) is
    maintained through reads, evictions, and all their interleavings.

    Corollaries connect to exec (multi-step) and eval (denotational).

    @source mooncake-store/src/master_service.cpp (all operations)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.StoreLTS
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.TraceEquivalence
    - MooncakeFormal.LTS.Denotational

    PROVIDES:
    - meta_update_preserves_consistency (status-preserving updates safe)
    - rich_step_preserves_consistency (HEADLINE: every enriched step safe)
    - rich_consistent_exec (HEADLINE: consistency through exec traces)
    - eval_preserves_consistency (HEADLINE: eval preserves consistency)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.StoreLTS.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.TraceEquivalence.
Require Import MooncakeFormal.LTS.Denotational.

(** =====================================================================
    Section 1: METADATA UPDATE PRESERVES CONSISTENCY
    ===================================================================== *)

(** Any metadata update that preserves om_status preserves
    store_consistent.  This covers both inc_refcnt and dec_refcnt.

    The proof has three parts:
    - objects_live: update_preserves_live from RefcountProtocol.v
    - transfers_coupled: transfers are unchanged
    - drain_consistent: status preservation means the INITIALIZED/PROCESSING
      exclusion is maintained through the mapped object list *)
Lemma meta_update_preserves_consistency : forall st oid f,
  (forall m, om_status (f m) = om_status m) ->
  store_consistent st ->
  store_consistent
    (mkStoreState (update_object_meta (ss_segment st) oid f) (ss_transfers st)).
Proof.
  intros st oid f Hstat [Hlive [Htc Hdc]].
  unfold store_consistent. repeat split.
  - (* objects_live: f preserves terminal status via status preservation *)
    unfold objects_live.
    apply (update_preserves_live (ss_segment st) oid f Hlive).
    intros m Hnt. rewrite (Hstat m). exact Hnt.
  - (* transfers_coupled: transfers unchanged *)
    exact Htc.
  - (* drain_consistent: status preservation means no new INIT/PROC *)
    unfold drain_consistent. simpl.
    intro Ha. specialize (Hdc Ha).
    apply Forall_forall. intros x Hin. simpl in Hin.
    apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
    rewrite Forall_forall in Hdc. specialize (Hdc y Hiny).
    destruct (Nat.eqb (om_id y) oid); subst.
    + destruct Hdc as [Hnp Hni].
      split; intro Habs; [apply Hnp | apply Hni];
        rewrite Hstat in Habs; exact Habs.
    + exact Hdc.
Qed.

(** =====================================================================
    Section 2: ENRICHED STEP PRESERVES CONSISTENCY -- HEADLINE
    ===================================================================== *)

(** HEADLINE: Every operation in the enriched LTS preserves
    store_consistent.

    For the original 5 labels, we delegate to the existing
    store_step_preserves_consistency (via individual lemmas).
    For the 3 new labels:
    - BeginRead (inc_segment_refcnt): meta_update with inc_refcnt
    - EndRead (dec_segment_refcnt): meta_update with dec_refcnt
    - Evict (remove_object): same as Remove

    This means the four protocol gates (readable iff COMPLETE,
    protected iff pinned/referenced/in-progress, allocatable iff SegOk,
    unmountable iff drained+empty) hold through ALL operations including
    concurrent reads and evictions. *)
Theorem rich_step_preserves_consistency : forall st l st',
  store_consistent st ->
  rich_store_step st l st' ->
  store_consistent st'.
Proof.
  intros st l st' Hsc Hstep. inversion Hstep; subst.
  - (* rstep_place *)
    apply place_preserves_consistency; assumption.
  - (* rstep_remove *)
    apply remove_preserves_consistency. exact Hsc.
  - (* rstep_begin_drain *)
    apply begin_drain_preserves_consistency; assumption.
  - (* rstep_complete_drain *)
    apply complete_drain_preserves_consistency; assumption.
  - (* rstep_unmount *)
    apply unmount_preserves_consistency; assumption.
  - (* rstep_begin_read — inc_segment_refcnt preserves consistency *)
    unfold inc_segment_refcnt.
    apply meta_update_preserves_consistency; [exact inc_preserves_status | exact Hsc].
  - (* rstep_end_read — dec_segment_refcnt preserves consistency *)
    unfold dec_segment_refcnt.
    apply meta_update_preserves_consistency; [exact dec_preserves_status | exact Hsc].
  - (* rstep_evict — same as remove *)
    apply remove_preserves_consistency. exact Hsc.
Qed.

(** =====================================================================
    Section 3: MULTI-STEP AND DENOTATIONAL -- HEADLINE
    ===================================================================== *)

(** HEADLINE: store_consistent is preserved through arbitrary enriched
    execution traces.

    Starting from a consistent store, ANY sequence of reads, evictions,
    removals, placements, and drain operations produces a consistent
    store.  This is the multi-step generalization of the single-step
    result, proved by induction on exec. *)
Theorem rich_consistent_exec : forall st ls st',
  store_consistent st ->
  exec st ls st' ->
  store_consistent st'.
Proof.
  intros st ls st' Hsc Hexec.
  induction Hexec as [s | s l ls s_mid s_final Hstep Hexec IH].
  - exact Hsc.
  - apply IH. exact (rich_step_preserves_consistency s l s_mid Hsc Hstep).
Qed.

(** HEADLINE: The computable eval function preserves store_consistent.

    If eval succeeds from a consistent state, the resulting state is
    consistent.  This licenses using eval for testing: compute the
    result of any trace, and the global invariant is guaranteed. *)
Theorem eval_preserves_consistency : forall st ls st',
  store_consistent st ->
  eval ls st = Some st' ->
  store_consistent st'.
Proof.
  intros st ls st' Hsc Heval.
  exact (rich_consistent_exec st ls st' Hsc (eval_sound ls st st' Heval)).
Qed.
