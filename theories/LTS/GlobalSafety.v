(** * GlobalSafety.v -- Capstone safety theorems for the Mooncake store.

    =========================================================================
    LAYER: 4 - APPLICATION (capstone composition)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Assembles the headline results from across the formalization into
    the definitive safety theorems a system designer cares about.

    The Mooncake KV cache store has three critical safety questions:

    Q1: Can a read-in-progress object be evicted?
        NO — Theorem: serving_safety

    Q2: Can the system drain segments while reads are active?
        YES — Theorem: drain_respects_readers

    Q3: Do read sessions affect store state?
        NO — Theorem: reads_are_transparent

    Q4: Is the global invariant maintained through all operations?
        YES — Theorem: invariant_preservation

    These compose results from EvictionSafety, DrainSafety,
    RichConsistency, CapacityCoherence, Diamond, ProtectionFrame,
    RefcountCounting, and ObjectLifecycle.

    @source mooncake-store/src/master_service.cpp (all operations)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.Diamond
    - MooncakeFormal.LTS.ProtectionFrame
    - MooncakeFormal.LTS.ObjectLifecycle
    - MooncakeFormal.LTS.TraceEquivalence
    - MooncakeFormal.LTS.RefcountCounting
    - MooncakeFormal.LTS.DrainSafety
    - MooncakeFormal.LTS.RichConsistency
    - MooncakeFormal.LTS.CapacityCoherence

    PROVIDES:
    - serving_safety (HEADLINE: read-in-progress objects cannot be evicted)
    - serving_path (HEADLINE: Place → complete → BeginRead is constructive)
    - drain_respects_readers (HEADLINE: drain lifecycle preserves active readers)
    - reads_are_transparent (HEADLINE: balanced reads don't change state)
    - batch_eviction_safe (HEADLINE: evicting unrelated objects preserves reads)
    - invariant_preservation (HEADLINE: well_formed is global invariant)
    - protection_dichotomy (HEADLINE: every object is protected xor evictable)
*)

Require Import List Arith.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Diamond.
Require Import MooncakeFormal.LTS.ProtectionFrame.
Require Import MooncakeFormal.LTS.ObjectLifecycle.
Require Import MooncakeFormal.LTS.TraceEquivalence.
Require Import MooncakeFormal.LTS.RefcountCounting.
Require Import MooncakeFormal.LTS.NoDupPreservation.
Require Import MooncakeFormal.LTS.DrainSafety.
Require Import MooncakeFormal.LTS.RichConsistency.
Require Import MooncakeFormal.LTS.CapacityCoherence.

(** =====================================================================
    Section 1: SERVING SAFETY — reads cannot be disrupted
    ===================================================================== *)

(** HEADLINE Q1: A read-in-progress object cannot be evicted.

    This is the fundamental safety property of Mooncake's disaggregated
    KV cache: once a decode node starts reading a block via RDMA, the
    block cannot be reclaimed until the read completes.  The refcount
    mechanism ensures this:

    BeginRead increments refcount → eviction_protected = true
                                 → no Evict step exists

    Combined with the frame property: operations on OTHER objects
    don't affect this object's refcount.  So eviction remains blocked
    through arbitrary concurrent activity. *)
Theorem serving_safety : forall st oid m ls st',
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  exec st ls st' ->
  Forall (fun l => label_targets l oid = false) ls ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  intros st oid m ls st' Hfind Hrc Hexec Hall.
  exact (full_drain_safety st ls st' oid m Hexec Hall Hfind Hrc).
Qed.

(** HEADLINE: The full serving path is constructive.

    If a COMPLETE object exists on the segment, a BeginRead step
    exists.  This means: any COMPLETE object is readable.  Combined
    with serving_safety, this gives: once an object reaches COMPLETE,
    it can be read, and while being read, it is protected. *)
Theorem serving_path : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  om_status m = RsComplete ->
  exists st', rich_store_step st (RLBeginRead oid) st'.
Proof.
  intros st oid m Hfind Hcomp.
  exact (read_possible st oid m Hfind Hcomp).
Qed.

(** =====================================================================
    Section 2: READ TRANSPARENCY — balanced reads don't change state
    ===================================================================== *)

(** HEADLINE Q3: A balanced read session (BeginRead then EndRead on
    the same object) leaves the store in exactly its original state.

    This means reads are purely observational — they temporarily
    protect an object (via refcount) but leave no trace.  Any trace
    with balanced read sessions is equivalent to the same trace with
    those sessions removed. *)
Theorem reads_are_transparent : forall st oid st1 st2,
  rich_store_step st (RLBeginRead oid) st1 ->
  rich_store_step st1 (RLEndRead oid) st2 ->
  st = st2.
Proof.
  exact read_session_store_transparent.
Qed.

(** Corollary: balanced reads preserve the well-formedness invariant
    trivially — because they don't change the state at all. *)
Corollary balanced_read_preserves_wf : forall st oid st1 st2,
  store_well_formed st ->
  rich_store_step st (RLBeginRead oid) st1 ->
  rich_store_step st1 (RLEndRead oid) st2 ->
  store_well_formed st2.
Proof.
  intros st oid st1 st2 Hwf Hbegin Hend.
  rewrite <- (reads_are_transparent st oid st1 st2 Hbegin Hend).
  exact Hwf.
Qed.

(** =====================================================================
    Section 3: DRAIN-READ SAFETY — drain lifecycle respects readers
    ===================================================================== *)

(** HEADLINE Q2: During segment drain, actively-read objects survive.

    After BeginDrain and arbitrary removals of OTHER objects (those
    not being read), the actively-read object retains its metadata
    and eviction remains impossible.

    This answers the central concurrency question: can Mooncake
    reclaim a segment while RDMA reads are still active on some of
    its objects?  Yes — the drain only removes non-read objects. *)
Theorem drain_respects_readers : forall st st_drain oids st' oid m,
  rich_store_step st RLBeginDrain st_drain ->
  exec st_drain (map RLRemove oids) st' ->
  ~ In oid oids ->
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  exact drain_phase_safety.
Qed.

(** =====================================================================
    Section 4: BATCH EVICTION SAFETY
    ===================================================================== *)

(** Batch eviction of objects not targeting an actively-read object
    preserves the read.  This covers the BatchEvict code path in
    Mooncake's eviction strategy. *)
Theorem batch_eviction_safe : forall st oids st' oid m,
  exec st (map RLEvict oids) st' ->
  ~ In oid oids ->
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  intros st oids st' oid m Hexec Hni Hfind Hrc.
  assert (Hall : Forall (fun l => label_targets l oid = false)
                        (map RLEvict oids)).
  { rewrite Forall_forall. intros l Hin.
    apply in_map_iff in Hin. destruct Hin as [oid' [Hl Hin']].
    subst. simpl. apply Nat.eqb_neq. intro Heq.
    apply Hni. rewrite <- Heq. exact Hin'. }
  split.
  - exact (trace_non_targeting_preserves_find
             st (map RLEvict oids) st' oid m
             (exec_to_lstar st (map RLEvict oids) st' Hexec)
             Hall Hfind).
  - exact (read_eviction_safety st' oid m
             (trace_non_targeting_preserves_find
                st (map RLEvict oids) st' oid m
                (exec_to_lstar st (map RLEvict oids) st' Hexec)
                Hall Hfind)
             Hrc).
Qed.

(** =====================================================================
    Section 5: INVARIANT PRESERVATION
    ===================================================================== *)

(** HEADLINE Q4: The combined structural invariant (store_consistent ∧
    capacity_coherent ∧ NoDup) is preserved by every operation. *)
Theorem invariant_preservation : forall st l st',
  store_well_formed st ->
  place_fresh st l ->
  rich_store_step st l st' ->
  store_well_formed st'.
Proof.
  exact step_preserves_well_formed.
Qed.

(** The global consistency invariant is independently preserved
    by every step, without needing freshness or NoDup. *)
Theorem consistency_always_preserved : forall st l st',
  store_consistent st ->
  rich_store_step st l st' ->
  store_consistent st'.
Proof.
  exact rich_step_preserves_consistency.
Qed.

(** =====================================================================
    Section 6: PROTECTION DICHOTOMY
    ===================================================================== *)

(** HEADLINE: Every findable object is in exactly one of two states:
    protected (eviction impossible) or evictable (eviction possible).
    There is no middle ground.

    Protected means: hard-pinned, or has active readers, or not yet
    readable (INITIALIZED/PROCESSING/FAILED).

    This is the safety/liveness characterization: every object either
    CAN be evicted (liveness for space recovery) or CANNOT be evicted
    (safety for active reads). *)
Theorem protection_dichotomy : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  (eviction_protected m = true /\
   ~ exists st', rich_store_step st (RLEvict oid) st') \/
  (eviction_protected m = false /\
   exists st', rich_store_step st (RLEvict oid) st').
Proof.
  exact read_or_evict.
Qed.

(** =====================================================================
    Section 7: REFCOUNT ACCOUNTING
    ===================================================================== *)

(** HEADLINE: Refcount is exactly the difference between BeginReads
    and EndReads in the trace history.  This makes protection a
    consequence of arithmetic: if more reads began than ended, the
    object is protected.

    reads_only_for l oid means: l either doesn't target oid, or l is
    BeginRead/EndRead for oid.  In other words, the only operations
    that touch oid's metadata are reads. *)
Theorem refcount_is_read_balance : forall st oid ls st' m m',
  exec st ls st' ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some m' ->
  Forall (fun l => reads_only_for l oid) ls ->
  om_ref_count m' + count_ends oid ls =
  om_ref_count m + count_begins oid ls.
Proof.
  exact refcount_counting.
Qed.
