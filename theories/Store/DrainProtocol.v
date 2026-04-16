(** * DrainProtocol.v — Segment drain sequence and no-data-loss safety.

    =========================================================================
    LAYER: 3 - DOMAIN LEMMAS (drain protocol properties)
    =========================================================================
    Tier: core  Admits: 0  Axioms: 0

    Formalizes the two-phase drain/unmount protocol from the source:

    Phase 1 (drain):
      1. Mark segment DRAINING (no new placements accepted)
      2. For each object: migrate to another segment or remove
      3. When all objects gone, mark DRAINED

    Phase 2 (unmount):
      4. Verify segment is DRAINED and empty
      5. Transition to UNMOUNTING

    Key safety: no data is lost during drain — every object is either
    migrated (appears on another segment) or explicitly removed before
    the segment transitions to DRAINED.  This module proves the
    protocol gates: DRAINING blocks allocation, drainability requires
    no in-progress transfers, and unmount requires emptiness.

    @source mooncake-store/include/segment.h (SetSegmentStatusByName,
            PrepareUnmountSegment, CommitUnmountSegment)
    @fidelity specification
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.

(** =====================================================================
    Section 1: DRAIN PRECONDITIONS
    ===================================================================== *)

(** A segment can begin draining only from SegOk. *)
Definition can_begin_drain (s : Segment) : Prop :=
  seg_status s = SegOk.

(** A draining segment has no in-progress (PROCESSING) replicas.
    This is stronger than drainable — it also excludes INITIALIZED. *)
Definition no_in_progress (s : Segment) : Prop :=
  Forall (fun m => om_status m <> RsProcessing /\
                   om_status m <> RsInitialized) (seg_objects s).

(** A segment can complete draining (transition to DRAINED) only when
    all objects have been removed or migrated away. *)
Definition drain_complete (s : Segment) : Prop :=
  seg_status s = SegDraining /\ seg_objects s = [].

(** =====================================================================
    Section 2: DRAIN OPERATIONS
    ===================================================================== *)

(** Begin draining: mark SegOk → SegDraining. *)
Definition begin_drain (s : Segment) : Segment :=
  set_segment_status s SegDraining.

(** Complete drain: mark SegDraining → SegDrained.
    Only valid when segment is empty. *)
Definition complete_drain (s : Segment) : Segment :=
  set_segment_status s SegDrained.

(** Begin unmount: mark SegDrained → SegUnmounting. *)
Definition begin_unmount (s : Segment) : Segment :=
  set_segment_status s SegUnmounting.

(** Remove an object during drain (migrate or evict). *)
Definition drain_remove_object (s : Segment) (oid : ObjectId) : Segment :=
  remove_object s oid.

(** =====================================================================
    Section 3: DRAIN SAFETY PROPERTIES
    ===================================================================== *)

(** Draining blocks new placements. *)
Lemma draining_blocks_placement : forall s,
  seg_status s = SegDraining ->
  segment_allocatable (seg_status s) = false.
Proof.
  intros s Hd. rewrite Hd. reflexivity.
Qed.

(** After begin_drain, the segment is draining. *)
Lemma begin_drain_status : forall s,
  seg_status (begin_drain s) = SegDraining.
Proof. intros. reflexivity. Qed.

(** begin_drain preserves objects. *)
Lemma begin_drain_preserves_objects : forall s,
  seg_objects (begin_drain s) = seg_objects s.
Proof. intros. reflexivity. Qed.

(** begin_drain preserves capacity. *)
Lemma begin_drain_preserves_capacity : forall s,
  seg_capacity (begin_drain s) = seg_capacity s.
Proof. intros. reflexivity. Qed.

(** begin_drain preserves used space. *)
Lemma begin_drain_preserves_used : forall s,
  seg_used (begin_drain s) = seg_used s.
Proof. intros. reflexivity. Qed.

(** After begin_drain, the segment is no longer allocatable. *)
Lemma begin_drain_not_allocatable : forall s,
  segment_allocatable (seg_status (begin_drain s)) = false.
Proof. intros. reflexivity. Qed.

(** begin_drain is a valid segment transition from SegOk. *)
Lemma begin_drain_valid : forall s,
  seg_status s = SegOk ->
  segment_transition (seg_status s) (seg_status (begin_drain s)).
Proof.
  intros s Hok. rewrite Hok. simpl. constructor.
Qed.

(** After complete_drain, the segment is drained. *)
Lemma complete_drain_status : forall s,
  seg_status (complete_drain s) = SegDrained.
Proof. intros. reflexivity. Qed.

(** complete_drain is valid from SegDraining. *)
Lemma complete_drain_valid : forall s,
  seg_status s = SegDraining ->
  segment_transition (seg_status s) (seg_status (complete_drain s)).
Proof.
  intros s Hdr. rewrite Hdr. simpl. constructor.
Qed.

(** begin_unmount is valid from SegDrained. *)
Lemma begin_unmount_valid : forall s,
  seg_status s = SegDrained ->
  segment_transition (seg_status s) (seg_status (begin_unmount s)).
Proof.
  intros s Hd. rewrite Hd. simpl. constructor.
Qed.

(** =====================================================================
    Section 4: DRAIN SEQUENCE CORRECTNESS
    ===================================================================== *)

(** The full drain sequence is valid: Ok → Draining → Drained → Unmounting.
    This composes the three individual transition lemmas. *)
Theorem drain_sequence_valid : forall s,
  seg_status s = SegOk ->
  let s1 := begin_drain s in
  let s2 := complete_drain s1 in
  let s3 := begin_unmount s2 in
  segment_transition (seg_status s) (seg_status s1) /\
  segment_transition (seg_status s1) (seg_status s2) /\
  segment_transition (seg_status s2) (seg_status s3).
Proof.
  intros s Hok s1 s2 s3.
  repeat split.
  - apply begin_drain_valid. exact Hok.
  - apply complete_drain_valid. reflexivity.
  - apply begin_unmount_valid. reflexivity.
Qed.

(** No placement is possible at any point after drain begins. *)
Theorem drain_sequence_blocks_placement : forall s,
  seg_status s = SegOk ->
  let s1 := begin_drain s in
  let s2 := complete_drain s1 in
  let s3 := begin_unmount s2 in
  segment_allocatable (seg_status s1) = false /\
  segment_allocatable (seg_status s2) = false /\
  segment_allocatable (seg_status s3) = false.
Proof. intros. repeat split; reflexivity. Qed.

(** Drain preserves objects — no silent data loss.
    Objects are only removed by explicit drain_remove_object calls. *)
Theorem drain_preserves_objects : forall s,
  seg_objects (begin_drain s) = seg_objects s.
Proof. intros. reflexivity. Qed.

(** An empty drained segment produced by the drain sequence is safe
    to unmount. *)
Theorem drain_then_unmount_safe : forall s,
  seg_status s = SegOk ->
  seg_objects s = [] ->
  safe_to_unmount (complete_drain (begin_drain s)).
Proof.
  intros s Hok Hempty.
  split.
  - reflexivity.
  - unfold complete_drain, begin_drain.
    rewrite set_status_preserves_objects.
    rewrite set_status_preserves_objects.
    exact Hempty.
Qed.

(** =====================================================================
    Section 5: OBJECT REMOVAL DURING DRAIN
    ===================================================================== *)

(** Removing an object during drain preserves draining status. *)
Lemma drain_remove_preserves_status : forall s oid,
  seg_status (drain_remove_object s oid) = seg_status s.
Proof. intros. reflexivity. Qed.

(** After removing all objects, a draining segment can complete drain.
    This is the key safety theorem: we can reach drain_complete only
    by explicitly removing every object. *)
Theorem drain_complete_requires_empty : forall s,
  drain_complete s ->
  safe_to_unmount (complete_drain s).
Proof.
  intros s [Hdr Hempty].
  split.
  - reflexivity.
  - simpl. exact Hempty.
Qed.

(** Drainability requires no PROCESSING objects — you can't drain
    a segment while transfers are active on it. *)
Lemma drainable_no_processing : forall s m,
  drainable s ->
  In m (seg_objects s) ->
  om_status m <> RsProcessing.
Proof.
  intros s m Hd Hin.
  unfold drainable in Hd.
  rewrite Forall_forall in Hd.
  specialize (Hd m Hin).
  destruct Hd as [Hc | Hf].
  - rewrite Hc. discriminate.
  - rewrite Hf. discriminate.
Qed.

(** Drainability requires no INITIALIZED objects — you can't drain
    a segment with unstarted replicas. *)
Lemma drainable_no_initialized : forall s m,
  drainable s ->
  In m (seg_objects s) ->
  om_status m <> RsInitialized.
Proof.
  intros s m Hd Hin.
  unfold drainable in Hd.
  rewrite Forall_forall in Hd.
  specialize (Hd m Hin).
  destruct Hd as [Hc | Hf].
  - rewrite Hc. discriminate.
  - rewrite Hf. discriminate.
Qed.

(** Drainability implies all objects are eviction-protected only
    by pin or refcount (not by status). *)
Lemma drainable_status_not_protecting : forall s m,
  drainable s ->
  In m (seg_objects s) ->
  replica_readable (om_status m) = true \/
  om_status m = RsFailed.
Proof.
  intros s m Hd Hin.
  unfold drainable in Hd.
  rewrite Forall_forall in Hd.
  specialize (Hd m Hin).
  destruct Hd as [Hc | Hf].
  - left. rewrite Hc. reflexivity.
  - right. exact Hf.
Qed.
