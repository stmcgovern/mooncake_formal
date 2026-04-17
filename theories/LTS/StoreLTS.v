(** * StoreLTS.v — Unified labeled transition system for the KV cache store.

    =========================================================================
    LAYER: 2 - BASE LEMMAS (LTS infrastructure)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Recasts the store as a single labeled transition system (LTS) and
    derives multi-step invariant preservation from the existing single-step
    theorems.  The key consumer theorem is [store_consistent_star]: the
    global invariant holds through arbitrary sequences of valid steps.

    @source composition of replica.h × segment.h × transfer_task.h
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core (types, state machines)
    - MooncakeFormal.Store.SegmentManager (Segment, operations)
    - MooncakeFormal.Store.DrainProtocol (drain operations)
    - MooncakeFormal.Composition.StoreComposition (store_consistent)
    - DistributedML.Concurrency.Preservation (star, lstar)

    PROVIDES:
    - StoreLabel (labeled operations)
    - store_step (unified step relation)
    - store_step_preserves_consistency (single-step)
    - store_consistent_star (multi-step via lstar)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.Preservation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Transfer.TransferProtocol.
Require Import MooncakeFormal.Transfer.ReplicaTransfer.
Require Import MooncakeFormal.Composition.StoreComposition.

(** =====================================================================
    Section 1: STORE LABELS
    ===================================================================== *)

(** Operations on the store, each a distinct label in the LTS. *)
Inductive StoreLabel : Set :=
  | LPlace (m : ObjectMeta)       (* place initialized object on segment *)
  | LRemove (oid : ObjectId)      (* remove object from segment *)
  | LBeginDrain                   (* SegOk → SegDraining *)
  | LCompleteDrain                (* SegDraining → SegDrained, segment empty *)
  | LUnmount.                    (* SegDrained → SegUnmounting *)

(** =====================================================================
    Section 2: STORE STEP RELATION
    ===================================================================== *)

(** The unified step relation.  Each constructor wraps an existing
    operation with its preconditions as guards. *)
Inductive store_step : StoreState -> StoreLabel -> StoreState -> Prop :=

  (** Place an initialized object on a healthy segment. *)
  | step_place : forall st m,
      seg_status (ss_segment st) = SegOk ->
      om_status m = RsInitialized ->
      replica_terminal (om_status m) = false ->
      store_step st (LPlace m)
        (mkStoreState (place_object (ss_segment st) m) (ss_transfers st))

  (** Remove an object from the segment (eviction or cleanup). *)
  | step_remove : forall st oid,
      store_step st (LRemove oid)
        (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st))

  (** Begin draining: SegOk → SegDraining, no in-progress objects. *)
  | step_begin_drain : forall st,
      seg_status (ss_segment st) = SegOk ->
      no_in_progress (ss_segment st) ->
      store_step st LBeginDrain
        (mkStoreState (begin_drain (ss_segment st)) (ss_transfers st))

  (** Complete drain: SegDraining → SegDrained, segment must be empty. *)
  | step_complete_drain : forall st,
      seg_status (ss_segment st) = SegDraining ->
      seg_objects (ss_segment st) = [] ->
      store_step st LCompleteDrain
        (mkStoreState (complete_drain (ss_segment st)) (ss_transfers st))

  (** Unmount: SegDrained → SegUnmounting. *)
  | step_unmount : forall st,
      safe_to_unmount (ss_segment st) ->
      store_step st LUnmount
        (mkStoreState (begin_unmount (ss_segment st)) (ss_transfers st)).

(** =====================================================================
    Section 3: SINGLE-STEP PRESERVATION
    ===================================================================== *)

(** Complete drain preserves store_consistent. *)
Lemma complete_drain_preserves_consistency : forall st,
  store_consistent st ->
  seg_status (ss_segment st) = SegDraining ->
  seg_objects (ss_segment st) = [] ->
  store_consistent
    (mkStoreState (complete_drain (ss_segment st)) (ss_transfers st)).
Proof.
  intros st [Hlive [Htc Hdc]] Hdr Hempty.
  unfold store_consistent. repeat split.
  - unfold objects_live, all_objects_live, complete_drain, set_segment_status.
    simpl. rewrite Hempty. constructor.
  - exact Htc.
  - unfold drain_consistent, complete_drain, set_segment_status.
    simpl. intros _. rewrite Hempty. constructor.
Qed.

(** Unmount preserves store_consistent. *)
Lemma unmount_preserves_consistency : forall st,
  store_consistent st ->
  safe_to_unmount (ss_segment st) ->
  store_consistent
    (mkStoreState (begin_unmount (ss_segment st)) (ss_transfers st)).
Proof.
  intros st [Hlive [Htc Hdc]] [Hdr Hempty].
  unfold store_consistent. repeat split.
  - unfold objects_live, all_objects_live, begin_unmount, set_segment_status.
    simpl. rewrite Hempty. constructor.
  - exact Htc.
  - unfold drain_consistent, begin_unmount, set_segment_status.
    simpl. intros _. rewrite Hempty. constructor.
Qed.

(** Every store_step preserves store_consistent. *)
Theorem store_step_preserves_consistency : forall st l st',
  store_consistent st ->
  store_step st l st' ->
  store_consistent st'.
Proof.
  intros st l st' Hsc Hstep. inversion Hstep; subst.
  - (* LPlace *)
    apply place_preserves_consistency; assumption.
  - (* LRemove *)
    apply remove_preserves_consistency. exact Hsc.
  - (* LBeginDrain *)
    apply begin_drain_preserves_consistency; assumption.
  - (* LCompleteDrain *)
    apply complete_drain_preserves_consistency; assumption.
  - (* LUnmount *)
    apply unmount_preserves_consistency; assumption.
Qed.

(** =====================================================================
    Section 4: MULTI-STEP PRESERVATION
    ===================================================================== *)

(** store_consistent is preserved through arbitrary sequences of valid
    store steps.  This is the main consumer theorem.

    Proof: instantiate DML's lstar_preserved with
    store_step_preserves_consistency. *)
Theorem store_consistent_star : forall st ls st',
  store_consistent st ->
  lstar store_step st ls st' ->
  store_consistent st'.
Proof.
  intros st ls st' Hsc Hstar.
  exact (lstar_preserved store_step store_consistent
           store_step_preserves_consistency
           st ls st' Hsc Hstar).
Qed.

(** =====================================================================
    Section 5: STEP CLASSIFICATION
    ===================================================================== *)

(** A step is "progress" if it advances the system toward quiescence
    rather than adding new external work.  Place adds a new object
    (increases rank), so it is not a progress step. *)
Definition is_progress_step (l : StoreLabel) : bool :=
  match l with
  | LPlace _ => false
  | _ => true
  end.

(** Every store_step produces a well-defined successor segment status. *)
Lemma store_step_segment_status : forall st l st',
  store_step st l st' ->
  seg_status (ss_segment st') =
    match l with
    | LPlace _ => seg_status (ss_segment st)
    | LRemove _ => seg_status (ss_segment st)
    | LBeginDrain => SegDraining
    | LCompleteDrain => SegDrained
    | LUnmount => SegUnmounting
    end.
Proof.
  intros st l st' Hstep. inversion Hstep; subst; reflexivity.
Qed.

(** Segment transitions arising from store_steps are valid. *)
Lemma store_step_valid_segment_transition : forall st l st',
  store_step st l st' ->
  is_progress_step l = true ->
  l <> LRemove (0) ->
  seg_status (ss_segment st') <> seg_status (ss_segment st) ->
  segment_transition (seg_status (ss_segment st)) (seg_status (ss_segment st')).
Proof.
  intros st l st' Hstep _ _ Hne.
  inversion Hstep; subst; simpl in *.
  - exfalso. apply Hne. reflexivity.
  - exfalso. apply Hne. reflexivity.
  - rewrite H. constructor.
  - rewrite H. constructor.
  - destruct H as [Hdr _]. rewrite Hdr. constructor.
Qed.
