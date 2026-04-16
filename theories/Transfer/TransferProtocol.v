(** * TransferProtocol.v — KV cache transfer protocol and safety.

    =========================================================================
    LAYER: 2 - BASE LEMMAS (transfer lifecycle properties)
    =========================================================================
    Tier: core  Admits: 0  Axioms: 0

    Formalizes the protocol for moving KV cache blocks between nodes:

    1. Allocate replica on destination segment (status = Initialized)
    2. Create transfer task (status = Pending)
    3. Execute transfer (Pending → Active → Completed/Failed)
    4. Update replica (Processing → Complete/Failed)
    5. On failure, clean up replica (→ Removed)

    Key safety: a transfer task must not outlive the replica it targets,
    and slice completion must be monotonic.

    @source Mooncake (kvcache-ai/Mooncake)
    @fidelity specification
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Core.DecidableEq.
Require Import MooncakeFormal.Core.Core.

(** =====================================================================
    Section 1: TRANSFER STATE MACHINE
    ===================================================================== *)

(** Valid transfer status transitions. *)
Inductive transfer_transition : TransferStatus -> TransferStatus -> Prop :=
  | tt_pend_active : transfer_transition TsPending TsActive
  | tt_active_comp : transfer_transition TsActive TsCompleted
  | tt_active_fail : transfer_transition TsActive TsFailed.

(** Terminal transfer states. *)
Definition transfer_terminal (s : TransferStatus) : bool :=
  match s with
  | TsCompleted => true
  | TsFailed => true
  | _ => false
  end.

(** =====================================================================
    Section 2: TRANSFER OPERATIONS
    ===================================================================== *)

Section TransferOps.

  (** Create a new transfer task. *)
  Definition create_task (op : OpCode) (oid : ObjectId)
      (src : NodeId) (dst : SegmentId) (total : nat) : TransferTask :=
    mkTransferTask op oid src dst TsPending total 0.

  (** Advance a transfer task by completing one slice. *)
  Definition complete_slice (t : TransferTask) : TransferTask :=
    mkTransferTask
      (tt_op t) (tt_object t) (tt_src_node t) (tt_dst_segment t)
      (tt_status t) (tt_total_slices t) (tt_done_slices t + 1).

  (** Set transfer status. *)
  Definition set_transfer_status (t : TransferTask) (s : TransferStatus)
      : TransferTask :=
    mkTransferTask
      (tt_op t) (tt_object t) (tt_src_node t) (tt_dst_segment t)
      s (tt_total_slices t) (tt_done_slices t).

  (** Activate a pending task. *)
  Definition activate_task (t : TransferTask) : TransferTask :=
    set_transfer_status t TsActive.

  (** Mark task as completed. *)
  Definition finish_task (t : TransferTask) : TransferTask :=
    set_transfer_status t TsCompleted.

  (** Mark task as failed. *)
  Definition fail_task (t : TransferTask) : TransferTask :=
    set_transfer_status t TsFailed.

End TransferOps.

(** =====================================================================
    Section 3: TRANSFER INVARIANTS
    ===================================================================== *)

(** Slice count monotonicity: done_slices <= total_slices. *)
Definition slice_invariant (t : TransferTask) : Prop :=
  tt_done_slices t <= tt_total_slices t.

(** A completed task has all slices done. *)
Definition completion_coherent (t : TransferTask) : Prop :=
  tt_status t = TsCompleted ->
  tt_done_slices t = tt_total_slices t.

(** =====================================================================
    Section 4: PROPERTIES
    ===================================================================== *)

(** A new task starts pending with 0 slices done. *)
Lemma create_task_pending : forall op oid src dst total,
  tt_status (create_task op oid src dst total) = TsPending.
Proof. intros. reflexivity. Qed.

Lemma create_task_zero_slices : forall op oid src dst total,
  tt_done_slices (create_task op oid src dst total) = 0.
Proof. intros. reflexivity. Qed.

(** A new task satisfies the slice invariant. *)
Lemma create_task_slice_inv : forall op oid src dst total,
  slice_invariant (create_task op oid src dst total).
Proof. intros. unfold slice_invariant. simpl. lia. Qed.

(** Completing a slice preserves the status. *)
Lemma complete_slice_preserves_status : forall t,
  tt_status (complete_slice t) = tt_status t.
Proof. intros. reflexivity. Qed.

(** Completing a slice increments done count. *)
Lemma complete_slice_count : forall t,
  tt_done_slices (complete_slice t) = tt_done_slices t + 1.
Proof. intros. reflexivity. Qed.

(** Completing a slice preserves the invariant when room remains. *)
Lemma complete_slice_preserves_inv : forall t,
  slice_invariant t ->
  tt_done_slices t < tt_total_slices t ->
  slice_invariant (complete_slice t).
Proof.
  intros t Hinv Hlt. unfold slice_invariant in *. simpl. lia.
Qed.

(** Activating preserves slice counts. *)
Lemma activate_preserves_slices : forall t,
  tt_done_slices (activate_task t) = tt_done_slices t /\
  tt_total_slices (activate_task t) = tt_total_slices t.
Proof. intros. split; reflexivity. Qed.

(** No self-transitions for transfers. *)
Lemma transfer_no_self_transition : forall s,
  ~ transfer_transition s s.
Proof. intros s H. inversion H. Qed.

(** No transition out of terminal states. *)
Lemma no_transition_from_completed : forall s,
  ~ transfer_transition TsCompleted s.
Proof. intros s H. inversion H. Qed.

Lemma no_transition_from_failed : forall s,
  ~ transfer_transition TsFailed s.
Proof. intros s H. inversion H. Qed.

(** Transition from Pending is only to Active. *)
Lemma transition_from_pending : forall s,
  transfer_transition TsPending s -> s = TsActive.
Proof. intros s H. inversion H. reflexivity. Qed.

(** Transition from Active is to Completed or Failed. *)
Lemma transition_from_active : forall s,
  transfer_transition TsActive s -> s = TsCompleted \/ s = TsFailed.
Proof. intros s H. inversion H; auto. Qed.

(** task_finished reflects terminal status. *)
Lemma task_finished_iff : forall t,
  task_finished t = true <->
  (tt_status t = TsCompleted \/ tt_status t = TsFailed).
Proof.
  intros t. unfold task_finished. split.
  - destruct (tt_status t); intro H; try discriminate; auto.
  - destruct (tt_status t); intro H; try reflexivity;
    destruct H as [H|H]; discriminate.
Qed.
