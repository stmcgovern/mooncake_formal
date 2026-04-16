(** * ReplicaTransfer.v — Linking transfer completion to replica status.

    =========================================================================
    LAYER: 3 - DOMAIN LEMMAS (transfer-replica bridge)
    =========================================================================
    Tier: core  Admits: 0  Axioms: 0

    Bridges the Transfer and Core layers: when a transfer task completes,
    the targeted replica transitions accordingly.  When a transfer fails,
    the replica transitions to FAILED.  A transfer cannot target a
    REMOVED replica.

    The key invariant: while a transfer is active (not terminal), the
    targeted replica must be in PROCESSING state.  This is the
    transfer-replica coupling that prevents orphaned transfers and
    premature replica promotion.

    @source mooncake-store/include/replica.h (mark_complete, mark_processing)
    @source mooncake-store/include/transfer_task.h (TransferFuture callback)
    @fidelity specification
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Transfer.TransferProtocol.

(** =====================================================================
    Section 1: TRANSFER-REPLICA PAIRING
    ===================================================================== *)

(** A transfer-replica pair: a transfer task and the replica it targets. *)
Record TransferReplicaPair := mkTRPair {
  trp_task    : TransferTask;
  trp_replica : ObjectMeta;
}.

(** The coupling invariant: while a transfer is active (non-terminal),
    the replica must be in PROCESSING state.  When the transfer is
    terminal, the replica must have advanced accordingly. *)
Definition transfer_replica_coupled (p : TransferReplicaPair) : Prop :=
  transfer_terminal (tt_status (trp_task p)) = false ->
  om_status (trp_replica p) = RsProcessing.

(** The task targets the correct object. *)
Definition transfer_targets_replica (p : TransferReplicaPair) : Prop :=
  tt_object (trp_task p) = om_id (trp_replica p) /\
  tt_dst_segment (trp_task p) = om_segment (trp_replica p).

(** =====================================================================
    Section 2: TRANSFER COMPLETION PROTOCOL
    ===================================================================== *)

(** Update replica status based on transfer outcome. *)
Definition apply_transfer_result (m : ObjectMeta) (t : TransferTask)
    : ObjectMeta :=
  if task_succeeded t then
    mkObjectMeta (om_id m) (om_segment m) RsComplete
                 (om_pin m) (om_ref_count m) (om_size m)
  else if task_finished t then
    mkObjectMeta (om_id m) (om_segment m) RsFailed
                 (om_pin m) (om_ref_count m) (om_size m)
  else m.  (* transfer still in progress — no change *)

(** =====================================================================
    Section 3: PROPERTIES
    ===================================================================== *)

(** A succeeded transfer promotes replica to COMPLETE. *)
Lemma transfer_success_completes : forall m t,
  task_succeeded t = true ->
  om_status (apply_transfer_result m t) = RsComplete.
Proof.
  intros m t Hs. unfold apply_transfer_result.
  rewrite Hs. reflexivity.
Qed.

(** A finished-but-not-succeeded transfer marks replica FAILED. *)
Lemma transfer_failure_fails : forall m t,
  task_finished t = true ->
  task_succeeded t = false ->
  om_status (apply_transfer_result m t) = RsFailed.
Proof.
  intros m t Hf Hns. unfold apply_transfer_result.
  rewrite Hns. rewrite Hf. reflexivity.
Qed.

(** An in-progress transfer leaves replica unchanged. *)
Lemma transfer_in_progress_unchanged : forall m t,
  task_finished t = false ->
  apply_transfer_result m t = m.
Proof.
  intros m t Hnf. unfold apply_transfer_result.
  assert (task_succeeded t = false) as Hns.
  { unfold task_succeeded, task_finished in *.
    destruct (tt_status t); try reflexivity; discriminate. }
  rewrite Hns. rewrite Hnf. reflexivity.
Qed.

(** apply_transfer_result preserves object identity. *)
Lemma transfer_result_preserves_id : forall m t,
  om_id (apply_transfer_result m t) = om_id m.
Proof.
  intros m t. unfold apply_transfer_result.
  destruct (task_succeeded t); simpl; try reflexivity.
  destruct (task_finished t); simpl; reflexivity.
Qed.

(** apply_transfer_result preserves segment. *)
Lemma transfer_result_preserves_segment : forall m t,
  om_segment (apply_transfer_result m t) = om_segment m.
Proof.
  intros m t. unfold apply_transfer_result.
  destruct (task_succeeded t); simpl; try reflexivity.
  destruct (task_finished t); simpl; reflexivity.
Qed.

(** apply_transfer_result preserves size. *)
Lemma transfer_result_preserves_size : forall m t,
  om_size (apply_transfer_result m t) = om_size m.
Proof.
  intros m t. unfold apply_transfer_result.
  destruct (task_succeeded t); simpl; try reflexivity.
  destruct (task_finished t); simpl; reflexivity.
Qed.

(** =====================================================================
    Section 4: COUPLING PRESERVATION
    ===================================================================== *)

(** If we apply the transfer result to the replica when the task finishes,
    the coupling invariant holds vacuously (task is terminal). *)
Lemma apply_result_decouples : forall m t,
  task_finished t = true ->
  transfer_replica_coupled
    (mkTRPair t (apply_transfer_result m t)).
Proof.
  intros m t Hf. unfold transfer_replica_coupled. simpl.
  intro Hnt.
  apply task_finished_iff in Hf. destruct Hf as [Hf|Hf];
  rewrite Hf in Hnt; simpl in Hnt; discriminate.
Qed.

(** A processing replica paired with a non-terminal task is coupled. *)
Lemma processing_is_coupled : forall t m,
  om_status m = RsProcessing ->
  transfer_replica_coupled (mkTRPair t m).
Proof.
  intros t m Hp. unfold transfer_replica_coupled. simpl.
  intros _. exact Hp.
Qed.

(** =====================================================================
    Section 5: REPLICA STATUS GATE
    ===================================================================== *)

(** A succeeded transfer produces a readable replica. *)
Lemma transfer_success_readable : forall m t,
  task_succeeded t = true ->
  replica_readable (om_status (apply_transfer_result m t)) = true.
Proof.
  intros m t Hs. rewrite transfer_success_completes; auto.
Qed.

(** A completed replica resulting from a successful transfer is
    valid for the PROCESSING → COMPLETE transition. *)
Lemma transfer_success_valid_transition : forall m t,
  om_status m = RsProcessing ->
  task_succeeded t = true ->
  replica_transition (om_status m)
                     (om_status (apply_transfer_result m t)).
Proof.
  intros m t Hp Hs. rewrite Hp.
  rewrite transfer_success_completes; auto.
  constructor.
Qed.

(** A failed transfer produces a valid PROCESSING → FAILED transition. *)
Lemma transfer_failure_valid_transition : forall m t,
  om_status m = RsProcessing ->
  task_finished t = true ->
  task_succeeded t = false ->
  replica_transition (om_status m)
                     (om_status (apply_transfer_result m t)).
Proof.
  intros m t Hp Hf Hns. rewrite Hp.
  rewrite transfer_failure_fails; auto.
  constructor.
Qed.

(** A REMOVED replica cannot be the target of a coupled transfer. *)
Lemma removed_not_coupled_active : forall t m,
  om_status m = RsRemoved ->
  transfer_terminal (tt_status t) = false ->
  ~ transfer_replica_coupled (mkTRPair t m).
Proof.
  intros t m Hr Hnt Hc.
  unfold transfer_replica_coupled in Hc. simpl in Hc.
  specialize (Hc Hnt). rewrite Hr in Hc. discriminate.
Qed.
