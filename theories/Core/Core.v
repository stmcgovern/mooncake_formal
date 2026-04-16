(** * Core.v — Foundation types for Mooncake KV cache disaggregated serving.

    =========================================================================
    LAYER: 1 - PRIMITIVE DEFINITIONS
    =========================================================================
    Tier: core  Admits: 0  Axioms: 0

    Mooncake disaggregates KV cache from the inference engine: prefill
    nodes produce KV blocks that are stored in a distributed pool,
    and decode nodes fetch them on demand.  The system manages replica
    lifecycle (produce → transfer → serve → evict) and segment-level
    storage health (ok → draining → drained → unmounting).

    This module defines the core types:
    - Replica status (lifecycle state machine)
    - Segment status (storage node health)
    - Pin levels (eviction protection)
    - Object metadata and transfer tasks
    - Eviction safety predicates

    @source Mooncake (kvcache-ai/Mooncake)
    @fidelity specification
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Core.DecidableEq.
Require Import DistributedML.Core.Finite.

(** =====================================================================
    Section 1: IDENTIFIERS
    ===================================================================== *)

(** Unique object identifier (hash of prefix tokens). *)
Definition ObjectId := nat.

(** Segment identifier — a storage node partition. *)
Definition SegmentId := nat.

(** Node identifier — prefill or decode engine. *)
Definition NodeId := nat.

(** =====================================================================
    Section 2: REPLICA STATUS
    ===================================================================== *)

(** Replica lifecycle: tracks one copy of a KV block on one segment.

    INITIALIZED → PROCESSING → COMPLETE → REMOVED
                             ↘ FAILED → REMOVED

    A replica is readable only when COMPLETE.
    A replica is evictable only when COMPLETE and not pinned. *)
Inductive ReplicaStatus : Set :=
  | RsInitialized  (* Allocated, not yet written *)
  | RsProcessing   (* Transfer in progress *)
  | RsComplete     (* Successfully stored, readable *)
  | RsFailed       (* Transfer failed *)
  | RsRemoved.     (* Evicted or cleaned up *)

(** Valid replica transitions. *)
Inductive replica_transition : ReplicaStatus -> ReplicaStatus -> Prop :=
  | rt_init_proc   : replica_transition RsInitialized RsProcessing
  | rt_proc_comp   : replica_transition RsProcessing RsComplete
  | rt_proc_fail   : replica_transition RsProcessing RsFailed
  | rt_comp_remove : replica_transition RsComplete RsRemoved
  | rt_fail_remove : replica_transition RsFailed RsRemoved.

(** Terminal state: REMOVED cannot transition further. *)
Definition replica_terminal (s : ReplicaStatus) : bool :=
  match s with RsRemoved => true | _ => false end.

(** Readable: only COMPLETE replicas serve reads. *)
Definition replica_readable (s : ReplicaStatus) : bool :=
  match s with RsComplete => true | _ => false end.

(** =====================================================================
    Section 3: SEGMENT STATUS
    ===================================================================== *)

(** Segment health: tracks a storage node's partition lifecycle.

    SegOk → SegDraining → SegDrained → SegUnmounting

    New replicas can only be placed on SegOk segments. *)
Inductive SegmentStatus : Set :=
  | SegOk          (* Healthy, accepting new replicas *)
  | SegDraining    (* Marked for drain, no new replicas *)
  | SegDrained     (* All replicas migrated away *)
  | SegUnmounting. (* Being removed from cluster *)

(** Valid segment transitions. *)
Inductive segment_transition : SegmentStatus -> SegmentStatus -> Prop :=
  | st_ok_drain     : segment_transition SegOk SegDraining
  | st_drain_drained : segment_transition SegDraining SegDrained
  | st_drained_unmount : segment_transition SegDrained SegUnmounting.

(** Allocatable: only SegOk segments accept new replicas. *)
Definition segment_allocatable (s : SegmentStatus) : bool :=
  match s with SegOk => true | _ => false end.

(** =====================================================================
    Section 4: PIN LEVELS AND EVICTION
    ===================================================================== *)

(** Pin levels: prevent eviction of hot KV blocks.
    HardPinned > SoftPinned > Unpinned. *)
Inductive PinLevel : Set :=
  | Unpinned     (* Evictable by LRU *)
  | SoftPinned   (* Evictable under pressure *)
  | HardPinned.  (* Not evictable *)

(** Pin level ordering: higher = stronger protection. *)
Definition pin_level_le (a b : PinLevel) : bool :=
  match a, b with
  | Unpinned, _ => true
  | SoftPinned, SoftPinned => true
  | SoftPinned, HardPinned => true
  | HardPinned, HardPinned => true
  | _, _ => false
  end.

(** =====================================================================
    Section 5: OBJECT METADATA
    ===================================================================== *)

(** Metadata for a cached KV block. *)
Record ObjectMeta := mkObjectMeta {
  om_id        : ObjectId;
  om_segment   : SegmentId;
  om_status    : ReplicaStatus;
  om_pin       : PinLevel;
  om_ref_count : nat;        (* active readers *)
  om_size      : nat;        (* size in bytes *)
}.

(** An object is protected from eviction if:
    - it is hard-pinned, OR
    - it has active readers (ref_count > 0), OR
    - it is not yet complete *)
Definition eviction_protected (m : ObjectMeta) : bool :=
  match om_pin m with
  | HardPinned => true
  | _ =>
    if Nat.ltb 0 (om_ref_count m) then true
    else negb (replica_readable (om_status m))
  end.

(** =====================================================================
    Section 6: TRANSFER TASKS
    ===================================================================== *)

(** Operation codes for transfers. *)
Inductive OpCode : Set :=
  | OpPut     (* Store KV block to segment *)
  | OpGet.    (* Fetch KV block from segment *)

(** Transfer status. *)
Inductive TransferStatus : Set :=
  | TsPending    (* Queued *)
  | TsActive     (* In progress *)
  | TsCompleted  (* Success *)
  | TsFailed.    (* Error *)

(** Transfer task: move a KV block between nodes. *)
Record TransferTask := mkTransferTask {
  tt_op          : OpCode;
  tt_object      : ObjectId;
  tt_src_node    : NodeId;
  tt_dst_segment : SegmentId;
  tt_status      : TransferStatus;
  tt_total_slices : nat;    (* total slices to transfer *)
  tt_done_slices  : nat;    (* slices completed *)
}.

(** A transfer is finished (success or failure). *)
Definition task_finished (t : TransferTask) : bool :=
  match tt_status t with
  | TsCompleted => true
  | TsFailed => true
  | _ => false
  end.

(** A transfer succeeded and all slices are done. *)
Definition task_succeeded (t : TransferTask) : bool :=
  match tt_status t with
  | TsCompleted => Nat.eqb (tt_done_slices t) (tt_total_slices t)
  | _ => false
  end.

(** =====================================================================
    Section 7: DECIDABLE EQUALITY
    ===================================================================== *)

Definition replica_status_eqb (x y : ReplicaStatus) : bool :=
  match x, y with
  | RsInitialized, RsInitialized => true
  | RsProcessing, RsProcessing => true
  | RsComplete, RsComplete => true
  | RsFailed, RsFailed => true
  | RsRemoved, RsRemoved => true
  | _, _ => false
  end.

Lemma replica_status_eqb_spec : forall x y,
  replica_status_eqb x y = true <-> x = y.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

#[global] Instance replica_status_DecEq : DecEq ReplicaStatus :=
  { dec_eqb := replica_status_eqb; dec_eqb_spec := replica_status_eqb_spec }.

Definition segment_status_eqb (x y : SegmentStatus) : bool :=
  match x, y with
  | SegOk, SegOk => true
  | SegDraining, SegDraining => true
  | SegDrained, SegDrained => true
  | SegUnmounting, SegUnmounting => true
  | _, _ => false
  end.

Lemma segment_status_eqb_spec : forall x y,
  segment_status_eqb x y = true <-> x = y.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

#[global] Instance segment_status_DecEq : DecEq SegmentStatus :=
  { dec_eqb := segment_status_eqb; dec_eqb_spec := segment_status_eqb_spec }.

Definition pin_level_eqb (x y : PinLevel) : bool :=
  match x, y with
  | Unpinned, Unpinned => true
  | SoftPinned, SoftPinned => true
  | HardPinned, HardPinned => true
  | _, _ => false
  end.

Lemma pin_level_eqb_spec : forall x y,
  pin_level_eqb x y = true <-> x = y.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

#[global] Instance pin_level_DecEq : DecEq PinLevel :=
  { dec_eqb := pin_level_eqb; dec_eqb_spec := pin_level_eqb_spec }.

Definition opcode_eqb (x y : OpCode) : bool :=
  match x, y with
  | OpPut, OpPut => true
  | OpGet, OpGet => true
  | _, _ => false
  end.

Lemma opcode_eqb_spec : forall x y,
  opcode_eqb x y = true <-> x = y.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

#[global] Instance opcode_DecEq : DecEq OpCode :=
  { dec_eqb := opcode_eqb; dec_eqb_spec := opcode_eqb_spec }.

Definition transfer_status_eqb (x y : TransferStatus) : bool :=
  match x, y with
  | TsPending, TsPending => true
  | TsActive, TsActive => true
  | TsCompleted, TsCompleted => true
  | TsFailed, TsFailed => true
  | _, _ => false
  end.

Lemma transfer_status_eqb_spec : forall x y,
  transfer_status_eqb x y = true <-> x = y.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

#[global] Instance transfer_status_DecEq : DecEq TransferStatus :=
  { dec_eqb := transfer_status_eqb; dec_eqb_spec := transfer_status_eqb_spec }.

(** =====================================================================
    Section 8: STATE MACHINE PROPERTIES
    ===================================================================== *)

(** No self-transitions for replicas. *)
Lemma replica_no_self_transition : forall s,
  ~ replica_transition s s.
Proof. intros s H. inversion H. Qed.

(** No self-transitions for segments. *)
Lemma segment_no_self_transition : forall s,
  ~ segment_transition s s.
Proof. intros s H. inversion H. Qed.

(** Readable implies complete. *)
Lemma readable_is_complete : forall s,
  replica_readable s = true -> s = RsComplete.
Proof. intros [] H; simpl in H; try discriminate; reflexivity. Qed.

(** Processing replicas are not evictable (they are protected). *)
Lemma processing_not_evictable : forall m,
  om_status m = RsProcessing ->
  eviction_protected m = true.
Proof.
  intros m Hs. unfold eviction_protected.
  destruct (om_pin m).
  - simpl. destruct (Nat.ltb 0 (om_ref_count m)); simpl; auto.
    rewrite Hs. simpl. reflexivity.
  - simpl. destruct (Nat.ltb 0 (om_ref_count m)); simpl; auto.
    rewrite Hs. simpl. reflexivity.
  - reflexivity.
Qed.

(** Hard-pinned objects are always protected. *)
Lemma hard_pinned_protected : forall m,
  om_pin m = HardPinned ->
  eviction_protected m = true.
Proof.
  intros m Hp. unfold eviction_protected. rewrite Hp. reflexivity.
Qed.

(** Objects with active readers are protected. *)
Lemma active_readers_protected : forall m,
  om_ref_count m > 0 ->
  eviction_protected m = true.
Proof.
  intros m Hr. unfold eviction_protected.
  destruct (om_pin m); simpl.
  - assert (Nat.ltb 0 (om_ref_count m) = true) as ->.
    { apply Nat.ltb_lt. lia. } reflexivity.
  - assert (Nat.ltb 0 (om_ref_count m) = true) as ->.
    { apply Nat.ltb_lt. lia. } reflexivity.
  - reflexivity.
Qed.

(** Only SegOk segments are allocatable. *)
Lemma allocatable_is_ok : forall s,
  segment_allocatable s = true -> s = SegOk.
Proof. intros [] H; simpl in H; try discriminate; reflexivity. Qed.

(** No transition out of REMOVED. *)
Lemma no_transition_from_removed : forall s,
  ~ replica_transition RsRemoved s.
Proof. intros s H. inversion H. Qed.

(** No transition out of SegUnmounting. *)
Lemma no_transition_from_unmounting : forall s,
  ~ segment_transition SegUnmounting s.
Proof. intros s H. inversion H. Qed.

(** Replica transitions preserve: not-yet-removed implies reachable from init. *)
Lemma replica_transition_from_init : forall s,
  replica_transition RsInitialized s -> s = RsProcessing.
Proof. intros s H. inversion H. reflexivity. Qed.

Lemma replica_transition_from_processing : forall s,
  replica_transition RsProcessing s -> s = RsComplete \/ s = RsFailed.
Proof. intros s H. inversion H; auto. Qed.
