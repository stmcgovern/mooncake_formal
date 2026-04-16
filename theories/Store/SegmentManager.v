(** * SegmentManager.v — Segment-level storage management.

    =========================================================================
    LAYER: 2 - BASE LEMMAS (segment lifecycle properties)
    =========================================================================
    Tier: core  Admits: 0  Axioms: 0

    Manages the storage segments that hold KV cache replicas.
    Each segment tracks its status, capacity, and hosted objects.
    Key safety: new replicas can only be placed on SegOk segments,
    and draining segments must migrate all replicas before unmounting.

    @source Mooncake (kvcache-ai/Mooncake)
    @fidelity specification
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Core.DecidableEq.
Require Import MooncakeFormal.Core.Core.

(** =====================================================================
    Section 1: SEGMENT STATE
    ===================================================================== *)

(** A segment's bookkeeping. *)
Record Segment := mkSegment {
  seg_id       : SegmentId;
  seg_status   : SegmentStatus;
  seg_capacity : nat;          (* max bytes *)
  seg_used     : nat;          (* bytes occupied *)
  seg_objects  : list ObjectMeta;
}.

(** A segment is well-formed: used <= capacity. *)
Definition segment_wf (s : Segment) : Prop :=
  seg_used s <= seg_capacity s.

(** A segment has room for an object of given size. *)
Definition segment_has_room (s : Segment) (size : nat) : bool :=
  Nat.leb (seg_used s + size) (seg_capacity s).

(** =====================================================================
    Section 2: SEGMENT OPERATIONS
    ===================================================================== *)

Section SegmentOps.

  (** Place a new object on a segment. *)
  Definition place_object (s : Segment) (m : ObjectMeta) : Segment :=
    mkSegment
      (seg_id s)
      (seg_status s)
      (seg_capacity s)
      (seg_used s + om_size m)
      (m :: seg_objects s).

  (** Remove an object from a segment by id. *)
  Definition remove_object (s : Segment) (oid : ObjectId) : Segment :=
    let removed := filter (fun m => negb (Nat.eqb (om_id m) oid)) (seg_objects s) in
    let freed := fold_left (fun acc m =>
      if Nat.eqb (om_id m) oid then acc + om_size m else acc) (seg_objects s) 0 in
    mkSegment
      (seg_id s)
      (seg_status s)
      (seg_capacity s)
      (seg_used s - freed)
      removed.

  (** Transition segment status. *)
  Definition set_segment_status (s : Segment) (new_status : SegmentStatus) : Segment :=
    mkSegment
      (seg_id s)
      new_status
      (seg_capacity s)
      (seg_used s)
      (seg_objects s).

  (** Check if segment is empty (no objects). *)
  Definition segment_empty (s : Segment) : bool :=
    match seg_objects s with
    | [] => true
    | _ => false
    end.

End SegmentOps.

(** =====================================================================
    Section 3: SAFETY INVARIANTS
    ===================================================================== *)

(** All objects on a segment are in non-removed state. *)
Definition all_objects_live (s : Segment) : Prop :=
  Forall (fun m => replica_terminal (om_status m) = false) (seg_objects s).

(** A segment can be drained only if all objects are removable
    (complete or failed, not processing). *)
Definition drainable (s : Segment) : Prop :=
  Forall (fun m =>
    om_status m = RsComplete \/ om_status m = RsFailed) (seg_objects s).

(** A drained segment must be empty before unmounting. *)
Definition safe_to_unmount (s : Segment) : Prop :=
  seg_status s = SegDrained /\ seg_objects s = [].

(** =====================================================================
    Section 4: PROPERTIES
    ===================================================================== *)

(** Placing an object on a SegOk segment preserves segment status. *)
Lemma place_preserves_status : forall s m,
  seg_status (place_object s m) = seg_status s.
Proof. intros. reflexivity. Qed.

(** Placing an object increases used space. *)
Lemma place_increases_used : forall s m,
  seg_used (place_object s m) = seg_used s + om_size m.
Proof. intros. reflexivity. Qed.

(** Placement is only safe on allocatable segments. *)
Lemma place_requires_ok : forall s,
  segment_allocatable (seg_status s) = true ->
  seg_status s = SegOk.
Proof. intros s H. apply allocatable_is_ok. exact H. Qed.

(** Setting status preserves objects. *)
Lemma set_status_preserves_objects : forall s new_st,
  seg_objects (set_segment_status s new_st) = seg_objects s.
Proof. intros. reflexivity. Qed.

(** Setting status preserves capacity. *)
Lemma set_status_preserves_capacity : forall s new_st,
  seg_capacity (set_segment_status s new_st) = seg_capacity s.
Proof. intros. reflexivity. Qed.

(** Empty segment is trivially drainable. *)
Lemma empty_segment_drainable : forall s,
  seg_objects s = [] -> drainable s.
Proof. intros s He. unfold drainable. rewrite He. constructor. Qed.

(** An empty drained segment is safe to unmount. *)
Lemma empty_drained_safe : forall s,
  seg_status s = SegDrained ->
  seg_objects s = [] ->
  safe_to_unmount s.
Proof. intros s Hst Ho. split; assumption. Qed.
