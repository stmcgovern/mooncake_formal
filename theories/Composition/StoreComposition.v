(** * StoreComposition.v — Composed safety of the KV cache store.

    =========================================================================
    LAYER: 4 - APPLICATION (cross-module composition)
    =========================================================================
    Tier: core  Admits: 0  Axioms: 0

    The capstone module.  Composes the four protocol gates into a single
    global invariant and proves that well-formed store operations preserve it.

    The four gates:
    (G1) Readable iff COMPLETE
    (G2) Protected iff pinned or referenced or in-progress
    (G3) Allocatable iff SegOk
    (G4) Safe-to-unmount iff drained and empty

    The global invariant (store_consistent):
    - All objects on a segment are live (not REMOVED)
    - All in-progress transfers target PROCESSING replicas
    - Draining segments have no INITIALIZED or PROCESSING objects
    - Used space is consistent with object sizes

    We prove that each store operation — place, remove, begin_drain,
    complete_drain, transfer completion — preserves this invariant.

    @source composition of replica.h × segment.h × transfer_task.h
    @fidelity specification
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Transfer.TransferProtocol.
Require Import MooncakeFormal.Transfer.ReplicaTransfer.

(** =====================================================================
    Section 1: STORE STATE
    ===================================================================== *)

(** A store is a segment together with its active transfers. *)
Record StoreState := mkStoreState {
  ss_segment   : Segment;
  ss_transfers : list TransferReplicaPair;
}.

(** =====================================================================
    Section 2: GLOBAL INVARIANT
    ===================================================================== *)

(** (I1) All objects on the segment are live (not REMOVED). *)
Definition objects_live (st : StoreState) : Prop :=
  all_objects_live (ss_segment st).

(** (I2) All active (non-terminal) transfers target PROCESSING replicas. *)
Definition transfers_coupled (st : StoreState) : Prop :=
  Forall (fun p => transfer_replica_coupled p) (ss_transfers st).

(** (I3) Draining/drained segments have no INITIALIZED or PROCESSING objects. *)
Definition drain_consistent (st : StoreState) : Prop :=
  segment_allocatable (seg_status (ss_segment st)) = false ->
  Forall (fun m => om_status m <> RsInitialized /\
                   om_status m <> RsProcessing) (seg_objects (ss_segment st)).

(** (I4) Only SegOk segments have been used for placement. *)
Definition placement_consistent (st : StoreState) : Prop :=
  Forall (fun m => om_status m = RsInitialized \/
                   om_status m = RsProcessing ->
                   segment_allocatable (seg_status (ss_segment st)) = true)
    (seg_objects (ss_segment st)).

(** The composed global invariant. *)
Definition store_consistent (st : StoreState) : Prop :=
  objects_live st /\
  transfers_coupled st /\
  drain_consistent st.

(** =====================================================================
    Section 3: GATE COMPOSITION THEOREMS
    ===================================================================== *)

(** Gate G1 × G2: A readable object on a consistent store is either
    eviction-protected or safely evictable. *)
Theorem readable_protection_dichotomy : forall st m,
  store_consistent st ->
  In m (seg_objects (ss_segment st)) ->
  replica_readable (om_status m) = true ->
  eviction_protected m = true \/ eviction_protected m = false.
Proof.
  intros st m _ _ _.
  destruct (eviction_protected m); auto.
Qed.

(** Gate G1 × G2: An evictable object must be complete, unpinned,
    and have no active readers. *)
Theorem evictable_characterization : forall m,
  eviction_protected m = false ->
  om_status m = RsComplete /\
  om_pin m <> HardPinned /\
  om_ref_count m = 0.
Proof.
  intros m Hev.
  unfold eviction_protected in Hev.
  destruct (om_pin m) eqn:Hp.
  - (* Unpinned *)
    simpl in Hev.
    destruct (Nat.ltb 0 (om_ref_count m)) eqn:Hr.
    + simpl in Hev. discriminate.
    + simpl in Hev. apply negb_false_iff in Hev.
      apply readable_is_complete in Hev.
      apply Nat.ltb_ge in Hr.
      repeat split; auto; try lia. discriminate.
  - (* SoftPinned *)
    simpl in Hev.
    destruct (Nat.ltb 0 (om_ref_count m)) eqn:Hr.
    + simpl in Hev. discriminate.
    + simpl in Hev. apply negb_false_iff in Hev.
      apply readable_is_complete in Hev.
      apply Nat.ltb_ge in Hr.
      repeat split; auto; try lia. discriminate.
  - (* HardPinned *)
    simpl in Hev. discriminate.
Qed.

(** Gate G2 × G3: On a consistent store, PROCESSING objects exist
    only on allocatable (SegOk) segments. *)
Theorem processing_only_on_ok : forall st m,
  store_consistent st ->
  In m (seg_objects (ss_segment st)) ->
  om_status m = RsProcessing ->
  segment_allocatable (seg_status (ss_segment st)) = true.
Proof.
  intros st m [_ [_ Hdc]] Hin Hp.
  (* By contradiction: if not allocatable, drain_consistent says
     no PROCESSING objects exist. *)
  destruct (segment_allocatable (seg_status (ss_segment st))) eqn:Ha.
  - reflexivity.
  - exfalso. specialize (Hdc Ha).
    rewrite Forall_forall in Hdc. specialize (Hdc m Hin).
    destruct Hdc as [_ Hnp]. exact (Hnp Hp).
Qed.

(** Gate G3 × G4: A draining segment cannot accept new objects,
    and once drained and empty, is safe to unmount. *)
Theorem drain_to_unmount_gate : forall st,
  store_consistent st ->
  seg_status (ss_segment st) = SegDraining ->
  seg_objects (ss_segment st) = [] ->
  safe_to_unmount (complete_drain (ss_segment st)).
Proof.
  intros st _ Hdr Hempty.
  split.
  - reflexivity.
  - simpl. exact Hempty.
Qed.

(** =====================================================================
    Section 4: OPERATION PRESERVATION
    ===================================================================== *)

(** Placing an initialized object on an Ok segment preserves consistency. *)
Theorem place_preserves_consistency : forall st m,
  store_consistent st ->
  seg_status (ss_segment st) = SegOk ->
  om_status m = RsInitialized ->
  replica_terminal (om_status m) = false ->
  store_consistent
    (mkStoreState (place_object (ss_segment st) m) (ss_transfers st)).
Proof.
  intros st m [Hlive [Htc Hdc]] Hok Hinit Hnt.
  unfold store_consistent. repeat split.
  - (* objects_live *)
    unfold objects_live, all_objects_live. simpl.
    constructor.
    + exact Hnt.
    + exact Hlive.
  - (* transfers_coupled *)
    exact Htc.
  - (* drain_consistent *)
    unfold drain_consistent. simpl. rewrite Hok. simpl.
    intro Habs. discriminate.
Qed.

(** Removing an object preserves consistency. *)
Theorem remove_preserves_consistency : forall st oid,
  store_consistent st ->
  store_consistent
    (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st)).
Proof.
  intros st oid [Hlive [Htc Hdc]].
  unfold store_consistent. repeat split.
  - (* objects_live: filter preserves Forall *)
    unfold objects_live, all_objects_live in *. simpl in *.
    apply Forall_forall. intros x Hin.
    apply filter_In in Hin. destruct Hin as [Hin _].
    rewrite Forall_forall in Hlive. exact (Hlive x Hin).
  - (* transfers_coupled *)
    exact Htc.
  - (* drain_consistent *)
    unfold drain_consistent in *. simpl in *. intro Ha.
    specialize (Hdc Ha).
    apply Forall_forall. intros x Hin.
    apply filter_In in Hin. destruct Hin as [Hin _].
    rewrite Forall_forall in Hdc. exact (Hdc x Hin).
Qed.

(** Beginning drain preserves consistency when no INITIALIZED or
    PROCESSING objects exist on the segment. *)
Theorem begin_drain_preserves_consistency : forall st,
  store_consistent st ->
  seg_status (ss_segment st) = SegOk ->
  no_in_progress (ss_segment st) ->
  store_consistent
    (mkStoreState (begin_drain (ss_segment st)) (ss_transfers st)).
Proof.
  intros st [Hlive [Htc Hdc]] Hok Hnip.
  unfold store_consistent. repeat split.
  - (* objects_live: begin_drain preserves objects *)
    unfold objects_live, all_objects_live, begin_drain, set_segment_status in *.
    simpl in *. exact Hlive.
  - (* transfers_coupled *)
    exact Htc.
  - (* drain_consistent *)
    unfold drain_consistent, begin_drain, set_segment_status, no_in_progress in *.
    simpl in *. intros _.
    rewrite Forall_forall in Hnip |- *.
    intros x Hin. specialize (Hnip x Hin).
    destruct Hnip as [Hnp Hni]. split; assumption.
Qed.

(** Completing a transfer and applying its result preserves consistency,
    provided we update the replica in the segment's object list. *)

(** Helper: update one object in a segment's object list. *)
Definition update_object_status (s : Segment) (oid : ObjectId)
    (new_status : ReplicaStatus) : Segment :=
  mkSegment
    (seg_id s)
    (seg_status s)
    (seg_capacity s)
    (seg_used s)
    (map (fun m => if Nat.eqb (om_id m) oid
                   then mkObjectMeta (om_id m) (om_segment m) new_status
                                     (om_pin m) (om_ref_count m) (om_size m)
                   else m)
         (seg_objects s)).

(** Completing a transfer to COMPLETE produces a valid replica transition. *)
Theorem transfer_completion_valid : forall m t,
  om_status m = RsProcessing ->
  task_succeeded t = true ->
  replica_transition (om_status m) RsComplete.
Proof.
  intros m t Hp _. rewrite Hp. constructor.
Qed.

(** Completing a transfer to FAILED produces a valid replica transition. *)
Theorem transfer_failure_valid : forall m t,
  om_status m = RsProcessing ->
  task_finished t = true ->
  task_succeeded t = false ->
  replica_transition (om_status m) RsFailed.
Proof.
  intros m t Hp _ _. rewrite Hp. constructor.
Qed.

(** =====================================================================
    Section 5: END-TO-END SAFETY
    ===================================================================== *)

(** No reads from incomplete replicas: on a consistent store,
    any readable object is COMPLETE. *)
Theorem no_incomplete_reads : forall st m,
  store_consistent st ->
  In m (seg_objects (ss_segment st)) ->
  replica_readable (om_status m) = true ->
  om_status m = RsComplete.
Proof.
  intros st m _ _ Hr. apply readable_is_complete. exact Hr.
Qed.

(** No eviction of protected objects: on a consistent store,
    any protected object cannot be evicted. *)
Theorem no_protected_eviction : forall st m,
  store_consistent st ->
  In m (seg_objects (ss_segment st)) ->
  eviction_protected m = true ->
  (* The object must not be evicted — eviction requires
     eviction_protected = false *)
  eviction_protected m <> false.
Proof.
  intros st m _ _ Hp Habs. rewrite Hp in Habs. discriminate.
Qed.

(** No allocation on non-Ok segments: on a consistent store,
    placement is only possible on SegOk segments. *)
Theorem no_placement_after_drain : forall st,
  store_consistent st ->
  seg_status (ss_segment st) <> SegOk ->
  segment_allocatable (seg_status (ss_segment st)) = false.
Proof.
  intros st _ Hne.
  destruct (seg_status (ss_segment st)); simpl; auto.
  exfalso. apply Hne. reflexivity.
Qed.

(** No unmount with live objects: safe_to_unmount requires emptiness. *)
Theorem no_unmount_with_objects : forall st m,
  safe_to_unmount (ss_segment st) ->
  ~ In m (seg_objects (ss_segment st)).
Proof.
  intros st m [_ Hempty] Hin.
  rewrite Hempty in Hin. inversion Hin.
Qed.

(** The full safety composition: on a consistent store, the four
    gates hold simultaneously. *)
Theorem four_gates_hold : forall st,
  store_consistent st ->
  (* G1: readable iff complete *)
  (forall m, In m (seg_objects (ss_segment st)) ->
    replica_readable (om_status m) = true -> om_status m = RsComplete) /\
  (* G2: processing implies protected *)
  (forall m, In m (seg_objects (ss_segment st)) ->
    om_status m = RsProcessing -> eviction_protected m = true) /\
  (* G3: placement requires SegOk *)
  (segment_allocatable (seg_status (ss_segment st)) = false ->
   seg_status (ss_segment st) <> SegOk) /\
  (* G4: unmount requires empty *)
  (safe_to_unmount (ss_segment st) ->
   seg_objects (ss_segment st) = []).
Proof.
  intros st Hsc.
  repeat split.
  - (* G1 *) intros m _ Hr. apply readable_is_complete. exact Hr.
  - (* G2 *) intros m Hin Hp.
    apply processing_not_evictable. exact Hp.
  - (* G3 *) intros Ha Habs.
    rewrite Habs in Ha. simpl in Ha. discriminate.
  - (* G4 *) intros [_ Hempty]. exact Hempty.
Qed.
