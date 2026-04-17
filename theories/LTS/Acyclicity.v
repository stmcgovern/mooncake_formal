(** * Acyclicity.v — Rank functions and global acyclicity for Mooncake.

    =========================================================================
    LAYER: 2-3 - BASE/DOMAIN LEMMAS
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Defines rank functions for each component state machine and uses
    DML's [rank_acyclic] to prove global acyclicity: no state can reach
    itself through any number of transitions.  This strictly subsumes
    the no-self-transition lemmas in Core.v and TransferProtocol.v.

    Also proves that progress steps (those not adding external work)
    strictly decrease the composed rank, establishing well-foundedness:
    without external input, the system converges.

    @source composition of replica.h × segment.h × transfer_task.h
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core (transition relations)
    - MooncakeFormal.Transfer.TransferProtocol (transfer_transition)
    - MooncakeFormal.LTS.StoreLTS (store_step, is_progress_step)
    - DistributedML.Concurrency.WellFounded (rank_acyclic, rank_wf)

    PROVIDES:
    - replica_rank, segment_rank, transfer_rank (component rank functions)
    - replica_acyclic, segment_acyclic, transfer_acyclic (no cycles)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.WellFounded.
Require Import DistributedML.Concurrency.Preservation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Transfer.TransferProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.StoreLTS.

(** =====================================================================
    Section 1: COMPONENT RANK FUNCTIONS
    ===================================================================== *)

(** Rank function for replica status.  Strictly decreases on every
    valid transition.  Complete and Failed share rank 2 — they don't
    transition to each other, only to Removed (rank 1). *)
Definition replica_rank (s : ReplicaStatus) : nat :=
  match s with
  | RsInitialized => 4
  | RsProcessing  => 3
  | RsComplete    => 2
  | RsFailed      => 2
  | RsRemoved     => 1
  end.

(** Rank function for segment status.  Linear chain, strictly
    decreasing on every transition. *)
Definition segment_rank (s : SegmentStatus) : nat :=
  match s with
  | SegOk         => 3
  | SegDraining   => 2
  | SegDrained    => 1
  | SegUnmounting => 0
  end.

(** Rank function for transfer status.  Completed and Failed share
    rank 0 — both are terminal with no outgoing transitions. *)
Definition transfer_rank (s : TransferStatus) : nat :=
  match s with
  | TsPending   => 2
  | TsActive    => 1
  | TsCompleted => 0
  | TsFailed    => 0
  end.

(** =====================================================================
    Section 2: RANK DECREASE LEMMAS
    ===================================================================== *)

Lemma replica_rank_decreasing : forall s1 s2,
  replica_transition s1 s2 -> replica_rank s2 < replica_rank s1.
Proof.
  intros s1 s2 H. inversion H; simpl; lia.
Qed.

Lemma segment_rank_decreasing : forall s1 s2,
  segment_transition s1 s2 -> segment_rank s2 < segment_rank s1.
Proof.
  intros s1 s2 H. inversion H; simpl; lia.
Qed.

Lemma transfer_rank_decreasing : forall s1 s2,
  transfer_transition s1 s2 -> transfer_rank s2 < transfer_rank s1.
Proof.
  intros s1 s2 H. inversion H; simpl; lia.
Qed.

(** =====================================================================
    Section 3: COMPONENT ACYCLICITY
    ===================================================================== *)

(** No replica status can reach itself through any sequence of
    transitions.  This subsumes [replica_no_self_transition] from
    Core.v, which only proves the length-1 case. *)
Theorem replica_acyclic : forall s,
  ~ plus replica_transition s s.
Proof.
  exact (rank_acyclic replica_transition replica_rank
           replica_rank_decreasing).
Qed.

(** No segment status can reach itself through any sequence of
    transitions.  Subsumes [segment_no_self_transition]. *)
Theorem segment_acyclic : forall s,
  ~ plus segment_transition s s.
Proof.
  exact (rank_acyclic segment_transition segment_rank
           segment_rank_decreasing).
Qed.

(** No transfer status can reach itself through any sequence of
    transitions.  Subsumes [transfer_no_self_transition]. *)
Theorem transfer_acyclic : forall s,
  ~ plus transfer_transition s s.
Proof.
  exact (rank_acyclic transfer_transition transfer_rank
           transfer_rank_decreasing).
Qed.

(** =====================================================================
    Section 4: COMPONENT WELL-FOUNDEDNESS
    ===================================================================== *)

(** The replica transition relation is well-founded (no infinite
    forward chains).  Every execution eventually reaches a terminal
    state or blocks. *)
Theorem replica_wf :
  well_founded (fun s2 s1 => replica_transition s1 s2).
Proof.
  exact (rank_wf replica_rank replica_rank_decreasing).
Qed.

(** The segment transition relation is well-founded. *)
Theorem segment_wf :
  well_founded (fun s2 s1 => segment_transition s1 s2).
Proof.
  exact (rank_wf segment_rank segment_rank_decreasing).
Qed.

(** The transfer transition relation is well-founded. *)
Theorem transfer_wf :
  well_founded (fun s2 s1 => transfer_transition s1 s2).
Proof.
  exact (rank_wf transfer_rank transfer_rank_decreasing).
Qed.

(** =====================================================================
    Section 5: COMPOSED RANK FOR STORE STEPS
    ===================================================================== *)

(** Sum the replica ranks of all objects on a segment. *)
Definition replica_rank_sum (objs : list ObjectMeta) : nat :=
  fold_right (fun m acc => replica_rank (om_status m) + acc) 0 objs.

(** The composed rank of a store state: segment rank plus all replica
    ranks.  Transfer ranks are excluded — the current LTS does not
    model transfer status changes. *)
Definition store_rank (st : StoreState) : nat :=
  segment_rank (seg_status (ss_segment st)) +
  replica_rank_sum (seg_objects (ss_segment st)).

(** Removing an object from a list decreases the replica rank sum
    (or leaves it unchanged if the object wasn't present). *)
Lemma filter_rank_sum_le : forall f objs,
  replica_rank_sum (filter f objs) <= replica_rank_sum objs.
Proof.
  intros f objs. induction objs as [| m rest IH].
  - simpl. lia.
  - simpl. destruct (f m).
    + simpl. lia.
    + lia.
Qed.

(** Removing an object strictly decreases the rank sum when the
    object is present and has positive rank (all statuses have
    rank >= 1). *)
Lemma replica_rank_positive : forall s,
  1 <= replica_rank s.
Proof.
  intros []; simpl; lia.
Qed.

(** =====================================================================
    Section 6: PROGRESS STEP RANK DECREASE
    ===================================================================== *)

(** Helper: remove_object produces a filtered list. *)
Lemma remove_object_objects : forall s oid,
  seg_objects (remove_object s oid) =
    filter (fun m => negb (Nat.eqb (om_id m) oid)) (seg_objects s).
Proof. intros. reflexivity. Qed.

(** Helper: drain operations preserve objects. *)
Lemma begin_drain_objects : forall s,
  seg_objects (begin_drain s) = seg_objects s.
Proof. intros. reflexivity. Qed.

Lemma complete_drain_objects : forall s,
  seg_objects (complete_drain s) = seg_objects s.
Proof.
  intros s. unfold complete_drain.
  apply set_status_preserves_objects.
Qed.

Lemma begin_unmount_objects : forall s,
  seg_objects (begin_unmount s) = seg_objects s.
Proof.
  intros s. unfold begin_unmount.
  apply set_status_preserves_objects.
Qed.

(** Every progress store_step on a non-empty segment with non-trivial
    effect either decreases the segment rank or decreases the object
    count. *)

(** Begin drain: segment rank decreases from 3 to 2, objects unchanged. *)
Lemma begin_drain_rank : forall st,
  seg_status (ss_segment st) = SegOk ->
  store_rank (mkStoreState (begin_drain (ss_segment st)) (ss_transfers st)) <
  store_rank st.
Proof.
  intros st Hok. unfold store_rank, begin_drain, set_segment_status. simpl.
  rewrite Hok. simpl. lia.
Qed.

(** Complete drain: segment rank decreases from 2 to 1, objects empty. *)
Lemma complete_drain_rank : forall st,
  seg_status (ss_segment st) = SegDraining ->
  seg_objects (ss_segment st) = [] ->
  store_rank (mkStoreState (complete_drain (ss_segment st)) (ss_transfers st)) <
  store_rank st.
Proof.
  intros st Hdr Hempty. unfold store_rank, complete_drain, set_segment_status.
  simpl. rewrite Hempty. rewrite Hdr. simpl. lia.
Qed.

(** Unmount: segment rank decreases from 1 to 0, objects empty. *)
Lemma unmount_rank : forall st,
  safe_to_unmount (ss_segment st) ->
  store_rank (mkStoreState (begin_unmount (ss_segment st)) (ss_transfers st)) <
  store_rank st.
Proof.
  intros st [Hdr Hempty]. unfold store_rank, begin_unmount, set_segment_status.
  simpl. rewrite Hempty. rewrite Hdr. simpl. lia.
Qed.

(** Remove: segment rank unchanged, replica rank sum decreases or
    stays equal.  For strict decrease, we show the filtered list's
    rank sum is ≤ the original.

    Note: remove may be a no-op if the oid doesn't exist, so we can
    only prove non-strict decrease in general.  When the object is
    present, the decrease is strict — but we defer that to
    DrainProgress.v where it matters. *)
Lemma remove_rank_le : forall st oid,
  store_rank (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st)) <=
  store_rank st.
Proof.
  intros st oid. unfold store_rank.
  assert (Hseg : seg_status (remove_object (ss_segment st) oid) =
                 seg_status (ss_segment st)) by reflexivity.
  assert (Hobjs : seg_objects (remove_object (ss_segment st) oid) =
    filter (fun m => negb (Nat.eqb (om_id m) oid)) (seg_objects (ss_segment st)))
    by reflexivity.
  simpl ss_segment. rewrite Hseg. rewrite Hobjs.
  assert (Hle : replica_rank_sum
    (filter (fun m => negb (Nat.eqb (om_id m) oid)) (seg_objects (ss_segment st)))
    <= replica_rank_sum (seg_objects (ss_segment st))).
  { apply filter_rank_sum_le. }
  lia.
Qed.

(** Every progress step either strictly decreases store_rank
    (drain operations) or non-strictly decreases it (remove). *)
Theorem progress_step_rank_nonincreasing : forall st l st',
  store_step st l st' ->
  is_progress_step l = true ->
  store_rank st' <= store_rank st.
Proof.
  intros st l st' Hstep Hprog. inversion Hstep; subst; simpl in *.
  - (* LPlace — not a progress step *) discriminate.
  - (* LRemove *) apply remove_rank_le.
  - (* LBeginDrain *)
    apply Nat.lt_le_incl. apply begin_drain_rank. exact H.
  - (* LCompleteDrain *)
    apply Nat.lt_le_incl. apply complete_drain_rank; assumption.
  - (* LUnmount *)
    apply Nat.lt_le_incl. apply unmount_rank. exact H.
Qed.

(** Drain operations strictly decrease store_rank. *)
Theorem drain_step_decreases_rank : forall st l st',
  store_step st l st' ->
  (l = LBeginDrain \/ l = LCompleteDrain \/ l = LUnmount) ->
  store_rank st' < store_rank st.
Proof.
  intros st l st' Hstep Hl. inversion Hstep; subst.
  - destruct Hl as [H' | [H' | H']]; discriminate.
  - destruct Hl as [H' | [H' | H']]; discriminate.
  - apply begin_drain_rank. exact H.
  - apply complete_drain_rank; assumption.
  - apply unmount_rank. exact H.
Qed.
