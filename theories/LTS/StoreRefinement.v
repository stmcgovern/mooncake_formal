(** * StoreRefinement.v — Component projections and invariant lifting.

    =========================================================================
    LAYER: 3 - DOMAIN LEMMAS (refinement morphisms)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Defines refinement morphisms that project the composed store state
    down to individual component state machines.  Uses DML's Refinement
    module to lift component invariants to the composed level and to
    project store traces down to component traces.

    @source composition of replica.h × segment.h
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.StoreLTS
    - DistributedML.Modal.Refinement
    - DistributedML.Concurrency.Preservation

    PROVIDES:
    - segment_step (labeled segment transitions)
    - project_segment, label_map_segment (refinement morphism)
    - segment_invariant_lift (component invariants hold in composed system)
    - segment_trace_projection (store traces project to segment traces)
    - segment_monotone (segment status never regresses)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.Preservation.
Require Import DistributedML.Modal.Refinement.
Require Import DistributedML.Concurrency.WellFounded.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.StoreLTS.
Require Import MooncakeFormal.LTS.Acyclicity.

(** =====================================================================
    Section 1: SEGMENT COMPONENT LTS
    ===================================================================== *)

(** Labels for the segment component in isolation. *)
Inductive SegmentLabel : Set :=
  | SLDrain     (* SegOk → SegDraining *)
  | SLComplete  (* SegDraining → SegDrained *)
  | SLUnmount.  (* SegDrained → SegUnmounting *)

(** The segment step relation as a labeled transition system. *)
Inductive segment_step : SegmentStatus -> SegmentLabel -> SegmentStatus -> Prop :=
  | ss_drain   : segment_step SegOk SLDrain SegDraining
  | ss_complete : segment_step SegDraining SLComplete SegDrained
  | ss_unmount : segment_step SegDrained SLUnmount SegUnmounting.

(** =====================================================================
    Section 2: REFINEMENT MORPHISM
    ===================================================================== *)

(** Project store state to segment status. *)
Definition project_segment (st : StoreState) : SegmentStatus :=
  seg_status (ss_segment st).

(** Map store labels to segment labels.  Segment operations are
    visible; all others are silent (don't affect segment status). *)
Definition label_map_segment (l : StoreLabel) : option SegmentLabel :=
  match l with
  | LBeginDrain => Some SLDrain
  | LCompleteDrain => Some SLComplete
  | LUnmount => Some SLUnmount
  | _ => None
  end.

(** =====================================================================
    Section 3: REFINEMENT HYPOTHESES
    ===================================================================== *)

(** Visible steps commute with projection: a segment-changing store
    step produces the corresponding segment transition. *)
Lemma visible_commute_segment : forall st l st' sl,
  store_step st l st' ->
  label_map_segment l = Some sl ->
  segment_step (project_segment st) sl (project_segment st').
Proof.
  intros st l st' sl Hstep Hlm.
  inversion Hstep; subst; simpl in Hlm;
    try discriminate.
  - (* LBeginDrain *)
    inversion Hlm; subst. unfold project_segment. simpl.
    rewrite H. constructor.
  - (* LCompleteDrain *)
    inversion Hlm; subst. unfold project_segment. simpl.
    rewrite H. constructor.
  - (* LUnmount *)
    inversion Hlm; subst. unfold project_segment. simpl.
    destruct H as [Hdr _]. rewrite Hdr. constructor.
Qed.

(** Silent steps don't change the segment projection. *)
Lemma silent_invisible_segment : forall st l st',
  store_step st l st' ->
  label_map_segment l = None ->
  project_segment st = project_segment st'.
Proof.
  intros st l st' Hstep Hlm.
  inversion Hstep; subst; simpl in Hlm;
    try discriminate.
  - (* LPlace *) unfold project_segment. simpl. reflexivity.
  - (* LRemove *) unfold project_segment. simpl. reflexivity.
Qed.

(** =====================================================================
    Section 4: INVARIANT LIFTING
    ===================================================================== *)

(** Any invariant preserved by the segment step relation is also
    preserved by the composed store step relation, when composed
    with the segment projection. *)
Theorem segment_invariant_lift : forall (inv : SegmentStatus -> Prop),
  (forall s l s', inv s -> segment_step s l s' -> inv s') ->
  forall st l st',
    inv (project_segment st) ->
    store_step st l st' ->
    inv (project_segment st').
Proof.
  exact (refinement_invariant_lift
           store_step segment_step
           project_segment label_map_segment
           visible_commute_segment silent_invisible_segment).
Qed.

(** Multi-step version: invariant preserved through store traces. *)
Theorem segment_star_invariant : forall (inv : SegmentStatus -> Prop),
  (forall s l s', inv s -> segment_step s l s' -> inv s') ->
  forall st ls st',
    inv (project_segment st) ->
    lstar store_step st ls st' ->
    inv (project_segment st').
Proof.
  exact (refinement_star_invariant
           store_step segment_step
           project_segment label_map_segment
           visible_commute_segment silent_invisible_segment).
Qed.

(** Store traces project to valid segment traces. *)
Theorem segment_trace_projection : forall st ls st',
  lstar store_step st ls st' ->
  lstar segment_step
    (project_segment st)
    (project_labels label_map_segment ls)
    (project_segment st').
Proof.
  exact (refinement_lstar_project
           store_step segment_step
           project_segment label_map_segment
           visible_commute_segment silent_invisible_segment).
Qed.

(** =====================================================================
    Section 5: APPLICATIONS — SEGMENT MONOTONICITY
    ===================================================================== *)

(** The segment never returns to a previous status.  We prove specific
    instances that capture the most useful monotonicity properties. *)

(** Once draining has begun, the segment is never Ok again. *)
Definition not_ok (s : SegmentStatus) : Prop := s <> SegOk.

Lemma segment_step_preserves_not_ok : forall s l s',
  not_ok s -> segment_step s l s' -> not_ok s'.
Proof.
  intros s l s' Hnok Hstep.
  inversion Hstep; subst; unfold not_ok; discriminate.
Qed.

Theorem once_draining_never_ok : forall st ls st',
  project_segment st <> SegOk ->
  lstar store_step st ls st' ->
  project_segment st' <> SegOk.
Proof.
  intros st ls st' Hnok Hstar.
  exact (segment_star_invariant not_ok
           segment_step_preserves_not_ok
           st ls st' Hnok Hstar).
Qed.

(** Once draining has begun, placement is always blocked. *)
Theorem once_draining_no_placement : forall st ls st',
  segment_allocatable (project_segment st) = false ->
  lstar store_step st ls st' ->
  segment_allocatable (project_segment st') = false.
Proof.
  intros st ls st' Ha Hstar.
  assert (Hnok : not_ok (project_segment st)).
  { unfold not_ok. intro Heq. rewrite Heq in Ha. simpl in Ha. discriminate. }
  assert (Hnok' : not_ok (project_segment st')).
  { exact (once_draining_never_ok st ls st' Hnok Hstar). }
  unfold not_ok, project_segment in *.
  destruct (seg_status (ss_segment st')) eqn:Hs; simpl.
  - exfalso. apply Hnok'. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Single-step: segment rank never increases. *)
Lemma segment_rank_step : forall st l st',
  store_step st l st' ->
  segment_rank (project_segment st') <= segment_rank (project_segment st).
Proof.
  intros st l st' Hstep. unfold project_segment.
  inversion Hstep; subst; simpl.
  - (* LPlace *) lia.
  - (* LRemove *) lia.
  - (* LBeginDrain *) rewrite H. simpl. lia.
  - (* LCompleteDrain *) rewrite H. simpl. lia.
  - (* LUnmount *) unfold safe_to_unmount in H.
    destruct H as [Hdr _]. rewrite Hdr. simpl. lia.
Qed.

(** Segment rank never increases through store traces. *)
Theorem segment_rank_monotone : forall st ls st',
  lstar store_step st ls st' ->
  segment_rank (project_segment st') <= segment_rank (project_segment st).
Proof.
  intros st ls st' Hstar.
  induction Hstar as [s | s1 l s2 ls' s3 Hstep Hrest IH].
  - lia.
  - assert (H12 := segment_rank_step s1 l s2 Hstep). lia.
Qed.
