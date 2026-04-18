(** * MultiSegment.v -- Cross-segment independence for distributed stores.

    =========================================================================
    LAYER: 3-4 - APPLICATION (multi-segment composition)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Mooncake's distributed pool contains multiple segments on different
    nodes.  This module formalizes the multi-segment model and proves
    cross-segment independence: operations on different segments do not
    affect each other.

    The key insight: since each segment has independent state, per-segment
    properties (well-formedness, capacity coherence, protection) lift
    trivially to the global store.  Cross-segment operations commute
    unconditionally — they don't even need to be "independent" in the
    label sense, because they touch completely separate state.

    @source mooncake-store/src/store.cpp (segment_map, per-segment ops)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.NoDupPreservation
    - MooncakeFormal.LTS.RichConsistency
    - MooncakeFormal.LTS.CapacityCoherence

    PROVIDES:
    - update_nth (list utility)
    - GlobalStore, GlobalLabel, global_step (multi-segment LTS)
    - cross_segment_frame (ops on segment i preserve segment j)
    - global_well_formed (all segments well-formed)
    - global_step_preserves_wf (HEADLINE: global well-formedness invariant)
    - cross_segment_diamond (HEADLINE: ops on different segments commute)
    - global_step_preserves_consistency (global consistency invariant)
*)

Require Import List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.NoDupPreservation.
Require Import MooncakeFormal.LTS.RichConsistency.
Require Import MooncakeFormal.LTS.CapacityCoherence.

(** =====================================================================
    Section 1: LIST UPDATE UTILITY
    ===================================================================== *)

(** Replace the i-th element of a list.  Out-of-bounds is a no-op. *)
Fixpoint update_nth {A : Type} (i : nat) (l : list A) (x : A) : list A :=
  match i, l with
  | 0, _ :: rest => x :: rest
  | S i', h :: rest => h :: update_nth i' rest x
  | _, [] => []
  end.

Lemma nth_error_update_same : forall {A : Type} (i : nat) (l : list A) (x : A),
  i < length l ->
  nth_error (update_nth i l x) i = Some x.
Proof.
  intros A i. induction i as [| i' IH]; intros [| h rest] x Hlt; simpl in *.
  - lia.
  - reflexivity.
  - lia.
  - apply IH. lia.
Qed.

Lemma nth_error_update_other : forall {A : Type} (i j : nat) (l : list A) (x : A),
  i <> j ->
  nth_error (update_nth i l x) j = nth_error l j.
Proof.
  intros A i. induction i as [| i' IH]; intros j [| h rest] x Hneq; simpl.
  - reflexivity.
  - destruct j as [| j']; [exfalso; exact (Hneq eq_refl) | reflexivity].
  - reflexivity.
  - destruct j as [| j'].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

Lemma length_update_nth : forall {A : Type} (i : nat) (l : list A) (x : A),
  i < length l ->
  length (update_nth i l x) = length l.
Proof.
  intros A i. induction i as [| i' IH]; intros [| h rest] x Hlt; simpl in *.
  - lia.
  - reflexivity.
  - lia.
  - f_equal. apply IH. lia.
Qed.

Lemma update_nth_nil : forall {A : Type} (i : nat) (x : A),
  update_nth i [] x = [].
Proof. intros A [| i'] x; reflexivity. Qed.

Lemma update_nth_comm : forall {A : Type} (i j : nat) (l : list A) (x y : A),
  i <> j ->
  update_nth j (update_nth i l x) y = update_nth i (update_nth j l y) x.
Proof.
  intros A i. induction i as [| i' IH]; intros j [| h rest] x y Hneq; simpl.
  - rewrite update_nth_nil. destruct j; reflexivity.
  - destruct j as [| j']; [exfalso; exact (Hneq eq_refl) | reflexivity].
  - rewrite update_nth_nil. destruct j; reflexivity.
  - destruct j as [| j']; [reflexivity |].
    simpl. f_equal. apply IH. lia.
Qed.

(** =====================================================================
    Section 2: GLOBAL STORE AND MULTI-SEGMENT STEP
    ===================================================================== *)

(** A global store is a collection of independent segment stores. *)
Definition GlobalStore := list StoreState.

(** A global label specifies which segment an operation targets. *)
Definition GlobalLabel := (nat * RichStoreLabel)%type.

(** Global step: apply a label to the specified segment. *)
Inductive global_step : GlobalStore -> GlobalLabel -> GlobalStore -> Prop :=
  | gstep : forall gs seg_id l st st',
      nth_error gs seg_id = Some st ->
      rich_store_step st l st' ->
      global_step gs (seg_id, l) (update_nth seg_id gs st').

(** =====================================================================
    Section 3: CROSS-SEGMENT FRAME
    ===================================================================== *)

(** CORE: Operations on segment i do not change segment j.

    This is the fundamental independence property of the multi-segment
    architecture — each segment's state is entirely local. *)
Theorem cross_segment_frame : forall gs seg_i l gs' seg_j st_j,
  global_step gs (seg_i, l) gs' ->
  seg_i <> seg_j ->
  nth_error gs seg_j = Some st_j ->
  nth_error gs' seg_j = Some st_j.
Proof.
  intros gs seg_i l gs' seg_j st_j Hstep Hneq Hnth.
  inversion Hstep as [? ? ? ? ? _ _]; subst.
  rewrite nth_error_update_other; [exact Hnth | exact Hneq].
Qed.

(** =====================================================================
    Section 4: GLOBAL WELL-FORMEDNESS
    ===================================================================== *)

(** All segments in the global store are well-formed. *)
Definition global_well_formed (gs : GlobalStore) : Prop :=
  Forall store_well_formed gs.

(** Forall is preserved by update_nth when the new element satisfies P. *)
Lemma Forall_update_nth : forall {A : Type} (P : A -> Prop)
    (i : nat) (l : list A) (x : A),
  Forall P l ->
  P x ->
  i < length l ->
  Forall P (update_nth i l x).
Proof.
  intros A P i. induction i as [| i' IH]; intros [| h rest] x Hall Hx Hlt;
    simpl in *; try lia.
  - inversion Hall; subst. exact (Forall_cons x Hx H2).
  - inversion Hall; subst.
    apply Forall_cons.
    + exact H1.
    + apply IH; [exact H2 | exact Hx | lia].
Qed.

(** HEADLINE: Global well-formedness is preserved by every global step,
    provided that Place operations use fresh IDs.

    The argument:
    - The targeted segment's well-formedness is preserved by
      step_preserves_well_formed (from CapacityCoherence.v)
    - All other segments are unchanged (cross_segment_frame) *)
Theorem global_step_preserves_wf : forall gs seg_id l gs',
  global_well_formed gs ->
  (forall st, nth_error gs seg_id = Some st -> place_fresh st l) ->
  global_step gs (seg_id, l) gs' ->
  global_well_formed gs'.
Proof.
  intros gs seg_id l gs' Hwf Hfresh Hstep.
  inversion Hstep as [? ? ? st0 st0' Hnth Hrich]; subst.
  unfold global_well_formed in *.
  assert (Hst_wf : store_well_formed st0).
  { rewrite Forall_forall in Hwf.
    exact (Hwf st0 (nth_error_In gs seg_id Hnth)). }
  assert (Hst'_wf : store_well_formed st0')
    by exact (step_preserves_well_formed st0 l st0' Hst_wf
               (Hfresh st0 Hnth) Hrich).
  assert (Hlt : seg_id < length gs)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  exact (Forall_update_nth store_well_formed seg_id gs st0' Hwf Hst'_wf Hlt).
Qed.

(** =====================================================================
    Section 5: GLOBAL CONSISTENCY
    ===================================================================== *)

(** All segments in the global store are consistent. *)
Definition global_consistent (gs : GlobalStore) : Prop :=
  Forall store_consistent gs.

(** Global consistency is preserved by every global step.
    Unlike well-formedness, consistency needs no freshness precondition. *)
Theorem global_step_preserves_consistency : forall gs seg_id l gs',
  global_consistent gs ->
  global_step gs (seg_id, l) gs' ->
  global_consistent gs'.
Proof.
  intros gs seg_id l gs' Hcons Hstep.
  inversion Hstep as [? ? ? st0 st0' Hnth Hrich]; subst.
  unfold global_consistent in *.
  assert (Hst_cons : store_consistent st0).
  { rewrite Forall_forall in Hcons.
    exact (Hcons st0 (nth_error_In gs seg_id Hnth)). }
  assert (Hst'_cons : store_consistent st0')
    by exact (rich_step_preserves_consistency st0 l st0' Hst_cons Hrich).
  assert (Hlt : seg_id < length gs)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  exact (Forall_update_nth store_consistent seg_id gs st0' Hcons Hst'_cons Hlt).
Qed.

(** =====================================================================
    Section 6: CROSS-SEGMENT COMMUTATIVITY
    ===================================================================== *)

(** HEADLINE: Operations on different segments commute unconditionally.

    This is stronger than label-level independence: we don't need to
    check what the operations are, only that they target different
    segments.  The multi-segment architecture provides structural
    commutativity by construction. *)
Theorem cross_segment_commute : forall gs seg_i seg_j l1 l2 gs1 gs12,
  seg_i <> seg_j ->
  global_step gs (seg_i, l1) gs1 ->
  global_step gs1 (seg_j, l2) gs12 ->
  exists gs2 gs21,
    global_step gs (seg_j, l2) gs2 /\
    global_step gs2 (seg_i, l1) gs21 /\
    gs12 = gs21.
Proof.
  intros gs seg_i seg_j l1 l2 gs1 gs12 Hneq Hstep1 Hstep2.
  inversion Hstep1 as [? ? ? st_i st_i' Hnth_i Hrich_i]; subst.
  inversion Hstep2 as [? ? ? st_j st_j' Hnth_j' Hrich_j]; subst.
  (* Segment j is unchanged by step on segment i *)
  assert (Hnth_j : nth_error gs seg_j = Some st_j).
  { rewrite nth_error_update_other in Hnth_j'; [exact Hnth_j' | exact Hneq]. }
  (* Segment i is unchanged by step on segment j *)
  assert (Hnth_i' : nth_error (update_nth seg_j gs st_j') seg_i = Some st_i).
  { rewrite nth_error_update_other; [exact Hnth_i | exact (not_eq_sym Hneq)]. }
  eexists. eexists.
  split; [| split].
  - exact (gstep gs seg_j l2 st_j st_j' Hnth_j Hrich_j).
  - exact (gstep (update_nth seg_j gs st_j') seg_i l1 st_i st_i' Hnth_i' Hrich_i).
  - exact (update_nth_comm seg_i seg_j gs st_i' st_j' Hneq).
Qed.

(** =====================================================================
    Section 7: SEGMENT COUNT PRESERVATION
    ===================================================================== *)

(** Global steps preserve the number of segments. *)
Theorem global_step_preserves_length : forall gs gl gs',
  global_step gs gl gs' ->
  length gs' = length gs.
Proof.
  intros gs gl gs' Hstep.
  inversion Hstep as [? seg_id ? ? ? Hnth _]; subst.
  apply length_update_nth.
  apply nth_error_Some. rewrite Hnth. discriminate.
Qed.
