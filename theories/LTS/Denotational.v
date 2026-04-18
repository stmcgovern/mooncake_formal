(** * Denotational.v -- Computable semantics and adequacy theorem.

    =========================================================================
    LAYER: 4 - APPLICATION (denotational/operational bridge)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Defines a total, computable evaluation function for the enriched LTS
    and proves it adequate w.r.t. the operational semantics (exec):

      eval ls st = Some st'  <->  exec st ls st'

    This bridges two views of the system:
    - Operational (exec): relational, used for safety proofs
    - Denotational (eval): functional, enables computation and extraction

    The compositionality theorem makes eval a monoid homomorphism:

      eval (ls1 ++ ls2) st = bind (eval ls1 st) (eval ls2)

    @source mooncake-store/src/master_service.cpp (operation dispatch)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.TraceEquivalence

    PROVIDES:
    - no_in_progress_b (decidable no_in_progress)
    - safe_to_unmount_b (decidable safe_to_unmount)
    - no_in_progress_reflect (boolean <-> Prop bridge)
    - safe_to_unmount_reflect (boolean <-> Prop bridge)
    - step_eval (computable single-step function)
    - eval (computable multi-step evaluation)
    - step_eval_sound (step_eval Some -> rich_store_step)
    - step_eval_complete (rich_store_step -> step_eval Some)
    - eval_sound (eval Some -> exec)
    - eval_complete (exec -> eval Some)
    - eval_adequacy (HEADLINE: eval = Some <-> exec)
    - eval_app (HEADLINE: compositionality over concatenation)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.TraceEquivalence.

(** =====================================================================
    Section 1: BOOLEAN DECISION PROCEDURES
    ===================================================================== *)

(** Boolean version of [no_in_progress]: checks that no object on the
    segment has status RsProcessing or RsInitialized. *)
Definition no_in_progress_b (s : Segment) : bool :=
  forallb (fun m =>
    negb (replica_status_eqb (om_status m) RsProcessing) &&
    negb (replica_status_eqb (om_status m) RsInitialized))
  (seg_objects s).

(** Boolean version of [safe_to_unmount]: segment is SegDrained
    and has no objects. *)
Definition safe_to_unmount_b (s : Segment) : bool :=
  segment_status_eqb (seg_status s) SegDrained && segment_empty s.

(** Reflection: [no_in_progress_b] decides [no_in_progress]. *)
Lemma no_in_progress_reflect : forall s,
  no_in_progress_b s = true <-> no_in_progress s.
Proof.
  intros s. unfold no_in_progress_b, no_in_progress.
  rewrite forallb_forall. rewrite Forall_forall.
  split; intros H x Hin; specialize (H x Hin).
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    split; intro Habs.
    + rewrite Habs in H1. simpl in H1. discriminate.
    + rewrite Habs in H2. simpl in H2. discriminate.
  - destruct H as [Hnp Hni].
    apply andb_true_iff. split; apply negb_true_iff.
    + destruct (replica_status_eqb (om_status x) RsProcessing) eqn:E.
      * exfalso. apply Hnp. apply replica_status_eqb_spec. exact E.
      * reflexivity.
    + destruct (replica_status_eqb (om_status x) RsInitialized) eqn:E.
      * exfalso. apply Hni. apply replica_status_eqb_spec. exact E.
      * reflexivity.
Qed.

(** Reflection: [safe_to_unmount_b] decides [safe_to_unmount]. *)
Lemma safe_to_unmount_reflect : forall s,
  safe_to_unmount_b s = true <-> safe_to_unmount s.
Proof.
  intros s. unfold safe_to_unmount_b, safe_to_unmount.
  split.
  - intros H. apply andb_true_iff in H. destruct H as [H1 H2].
    split.
    + apply segment_status_eqb_spec. exact H1.
    + unfold segment_empty in H2.
      destruct (seg_objects s); [reflexivity | discriminate].
  - intros [H1 H2].
    apply andb_true_iff. split.
    + apply segment_status_eqb_spec. exact H1.
    + unfold segment_empty. rewrite H2. reflexivity.
Qed.

(** =====================================================================
    Section 2: COMPUTABLE SINGLE-STEP FUNCTION
    ===================================================================== *)

(** Computable evaluation of a single enriched step.  Returns [Some st']
    when the label's preconditions are met, [None] otherwise.  Each case
    mirrors one constructor of [rich_store_step]. *)
Definition step_eval (st : StoreState) (l : RichStoreLabel) : option StoreState :=
  match l with
  | RLPlace m =>
      if segment_status_eqb (seg_status (ss_segment st)) SegOk &&
         replica_status_eqb (om_status m) RsInitialized &&
         negb (replica_terminal (om_status m))
      then Some (mkStoreState (place_object (ss_segment st) m) (ss_transfers st))
      else None
  | RLRemove oid =>
      Some (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st))
  | RLBeginDrain =>
      if segment_status_eqb (seg_status (ss_segment st)) SegOk &&
         no_in_progress_b (ss_segment st)
      then Some (mkStoreState (begin_drain (ss_segment st)) (ss_transfers st))
      else None
  | RLCompleteDrain =>
      if segment_status_eqb (seg_status (ss_segment st)) SegDraining &&
         segment_empty (ss_segment st)
      then Some (mkStoreState (complete_drain (ss_segment st)) (ss_transfers st))
      else None
  | RLUnmount =>
      if safe_to_unmount_b (ss_segment st)
      then Some (mkStoreState (begin_unmount (ss_segment st)) (ss_transfers st))
      else None
  | RLBeginRead oid =>
      match find_object (ss_segment st) oid with
      | Some m =>
          if replica_status_eqb (om_status m) RsComplete
          then Some (mkStoreState (inc_segment_refcnt (ss_segment st) oid) (ss_transfers st))
          else None
      | None => None
      end
  | RLEndRead oid =>
      match find_object (ss_segment st) oid with
      | Some m =>
          if Nat.ltb 0 (om_ref_count m)
          then Some (mkStoreState (dec_segment_refcnt (ss_segment st) oid) (ss_transfers st))
          else None
      | None => None
      end
  | RLEvict oid =>
      match find_object (ss_segment st) oid with
      | Some m =>
          if negb (eviction_protected m)
          then Some (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st))
          else None
      | None => None
      end
  end.

(** =====================================================================
    Section 3: COMPUTABLE MULTI-STEP EVALUATION
    ===================================================================== *)

(** Evaluate a trace (list of labels) from a starting state.
    Returns [Some st'] if all steps succeed, [None] if any step's
    preconditions fail. *)
Fixpoint eval (ls : list RichStoreLabel) (st : StoreState) : option StoreState :=
  match ls with
  | [] => Some st
  | l :: rest =>
      match step_eval st l with
      | Some st' => eval rest st'
      | None => None
      end
  end.

(** =====================================================================
    Section 4: SINGLE-STEP ADEQUACY
    ===================================================================== *)

(** Soundness: if [step_eval] succeeds, the operational step holds. *)
Lemma step_eval_sound : forall st l st',
  step_eval st l = Some st' ->
  rich_store_step st l st'.
Proof.
  intros st l st' Heval. destruct l; simpl in Heval.
  - (* RLPlace *)
    destruct (segment_status_eqb (seg_status (ss_segment st)) SegOk) eqn:E1;
      simpl in Heval; [| discriminate].
    destruct (replica_status_eqb (om_status m) RsInitialized) eqn:E2;
      simpl in Heval; [| discriminate].
    destruct (replica_terminal (om_status m)) eqn:E3;
      simpl in Heval; [discriminate |].
    inversion Heval; subst.
    apply rstep_place.
    + apply segment_status_eqb_spec. exact E1.
    + apply replica_status_eqb_spec. exact E2.
    + exact E3.
  - (* RLRemove *)
    inversion Heval; subst.
    apply rstep_remove.
  - (* RLBeginDrain *)
    destruct (segment_status_eqb (seg_status (ss_segment st)) SegOk) eqn:E1;
      simpl in Heval; [| discriminate].
    destruct (no_in_progress_b (ss_segment st)) eqn:E2;
      simpl in Heval; [| discriminate].
    inversion Heval; subst.
    apply rstep_begin_drain.
    + apply segment_status_eqb_spec. exact E1.
    + apply no_in_progress_reflect. exact E2.
  - (* RLCompleteDrain *)
    destruct (segment_status_eqb (seg_status (ss_segment st)) SegDraining) eqn:E1;
      simpl in Heval; [| discriminate].
    destruct (segment_empty (ss_segment st)) eqn:E2;
      simpl in Heval; [| discriminate].
    inversion Heval; subst.
    apply rstep_complete_drain.
    + apply segment_status_eqb_spec. exact E1.
    + unfold segment_empty in E2.
      destruct (seg_objects (ss_segment st)); [reflexivity | discriminate].
  - (* RLUnmount *)
    destruct (safe_to_unmount_b (ss_segment st)) eqn:E;
      [| discriminate].
    inversion Heval; subst.
    apply rstep_unmount.
    apply safe_to_unmount_reflect. exact E.
  - (* RLBeginRead *)
    destruct (find_object (ss_segment st) oid) as [m|] eqn:Hfind; [| discriminate].
    destruct (replica_status_eqb (om_status m) RsComplete) eqn:E; [| discriminate].
    inversion Heval; subst.
    exact (rstep_begin_read st oid m Hfind
             (proj1 (replica_status_eqb_spec _ _) E)).
  - (* RLEndRead *)
    destruct (find_object (ss_segment st) oid) as [m|] eqn:Hfind; [| discriminate].
    destruct (Nat.ltb 0 (om_ref_count m)) eqn:E; [| discriminate].
    inversion Heval; subst.
    exact (rstep_end_read st oid m Hfind
             (proj1 (Nat.ltb_lt 0 (om_ref_count m)) E)).
  - (* RLEvict *)
    destruct (find_object (ss_segment st) oid) as [m|] eqn:Hfind; [| discriminate].
    destruct (negb (eviction_protected m)) eqn:E; [| discriminate].
    inversion Heval; subst.
    exact (rstep_evict st oid m Hfind
             (proj1 (negb_true_iff _) E)).
Qed.

(** Completeness: every operational step is captured by [step_eval]. *)
Lemma step_eval_complete : forall st l st',
  rich_store_step st l st' ->
  step_eval st l = Some st'.
Proof.
  intros st l st' Hstep. inversion Hstep; subst; simpl.
  - (* rstep_place *)
    replace (segment_status_eqb (seg_status (ss_segment st)) SegOk) with true
      by (symmetry; apply segment_status_eqb_spec; assumption). simpl.
    replace (replica_status_eqb (om_status m) RsInitialized) with true
      by (symmetry; apply replica_status_eqb_spec; assumption). simpl.
    rewrite H1. reflexivity.
  - (* rstep_remove *)
    reflexivity.
  - (* rstep_begin_drain *)
    replace (segment_status_eqb (seg_status (ss_segment st)) SegOk) with true
      by (symmetry; apply segment_status_eqb_spec; assumption). simpl.
    replace (no_in_progress_b (ss_segment st)) with true
      by (symmetry; apply no_in_progress_reflect; assumption).
    reflexivity.
  - (* rstep_complete_drain *)
    replace (segment_status_eqb (seg_status (ss_segment st)) SegDraining) with true
      by (symmetry; apply segment_status_eqb_spec; assumption). simpl.
    unfold segment_empty. rewrite H0. reflexivity.
  - (* rstep_unmount *)
    replace (safe_to_unmount_b (ss_segment st)) with true
      by (symmetry; apply safe_to_unmount_reflect; assumption).
    reflexivity.
  - (* rstep_begin_read *)
    rewrite H.
    replace (replica_status_eqb (om_status m) RsComplete) with true
      by (symmetry; apply replica_status_eqb_spec; assumption).
    reflexivity.
  - (* rstep_end_read *)
    rewrite H.
    replace (Nat.ltb 0 (om_ref_count m)) with true
      by (symmetry; apply Nat.ltb_lt; exact H0).
    reflexivity.
  - (* rstep_evict *)
    rewrite H.
    replace (negb (eviction_protected m)) with true
      by (symmetry; apply negb_true_iff; exact H0).
    reflexivity.
Qed.

(** =====================================================================
    Section 5: MULTI-STEP ADEQUACY -- HEADLINE
    ===================================================================== *)

(** Soundness: [eval] producing [Some st'] implies [exec]. *)
Theorem eval_sound : forall ls st st',
  eval ls st = Some st' ->
  exec st ls st'.
Proof.
  induction ls as [| l ls IH]; intros st st' Heval; simpl in Heval.
  - inversion Heval; subst. constructor.
  - destruct (step_eval st l) as [s_mid|] eqn:Hse; [| discriminate].
    econstructor.
    + exact (step_eval_sound st l s_mid Hse).
    + exact (IH s_mid st' Heval).
Qed.

(** Completeness: [exec] implies [eval] produces [Some st']. *)
Theorem eval_complete : forall ls st st',
  exec st ls st' ->
  eval ls st = Some st'.
Proof.
  intros ls st st' Hexec.
  induction Hexec as [s | s l ls s_mid s_final Hstep Hexec IH].
  - reflexivity.
  - simpl. rewrite (step_eval_complete s l s_mid Hstep). exact IH.
Qed.

(** HEADLINE: Adequacy theorem -- [eval] and [exec] agree exactly.

    The computable [eval] function is a faithful implementation of the
    relational [exec]: they accept the same traces and produce the
    same final states.  This licenses using [eval] for computation
    (testing, extraction) and [exec] for proof (induction, case analysis). *)
Theorem eval_adequacy : forall ls st st',
  eval ls st = Some st' <-> exec st ls st'.
Proof.
  split.
  - exact (eval_sound ls st st').
  - exact (eval_complete ls st st').
Qed.

(** =====================================================================
    Section 6: COMPOSITIONALITY -- HEADLINE
    ===================================================================== *)

(** HEADLINE: [eval] distributes over trace concatenation.

    This is the monoid homomorphism property: [eval] maps the list
    monoid (with [++]) to the option-state monoid (with Kleisli
    composition).  It follows from the fold structure of [eval]. *)
Theorem eval_app : forall ls1 ls2 st,
  eval (ls1 ++ ls2) st =
    match eval ls1 st with
    | Some s => eval ls2 s
    | None => None
    end.
Proof.
  induction ls1 as [| l ls1 IH]; intros ls2 st; simpl.
  - reflexivity.
  - destruct (step_eval st l) as [s_mid|].
    + exact (IH ls2 s_mid).
    + reflexivity.
Qed.

(** Corollary: if both halves succeed, the concatenation succeeds. *)
Corollary eval_app_some : forall ls1 ls2 st s_mid st',
  eval ls1 st = Some s_mid ->
  eval ls2 s_mid = Some st' ->
  eval (ls1 ++ ls2) st = Some st'.
Proof.
  intros ls1 ls2 st s_mid st' H1 H2.
  rewrite eval_app, H1. exact H2.
Qed.

(** Corollary: if the first half fails, the concatenation fails. *)
Corollary eval_app_none : forall ls1 ls2 st,
  eval ls1 st = None ->
  eval (ls1 ++ ls2) st = None.
Proof.
  intros ls1 ls2 st H.
  rewrite eval_app, H. reflexivity.
Qed.
