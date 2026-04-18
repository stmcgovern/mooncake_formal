(** * AbstractCommutation.v -- The general permutation invariance theorem.

    =========================================================================
    LAYER: 2-3 - DOMAIN (abstract algebraic framework)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Strip away Mooncake and ask: what STRUCTURE makes permutation
    invariance work?  The answer is surprisingly minimal.

    Given any labeled transition system (State, Label, step) with an
    independence relation (indep) satisfying just TWO axioms:

      (I)  Irreflexivity: ~ indep l l
      (II) Swap: if l1;l2 executable and indep l1 l2,
                 then l2;l1 executable with the same result

    then full permutation invariance holds for pairwise-independent
    traces.  Symmetry of indep is NOT needed — pairwise quantification
    handles both directions.

    The Mooncake store is one instance.  Any concurrent system with
    independent operations is another.

    The proof factors into three steps:
    1. Irreflexivity + pairwise independence => NoDup (no duplicates)
    2. NoDup transfers through Permutation (standard library)
    3. Induction on Permutation derivation using Swap axiom

    @source (abstract — no source correspondence)
    @fidelity specification
    @abstraction algebraic-framework

    DEPENDENCIES:
    - Coq.Lists.List, Coq.Sorting.Permutation (abstract section)
    - MooncakeFormal.LTS.EvictionSafety (Mooncake instance)
    - MooncakeFormal.LTS.Diamond (Mooncake instance)
    - MooncakeFormal.LTS.PermutationInvariance (Mooncake instance)
    - MooncakeFormal.LTS.TraceEquivalence (Mooncake instance)

    PROVIDES:
    - aexec (multi-step execution for abstract LTS)
    - pairwise_indep (pairwise independence of a label list)
    - pairwise_indep_NoDup (independence => no duplicates)
    - pairwise_indep_perm (independence transfers through Permutation)
    - abstract_permutation_invariance (HEADLINE: the general theorem)
    - mooncake_indep (Mooncake independence: object ops on different IDs)
    - mooncake_permutation (HEADLINE: Mooncake as instance)
*)

Require Import List Arith Lia.
Import ListNotations.
Require Import Permutation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Diamond.
Require Import MooncakeFormal.LTS.PermutationInvariance.
Require Import MooncakeFormal.LTS.TraceEquivalence.

(** =====================================================================
    THE ABSTRACT FRAMEWORK — Two axioms, one theorem
    ===================================================================== *)

Section AbstractPermutation.

Variables (State Label : Type).
Variable step : State -> Label -> State -> Prop.
Variable indep : Label -> Label -> Prop.

(** Multi-step execution: apply a sequence of labels. *)
Inductive aexec : State -> list Label -> State -> Prop :=
  | aexec_nil : forall s, aexec s [] s
  | aexec_step : forall s l ls s' s'',
      step s l s' -> aexec s' ls s'' -> aexec s (l :: ls) s''.

Lemma aexec_cons_inv : forall s l ls s'',
  aexec s (l :: ls) s'' ->
  exists s', step s l s' /\ aexec s' ls s''.
Proof.
  intros s l ls s'' H. inversion H; subst. eexists. split; eassumption.
Qed.

(** =====================================================================
    THE TWO AXIOMS
    ===================================================================== *)

(** Axiom I: No label is independent of itself. *)
Hypothesis indep_irrefl : forall l, ~ indep l l.

(** Axiom II: Independent operations can be swapped.
    If l1;l2 is executable and they are independent, then l2;l1
    is also executable and reaches the same state. *)
Hypothesis swap_step : forall s l1 l2 s1 s12,
  indep l1 l2 ->
  step s l1 s1 -> step s1 l2 s12 ->
  exists s2 s21,
    step s l2 s2 /\ step s2 l1 s21 /\ s12 = s21.

(** =====================================================================
    PAIRWISE INDEPENDENCE AND ITS CONSEQUENCES
    ===================================================================== *)

(** All distinct pairs in a list are independent. *)
Definition pairwise_indep (ls : list Label) : Prop :=
  forall i j li lj,
    i < length ls -> j < length ls -> i <> j ->
    nth_error ls i = Some li -> nth_error ls j = Some lj ->
    indep li lj.

(** KEY LEMMA: Irreflexivity + pairwise independence implies NoDup.

    If the same label appeared twice, pairwise_indep would require
    it to be independent of itself — contradicting irreflexivity. *)
Lemma pairwise_indep_NoDup : forall ls,
  pairwise_indep ls -> NoDup ls.
Proof.
  induction ls as [| a rest IH]; intros Hpi.
  - exact (NoDup_nil Label).
  - apply NoDup_cons.
    + intro Hin. apply In_nth_error in Hin. destruct Hin as [j Hj].
      assert (Hjlt : j < length rest)
        by (apply nth_error_Some; rewrite Hj; discriminate).
      apply (indep_irrefl a).
      eapply (Hpi 0 (S j) a a); simpl; try lia; [reflexivity | exact Hj].
    + apply IH. intros i j li lj Hi Hj Hneq Hni Hnj.
      apply (Hpi (S i) (S j) li lj); simpl; try lia; assumption.
Qed.

(** Pairwise independence transfers through Permutation.

    This is where NoDup does its work: in the perm_trans case,
    two labels that map to the same position in ls1 must be equal,
    but NoDup(ls2) forbids duplicates at different positions. *)
Lemma pairwise_indep_perm : forall ls1 ls2,
  Permutation ls1 ls2 ->
  pairwise_indep ls1 ->
  pairwise_indep ls2.
Proof.
  intros ls1 ls2 Hperm Hpi.
  unfold pairwise_indep.
  intros i j li lj Hi Hj Hneq Hni Hnj.
  assert (Hin_li : In li ls1).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm |].
    eapply nth_error_In; eauto. }
  assert (Hin_lj : In lj ls1).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm |].
    eapply nth_error_In; eauto. }
  apply In_nth_error in Hin_li. destruct Hin_li as [i' Hi'].
  apply In_nth_error in Hin_lj. destruct Hin_lj as [j' Hj'].
  destruct (Nat.eq_dec i' j') as [Heq_ij | Hneq_ij].
  - (* i' = j' => li = lj => duplicate in ls2 => contradicts NoDup *)
    subst. rewrite Hi' in Hj'. inversion Hj'; subst.
    exfalso. apply Hneq.
    apply (proj1 (NoDup_nth_error ls2)
             (Permutation_NoDup Hperm (pairwise_indep_NoDup ls1 Hpi))
             i j Hi).
    rewrite Hni. rewrite Hnj. reflexivity.
  - (* i' <> j' => use pairwise_indep on ls1 *)
    assert (Hi'lt : i' < length ls1)
      by (apply nth_error_Some; rewrite Hi'; discriminate).
    assert (Hj'lt : j' < length ls1)
      by (apply nth_error_Some; rewrite Hj'; discriminate).
    exact (Hpi i' j' li lj Hi'lt Hj'lt Hneq_ij Hi' Hj').
Qed.

(** =====================================================================
    THE THEOREM
    ===================================================================== *)

(** HEADLINE: Any permutation of pairwise-independent operations,
    from a state where the original order is executable, is itself
    executable and reaches the same final state.

    This is the Cartier-Foata theorem for abstract LTS:
    scheduling order is irrelevant for independent operations.

    The proof needs only two axioms: irreflexivity and swap. *)
Theorem abstract_permutation_invariance : forall ls1 ls2 st st1,
  Permutation ls1 ls2 ->
  pairwise_indep ls1 ->
  aexec st ls1 st1 ->
  exists st2, aexec st ls2 st2 /\ st1 = st2.
Proof.
  intros ls1 ls2 st st1 Hperm.
  revert st st1.
  induction Hperm as [
    | a ls1 ls2 Hperm IH
    | a b ls
    | ls1 ls2 ls3 Hperm1 IH1 Hperm2 IH2
  ]; intros st st1 Hpi Hexec.
  - (* perm_nil *)
    exists st1. split; [exact Hexec | reflexivity].
  - (* perm_skip a — peel off the common head *)
    destruct (aexec_cons_inv _ _ _ _ Hexec) as [s1 [Ha Hrest]].
    assert (Hpi' : pairwise_indep ls1).
    { intros i j li lj Hi Hj Hneq Hni Hnj.
      apply (Hpi (S i) (S j) li lj); simpl; try lia; assumption. }
    destruct (IH s1 st1 Hpi' Hrest) as [st2 [Hexec2 Heq]].
    exists st2. split; [exact (aexec_step _ _ _ _ _ Ha Hexec2) | exact Heq].
  - (* perm_swap a b — the heart: use the Swap axiom *)
    destruct (aexec_cons_inv _ _ _ _ Hexec) as [sa [Hb Hrest_ab]].
    destruct (aexec_cons_inv _ _ _ _ Hrest_ab) as [sab [Ha Hrest]].
    assert (Hindep : indep b a).
    { eapply (Hpi 0 1 b a); simpl; try lia; reflexivity. }
    destruct (swap_step st b a sa sab Hindep Hb Ha)
      as [sb [sba [Ha' [Hb' Heq]]]].
    exists st1. split; [| reflexivity].
    econstructor; [exact Ha' |].
    econstructor; [exact Hb' |].
    subst. exact Hrest.
  - (* perm_trans — compose via pairwise_indep_perm *)
    assert (Hpi2 : pairwise_indep ls2)
      by exact (pairwise_indep_perm ls1 ls2 Hperm1 Hpi).
    destruct (IH1 st st1 Hpi Hexec) as [st2 [Hexec2 Heq1]].
    subst st2.
    destruct (IH2 st st1 Hpi2 Hexec2) as [st3 [Hexec3 Heq2]].
    exists st3. split; [exact Hexec3 | exact Heq2].
Qed.

End AbstractPermutation.

(** =====================================================================
    MOONCAKE AS AN INSTANCE
    ===================================================================== *)

(** Independence for Mooncake: two labels target different objects. *)
Definition mooncake_indep (l1 l2 : RichStoreLabel) : Prop :=
  exists oid1 oid2,
    object_op l1 oid1 /\ object_op l2 oid2 /\ oid1 <> oid2.

Lemma mooncake_indep_irrefl : forall l, ~ mooncake_indep l l.
Proof.
  intros l [oid1 [oid2 [Hop1 [Hop2 Hneq]]]].
  apply Hneq. exact (object_op_det l oid1 oid2 Hop1 Hop2).
Qed.

Lemma mooncake_swap : forall s l1 l2 s1 s12,
  mooncake_indep l1 l2 ->
  rich_store_step s l1 s1 -> rich_store_step s1 l2 s12 ->
  exists s2 s21,
    rich_store_step s l2 s2 /\ rich_store_step s2 l1 s21 /\ s12 = s21.
Proof.
  intros s l1 l2 s1 s12 [oid1 [oid2 [Hop1 [Hop2 Hneq]]]] Hs1 Hs12.
  exact (object_op_swap_executable s l1 l2 oid1 oid2 s1 s12
           Hop1 Hop2 Hneq Hs1 Hs12).
Qed.

(** HEADLINE: Mooncake's permutation invariance is an instance of
    the abstract theorem — a one-line instantiation. *)
Theorem mooncake_permutation : forall ls1 ls2 st st1,
  Permutation ls1 ls2 ->
  pairwise_indep RichStoreLabel mooncake_indep ls1 ->
  aexec StoreState RichStoreLabel rich_store_step st ls1 st1 ->
  exists st2,
    aexec StoreState RichStoreLabel rich_store_step st ls2 st2 /\ st1 = st2.
Proof.
  exact (abstract_permutation_invariance
           StoreState RichStoreLabel rich_store_step mooncake_indep
           mooncake_indep_irrefl mooncake_swap).
Qed.

(** =====================================================================
    BRIDGE: aexec <-> exec
    ===================================================================== *)

(** The abstract aexec and Mooncake's exec are structurally identical. *)
Lemma exec_to_aexec : forall st ls st',
  exec st ls st' ->
  aexec StoreState RichStoreLabel rich_store_step st ls st'.
Proof.
  induction 1; [constructor | econstructor; eassumption].
Qed.

Lemma aexec_to_exec : forall st ls st',
  aexec StoreState RichStoreLabel rich_store_step st ls st' ->
  exec st ls st'.
Proof.
  induction 1; [constructor | econstructor; eassumption].
Qed.
