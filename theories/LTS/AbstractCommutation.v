(** * AbstractCommutation.v -- Mooncake as instance of DML's Commutation.

    =========================================================================
    LAYER: 2-3 - DOMAIN (abstract algebraic framework instance)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    DML's DistributedML.Concurrency.Commutation provides the abstract
    Cartier-Foata theorem: any LTS with an independence relation
    satisfying irreflexivity and swap admits full permutation invariance
    for pairwise-independent traces.

    This module instantiates it for Mooncake:
    - mooncake_indep: two labels target different objects
    - mooncake_indep_irrefl: object_op target is deterministic
    - mooncake_swap: from object_op_swap_executable
    - mooncake_permutation: one-line instantiation of the abstract theorem

    @source (abstract — no source correspondence)
    @fidelity specification
    @abstraction algebraic-framework

    DEPENDENCIES:
    - DistributedML.Concurrency.Commutation (abstract framework)
    - DistributedML.Concurrency.Preservation (lstar)
    - MooncakeFormal.LTS.EvictionSafety (rich_store_step)
    - MooncakeFormal.LTS.Diamond (object_op)
    - MooncakeFormal.LTS.PermutationInvariance (object_op_swap_executable)
    - MooncakeFormal.LTS.TraceEquivalence (exec)

    PROVIDES:
    - mooncake_indep (Mooncake independence: object ops on different IDs)
    - mooncake_permutation (HEADLINE: Mooncake as instance of abstract theorem)
    - exec_to_lstar_rich, lstar_rich_to_exec (bridge lemmas)
*)

Require Import List.
Import ListNotations.
Require Import Permutation.
Require Import DistributedML.Concurrency.Preservation.
Require Import DistributedML.Concurrency.Commutation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Diamond.
Require Import MooncakeFormal.LTS.PermutationInvariance.
Require Import MooncakeFormal.LTS.TraceEquivalence.

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

(** HEADLINE: Mooncake's permutation invariance is a direct instance of
    DML's abstract commutation theorem — a one-line instantiation. *)
Theorem mooncake_permutation : forall ls1 ls2 st st1,
  Permutation ls1 ls2 ->
  pairwise_indep mooncake_indep ls1 ->
  lstar rich_store_step st ls1 st1 ->
  exists st2,
    lstar rich_store_step st ls2 st2 /\ st1 = st2.
Proof.
  exact (commutation_invariance rich_store_step
           mooncake_indep_irrefl mooncake_swap).
Qed.

(** =====================================================================
    BRIDGE: lstar <-> exec
    ===================================================================== *)

(** The DML lstar and Mooncake's exec are structurally identical. *)
Lemma exec_to_lstar_rich : forall st ls st',
  exec st ls st' ->
  lstar rich_store_step st ls st'.
Proof.
  induction 1; [constructor | econstructor; eassumption].
Qed.

Lemma lstar_rich_to_exec : forall st ls st',
  lstar rich_store_step st ls st' ->
  exec st ls st'.
Proof.
  induction 1; [constructor | econstructor; eassumption].
Qed.
