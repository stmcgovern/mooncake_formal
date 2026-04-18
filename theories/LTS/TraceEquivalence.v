(** * TraceEquivalence.v — Trace monoid and the permutation theorem.

    =========================================================================
    LAYER: 4 - APPLICATION (algebraic structure of the LTS)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    The Mooncake store's enriched LTS has a Mazurkiewicz trace monoid
    structure: independent operations commute.  This module makes the
    structure explicit and proves the permutation theorem — swapping
    adjacent independent operations in a trace preserves the final state.

    The proof factors through three layers:
    1. Execution: deterministic multi-step execution from label sequences
    2. Independence: label classification and the unified diamond property
    3. Permutation: adjacent swap of independent operations preserves result

    @source mooncake-store/src/master_service.cpp (concurrent operations)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.Diamond

    PROVIDES:
    - exec (multi-step execution of a label sequence)
    - rich_store_step_deterministic (single-step determinism)
    - exec_deterministic (multi-step determinism)
    - exec_cons_inv (inversion for cons execution)
    - exec_split (split execution at concatenation point)
    - exec_join (join execution of concatenated lists)
    - status_op (classifies status-changing labels)
    - independent (label independence relation)
    - independent_sym (independence is symmetric)
    - independent_diamond (HEADLINE: unified diamond for independent ops)
    - swap_preserves_result (HEADLINE: adjacent swap preserves final state)
*)

Require Import List.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.Diamond.

(** =====================================================================
    Section 1: MULTI-STEP EXECUTION
    ===================================================================== *)

(** Execute a sequence of labels from a starting state. *)
Inductive exec : StoreState -> list RichStoreLabel -> StoreState -> Prop :=
  | exec_nil : forall st, exec st [] st
  | exec_cons : forall st l ls st' st'',
      rich_store_step st l st' ->
      exec st' ls st'' ->
      exec st (l :: ls) st''.

(** Single-step determinism: the enriched step relation is deterministic.
    For any state and label, there is at most one successor state. *)
Lemma rich_store_step_deterministic : forall st l st1 st2,
  rich_store_step st l st1 ->
  rich_store_step st l st2 ->
  st1 = st2.
Proof.
  intros st l st1 st2 H1 H2.
  inversion H1; subst; inversion H2; subst; reflexivity.
Qed.

(** Inversion principle for exec on a cons list. *)
Lemma exec_cons_inv : forall st l ls st',
  exec st (l :: ls) st' ->
  exists st_mid, rich_store_step st l st_mid /\ exec st_mid ls st'.
Proof.
  intros st l ls st' H. inversion H; subst. eauto.
Qed.

(** Multi-step determinism: the same label sequence from the same state
    always reaches the same final state. *)
Lemma exec_deterministic : forall st ls st1,
  exec st ls st1 ->
  forall st2, exec st ls st2 -> st1 = st2.
Proof.
  intros st ls st1 H1. induction H1 as [st | st l ls st' st1 Hstep Hexec IH].
  - intros st2 H2. inversion H2; subst. reflexivity.
  - intros st2 H2.
    destruct (exec_cons_inv _ _ _ _ H2) as [st_mid [Hstep2 Hexec2]].
    assert (st' = st_mid).
    { eapply rich_store_step_deterministic; eassumption. }
    subst. exact (IH _ Hexec2).
Qed.

(** Split execution at a list concatenation point. *)
Lemma exec_split : forall ls1 ls2 st st',
  exec st (ls1 ++ ls2) st' ->
  exists st_mid, exec st ls1 st_mid /\ exec st_mid ls2 st'.
Proof.
  induction ls1 as [| l ls1 IH]; intros ls2 st st' Hexec.
  - exists st. split; [constructor | exact Hexec].
  - simpl in Hexec.
    destruct (exec_cons_inv _ _ _ _ Hexec) as [s1 [Hstep Hrest]].
    destruct (IH ls2 s1 st' Hrest) as [st_mid [H1 H2]].
    exists st_mid. split.
    + exact (exec_cons st l ls1 s1 st_mid Hstep H1).
    + exact H2.
Qed.

(** Join execution of concatenated label lists. *)
Lemma exec_join : forall ls1 ls2 st st_mid st',
  exec st ls1 st_mid ->
  exec st_mid ls2 st' ->
  exec st (ls1 ++ ls2) st'.
Proof.
  intros ls1. induction ls1 as [| l ls1 IH]; intros ls2 st st_mid st' H1 H2.
  - inversion H1; subst. exact H2.
  - simpl.
    destruct (exec_cons_inv _ _ _ _ H1) as [s1 [Hstep Hrest]].
    eapply exec_cons.
    + exact Hstep.
    + exact (IH ls2 s1 st_mid st' Hrest H2).
Qed.

(** =====================================================================
    Section 2: LABEL INDEPENDENCE
    ===================================================================== *)

(** Classifies status-changing operations (modify segment status only). *)
Inductive status_op : RichStoreLabel -> Prop :=
  | sop_begin_drain : status_op RLBeginDrain
  | sop_complete_drain : status_op RLCompleteDrain
  | sop_unmount : status_op RLUnmount.

(** Two labels are independent if they modify disjoint parts of the state:
    - Both are object operations targeting different objects, or
    - One is a status operation and the other is an object operation.

    Independent operations commute: their execution order does not affect
    the resulting state.  This is the concurrency relation of the
    Mazurkiewicz trace monoid. *)
Definition independent (l1 l2 : RichStoreLabel) : Prop :=
  (exists oid1 oid2,
     object_op l1 oid1 /\ object_op l2 oid2 /\ oid1 <> oid2) \/
  (status_op l1 /\ exists oid, object_op l2 oid) \/
  (status_op l2 /\ exists oid, object_op l1 oid).

(** Independence is symmetric. *)
Lemma independent_sym : forall l1 l2,
  independent l1 l2 -> independent l2 l1.
Proof.
  intros l1 l2 [(oid1 & oid2 & H1 & H2 & Hneq) |
                 [(Hs & oid & Ho) | (Hs & oid & Ho)]].
  - left. exists oid2, oid1. auto using not_eq_sym.
  - right. right. exact (conj Hs (ex_intro _ oid Ho)).
  - right. left. exact (conj Hs (ex_intro _ oid Ho)).
Qed.

(** =====================================================================
    Section 3: UNIFIED DIAMOND PROPERTY
    ===================================================================== *)

(** HEADLINE: Unified diamond property for independent operations.

    If two independent operations can both execute from the same state
    in either order, they produce the same final state.  This unifies
    all individual diamond theorems from Diamond.v:
    - 16 object x object combinations (via general_object_diamond)
    - 24 status x object combinations (3 status ops x 4 object ops x
      2 orderings, all solved by reflexivity) *)
Theorem independent_diamond : forall st l1 l2 st1 st2 st12 st21,
  independent l1 l2 ->
  rich_store_step st l1 st1 ->
  rich_store_step st1 l2 st12 ->
  rich_store_step st l2 st2 ->
  rich_store_step st2 l1 st21 ->
  st12 = st21.
Proof.
  intros st l1 l2 st1 st2 st12 st21 Hind H1 H12 H2 H21.
  destruct Hind as [(oid1 & oid2 & Hop1 & Hop2 & Hneq) |
                    [(Hsop & oid & Hop) | (Hsop & oid & Hop)]].
  - (* Both object ops on different IDs *)
    exact (general_object_diamond st l1 l2 oid1 oid2 st1 st2 st12 st21
             Hop1 Hop2 Hneq H1 H12 H2 H21).
  - (* l1 is status op, l2 is object op *)
    inversion Hsop; subst; inversion Hop; subst;
    inversion H1; subst; inversion H12; subst;
    inversion H2; subst; inversion H21; subst;
    reflexivity.
  - (* l2 is status op, l1 is object op *)
    inversion Hsop; subst; inversion Hop; subst;
    inversion H1; subst; inversion H12; subst;
    inversion H2; subst; inversion H21; subst;
    reflexivity.
Qed.

(** =====================================================================
    Section 4: PERMUTATION THEOREM — HEADLINE
    ===================================================================== *)

(** HEADLINE: Swapping adjacent independent operations in a trace
    preserves the final state.

    This is the Mazurkiewicz trace equivalence theorem instantiated for
    the Mooncake store.  If two schedulings of a trace differ by
    swapping one pair of adjacent independent operations, and both are
    executable, they reach the same final state.

    The proof:
    1. Split both executions at the common prefix
    2. Determinism: both reach the same state after the prefix
    3. Diamond: the two orders of the swapped pair yield the same state
    4. Determinism: the common suffix from the same state yields the same end

    The full multi-swap permutation theorem (any number of adjacent swaps
    of independent operations) follows by induction, provided each
    intermediate ordering is also executable.  Executability preservation
    under swap requires reverse frame lemmas (find_object is preserved
    backward through non-targeting operations) — a clear next step. *)
Theorem swap_preserves_result : forall pre l1 l2 post st st1 st2,
  independent l1 l2 ->
  exec st (pre ++ l1 :: l2 :: post) st1 ->
  exec st (pre ++ l2 :: l1 :: post) st2 ->
  st1 = st2.
Proof.
  intros pre l1 l2 post st st1 st2 Hind Hexec1 Hexec2.
  (* Split at the prefix *)
  destruct (exec_split pre (l1 :: l2 :: post) st st1 Hexec1)
    as [s [Hpre1 Hrest1]].
  destruct (exec_split pre (l2 :: l1 :: post) st st2 Hexec2)
    as [s' [Hpre2 Hrest2]].
  (* Both reach the same state after the prefix *)
  assert (Hs : s = s') by (eapply exec_deterministic; eassumption).
  subst s'.
  (* Decompose l1::l2::post *)
  destruct (exec_cons_inv _ _ _ _ Hrest1) as [s1 [Hs1 Hrest1']].
  destruct (exec_cons_inv _ _ _ _ Hrest1') as [s12 [Hs12 Hpost1]].
  (* Decompose l2::l1::post *)
  destruct (exec_cons_inv _ _ _ _ Hrest2) as [s2 [Hs2 Hrest2']].
  destruct (exec_cons_inv _ _ _ _ Hrest2') as [s21 [Hs21 Hpost2]].
  (* Diamond: swapped pair reaches the same state *)
  assert (Hd : s12 = s21).
  { exact (independent_diamond s l1 l2 s1 s2 s12 s21 Hind Hs1 Hs12 Hs2 Hs21). }
  subst s21.
  (* Determinism on the suffix *)
  exact (exec_deterministic s12 post st1 Hpost1 _ Hpost2).
Qed.
