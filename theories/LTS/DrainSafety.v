(** * DrainSafety.v -- Drain lifecycle respects active readers.

    =========================================================================
    LAYER: 4 - APPLICATION (composition of safety + lifecycle)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Composes the frame properties (ProtectionFrame.v), eviction safety
    (EvictionSafety.v), NoDup preservation (NoDupPreservation.v), and
    the denotational semantics (Denotational.v) to prove the key
    operational question:

      Can Mooncake drain a segment while reads are in progress?

    Answer: yes, as long as the drain removes only non-read objects.
    Actively-read objects (refcount > 0) survive all removals of OTHER
    objects.  Their metadata is preserved unchanged, and eviction
    remains blocked throughout.

    The headline theorem (drain_phase_safety): after BeginDrain and
    arbitrary removals of other objects, an actively-read object is
    still findable with the same metadata, and eviction is impossible.

    @source mooncake-store/src/master_service.cpp (drain + concurrent reads)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.ProtectionFrame
    - MooncakeFormal.LTS.TraceEquivalence
    - MooncakeFormal.LTS.NoDupPreservation
    - MooncakeFormal.LTS.Denotational
    - DistributedML.Concurrency.Preservation (lstar)

    PROVIDES:
    - exec_to_lstar (bridge exec -> lstar)
    - lstar_to_exec (bridge lstar -> exec)
    - remove_labels_non_targeting (removal trace doesn't target absent IDs)
    - removal_trace_preserves_find (GENERAL: multi-step removal frame)
    - nodup_removal_trace (NoDup preserved through removal traces)
    - drain_phase_safety (HEADLINE: drain respects active readers)
    - drain_phase_eval (HEADLINE: denotational drain respects readers)
    - status_labels_non_targeting (status ops don't target any object)
    - full_drain_safety (HEADLINE: BeginDrain + removals + CompleteDrain safe)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.Preservation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.ProtectionFrame.
Require Import MooncakeFormal.LTS.TraceEquivalence.
Require Import MooncakeFormal.LTS.NoDupPreservation.
Require Import MooncakeFormal.LTS.Denotational.

(** =====================================================================
    Section 1: exec <-> lstar BRIDGE
    ===================================================================== *)

(** [exec] and [lstar rich_store_step] are structurally identical
    relations.  These two lemmas allow composing results proved with
    either formulation. *)

Lemma exec_to_lstar : forall st ls st',
  exec st ls st' -> lstar rich_store_step st ls st'.
Proof.
  intros st ls st' H. induction H.
  - apply lstar_refl.
  - eapply lstar_step; eauto.
Qed.

Lemma lstar_to_exec : forall st ls st',
  lstar rich_store_step st ls st' -> exec st ls st'.
Proof.
  intros st ls st' H. induction H.
  - constructor.
  - econstructor; eauto.
Qed.

(** =====================================================================
    Section 2: REMOVAL TRACE FRAME PROPERTIES
    ===================================================================== *)

(** A trace of RLRemove labels targeting IDs in [oids] does not
    target any ID outside [oids]. *)
Lemma remove_labels_non_targeting : forall oids oid,
  ~ In oid oids ->
  Forall (fun l => label_targets l oid = false) (map RLRemove oids).
Proof.
  induction oids as [| oid' rest IH]; intros oid Hni.
  - constructor.
  - simpl. constructor.
    + simpl. apply Nat.eqb_neq.
      intro Heq. apply Hni. left. exact Heq.
    + apply IH. intro Hin. apply Hni. right. exact Hin.
Qed.

(** Multi-step removal of objects in [oids] preserves find_object
    for any ID not in [oids].

    This lifts the single-step frame property
    (non_targeting_preserves_find) to arbitrary-length removal traces.
    The key insight: if oid is not in the removal list, then no
    RLRemove in the trace targets oid. *)
Theorem removal_trace_preserves_find : forall oids st st' oid m,
  exec st (map RLRemove oids) st' ->
  ~ In oid oids ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some m.
Proof.
  intros oids st st' oid m Hexec Hni Hfind.
  exact (trace_non_targeting_preserves_find
           st (map RLRemove oids) st' oid m
           (exec_to_lstar st (map RLRemove oids) st' Hexec)
           (remove_labels_non_targeting oids oid Hni)
           Hfind).
Qed.

(** NoDup is preserved through a removal trace. *)
Theorem nodup_removal_trace : forall oids st st',
  exec st (map RLRemove oids) st' ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  NoDup (map om_id (seg_objects (ss_segment st'))).
Proof.
  induction oids as [| oid rest IH]; intros st st' Hexec Hnd.
  - simpl in Hexec. inversion Hexec; subst. exact Hnd.
  - simpl in Hexec.
    destruct (exec_cons_inv st (RLRemove oid) (map RLRemove rest) st' Hexec)
      as [st_mid [Hstep Hrest]].
    apply (IH st_mid st' Hrest).
    exact (nodup_step_preserved st (RLRemove oid) st_mid Hstep I Hnd).
Qed.

(** =====================================================================
    Section 3: DRAIN PHASE SAFETY -- HEADLINE
    ===================================================================== *)

(** BeginDrain does not target any object (it only changes status). *)
Lemma begin_drain_non_targeting : forall oid,
  label_targets RLBeginDrain oid = false.
Proof. reflexivity. Qed.

(** CompleteDrain does not target any object. *)
Lemma complete_drain_non_targeting : forall oid,
  label_targets RLCompleteDrain oid = false.
Proof. reflexivity. Qed.

(** Unmount does not target any object. *)
Lemma unmount_non_targeting : forall oid,
  label_targets RLUnmount oid = false.
Proof. reflexivity. Qed.

(** Status operations (BeginDrain, CompleteDrain, Unmount) form a
    non-targeting trace for any object. *)
Lemma status_labels_non_targeting : forall ls oid,
  Forall (fun l => l = RLBeginDrain \/ l = RLCompleteDrain \/ l = RLUnmount) ls ->
  Forall (fun l => label_targets l oid = false) ls.
Proof.
  intros ls oid Hall. rewrite Forall_forall in Hall |- *.
  intros l Hin. destruct (Hall l Hin) as [H | [H | H]]; subst; reflexivity.
Qed.

(** HEADLINE: During the drain phase, actively-read objects survive.

    After BeginDrain and arbitrary removals of OTHER objects, an
    actively-read object (refcount > 0) retains its metadata unchanged
    and eviction remains impossible.

    This composes three independent results:
    1. BeginDrain preserves find (status change only)
    2. Removal trace preserves find for non-targeted IDs (frame property)
    3. Positive refcount blocks eviction (read-eviction safety)

    The theorem answers: "Can Mooncake drain a segment while reads
    are in progress?"  Yes — the drain phase only removes objects
    that are NOT being read.  Actively-read objects are untouched. *)
Theorem drain_phase_safety : forall st st_drain oids st' oid m,
  rich_store_step st RLBeginDrain st_drain ->
  exec st_drain (map RLRemove oids) st' ->
  ~ In oid oids ->
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  intros st st_drain oids st' oid m Hdrain Hexec Hni Hfind Hrc.
  (* Step 1: BeginDrain preserves find *)
  assert (Hfind_drain : find_object (ss_segment st_drain) oid = Some m).
  { exact (non_targeting_preserves_find st RLBeginDrain st_drain oid m
             Hdrain (begin_drain_non_targeting oid) Hfind). }
  (* Step 2: Removal trace preserves find *)
  assert (Hfind' : find_object (ss_segment st') oid = Some m).
  { exact (removal_trace_preserves_find oids st_drain st' oid m
             Hexec Hni Hfind_drain). }
  (* Step 3: Active readers block eviction *)
  split.
  - exact Hfind'.
  - exact (read_eviction_safety st' oid m Hfind' Hrc).
Qed.

(** =====================================================================
    Section 4: DENOTATIONAL CONNECTION
    ===================================================================== *)

(** HEADLINE: The denotational semantics agrees — evaluating a drain
    trace that skips an actively-read object preserves it.

    This connects the computable [eval] function with the drain safety
    theorem: if eval succeeds on a drain trace, the operational safety
    guarantees hold for the resulting state. *)
Theorem drain_phase_eval : forall st oids st' oid m,
  eval (RLBeginDrain :: map RLRemove oids) st = Some st' ->
  ~ In oid oids ->
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  intros st oids st' oid m Heval Hni Hfind Hrc.
  apply eval_adequacy in Heval.
  destruct (exec_cons_inv st RLBeginDrain (map RLRemove oids) st' Heval)
    as [st_drain [Hdrain Hexec]].
  exact (drain_phase_safety st st_drain oids st' oid m
           Hdrain Hexec Hni Hfind Hrc).
Qed.

(** =====================================================================
    Section 5: FULL DRAIN LIFECYCLE SAFETY
    ===================================================================== *)

(** Full drain lifecycle with CompleteDrain also preserves readers.

    If a segment starts in SegOk, we execute BeginDrain, then remove
    a set of objects (not including the actively-read one), then
    CompleteDrain — the actively-read object survives throughout.

    Note: CompleteDrain requires [seg_objects = []], which means the
    segment must be empty.  This theorem covers the case where the
    actively-read object has already been removed between the removal
    phase and CompleteDrain (e.g., after EndRead + Remove/Evict). *)
Theorem full_drain_safety : forall st ls st' oid m,
  exec st ls st' ->
  Forall (fun l => label_targets l oid = false) ls ->
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  find_object (ss_segment st') oid = Some m /\
  ~ exists st'', rich_store_step st' (RLEvict oid) st''.
Proof.
  intros st ls st' oid m Hexec Hall Hfind Hrc.
  assert (Hfind' : find_object (ss_segment st') oid = Some m).
  { exact (trace_non_targeting_preserves_find
             st ls st' oid m
             (exec_to_lstar st ls st' Hexec) Hall Hfind). }
  split.
  - exact Hfind'.
  - exact (read_eviction_safety st' oid m Hfind' Hrc).
Qed.

(** Corollary: any non-targeting trace preserves NoDup. *)
Corollary nodup_non_targeting_trace : forall st ls st',
  exec st ls st' ->
  Forall (fun l => match l with RLPlace _ => False | _ => True end) ls ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  NoDup (map om_id (seg_objects (ss_segment st'))).
Proof.
  intros st ls st' Hexec Hall Hnd.
  induction Hexec as [s | s l ls s_mid s_final Hstep Hexec IH].
  - exact Hnd.
  - inversion Hall as [| ? ? Hl Hls]; subst.
    apply IH; [exact Hls |].
    apply (nodup_step_preserved s l s_mid Hstep).
    + destruct l; simpl; try exact I. contradiction.
    + exact Hnd.
Qed.
