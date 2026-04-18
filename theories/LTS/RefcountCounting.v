(** * RefcountCounting.v — Refcount conservation law across traces.

    =========================================================================
    LAYER: 4 - APPLICATION (quantitative trace invariant)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    The refcount of an object tracks active readers.  This module proves
    the conservation law: across any trace where only BeginRead/EndRead
    target the object,

      refcount_final + #EndRead = refcount_initial + #BeginRead

    This is the quantitative bridge between trace-level operations and
    state-level protection.  As a corollary, if more reads have begun
    than ended, the object remains protected from eviction.

    @source mooncake-store/include/replica.h (inc_refcnt, dec_refcnt)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety
    - MooncakeFormal.LTS.ProtectionFrame
    - MooncakeFormal.LTS.TraceEquivalence

    PROVIDES:
    - count_begins (count BeginRead for an object in a trace)
    - count_ends (count EndRead for an object in a trace)
    - reads_only_for (label classification for counting)
    - find_after_update_seg (segment-level lookup after update)
    - begin_read_find (BeginRead updates find result to inc_refcnt)
    - end_read_find (EndRead updates find result to dec_refcnt)
    - refcount_counting (HEADLINE: refcount conservation law)
    - protection_from_counting (HEADLINE: excess begins imply protection)
*)

Require Import List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.
Require Import MooncakeFormal.LTS.ProtectionFrame.
Require Import MooncakeFormal.LTS.TraceEquivalence.

(** =====================================================================
    Section 1: COUNTING FUNCTIONS
    ===================================================================== *)

(** Count BeginRead operations for a specific object in a trace. *)
Fixpoint count_begins (oid : ObjectId) (ls : list RichStoreLabel) : nat :=
  match ls with
  | [] => 0
  | RLBeginRead oid' :: rest =>
      if Nat.eqb oid' oid then S (count_begins oid rest)
      else count_begins oid rest
  | _ :: rest => count_begins oid rest
  end.

(** Count EndRead operations for a specific object in a trace. *)
Fixpoint count_ends (oid : ObjectId) (ls : list RichStoreLabel) : nat :=
  match ls with
  | [] => 0
  | RLEndRead oid' :: rest =>
      if Nat.eqb oid' oid then S (count_ends oid rest)
      else count_ends oid rest
  | _ :: rest => count_ends oid rest
  end.

(** A label is reads-only-for an object if it either does not target
    the object, or is a BeginRead/EndRead for that object.  This
    excludes Place, Remove, and Evict — operations that would destroy
    the object or create a duplicate. *)
Definition reads_only_for (l : RichStoreLabel) (oid : ObjectId) : Prop :=
  label_targets l oid = false \/ l = RLBeginRead oid \/ l = RLEndRead oid.

(** =====================================================================
    Section 2: COUNTING COMPUTATION LEMMAS
    ===================================================================== *)

(** Non-targeting labels do not contribute to BeginRead count. *)
Lemma count_begins_non_targeting : forall oid l rest,
  label_targets l oid = false ->
  count_begins oid (l :: rest) = count_begins oid rest.
Proof.
  intros oid l rest Htarget.
  destruct l; simpl in *; try reflexivity.
  rewrite Htarget. reflexivity.
Qed.

(** Non-targeting labels do not contribute to EndRead count. *)
Lemma count_ends_non_targeting : forall oid l rest,
  label_targets l oid = false ->
  count_ends oid (l :: rest) = count_ends oid rest.
Proof.
  intros oid l rest Htarget.
  destruct l; simpl in *; try reflexivity.
  rewrite Htarget. reflexivity.
Qed.

(** BeginRead increments count_begins for the matching object. *)
Lemma count_begins_begin_read : forall oid rest,
  count_begins oid (RLBeginRead oid :: rest) = S (count_begins oid rest).
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

(** BeginRead does not affect count_ends. *)
Lemma count_ends_begin_read : forall oid rest,
  count_ends oid (RLBeginRead oid :: rest) = count_ends oid rest.
Proof. intros. reflexivity. Qed.

(** EndRead increments count_ends for the matching object. *)
Lemma count_ends_end_read : forall oid rest,
  count_ends oid (RLEndRead oid :: rest) = S (count_ends oid rest).
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

(** EndRead does not affect count_begins. *)
Lemma count_begins_end_read : forall oid rest,
  count_begins oid (RLEndRead oid :: rest) = count_begins oid rest.
Proof. intros. reflexivity. Qed.

(** =====================================================================
    Section 3: SEGMENT-LEVEL LOOKUP AFTER UPDATE
    ===================================================================== *)

(** Bridge from list-level find_after_update to segment level.
    After update_object_meta with id-preserving f, find returns f(m). *)
Lemma find_after_update_seg : forall seg oid f m,
  find_object seg oid = Some m ->
  (forall x, om_id (f x) = om_id x) ->
  find_object (update_object_meta seg oid f) oid = Some (f m).
Proof.
  intros seg oid f m Hfind Hpres.
  unfold find_object in *. unfold update_object_meta. simpl.
  apply find_after_update; assumption.
Qed.

(** =====================================================================
    Section 4: SINGLE-STEP REFCOUNT TRACKING
    ===================================================================== *)

(** After BeginRead, find_object returns inc_refcnt of the original. *)
Lemma begin_read_find : forall st oid m st',
  rich_store_step st (RLBeginRead oid) st' ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some (inc_refcnt m).
Proof.
  intros st oid m st' Hstep Hfind.
  inversion Hstep; subst. simpl.
  unfold inc_segment_refcnt.
  apply find_after_update_seg; [exact Hfind | exact inc_preserves_id].
Qed.

(** After EndRead, find_object returns dec_refcnt of the original. *)
Lemma end_read_find : forall st oid m st',
  rich_store_step st (RLEndRead oid) st' ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some (dec_refcnt m).
Proof.
  intros st oid m st' Hstep Hfind.
  inversion Hstep; subst. simpl.
  unfold dec_segment_refcnt.
  apply find_after_update_seg; [exact Hfind | exact dec_preserves_id].
Qed.

(** =====================================================================
    Section 5: REFCOUNT CONSERVATION LAW — HEADLINE
    ===================================================================== *)

(** HEADLINE: Refcount conservation law.

    Across any execution where only BeginRead/EndRead target a given
    object, the refcount satisfies an exact accounting identity:

      refcount_final + #EndRead = refcount_initial + #BeginRead

    This is a counting conservation law: refcount tokens are neither
    created nor destroyed, only moved between the counter and the
    trace.  Each BeginRead deposits a token into the counter; each
    EndRead withdraws one.  The total is conserved.

    The proof is by induction on the execution, with three cases per
    step: non-targeting (frame preserves find and both counts),
    BeginRead (inc_refcnt adds 1 to counter and 1 to #BeginRead),
    EndRead (dec_refcnt subtracts 1 from counter but adds 1 to
    #EndRead, requiring positive refcount for nat subtraction). *)
Theorem refcount_counting : forall st oid ls st' m m',
  exec st ls st' ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some m' ->
  Forall (fun l => reads_only_for l oid) ls ->
  om_ref_count m' + count_ends oid ls = om_ref_count m + count_begins oid ls.
Proof.
  intros st oid ls st' m m' Hexec.
  revert m m'.
  induction Hexec as [s | s l ls s_mid s_final Hstep Hexec IH];
    intros m m' Hfind Hfind' Hall.
  - (* Base: ls = [], same state *)
    rewrite Hfind in Hfind'. inversion Hfind'; subst.
    simpl. lia.
  - (* Cons: l :: ls *)
    inversion Hall as [| ? ? Hro Hls]; subst.
    destruct Hro as [Hnt | [Hbegin | Hend]].
    + (* Non-targeting: frame preserves find, counts unchanged *)
      assert (Hfmid : find_object (ss_segment s_mid) oid = Some m).
      { exact (non_targeting_preserves_find s l s_mid oid m Hstep Hnt Hfind). }
      rewrite (count_begins_non_targeting oid l ls Hnt).
      rewrite (count_ends_non_targeting oid l ls Hnt).
      exact (IH m m' Hfmid Hfind' Hls).
    + (* BeginRead: inc_refcnt adds 1 to counter *)
      subst l.
      assert (Hfmid : find_object (ss_segment s_mid) oid = Some (inc_refcnt m)).
      { exact (begin_read_find s oid m s_mid Hstep Hfind). }
      rewrite count_begins_begin_read, count_ends_begin_read.
      assert (Heq := IH (inc_refcnt m) m' Hfmid Hfind' Hls).
      simpl in Heq. lia.
    + (* EndRead: dec_refcnt subtracts 1, requires positive refcount *)
      subst l.
      destruct (end_read_requires_positive s oid s_mid Hstep)
        as [m0 [Hfind0 Hrc0]].
      assert (m0 = m) by congruence. subst m0.
      assert (Hfmid : find_object (ss_segment s_mid) oid = Some (dec_refcnt m)).
      { exact (end_read_find s oid m s_mid Hstep Hfind). }
      rewrite count_begins_end_read, count_ends_end_read.
      assert (Heq := IH (dec_refcnt m) m' Hfmid Hfind' Hls).
      simpl in Heq. lia.
Qed.

(** =====================================================================
    Section 6: SAFETY COROLLARY
    ===================================================================== *)

(** HEADLINE: If more reads have begun than ended (accounting for the
    initial refcount), the object remains protected from eviction.

    This connects trace-level counting to state-level safety: the
    eviction protection predicate is a consequence of the arithmetic
    of the conservation law.  Read-eviction safety (EvictionSafety.v)
    becomes a corollary of counting. *)
Corollary protection_from_counting : forall st oid ls st' m m',
  exec st ls st' ->
  find_object (ss_segment st) oid = Some m ->
  find_object (ss_segment st') oid = Some m' ->
  Forall (fun l => reads_only_for l oid) ls ->
  om_ref_count m + count_begins oid ls > count_ends oid ls ->
  eviction_protected m' = true.
Proof.
  intros st oid ls st' m m' Hexec Hfind Hfind' Hall Hineq.
  apply active_readers_protected.
  assert (Heq := refcount_counting st oid ls st' m m' Hexec Hfind Hfind' Hall).
  lia.
Qed.
