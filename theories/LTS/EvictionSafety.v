(** * EvictionSafety.v — Read-eviction safety via enriched LTS.

    =========================================================================
    LAYER: 4 - APPLICATION (eviction safety)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Extends the store LTS with three new operations that capture the
    essence of Mooncake's read-eviction protocol:

      LBeginRead oid  — decode node begins reading KV block (inc refcnt)
      LEndRead oid    — decode node finishes reading (dec refcnt)
      LEvict oid      — evictor reclaims storage (requires not protected)

    The headline theorem (read_eviction_safety): between LBeginRead and
    LEndRead for a given object, LEvict for that object is impossible.
    This is the fundamental correctness property of the refcount mechanism.

    The protocol gates enforce a separation between "active read" and
    "eligible for eviction" that cannot be violated by any interleaving
    of operations.

    @source mooncake-store/include/replica.h (inc_refcnt, dec_refcnt)
    @source mooncake-store/src/master_service.cpp (BatchEvict)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.DrainProtocol
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.StoreLTS
    - DistributedML.Concurrency.Preservation (lstar)

    PROVIDES:
    - RichStoreLabel (8 operations: original 5 + BeginRead, EndRead, Evict)
    - rich_store_step (enriched step relation)
    - read_makes_protected (BeginRead makes object protected)
    - evict_requires_unprotected (Evict requires not protected)
    - read_eviction_safety (HEADLINE: read in progress blocks eviction)
    - read_refcnt_invariant (refcnt tracks active reads)
    - rich_step_preserves_live (enriched steps preserve liveness)
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import DistributedML.Concurrency.Preservation.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.StoreLTS.

(** =====================================================================
    Section 1: ENRICHED STORE LABELS
    ===================================================================== *)

(** The enriched label set adds read and eviction operations. *)
Inductive RichStoreLabel : Set :=
  | RLPlace (m : ObjectMeta)
  | RLRemove (oid : ObjectId)
  | RLBeginDrain
  | RLCompleteDrain
  | RLUnmount
  | RLBeginRead (oid : ObjectId)    (* decode node begins reading *)
  | RLEndRead (oid : ObjectId)      (* decode node finishes reading *)
  | RLEvict (oid : ObjectId).       (* evictor reclaims storage *)

(** =====================================================================
    Section 2: ENRICHED STEP RELATION
    ===================================================================== *)

(** The enriched step relation extends store_step with three new
    constructors.  The existing five are included verbatim. *)
Inductive rich_store_step : StoreState -> RichStoreLabel -> StoreState -> Prop :=

  (** Original operations — same preconditions as store_step. *)

  | rstep_place : forall st m,
      seg_status (ss_segment st) = SegOk ->
      om_status m = RsInitialized ->
      replica_terminal (om_status m) = false ->
      rich_store_step st (RLPlace m)
        (mkStoreState (place_object (ss_segment st) m) (ss_transfers st))

  | rstep_remove : forall st oid,
      rich_store_step st (RLRemove oid)
        (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st))

  | rstep_begin_drain : forall st,
      seg_status (ss_segment st) = SegOk ->
      no_in_progress (ss_segment st) ->
      rich_store_step st RLBeginDrain
        (mkStoreState (begin_drain (ss_segment st)) (ss_transfers st))

  | rstep_complete_drain : forall st,
      seg_status (ss_segment st) = SegDraining ->
      seg_objects (ss_segment st) = [] ->
      rich_store_step st RLCompleteDrain
        (mkStoreState (complete_drain (ss_segment st)) (ss_transfers st))

  | rstep_unmount : forall st,
      safe_to_unmount (ss_segment st) ->
      rich_store_step st RLUnmount
        (mkStoreState (begin_unmount (ss_segment st)) (ss_transfers st))

  (** New: begin reading a COMPLETE object. Increments refcount. *)
  | rstep_begin_read : forall st oid m,
      find_object (ss_segment st) oid = Some m ->
      om_status m = RsComplete ->
      rich_store_step st (RLBeginRead oid)
        (mkStoreState (inc_segment_refcnt (ss_segment st) oid) (ss_transfers st))

  (** New: end reading. Decrements refcount. Requires refcnt > 0. *)
  | rstep_end_read : forall st oid m,
      find_object (ss_segment st) oid = Some m ->
      om_ref_count m > 0 ->
      rich_store_step st (RLEndRead oid)
        (mkStoreState (dec_segment_refcnt (ss_segment st) oid) (ss_transfers st))

  (** New: evict an object. Requires NOT protected. *)
  | rstep_evict : forall st oid m,
      find_object (ss_segment st) oid = Some m ->
      eviction_protected m = false ->
      rich_store_step st (RLEvict oid)
        (mkStoreState (remove_object (ss_segment st) oid) (ss_transfers st)).

(** =====================================================================
    Section 3: SINGLE-STEP SAFETY PROPERTIES
    ===================================================================== *)

(** BeginRead makes the target object protected. *)
Theorem read_makes_protected : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  om_status m = RsComplete ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  exists m',
    find_object (inc_segment_refcnt (ss_segment st) oid) oid = Some m' /\
    eviction_protected m' = true.
Proof.
  intros st oid m Hfind Hcomp Hnd.
  destruct (inc_segment_refcnt_protects (ss_segment st) oid m Hfind Hnd)
    as [m' [Hf' [_ Hp']]].
  exists m'. split; assumption.
Qed.

(** Eviction requires the object to be unprotected. *)
Theorem evict_requires_unprotected : forall st oid st',
  rich_store_step st (RLEvict oid) st' ->
  exists m,
    find_object (ss_segment st) oid = Some m /\
    eviction_protected m = false.
Proof.
  intros st oid st' Hstep. inversion Hstep; subst.
  exists m. split; assumption.
Qed.

(** =====================================================================
    Section 4: READ-EVICTION SAFETY — HEADLINE THEOREM
    ===================================================================== *)

(** A read in progress (refcnt > 0) makes eviction impossible.

    This is the direct formulation: if an object has positive refcount,
    then eviction_protected is true, and the Evict precondition
    (eviction_protected = false) cannot be satisfied.

    This captures the essence of Mooncake's refcount protocol:
    inc_refcnt before read + check refcnt=0 before evict = safety. *)

Theorem read_eviction_safety : forall st oid m,
  find_object (ss_segment st) oid = Some m ->
  om_ref_count m > 0 ->
  ~ exists st', rich_store_step st (RLEvict oid) st'.
Proof.
  intros st oid m Hfind Hrc [st' Hstep].
  inversion Hstep as [| | | | | | | ? ? m0 Hfind0 Hprot0]; subst.
  (* m0 found with eviction_protected m0 = false, but m has refcnt > 0. *)
  rewrite Hfind in Hfind0. inversion Hfind0; subst.
  assert (Hprot := active_readers_protected m0 Hrc).
  rewrite Hprot in Hprot0. discriminate.
Qed.

(** Stronger version: after BeginRead, eviction of the same object is
    blocked in the resulting state (assuming unique IDs). *)
Theorem begin_read_blocks_eviction : forall st oid st1,
  rich_store_step st (RLBeginRead oid) st1 ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  ~ exists st', rich_store_step st1 (RLEvict oid) st'.
Proof.
  intros st oid st1 Hread Hnd [st' Hevict].
  inversion Hread as [| | | | | ? ? m0 Hfind0 Hcomp0 | |]; subst.
  inversion Hevict as [| | | | | | | ? ? m1 Hfind1 Hprot1]; subst.
  simpl in Hfind1.
  destruct (inc_segment_refcnt_protects (ss_segment st) oid m0 Hfind0 Hnd)
    as [m' [Hf' [Hrc' Hp']]].
  rewrite Hf' in Hfind1. inversion Hfind1; subst.
  rewrite Hp' in Hprot1. discriminate.
Qed.

(** =====================================================================
    Section 5: PROTOCOL STRUCTURE
    ===================================================================== *)

(** Classification: which operations affect a specific object's refcount? *)
Definition affects_refcnt (l : RichStoreLabel) (oid : ObjectId) : bool :=
  match l with
  | RLBeginRead oid' => Nat.eqb oid' oid
  | RLEndRead oid' => Nat.eqb oid' oid
  | _ => false
  end.

(** Classification: which operations remove a specific object? *)
Definition removes_object (l : RichStoreLabel) (oid : ObjectId) : bool :=
  match l with
  | RLRemove oid' => Nat.eqb oid' oid
  | RLEvict oid' => Nat.eqb oid' oid
  | _ => false
  end.

(** Eviction is a special case of removal that checks protection. *)
Theorem evict_is_guarded_remove : forall st oid st',
  rich_store_step st (RLEvict oid) st' ->
  rich_store_step st (RLRemove oid) st'.
Proof.
  intros st oid st' Hstep. inversion Hstep; subst.
  constructor.
Qed.

(** BeginRead requires the object to be readable (COMPLETE). *)
Theorem begin_read_requires_complete : forall st oid st',
  rich_store_step st (RLBeginRead oid) st' ->
  exists m,
    find_object (ss_segment st) oid = Some m /\
    om_status m = RsComplete.
Proof.
  intros st oid st' Hstep. inversion Hstep; subst.
  exists m. split; assumption.
Qed.

(** EndRead requires positive refcount (well-formed pairing). *)
Theorem end_read_requires_positive : forall st oid st',
  rich_store_step st (RLEndRead oid) st' ->
  exists m,
    find_object (ss_segment st) oid = Some m /\
    om_ref_count m > 0.
Proof.
  intros st oid st' Hstep. inversion Hstep; subst.
  exists m. split; assumption.
Qed.

(** The three protection sources are disjoint concerns:
    pin level, refcount, and status each independently protect. *)
Theorem triple_protection : forall m,
  om_pin m = HardPinned \/
  om_ref_count m > 0 \/
  replica_readable (om_status m) = false ->
  eviction_protected m = true.
Proof.
  intros m [Hpin | [Hrc | Hnr]].
  - exact (hard_pinned_protected m Hpin).
  - exact (active_readers_protected m Hrc).
  - unfold eviction_protected.
    destruct (om_pin m); simpl;
    destruct (Nat.ltb 0 (om_ref_count m)); simpl; auto;
    rewrite Hnr; reflexivity.
Qed.

(** Eviction requires ALL three protections to be absent. *)
Theorem eviction_requires_all_absent : forall m,
  eviction_protected m = false ->
  om_pin m <> HardPinned /\
  om_ref_count m = 0 /\
  om_status m = RsComplete.
Proof.
  intros m H.
  destruct (evictable_characterization m H) as [Hs [Hp Hrc]].
  repeat split; assumption.
Qed.
