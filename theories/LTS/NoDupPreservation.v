(** * NoDupPreservation.v — NoDup is an invariant of the enriched LTS.

    =========================================================================
    LAYER: 3-4 - DOMAIN/APPLICATION (invariant preservation)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Many theorems in this formalization assume NoDup (unique object IDs)
    as a hypothesis.  This module closes the gap by proving that NoDup
    is preserved by every operation in the enriched LTS.

    The core insight: filter preserves NoDup (removal), map preserves
    NoDup when the key function is preserved (update), and cons
    preserves NoDup when the new key is fresh (placement).  Since every
    enriched step is one of these three, NoDup is an invariant.

    @source mooncake-store/src/master_service.cpp (object ID management)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core
    - MooncakeFormal.Store.SegmentManager
    - MooncakeFormal.Store.RefcountProtocol
    - MooncakeFormal.Composition.StoreComposition
    - MooncakeFormal.LTS.EvictionSafety

    PROVIDES:
    - in_map_of_filter (membership in filtered map implies membership in map)
    - nodup_filter_preserved (filter preserves NoDup)
    - nodup_map_id_preserved (id-preserving map preserves NoDup)
    - nodup_remove_preserved (remove_object preserves NoDup)
    - nodup_update_preserved (update_object_meta preserves NoDup)
    - nodup_inc_refcnt_preserved (inc_segment_refcnt preserves NoDup)
    - nodup_dec_refcnt_preserved (dec_segment_refcnt preserves NoDup)
    - nodup_place_preserved (place_object preserves NoDup when ID is fresh)
    - nodup_step_preserved (HEADLINE: enriched step preserves NoDup)
*)

Require Import List Arith.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.
Require Import MooncakeFormal.Store.DrainProtocol.
Require Import MooncakeFormal.Store.RefcountProtocol.
Require Import MooncakeFormal.Composition.StoreComposition.
Require Import MooncakeFormal.LTS.EvictionSafety.

(** =====================================================================
    Section 1: LIST-LEVEL NoDup PRESERVATION
    ===================================================================== *)

(** Membership in a filtered+mapped list implies membership in the
    original mapped list. *)
Lemma in_map_of_filter :
  forall (objs : list ObjectMeta) (p : ObjectMeta -> bool) x,
  In x (map om_id (filter p objs)) -> In x (map om_id objs).
Proof.
  intros objs p x. induction objs as [| h rest IH]; intro Hin.
  - exact Hin.
  - simpl in Hin |- *. destruct (p h); simpl in Hin.
    + destruct Hin as [Heq | Hin].
      * left. exact Heq.
      * right. exact (IH Hin).
    + right. exact (IH Hin).
Qed.

(** Filtering preserves NoDup on projected keys. *)
Lemma nodup_filter_preserved :
  forall (objs : list ObjectMeta) (p : ObjectMeta -> bool),
  NoDup (map om_id objs) ->
  NoDup (map om_id (filter p objs)).
Proof.
  intros objs p. induction objs as [| h rest IH]; intro Hnd.
  - constructor.
  - simpl in Hnd |- *. inversion Hnd as [| ? ? Hni Hnd']; subst.
    destruct (p h).
    + simpl. constructor.
      * intro Hin. exact (Hni (in_map_of_filter rest p _ Hin)).
      * exact (IH Hnd').
    + exact (IH Hnd').
Qed.

(** Membership in an id-preserving mapped list equals membership in
    the original mapped list. *)
Lemma in_map_of_id_map :
  forall (objs : list ObjectMeta) oid (f : ObjectMeta -> ObjectMeta) x,
  (forall m, om_id (f m) = om_id m) ->
  In x (map om_id (map (fun m => if Nat.eqb (om_id m) oid then f m else m) objs)) ->
  In x (map om_id objs).
Proof.
  intros objs oid f x Hpres. induction objs as [| h rest IH]; intro Hin.
  - exact Hin.
  - simpl in Hin |- *. destruct (Nat.eqb (om_id h) oid); simpl in Hin.
    + destruct Hin as [Heq | Hin].
      * left. rewrite Hpres in Heq. exact Heq.
      * right. exact (IH Hin).
    + destruct Hin as [Heq | Hin].
      * left. exact Heq.
      * right. exact (IH Hin).
Qed.

(** Map with an id-preserving function preserves NoDup on projected keys. *)
Lemma nodup_map_id_preserved :
  forall (objs : list ObjectMeta) oid (f : ObjectMeta -> ObjectMeta),
  (forall m, om_id (f m) = om_id m) ->
  NoDup (map om_id objs) ->
  NoDup (map om_id (map (fun x => if Nat.eqb (om_id x) oid then f x else x) objs)).
Proof.
  intros objs oid f Hpres. induction objs as [| h rest IH]; intro Hnd.
  - constructor.
  - simpl in Hnd |- *. inversion Hnd as [| ? ? Hni Hnd']; subst.
    destruct (Nat.eqb (om_id h) oid) eqn:Heq; simpl.
    + rewrite Hpres. constructor.
      * intro Hin. exact (Hni (in_map_of_id_map rest oid f _ Hpres Hin)).
      * exact (IH Hnd').
    + constructor.
      * intro Hin. exact (Hni (in_map_of_id_map rest oid f _ Hpres Hin)).
      * exact (IH Hnd').
Qed.

(** =====================================================================
    Section 2: SEGMENT-LEVEL NoDup PRESERVATION
    ===================================================================== *)

(** remove_object preserves NoDup. *)
Lemma nodup_remove_preserved : forall seg oid,
  NoDup (map om_id (seg_objects seg)) ->
  NoDup (map om_id (seg_objects (remove_object seg oid))).
Proof.
  intros seg oid Hnd. unfold remove_object. simpl.
  apply nodup_filter_preserved. exact Hnd.
Qed.

(** update_object_meta preserves NoDup when f preserves om_id. *)
Lemma nodup_update_preserved : forall seg oid (f : ObjectMeta -> ObjectMeta),
  (forall m, om_id (f m) = om_id m) ->
  NoDup (map om_id (seg_objects seg)) ->
  NoDup (map om_id (seg_objects (update_object_meta seg oid f))).
Proof.
  intros seg oid f Hpres Hnd. unfold update_object_meta. simpl.
  apply nodup_map_id_preserved; assumption.
Qed.

(** inc_segment_refcnt preserves NoDup. *)
Lemma nodup_inc_refcnt_preserved : forall seg oid,
  NoDup (map om_id (seg_objects seg)) ->
  NoDup (map om_id (seg_objects (inc_segment_refcnt seg oid))).
Proof.
  intros seg oid Hnd. unfold inc_segment_refcnt.
  apply nodup_update_preserved; [exact inc_preserves_id | exact Hnd].
Qed.

(** dec_segment_refcnt preserves NoDup. *)
Lemma nodup_dec_refcnt_preserved : forall seg oid,
  NoDup (map om_id (seg_objects seg)) ->
  NoDup (map om_id (seg_objects (dec_segment_refcnt seg oid))).
Proof.
  intros seg oid Hnd. unfold dec_segment_refcnt.
  apply nodup_update_preserved; [exact dec_preserves_id | exact Hnd].
Qed.

(** place_object preserves NoDup when the new object's ID is fresh. *)
Lemma nodup_place_preserved : forall seg m,
  ~ In (om_id m) (map om_id (seg_objects seg)) ->
  NoDup (map om_id (seg_objects seg)) ->
  NoDup (map om_id (seg_objects (place_object seg m))).
Proof.
  intros seg m Hfresh Hnd.
  unfold place_object. simpl.
  exact (NoDup_cons (om_id m) Hfresh Hnd).
Qed.

(** =====================================================================
    Section 3: STEP-LEVEL NoDup PRESERVATION — HEADLINE THEOREM
    ===================================================================== *)

(** Classifies the well-formedness condition for Place operations:
    placed objects must have IDs not already present in the segment. *)
Definition place_fresh (st : StoreState) (l : RichStoreLabel) : Prop :=
  match l with
  | RLPlace m => ~ In (om_id m) (map om_id (seg_objects (ss_segment st)))
  | _ => True
  end.

(** HEADLINE: Every enriched step preserves NoDup, provided that
    Place operations supply fresh IDs.

    For all non-Place operations, the [place_fresh] condition is
    trivially True, so this theorem applies unconditionally.
    Only Place requires the caller to supply a fresh ID — which
    corresponds to the source invariant that object IDs are unique. *)
Theorem nodup_step_preserved : forall st l st',
  rich_store_step st l st' ->
  place_fresh st l ->
  NoDup (map om_id (seg_objects (ss_segment st))) ->
  NoDup (map om_id (seg_objects (ss_segment st'))).
Proof.
  intros st l st' Hstep Hfresh Hnd.
  inversion Hstep; subst; simpl in *.
  - (* rstep_place *)
    apply nodup_place_preserved; assumption.
  - (* rstep_remove *)
    apply nodup_remove_preserved. exact Hnd.
  - (* rstep_begin_drain *)
    unfold begin_drain, set_segment_status. simpl. exact Hnd.
  - (* rstep_complete_drain *)
    unfold complete_drain, set_segment_status. simpl. exact Hnd.
  - (* rstep_unmount *)
    unfold begin_unmount, set_segment_status. simpl. exact Hnd.
  - (* rstep_begin_read *)
    apply nodup_inc_refcnt_preserved. exact Hnd.
  - (* rstep_end_read *)
    apply nodup_dec_refcnt_preserved. exact Hnd.
  - (* rstep_evict *)
    apply nodup_remove_preserved. exact Hnd.
Qed.
