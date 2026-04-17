(** * RefcountProtocol.v — Reference counting as a protection protocol.

    =========================================================================
    LAYER: 2-3 - BASE/DOMAIN LEMMAS (refcount operations)
    =========================================================================
    Tier: exploratory  Admits: 0  Axioms: 0

    Formalizes the refcount mechanism that protects objects from eviction
    during active reads.  This is the most critical safety mechanism in
    Mooncake: a decode node increments refcount before reading a KV cache
    block via RDMA, and decrements it after the read completes.  Eviction
    checks refcount = 0 before reclaiming storage.

    The protocol:
      1. Reader calls inc_refcnt (BeginRead)
      2. Reader accesses data
      3. Reader calls dec_refcnt (EndRead)
      4. Evictor checks refcnt = 0 before evicting

    Key safety: between steps 1 and 3, the object is protected from
    eviction.  This module proves the connection between refcount
    operations and eviction protection.

    @source mooncake-store/include/replica.h (inc_refcnt, dec_refcnt,
            get_refcnt, fn_is_busy)
    @fidelity specification
    @abstraction behavioral-model

    DEPENDENCIES:
    - MooncakeFormal.Core.Core (ObjectMeta, eviction_protected, PinLevel)
    - MooncakeFormal.Store.SegmentManager (Segment, seg_objects)

    PROVIDES:
    - find_object (look up object by ID)
    - update_object_meta (update a specific object in segment)
    - inc_refcnt, dec_refcnt (refcount operations on ObjectMeta)
    - inc_segment_refcnt, dec_segment_refcnt (segment-level operations)
    - inc_protects (incrementing refcount makes object protected)
    - dec_from_positive (decrementing from n+1 gives n)
    - refcnt_positive_protected (refcnt > 0 implies protected)
    - update_preserves_status, update_preserves_objects_length
*)

Require Import Bool List Arith Lia.
Import ListNotations.
Require Import MooncakeFormal.Core.Core.
Require Import MooncakeFormal.Store.SegmentManager.

(** =====================================================================
    Section 1: OBJECT LOOKUP
    ===================================================================== *)

(** Find an object in a segment by ID. *)
Fixpoint find_object_in (objs : list ObjectMeta) (oid : ObjectId) : option ObjectMeta :=
  match objs with
  | [] => None
  | m :: rest =>
    if Nat.eqb (om_id m) oid then Some m
    else find_object_in rest oid
  end.

Definition find_object (seg : Segment) (oid : ObjectId) : option ObjectMeta :=
  find_object_in (seg_objects seg) oid.

(** find_object_in finds an element that is In the list. *)
Lemma find_object_in_some : forall objs oid m,
  find_object_in objs oid = Some m ->
  In m objs /\ om_id m = oid.
Proof.
  intros objs oid m. induction objs as [| h rest IH].
  - simpl. discriminate.
  - simpl. destruct (Nat.eqb (om_id h) oid) eqn:Heq.
    + intros H. inversion H; subst. split.
      * left. reflexivity.
      * apply Nat.eqb_eq. exact Heq.
    + intros H. destruct (IH H) as [Hin Hid]. split.
      * right. exact Hin.
      * exact Hid.
Qed.

(** If an object is In the list with unique IDs, find succeeds. *)
Lemma find_object_in_present : forall objs m,
  In m objs ->
  NoDup (map om_id objs) ->
  find_object_in objs (om_id m) = Some m.
Proof.
  intros objs m Hin Hnd. induction objs as [| h rest IH].
  - inversion Hin.
  - simpl. destruct (Nat.eqb (om_id h) (om_id m)) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      destruct Hin as [Heq' | Hin'].
      * subst. reflexivity.
      * (* h ≠ m but same ID: contradicts NoDup *)
        exfalso. inversion Hnd; subst.
        apply H1. rewrite Heq. apply in_map. exact Hin'.
    + destruct Hin as [Heq' | Hin'].
      * subst. rewrite Nat.eqb_refl in Heq. discriminate.
      * inversion Hnd; subst. exact (IH Hin' H2).
Qed.

(** =====================================================================
    Section 2: REFCOUNT OPERATIONS ON OBJECT METADATA
    ===================================================================== *)

(** Increment reference count. *)
Definition inc_refcnt (m : ObjectMeta) : ObjectMeta :=
  mkObjectMeta (om_id m) (om_segment m) (om_status m)
               (om_pin m) (S (om_ref_count m)) (om_size m).

(** Decrement reference count (saturating at 0). *)
Definition dec_refcnt (m : ObjectMeta) : ObjectMeta :=
  mkObjectMeta (om_id m) (om_segment m) (om_status m)
               (om_pin m) (om_ref_count m - 1) (om_size m).

(** inc_refcnt preserves identity. *)
Lemma inc_preserves_id : forall m,
  om_id (inc_refcnt m) = om_id m.
Proof. intros. reflexivity. Qed.

(** dec_refcnt preserves identity. *)
Lemma dec_preserves_id : forall m,
  om_id (dec_refcnt m) = om_id m.
Proof. intros. reflexivity. Qed.

(** inc_refcnt result has positive refcount. *)
Lemma inc_refcnt_positive : forall m,
  om_ref_count (inc_refcnt m) > 0.
Proof. intros m. simpl. lia. Qed.

(** dec_refcnt from positive decreases by 1. *)
Lemma dec_refcnt_from_positive : forall m,
  om_ref_count m > 0 ->
  om_ref_count (dec_refcnt m) = om_ref_count m - 1.
Proof. intros. reflexivity. Qed.

(** inc then dec is identity on refcount. *)
Lemma inc_dec_refcnt : forall m,
  om_ref_count (dec_refcnt (inc_refcnt m)) = om_ref_count m.
Proof. intros m. simpl. lia. Qed.

(** =====================================================================
    Section 3: REFCOUNT AND EVICTION PROTECTION
    ===================================================================== *)

(** THE KEY SAFETY LEMMA: incrementing refcount makes an object
    protected from eviction, regardless of pin level or status. *)
Theorem inc_protects : forall m,
  eviction_protected (inc_refcnt m) = true.
Proof.
  intros m. apply active_readers_protected.
  apply inc_refcnt_positive.
Qed.

(** Positive refcount implies protection. *)
Theorem refcnt_positive_protected : forall m,
  om_ref_count m > 0 ->
  eviction_protected m = true.
Proof. exact active_readers_protected. Qed.

(** Evictable implies zero refcount. *)
Theorem evictable_zero_refcnt : forall m,
  eviction_protected m = false ->
  om_ref_count m = 0.
Proof.
  intros m H. unfold eviction_protected in H.
  destruct (om_pin m); simpl in H; try discriminate.
  all: destruct (Nat.ltb 0 (om_ref_count m)) eqn:Hrc; simpl in H;
       try discriminate.
  all: apply Nat.ltb_ge in Hrc; lia.
Qed.

(** Evictable implies COMPLETE status. *)
Theorem evictable_is_complete : forall m,
  eviction_protected m = false ->
  om_status m = RsComplete.
Proof.
  intros m H. unfold eviction_protected in H.
  destruct (om_pin m); simpl in H; try discriminate.
  all: destruct (Nat.ltb 0 (om_ref_count m)) eqn:Hrc; simpl in H;
       try discriminate.
  all: destruct (om_status m); simpl in H; try discriminate; reflexivity.
Qed.

(** Evictable implies not hard-pinned. *)
Theorem evictable_not_hard_pinned : forall m,
  eviction_protected m = false ->
  om_pin m <> HardPinned.
Proof.
  intros m H. unfold eviction_protected in H.
  destruct (om_pin m); simpl in H; try discriminate.
  all: intro Habs; discriminate.
Qed.

(** =====================================================================
    Section 4: SEGMENT-LEVEL REFCOUNT OPERATIONS
    ===================================================================== *)

(** Update a specific object's metadata in a segment. *)
Definition update_object_meta (seg : Segment) (oid : ObjectId)
    (f : ObjectMeta -> ObjectMeta) : Segment :=
  mkSegment
    (seg_id seg)
    (seg_status seg)
    (seg_capacity seg)
    (seg_used seg)
    (map (fun m => if Nat.eqb (om_id m) oid then f m else m) (seg_objects seg)).

(** Increment refcount of a specific object in segment. *)
Definition inc_segment_refcnt (seg : Segment) (oid : ObjectId) : Segment :=
  update_object_meta seg oid inc_refcnt.

(** Decrement refcount of a specific object in segment. *)
Definition dec_segment_refcnt (seg : Segment) (oid : ObjectId) : Segment :=
  update_object_meta seg oid dec_refcnt.

(** update_object_meta preserves segment status. *)
Lemma update_preserves_status : forall seg oid f,
  seg_status (update_object_meta seg oid f) = seg_status seg.
Proof. intros. reflexivity. Qed.

(** update_object_meta preserves segment capacity. *)
Lemma update_preserves_capacity : forall seg oid f,
  seg_capacity (update_object_meta seg oid f) = seg_capacity seg.
Proof. intros. reflexivity. Qed.

(** update_object_meta preserves segment used space. *)
Lemma update_preserves_used : forall seg oid f,
  seg_used (update_object_meta seg oid f) = seg_used seg.
Proof. intros. reflexivity. Qed.

(** update_object_meta preserves object count. *)
Lemma update_preserves_objects_length : forall seg oid f,
  length (seg_objects (update_object_meta seg oid f)) =
  length (seg_objects seg).
Proof.
  intros. simpl. apply map_length.
Qed.

(** update_object_meta preserves IDs when f preserves IDs. *)
Lemma update_preserves_ids : forall seg oid f,
  (forall m, om_id (f m) = om_id m) ->
  map om_id (seg_objects (update_object_meta seg oid f)) =
  map om_id (seg_objects seg).
Proof.
  intros seg oid f Hpres. simpl.
  rewrite map_map. apply map_ext.
  intros m. destruct (Nat.eqb (om_id m) oid); auto.
Qed.

(** Finding an object after update_object_meta gives f(original). *)
Lemma find_after_update : forall objs oid f m,
  find_object_in objs oid = Some m ->
  (forall x, om_id (f x) = om_id x) ->
  find_object_in
    (map (fun x => if Nat.eqb (om_id x) oid then f x else x) objs) oid
    = Some (f m).
Proof.
  intros objs oid f m Hfind Hpres.
  induction objs as [| h rest IH].
  - simpl in Hfind. discriminate.
  - simpl in *. destruct (Nat.eqb (om_id h) oid) eqn:Heq.
    + inversion Hfind; subst. simpl. rewrite Hpres. rewrite Heq. reflexivity.
    + simpl. rewrite Heq. exact (IH Hfind).
Qed.

(** After inc_segment_refcnt, finding the object gives positive refcount. *)
Lemma inc_segment_refcnt_protects : forall seg oid m,
  find_object seg oid = Some m ->
  NoDup (map om_id (seg_objects seg)) ->
  exists m',
    find_object (inc_segment_refcnt seg oid) oid = Some m' /\
    om_ref_count m' > 0 /\
    eviction_protected m' = true.
Proof.
  intros seg oid m Hfind Hnd.
  exists (inc_refcnt m). split; [| split].
  - unfold find_object, inc_segment_refcnt, update_object_meta. simpl.
    apply find_after_update.
    + exact Hfind.
    + exact inc_preserves_id.
  - apply inc_refcnt_positive.
  - apply inc_protects.
Qed.

(** =====================================================================
    Section 5: LIVENESS AND PAIRING
    ===================================================================== *)

(** update_object_meta preserves all_objects_live when f preserves
    non-terminal status. *)
Lemma update_preserves_live : forall seg oid f,
  all_objects_live seg ->
  (forall m, replica_terminal (om_status m) = false ->
             replica_terminal (om_status (f m)) = false) ->
  all_objects_live (update_object_meta seg oid f).
Proof.
  intros seg oid f Hlive Hpres.
  unfold all_objects_live in *. simpl.
  rewrite Forall_forall. intros x Hin.
  apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
  rewrite Forall_forall in Hlive.
  destruct (Nat.eqb (om_id y) oid); subst x.
  - apply Hpres. exact (Hlive y Hiny).
  - exact (Hlive y Hiny).
Qed.

(** inc_refcnt preserves replica terminal status. *)
Lemma inc_preserves_terminal : forall m,
  replica_terminal (om_status (inc_refcnt m)) = replica_terminal (om_status m).
Proof. intros. reflexivity. Qed.

(** dec_refcnt preserves replica terminal status. *)
Lemma dec_preserves_terminal : forall m,
  replica_terminal (om_status (dec_refcnt m)) = replica_terminal (om_status m).
Proof. intros. reflexivity. Qed.

(** inc_refcnt preserves status. *)
Lemma inc_preserves_status : forall m,
  om_status (inc_refcnt m) = om_status m.
Proof. intros. reflexivity. Qed.

(** dec_refcnt preserves status. *)
Lemma dec_preserves_status : forall m,
  om_status (dec_refcnt m) = om_status m.
Proof. intros. reflexivity. Qed.
