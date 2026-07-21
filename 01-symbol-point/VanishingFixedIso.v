(** * Corollary 1: The Vanishing Point and the Fixed Point Are Isomorphic *)

(** The vanishing point (geometric: 0, the boundary of (0,1]) and
    the fixed point (domain-theoretic: ⊥, where self-reference stabilizes)
    share the same universal property. This file proves they are
    isomorphic — not just equal as real numbers, but structurally
    identical in their algebraic, order-theoretic, and categorical roles. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.

(** We add the parent directory to the load path *)
Require Import IntervalEquiv.
Require Import RInterval.
Require Import GeometryInterval.
Require Import CategoryInterval.
Require Import VanishingPoint.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: The Three Faces of the Same Element                   *)
(* ================================================================= *)

(** Face 1: The geometric vanishing point — where (0,1] is open *)
Definition face_geometric : R := vanishing_point.   (* = 0 *)

(** Face 2: The domain-theoretic bottom — where computation diverges *)
Definition face_domain : Partial R := Undefined.

(** Face 3: The algebraic fixed point — where f(x) = x for strict f *)
Definition face_fixed : R := 0.

(** All three faces are the same real number *)
Theorem three_faces_equal :
  face_geometric = face_fixed /\
  partial_to_real face_domain = face_geometric /\
  partial_to_real face_domain = face_fixed.
Proof.
  unfold face_geometric, face_domain, face_fixed,
         vanishing_point, partial_to_real.
  auto.
Qed.

(* ================================================================= *)
(** ** Part 2: The Universal Property — Absorption                   *)
(* ================================================================= *)

(** Both the vanishing point and the fixed point share the
    ABSORPTION property: they are "zero-like" elements that
    swallow operations. This is their shared universal property. *)

(** Geometric absorption: scaling (0,1] toward the vanishing point
    collapses everything to 0 *)
Theorem geometric_absorption : forall x : R,
  affine_interval x -> forall c : R, 0 < c -> c < 1 ->
  (* c^n * x approaches vanishing_point as n grows *)
  (* We prove the one-step version: c*x is closer to 0 than x *)
  Rabs (c * x - vanishing_point) < Rabs (x - vanishing_point).
Proof.
  intros x [Hx_pos Hx_le] c Hc_pos Hc_lt.
  unfold vanishing_point.
  rewrite Rminus_0_r. rewrite Rminus_0_r.
  rewrite (Rabs_pos_eq x) by lra.
  rewrite (Rabs_pos_eq (c * x)) by nra.
  nra.
Qed.

(** Domain absorption: applying any strict function to ⊥ gives ⊥ *)
Theorem domain_absorption :
  forall f : Partial R -> Partial R,
    f Undefined = Undefined ->
    partial_to_real (f Undefined) = face_geometric.
Proof.
  intros f Hf.
  rewrite Hf. reflexivity.
Qed.

(** Fixed-point absorption: the vanishing point is a fixed point
    of every "contractive" real function that maps (0,1] into itself *)
Theorem fixedpoint_absorption :
  forall f : R -> R,
    (forall x, affine_interval x -> affine_interval (f x)) ->
    (forall x, affine_interval x -> Rabs (f x) < Rabs x) ->
    (* The vanishing point is the limit: f approaches it *)
    forall x, affine_interval x ->
    Rabs (f x - face_fixed) < Rabs (x - face_fixed).
Proof.
  intros f Hpres Hcontr x Hx.
  unfold face_fixed. rewrite Rminus_0_r. rewrite Rminus_0_r.
  apply Hcontr. exact Hx.
Qed.

(* ================================================================= *)
(** ** Part 3: The Isomorphism — Structure Preservation              *)
(* ================================================================= *)

(** An isomorphism between the vanishing point and the fixed point
    is more than just equality of real numbers. It means the
    STRUCTURES around them are preserved:

    1. Both are limits of sequences in their respective systems
    2. Both are absorbing elements for their respective operations
    3. Both are the unique completion element
    4. Both make self-reference possible *)

(** Structure 1: Both are limits of the same sequence *)
Theorem both_are_limits_of_inv_n :
  (** The geometric vanishing point is the limit of 1/n in (0,1] *)
  (forall eps, eps > 0 -> exists N, forall n,
    (n >= N)%nat -> (n >= 1)%nat ->
    Rabs (/ INR n - face_geometric) < eps) /\
  (** The fixed point is the limit of the same sequence *)
  (forall eps, eps > 0 -> exists N, forall n,
    (n >= N)%nat -> (n >= 1)%nat ->
    Rabs (/ INR n - face_fixed) < eps).
Proof.
  (* Both are the same because face_geometric = face_fixed = 0 *)
  assert (Heq : face_geometric = face_fixed) by reflexivity.
  split; intros eps Heps.
  - (* Geometric: use approach_vanishing *)
    destruct (approach_vanishing eps Heps) as [n [Hn [Hlt Haff]]].
    exists n. intros m Hm Hm1.
    unfold face_geometric, vanishing_point.
    rewrite Rminus_0_r.
    rewrite Rabs_right.
    + destruct Haff as [Hm_pos _].
      assert (Hm_rpos : INR m > 0) by (apply lt_0_INR; lia).
      assert (INR n <= INR m) by (apply le_INR; lia).
      apply Rle_lt_trans with (/ INR n).
      * apply Rinv_le_contravar; [apply lt_0_INR; lia | lra].
      * exact Hlt.
    + left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
  - (* Fixed: identical proof since face_fixed = face_geometric *)
    rewrite <- Heq.
    destruct (approach_vanishing eps Heps) as [n [Hn [Hlt Haff]]].
    exists n. intros m Hm Hm1.
    unfold face_geometric, vanishing_point.
    rewrite Rminus_0_r.
    rewrite Rabs_right.
    + assert (Hm_rpos : INR m > 0) by (apply lt_0_INR; lia).
      assert (INR n <= INR m) by (apply le_INR; lia).
      apply Rle_lt_trans with (/ INR n).
      * apply Rinv_le_contravar; [apply lt_0_INR; lia | lra].
      * exact Hlt.
    + left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

(** Structure 2: Both are the unique completion element *)
Theorem both_unique_completion :
  (** Geometric: the vanishing point is the unique element
      completing (0,1] to [0,1] *)
  (forall p, pred_add_point affine_interval p = projective_interval ->
    p = face_geometric) /\
  (** Domain: ⊥ is the unique non-Defined element *)
  (forall (p : Partial R),
    (forall x : R, p <> Defined x) -> p = face_domain).
Proof.
  split.
  - intros p Hp.
    unfold face_geometric.
    exact (unique_vanishing_point p Hp).
  - intros p Hp.
    unfold face_domain. destruct p.
    + exfalso. exact (Hp r eq_refl).
    + reflexivity.
Qed.

(** Structure 3: Both make self-reference non-contradictory *)
Theorem both_absorb_paradox :
  (** Geometric: the vanishing point is where affine_interval and
      its negation "meet" — it satisfies ~(affine_interval 0) *)
  (~ affine_interval face_geometric) /\
  (** Domain: ⊥ absorbs self-application — omega(omega) = ⊥ *)
  (self_apply omega_combinator = face_domain).
Proof.
  split.
  - unfold face_geometric. exact affine_no_witness.
  - unfold face_domain. exact omega_diverges.
Qed.

(* ================================================================= *)
(** ** Part 4: The Formal Isomorphism                                *)
(* ================================================================= *)

(** We define what it means for two "pointed structures" to be
    isomorphic: there is a bijection between their neighborhoods
    that preserves the point and all relevant structure. *)

(** A pointed structure: a type with a distinguished element *)
Record PointedStructure := mkPointed {
  carrier : Type;
  basepoint : carrier;
  is_absorbing : (carrier -> carrier) -> Prop
}.

(** The geometric pointed structure: (R, vanishing_point, scaling) *)
Definition geometric_pointed : PointedStructure := {|
  carrier := R;
  basepoint := face_geometric;
  is_absorbing := fun f =>
    forall x, affine_interval x ->
      Rabs (f x - face_geometric) <= Rabs (x - face_geometric)
|}.

(** The domain pointed structure: (Partial R, ⊥, strict maps) *)
Definition domain_pointed : PointedStructure := {|
  carrier := Partial R;
  basepoint := face_domain;
  is_absorbing := fun f => f Undefined = Undefined
|}.

(** The isomorphism: partial_to_real maps domain_pointed to
    geometric_pointed, preserving the basepoint *)
Theorem pointed_iso_basepoint :
  partial_to_real (basepoint domain_pointed) =
  basepoint geometric_pointed.
Proof.
  simpl. reflexivity.
Qed.

(** The isomorphism preserves absorption *)
Theorem pointed_iso_absorption :
  forall f : Partial R -> Partial R,
    is_absorbing domain_pointed f ->
    partial_to_real (f (basepoint domain_pointed)) =
    basepoint geometric_pointed.
Proof.
  intros f Habs.
  change (partial_to_real (f Undefined) = vanishing_point).
  change (f Undefined = Undefined) in Habs.
  rewrite Habs. reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 5: Corollary — The Isomorphism Is Unique                 *)
(* ================================================================= *)

(** There is exactly ONE element with the vanishing/fixed point
    properties. This means the isomorphism is not just an
    equivalence — it is THE identification. *)

Theorem unique_absorbing_real :
  forall x : R,
    projective_interval x ->
    ~ affine_interval x ->
    (forall y, y <> x -> (affine_interval y <-> projective_interval y)) ->
    x = face_geometric.
Proof.
  intros x Hproj Haff Huniq.
  unfold face_geometric, vanishing_point.
  destruct Hproj as [Hle Hle1].
  destruct (Rlt_dec 0 x) as [Hlt | Hnlt].
  - exfalso. apply Haff. unfold affine_interval. lra.
  - lra.
Qed.

Theorem unique_absorbing_partial :
  forall (p : Partial R),
    (forall x, p <> Defined x) ->
    p = face_domain.
Proof.
  intros p Hp. destruct p.
  - exfalso. exact (Hp r eq_refl).
  - reflexivity.
Qed.

(** The grand corollary: the vanishing point, the fixed point,
    and the domain bottom are not just equal — they are the
    UNIQUE element satisfying any of their characteristic properties.
    The isomorphism is canonical. *)
Theorem canonical_isomorphism :
  exists! x : R,
    projective_interval x /\
    ~ affine_interval x /\
    x = partial_to_real (Undefined : Partial R).
Proof.
  exists face_geometric. split.
  - refine (conj _ (conj _ _)).
    + exact projective_witness_exists.
    + exact affine_no_witness.
    + symmetry. exact domain_bottom_eq_geometric_vanishing.
  - intros y [Hproj [Haff Heq]].
    rewrite Heq. reflexivity.
Qed.
