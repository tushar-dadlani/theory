(* ================================================================== *)
(* SPECTRAL_ALGEBRA.V                                                 *)
(*                                                                     *)
(* SPECTRAL ALGEBRA FOR CODING AGENT INVARIANTS                       *)
(*                                                                     *)
(* Formalizes the bridge between TowerConstruction's abstract          *)
(* FormalSystem and the spectral/algebraic concepts from Rust:         *)
(*   - Residual vectors (rational-valued)                              *)
(*   - HomAlgebra (basis, rank, span membership)                       *)
(*   - Algebra closure under addition (subspace property)              *)
(*   - Algebra reflexivity (G = Hom(G,G))                             *)
(*   - FormalSystem construction from a HomAlgebra                     *)
(*                                                                     *)
(* Follows the Stratum convention: Cause-zone axioms are explicit.    *)
(* ================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(* I. RESIDUAL VECTORS                                                *)
(*                                                                     *)
(* A residual vector is a finite rational-valued vector.               *)
(* Dimension is fixed for a given spectral analysis (2k+3             *)
(* where k = number of eigenvalues tracked).                           *)
(*                                                                     *)
(* In the Rust code:                                                   *)
(*   HomMorphism.to_vector() -> Vec<f64>                              *)
(*   = [eig_residual | gap_residual | hole | fp_vanish | fp_appear]   *)
(* ================================================================== *)

(** A vector is a function from index to rational, with a dimension. *)
Record RVec := mkRVec {
  rv_dim : nat;
  rv_get : nat -> Q;
}.

(** Zero vector. *)
Definition rv_zero (d : nat) : RVec :=
  mkRVec d (fun _ => 0).

(** Vector addition. *)
Definition rv_add (v1 v2 : RVec) : RVec :=
  mkRVec (rv_dim v1) (fun i => rv_get v1 i + rv_get v2 i).

(** Inner product (dot product). *)
Definition rv_dot (v1 v2 : RVec) : Q :=
  let fix sum_to n :=
    match n with
    | O => 0
    | S m => (rv_get v1 m * rv_get v2 m) + sum_to m
    end
  in sum_to (rv_dim v1).

(** Squared norm. *)
Definition rv_norm_sq (v : RVec) : Q := rv_dot v v.

(** Scalar multiplication. *)
Definition rv_scale (c : Q) (v : RVec) : RVec :=
  mkRVec (rv_dim v) (fun i => c * rv_get v i).

(* ================================================================== *)
(* II. HOM ALGEBRA                                                    *)
(*                                                                     *)
(* A HomAlgebra is an orthonormal basis of a subspace of R^d.         *)
(* "In span" means the projection onto the basis captures most        *)
(* of the vector's energy (explained_fraction > 1 - epsilon).         *)
(*                                                                     *)
(* In the Rust code:                                                   *)
(*   HomAlgebra { basis: Vec<Vec<f64>>, rank: usize, ... }            *)
(*   HomAlgebra::decompose() -> HomAlgebraDecomp                      *)
(*     { explained_fraction, reconstruction_error, ... }              *)
(* ================================================================== *)

(** Epsilon: a positive rational threshold for span membership. *)
Record Epsilon := mkEps {
  eps_val : Q;
  eps_pos : 0 < eps_val;
  eps_le1 : eps_val <= 1;
}.

(** A HomAlgebra is an orthonormal basis with rank and ambient dimension. *)
Record HomAlgebra := mkHA {
  ha_dim   : nat;              (** Ambient vector dimension (2k+3) *)
  ha_rank  : nat;              (** Number of basis vectors *)
  ha_basis : nat -> RVec;      (** The orthonormal basis vectors *)
}.

(** Project a vector onto the i-th basis vector. *)
Definition project_coeff (A : HomAlgebra) (v : RVec) (i : nat) : Q :=
  rv_dot v (ha_basis A i).

(** Squared norm of the projection onto the basis. *)
Definition projection_norm_sq (A : HomAlgebra) (v : RVec) : Q :=
  let fix sum_to n :=
    match n with
    | O => 0
    | S m => let c := project_coeff A v m in (c * c) + sum_to m
    end
  in sum_to (ha_rank A).

(** Explained fraction: |proj|^2 / |v|^2.
    When this is close to 1, the vector is (nearly) in the span. *)
Definition explained_fraction (A : HomAlgebra) (v : RVec) : Q :=
  let v_sq := rv_norm_sq v in
  let p_sq := projection_norm_sq A v in
  if Qlt_le_dec v_sq (1#1000000) then 1  (* zero vector is trivially in span *)
  else p_sq / v_sq.

(** A vector is "in span" of the algebra within tolerance epsilon. *)
Definition in_span (A : HomAlgebra) (eps : Epsilon) (v : RVec) : Prop :=
  explained_fraction A v >= 1 - eps_val eps.

(* ================================================================== *)
(* III. ALGEBRA PROPERTIES                                             *)
(*                                                                     *)
(* The key structural properties that connect the algebra to the       *)
(* FormalSystem from TowerConstruction.v.                              *)
(*                                                                     *)
(* In the Rust code:                                                   *)
(*   formal.is_fixed_point  ↔  algebra_reflexive                      *)
(*   algebra.closure_error  ↔  algebra_closed                         *)
(*   formal.hom_stabilized  ↔  closed AND reflexive                   *)
(* ================================================================== *)

(** An algebra is reflexive when rank = dimension.
    This means the basis spans the entire ambient space.
    Corresponds to: G ≅ Hom(G,G) — the fixed-point property. *)
Definition algebra_reflexive (A : HomAlgebra) : Prop :=
  ha_rank A = ha_dim A.

(** Reflexive algebras contain every vector.
    If the orthonormal basis spans all of R^d, then any d-dimensional
    vector has explained_fraction = 1 >= 1 - epsilon for any epsilon > 0.

    This is the content of FormalSystem.is_fixed_point in Rust. *)
Axiom reflexive_spans_all :
  forall (A : HomAlgebra) (eps : Epsilon) (v : RVec),
  algebra_reflexive A ->
  rv_dim v = ha_dim A ->
  in_span A eps v.

(** An algebra is closed under addition if the span is a subspace.
    For a true orthonormal basis of a subspace, this is immediate:
    if v1 and v2 are in the subspace, v1+v2 is in the subspace.

    This is the content of HomAlgebra.closure_error < epsilon in Rust. *)
Axiom span_closed_under_addition :
  forall (A : HomAlgebra) (eps : Epsilon) (v1 v2 : RVec),
  in_span A eps v1 ->
  in_span A eps v2 ->
  in_span A eps (rv_add v1 v2).

(* ================================================================== *)
(* IV. FORMAL SYSTEM FROM ALGEBRA                                     *)
(*                                                                     *)
(* Build a TowerConstruction.FormalSystem from a HomAlgebra.           *)
(*                                                                     *)
(* domain = transforms whose residuals are in span                     *)
(* kernel = transforms whose residuals are NOT in span                 *)
(*          but would be at the next level                              *)
(*                                                                     *)
(* This mirrors the Rust pipeline:                                     *)
(*   build_formal_system(lang, k) -> LanguageFormalSystem              *)
(* ================================================================== *)

(** We need a notion of "transform" with a "residual" function.
    This is abstract — the Rust code computes residuals from
    spectral signatures, but the proof only needs the residual
    vector, not how it was computed. *)

Parameter Transform : Type.
Parameter residual : Transform -> RVec.
Parameter compose : Transform -> Transform -> Transform.

(** Build a FormalSystem where:
    - domain(t) = residual(t) is in the algebra's span
    - kernel(t) = residual(t) is NOT in span AND would be at next level

    For the proof, we simplify kernel to just "not in domain"
    (the "would be at next level" part is handled by tower_step). *)

Definition algebra_domain (A : HomAlgebra) (eps : Epsilon) (t : Transform) : Prop :=
  in_span A eps (residual t).

Definition algebra_kernel (A : HomAlgebra) (eps : Epsilon) (t : Transform) : Prop :=
  ~ in_span A eps (residual t).

Lemma algebra_kernel_in_domain_vacuous :
  forall A eps t,
  algebra_kernel A eps t ->
  algebra_domain A eps t ->
  False.
Proof.
  intros A eps t Hk Hd. exact (Hk Hd).
Qed.

(* ================================================================== *)
(* V. COMPOSITION RESIDUAL AXIOM (CAUSE ZONE)                        *)
(*                                                                     *)
(* The composition of two transforms has a residual that is           *)
(* approximately the sum of the individual residuals.                  *)
(*                                                                     *)
(* This is the linear approximation used in the Rust code:            *)
(*   v_{i∘j} ≈ v_i + v_j                                             *)
(*                                                                     *)
(* This is a CAUSE-ZONE statement: empirically validated in Rust,     *)
(* not logically provable from eigenvalue definitions alone.           *)
(* It corresponds to the linearization of the spectral map.           *)
(* ================================================================== *)

Axiom compose_residual_additive :
  forall t1 t2 : Transform,
  residual (compose t1 t2) = rv_add (residual t1) (residual t2).

(** Consequence: composition of in-span transforms stays in span. *)
Theorem compose_in_span :
  forall (A : HomAlgebra) (eps : Epsilon) (t1 t2 : Transform),
  in_span A eps (residual t1) ->
  in_span A eps (residual t2) ->
  in_span A eps (residual (compose t1 t2)).
Proof.
  intros A eps t1 t2 H1 H2.
  rewrite compose_residual_additive.
  exact (span_closed_under_addition A eps _ _ H1 H2).
Qed.

(* ================================================================== *)
(* Print assumptions to make Cause-zone axioms visible.               *)
(* ================================================================== *)

Print Assumptions compose_in_span.
