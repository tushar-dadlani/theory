(* ================================================================= *)
(*  ProductMobius.v                                                   *)
(*                                                                    *)
(*  GAP-FILL: lifting MobiusReciprocal and VonMangoldt to the 2-prime   *)
(*  PRODUCT lattice (divisors of p^a q^b), axiom-free over Q.          *)
(*                                                                    *)
(*  MOBIUS / RECIPROCAL SIDE.  The Mobius function is MULTIPLICATIVE:    *)
(*  mu(p^a q^b) = mu(p^a) mu(q^b).  So the 2D Mobius (reciprocal Euler)  *)
(*  series factors into the product of the two 1D series, and for K>=2   *)
(*  collapses to the product of reciprocal Euler factors:               *)
(*                                                                    *)
(*     sum_{a<K} sum_{b<K} mu(p^a) mu(q^b) x^a y^b  =  (1-x)(1-y).       *)
(*                                                                    *)
(*  VON MANGOLDT SIDE.  On the product lattice the von Mangoldt function *)
(*  is the 2D Mobius transform (M2, from ProductFTC) of the additive log *)
(*  Lsum(i,j) = i*Lp + j*Lq.  It is SUPPORTED ON THE PRIME POWERS (the    *)
(*  axes): it equals Lp on the p-axis, Lq on the q-axis, 0 at the origin, *)
(*  and -- crucially -- 0 on the INTERIOR (a,b >= 1), because p^a q^b     *)
(*  with a,b >= 1 is not a prime power.  vm2_interior_zero is that fact.  *)
(* ================================================================= *)

Require Import MobiusReciprocal.
Require Import ProductFTC.
Require Import PosetMobiusFTC.
Require Import PrimonGas.
From Stdlib Require Import QArith Lqa ZArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  1.  MOBIUS / RECIPROCAL ON THE PRODUCT                           *)
(* ================================================================= *)

(* a separable double sum factors into the product of the sums *)
Lemma double_sum_sep : forall (u v : nat -> Q) L1 L2,
  qsum (map (fun a => qsum (map (fun b => u a * v b) L2)) L1)
  == qsum (map u L1) * qsum (map v L2).
Proof.
  intros u v L1 L2.
  transitivity (qsum (map (fun a => u a * qsum (map v L2)) L1)).
  - apply qsum_map_ext; intro a; apply qsum_map_scale_l.
  - apply qsum_map_scale_r.
Qed.

(* the product Mobius function is multiplicative (definitional) *)
Definition mu2 (a b : nat) : Z := (mu_pp a * mu_pp b)%Z.

Lemma mu2_mult : forall a b, mu2 a b = (mu_pp a * mu_pp b)%Z.
Proof. reflexivity. Qed.

(* the 2D Mobius (reciprocal Euler) series, with separable summand *)
Definition museries2 (x y : Q) (K : nat) : Q :=
  qsum (map (fun a => qsum (map (fun b => muterm x a * muterm y b) (seq 0 K))) (seq 0 K)).

Lemma museries2_factor : forall x y K,
  museries2 x y K == museries x K * museries y K.
Proof. intros x y K; unfold museries2, museries; apply double_sum_sep. Qed.

(* for K >= 2 the 2D reciprocal series collapses to (1-x)(1-y):          *)
(* the product of two reciprocal Euler factors = 1/(zeta_p * zeta_q).    *)
Theorem mu2_reciprocal : forall x y n,
  museries2 x y (S (S n)) == (1 - x) * (1 - y).
Proof.
  intros x y n; rewrite museries2_factor.
  rewrite (museries_from2 x n), (museries_from2 y n); reflexivity.
Qed.

(* ================================================================= *)
(*  2.  VON MANGOLDT ON THE PRODUCT                                  *)
(* ================================================================= *)

Section VMProduct.

Variables Lp Lq : Q.   (* single-particle energies Lp = log p, Lq = log q *)

(* the additive log on the product lattice: log(p^i q^j) = i*Lp + j*Lq *)
Definition Lsum (i j : nat) : Q := inject_Z (Z.of_nat i) * Lp + inject_Z (Z.of_nat j) * Lq.

Lemma injSk : forall k, inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1.
Proof.
  intro k; replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
  rewrite inject_Z_plus; reflexivity.
Qed.

Lemma inj0 : inject_Z (Z.of_nat 0) == 0.
Proof. reflexivity. Qed.

(* origin: Lambda(1) = 0 *)
Theorem vm2_origin : M2 Lsum 0 0 == 0.
Proof.
  unfold M2, Lsum; cbn [mobius_t]; rewrite !inj0; ring.
Qed.

(* p-axis: Lambda(p^{m+1}) = log p = Lp *)
Theorem vm2_axis_p : forall m, M2 Lsum (S m) 0 == Lp.
Proof.
  intro m; unfold M2, Lsum; cbn [mobius_t]; rewrite !injSk, !inj0; ring.
Qed.

(* q-axis: Lambda(q^{n+1}) = log q = Lq *)
Theorem vm2_axis_q : forall n, M2 Lsum 0 (S n) == Lq.
Proof.
  intro n; unfold M2, Lsum; cbn [mobius_t]; rewrite !injSk, !inj0; ring.
Qed.

(* INTERIOR: Lambda(p^{m+1} q^{n+1}) = 0 -- von Mangoldt is supported     *)
(* only on prime powers, so it vanishes on genuine products.            *)
Theorem vm2_interior_zero : forall m n, M2 Lsum (S m) (S n) == 0.
Proof.
  intros m n; unfold M2, Lsum; cbn [mobius_t]; rewrite !injSk; ring.
Qed.

End VMProduct.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — Mobius/von Mangoldt on the product, axiom-free  *)
(* ----------------------------------------------------------------- *)

Theorem product_mobius :
  (* Mobius is multiplicative on the product lattice *)
  (forall a b, mu2 a b = (mu_pp a * mu_pp b)%Z)
  (* the 2D reciprocal series factors ... *)
  /\ (forall x y K, museries2 x y K == museries x K * museries y K)
  (* ... and collapses to the product of reciprocal Euler factors *)
  /\ (forall x y n, museries2 x y (S (S n)) == (1 - x) * (1 - y))
  (* von Mangoldt on the product: supported on the axes (prime powers) *)
  /\ (forall Lp Lq m, M2 (Lsum Lp Lq) (S m) 0 == Lp)
  /\ (forall Lp Lq n, M2 (Lsum Lp Lq) 0 (S n) == Lq)
  (* and ZERO on the interior a,b >= 1 (p^a q^b is not a prime power) *)
  /\ (forall Lp Lq m n, M2 (Lsum Lp Lq) (S m) (S n) == 0).
Proof.
  split; [ exact mu2_mult | ].
  split; [ exact museries2_factor | ].
  split; [ exact mu2_reciprocal | ].
  split; [ exact vm2_axis_p | ].
  split; [ exact vm2_axis_q | exact vm2_interior_zero ].
Qed.

Print Assumptions product_mobius.

(* ================================================================= *)
(*  END ProductMobius.v                                               *)
(*  Mobius multiplicative on the product (2D reciprocal series ->       *)
(*  (1-x)(1-y)); von Mangoldt = M2 of the additive log, supported on     *)
(*  the axes (Lp, Lq) and ZERO on the interior.  Closed under global ctx.*)
(* ================================================================= *)
