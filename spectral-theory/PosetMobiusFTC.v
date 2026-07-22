(* ================================================================= *)
(*  PosetMobiusFTC.v                                                  *)
(*                                                                    *)
(*  The POSET MOBIUS INVERSION = discrete FUNDAMENTAL THEOREM OF       *)
(*  CALCULUS on the divisibility lattice, over Q, axiom-free.          *)
(*                                                                    *)
(*  On the single-prime divisibility lattice -- the divisors of p^m,   *)
(*  which form a CHAIN [0..m] under divisibility (indexed by the        *)
(*  exponent) -- the two adjoint operations are:                       *)
(*                                                                    *)
(*    zeta transform    Z[f](n) = sum_{j=0}^{n} f(j)   (divisor sum,    *)
(*                                            = discrete INTEGRATION)   *)
(*    Mobius transform  M[g](n) = g(n) - g(n-1)        (backward diff., *)
(*                                            = discrete DIFFERENTIATION)*)
(*                                                                    *)
(*  They are mutually inverse -- the discrete Fundamental Theorem of    *)
(*  Calculus, which IS Mobius inversion on the chain:                  *)
(*                                                                    *)
(*    ftc_1 : M[Z[f]] = f      (differentiate the integral)            *)
(*    ftc_2 : Z[M[g]] = g      (integrate the derivative; telescoping)  *)
(*                                                                    *)
(*  and M is exactly the poset-Mobius convolution  sum_{d|n} mu(n/d)    *)
(*  g(d)  (mobius_t_is_mu_conv, via VonMangoldt.dconv / dconv_mu, with   *)
(*  mu the divisibility Mobius function = MobiusReciprocal.mu_pp).      *)
(*                                                                    *)
(*  This is the poset Mobius inversion on the single-prime chain; the   *)
(*  full divisibility lattice (FreeDivMeet) is a product of chains, so   *)
(*  the inversion extends coordinatewise.  The fully general N+         *)
(*  divisor-sum form needs divisor enumeration and is deferred.         *)
(* ================================================================= *)

Require Import PrimonGas.
Require Import VonMangoldt.
From Stdlib Require Import QArith Lqa ZArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  1.  THE TWO TRANSFORMS                                            *)
(* ================================================================= *)

(* zeta transform: the divisor sum on the chain = discrete integration *)
Definition zeta_t (f : nat -> Q) (n : nat) : Q := qsum (map f (seq 0 (S n))).

(* Mobius transform: the backward difference = discrete differentiation *)
Definition mobius_t (g : nat -> Q) (n : nat) : Q :=
  match n with O => g O | S m => g (S m) - g m end.

Lemma zeta_t_rec : forall f n, zeta_t f (S n) == zeta_t f n + f (S n).
Proof.
  intros f n; unfold zeta_t.
  rewrite seq_S, map_app, qsum_app; simpl; ring.
Qed.

(* ================================================================= *)
(*  2.  THE DISCRETE FUNDAMENTAL THEOREM OF CALCULUS                  *)
(* ================================================================= *)

(* differentiate the integral: M[Z[f]] = f *)
Theorem ftc_1 : forall f n, mobius_t (zeta_t f) n == f n.
Proof.
  intros f [|m].
  - cbn [mobius_t]; unfold zeta_t; simpl; ring.
  - cbn [mobius_t]; rewrite zeta_t_rec; ring.
Qed.

(* integrate the derivative: Z[M[g]] = g  (telescoping) *)
Theorem ftc_2 : forall g n, zeta_t (mobius_t g) n == g n.
Proof.
  intros g; induction n as [|m IH].
  - unfold zeta_t; simpl; cbn [mobius_t]; ring.
  - rewrite zeta_t_rec, IH; cbn [mobius_t]; ring.
Qed.

(* ================================================================= *)
(*  3.  THE MOBIUS TRANSFORM IS THE POSET-MOBIUS CONVOLUTION          *)
(* ================================================================= *)

(* M[g](n) = sum_{j=0}^{n} mu(n-j) g(j) = sum_{d|p^n} mu(p^n/d) g(d):    *)
(* the backward difference IS the divisibility-Mobius convolution.       *)
Theorem mobius_t_is_mu_conv : forall g n, (1 <= n)%nat ->
  mobius_t g n == dconv muf g n.
Proof.
  intros g [|m] Hn; [ lia | ].
  cbn [mobius_t]; rewrite dconv_mu by lia.
  replace (S m - 1)%nat with m by lia; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — axiom-free over Q                               *)
(* ----------------------------------------------------------------- *)

Theorem poset_mobius_ftc :
  (* differentiate the integral *)
  (forall f n, mobius_t (zeta_t f) n == f n)
  (* integrate the derivative (telescoping) *)
  /\ (forall g n, zeta_t (mobius_t g) n == g n)
  (* the Mobius transform is the poset-Mobius convolution *)
  /\ (forall g n, (1 <= n)%nat -> mobius_t g n == dconv muf g n).
Proof.
  split; [ exact ftc_1 | ].
  split; [ exact ftc_2 | exact mobius_t_is_mu_conv ].
Qed.

Print Assumptions poset_mobius_ftc.

(* ================================================================= *)
(*  END PosetMobiusFTC.v                                              *)
(*  Discrete FTC / Mobius inversion on the divisibility chain: the      *)
(*  divisor-sum (zeta, integration) and backward-difference (Mobius,    *)
(*  differentiation) transforms are mutually inverse, and the Mobius     *)
(*  transform is the poset-Mobius convolution.                          *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
