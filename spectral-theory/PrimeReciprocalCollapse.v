(* ================================================================= *)
(*  PrimeReciprocalCollapse.v  —  (1/prime)^inf vs (1/primorial)^inf.    *)
(*                                                                    *)
(*  The two reciprocal collapses of the prime notions of infinity:      *)
(*                                                                    *)
(*   DEPTH  (1/prime)^inf     :  (1/p)^n -> 0   (one prime, exponent n). *)
(*   BREADTH (1/primorial)^inf:  1/primorial k -> 0 (prime-count k).     *)
(*                                                                    *)
(*  They meet through the identity                                      *)
(*    1/primorial k = prod_{i<k} 1/p_i = prod_{i<k} (1/p_i)^1,          *)
(*  i.e. breadth is the product of the n=1 rungs of the primes' depth    *)
(*  ladders.  And breadth is dominated by (indeed far outruns) the       *)
(*  first prime's depth collapse:                                        *)
(*    1/primorial k <= (1/2)^k.                                          *)
(*                                                                    *)
(*  So (1/primorial)^inf collapses at least as fast as (1/2)^inf (the    *)
(*  reciprocal of the first prime's tower), and both -> 0.  This is the   *)
(*  breadth-axis of the Euler product zeta(s)=prod_p sum_n p^{-ns}, of    *)
(*  which (1/prime)^inf is the depth-axis (the inner geometric sum).      *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import PrimeInfinities CountTwoCollapse.
Open Scope R_scope.

Section Dual.
Variable P : nat -> R.                 (* abstract prime enumeration *)
Hypothesis HP : forall i, 2 <= P i.    (* each prime is >= 2 *)

Fixpoint primorial (k : nat) : R :=
  match k with 0 => 1 | S k' => primorial k' * P k' end.

Lemma primorial_pos : forall k, 0 < primorial k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rmult_lt_0_compat; [ exact IH | pose proof (HP k); lra ].
Qed.

(* BREADTH is multiplicative across primes: the reciprocal folds in 1/P k *)
Lemma inv_primorial_rec : forall k, / primorial (S k) = / primorial k * / P k.
Proof. intro k. cbn [primorial]. rewrite Rinv_mult. reflexivity. Qed.

Lemma primorial_ge_pow2 : forall k, 2 ^ k <= primorial k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rle_trans with (2 ^ k * 2).
  - lra.
  - apply Rmult_le_compat;
      [ apply pow_le; lra | lra | exact IH | apply HP ].
Qed.

(* BREADTH is dominated by the first prime's DEPTH collapse (1/2)^k *)
Theorem inv_primorial_le_pow2 : forall k, / primorial k <= (/ 2) ^ k.
Proof.
  intro k. rewrite <- Rinv_pow by lra.
  apply Rinv_le_contravar; [ apply pow_lt; lra | apply primorial_ge_pow2 ].
Qed.

(* (1/primorial)^inf: the breadth collapse to 0 *)
Theorem inv_primorial_cv0 : Un_cv (fun k => / primorial k) 0.
Proof.
  intros eps Heps. destruct (inv2_pow_cv0 eps Heps) as [N HN]. exists N. intros n Hn.
  specialize (HN n Hn). unfold R_dist in *. rewrite Rminus_0_r in *.
  assert (H1 : 0 <= / primorial n) by (apply Rlt_le, Rinv_0_lt_compat, primorial_pos).
  assert (H2 : / primorial n <= (/ 2) ^ n) by apply inv_primorial_le_pow2.
  assert (H3 : 0 <= (/ 2) ^ n) by (apply pow_le; lra).
  rewrite Rabs_right in HN by (apply Rle_ge; exact H3).
  rewrite Rabs_right by (apply Rle_ge; exact H1). lra.
Qed.

(* ===== depth vs breadth, bundled ===== *)
Theorem prime_vs_primorial_reciprocal :
  (forall p, 2 <= p -> Un_cv (fun n => (/ p) ^ n) 0)         (* (1/prime)^inf: DEPTH, one prime *)
  /\ (forall k, / primorial (S k) = / primorial k * / P k)   (* BREADTH multiplicative across primes *)
  /\ (forall k, / primorial k <= (/ 2) ^ k)                 (* breadth dominated by first prime's depth *)
  /\ Un_cv (fun k => / primorial k) 0.                      (* (1/primorial)^inf: BREADTH collapse *)
Proof.
  split; [ intros p Hp; apply inv_prime_pow_cv0; exact Hp | ].
  split; [ apply inv_primorial_rec | ].
  split; [ apply inv_primorial_le_pow2 | apply inv_primorial_cv0 ].
Qed.

End Dual.

Print Assumptions inv_primorial_le_pow2.
Print Assumptions prime_vs_primorial_reciprocal.
