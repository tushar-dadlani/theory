(* ================================================================= *)
(*  PrimeInfinities.v  —  prime^inf and primorial^inf, reconciled with   *)
(*  the additive index 1+1+...+1.                                       *)
(*                                                                    *)
(*  The count-2 thread (CountTwoCollapse.v) built 2^inf (2^n -> +inf)     *)
(*  and its collapse (c/2^n -> 0).  Here we generalize to the THREE       *)
(*  prime notions of infinity and show they are all indexed by the same  *)
(*  additive count 1+1+...+1:                                           *)
(*                                                                    *)
(*   (A) prime^inf  :  for any base p >= 2 (2 = the first prime being    *)
(*        the smallest such base),  p^n -> +inf,  c/p^n -> 0.            *)
(*   (B) the reconciliation  :  the ADDITIVE sum over the exponent-count  *)
(*        k of the prime fugacity (1/p)^k equals the per-prime resolvent  *)
(*        Sum_k (1/p)^k = p/(p-1)  (the geometric Euler factor at s=1) -- *)
(*        additive-over-count <-> multiplicative-per-prime.              *)
(*   (C) primorial^inf  :  primorial k = prod_{i<k} p_i -> +inf, indexed  *)
(*        by the prime-COUNT k (again 1+1+...+1).                         *)
(*   (D) the additive index itself  :  1+1+...+1 (k ones) = INR k, and    *)
(*        (1+1+...+1) -> +inf; this k is the exponent in p^n AND the      *)
(*        prime-count in the primorial.                                  *)
(*                                                                    *)
(*  Axiom-clean.  Reuses CountTwoCollapse (2^inf) and LogGeomSeries       *)
(*  (geometric series), and the repo's abstract prime enumeration        *)
(*  idiom (P : nat -> R, P i >= 2) from PrimorialEuler.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import CountTwoCollapse LogGeomSeries BaselZeta.
Open Scope R_scope.

(* ===== (A) prime^inf: the geometric infinity for any base p >= 2 ===== *)

(* generalizes CountTwoCollapse.pow2_ge_Sn *)
Lemma prime_pow_ge_Sn : forall p n, 2 <= p -> INR n + 1 <= p ^ n.
Proof.
  intros p n Hp. apply Rle_trans with (2 ^ n); [ apply pow2_ge_Sn | ].
  apply pow_incr; lra.
Qed.

(* prime^inf: p^n -> +infinity (generalizes pow2_cv_infty, the 2^inf) *)
Theorem prime_pow_cv_infty : forall p, 2 <= p -> cv_infty (fun n => p ^ n).
Proof.
  intros p Hp M. destruct (INR_unbounded (M - 1)) as [N HN].
  exists N. intros n Hn. pose proof (prime_pow_ge_Sn p n Hp).
  assert (INR N <= INR n) by (apply le_INR; exact Hn). lra.
Qed.

Lemma inv_prime_lt1 : forall p, 2 <= p -> / p < 1.
Proof.
  intros p Hp. apply Rmult_lt_reg_l with p; [ lra | ].
  rewrite Rinv_r by lra. lra.
Qed.

Lemma inv_prime_pow_cv0 : forall p, 2 <= p -> Un_cv (fun n => (/ p) ^ n) 0.
Proof.
  intros p Hp. apply pow_cv0. rewrite Rabs_right.
  - apply inv_prime_lt1; exact Hp.
  - apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; lra.
Qed.

(* the collapse: c / p^n -> 0 for any prime base p >= 2 *)
Theorem over_prime_pow_cv0 : forall p c, 2 <= p -> Un_cv (fun n => c / p ^ n) 0.
Proof.
  intros p c Hp. apply (Un_cv_ext (fun n => c * (/ p) ^ n)).
  - intro n. unfold Rdiv. rewrite Rinv_pow by lra. reflexivity.
  - apply Un_cv_scal_0. apply inv_prime_pow_cv0; exact Hp.
Qed.

(* ===== (B) reconciliation: additive count -> per-prime resolvent ===== *)

Lemma inv_1_sub_inv : forall p, 2 <= p -> / (1 - / p) = p / (p - 1).
Proof. intros p Hp. field. split; lra. Qed.

Lemma pow_shift_cv0 : forall q, Rabs q < 1 -> Un_cv (fun K => q ^ (S K)) 0.
Proof.
  intros q Hq. apply (Un_cv_ext (fun K => q * q ^ K)).
  - intro K; reflexivity.
  - apply Un_cv_scal_0. apply pow_cv0; exact Hq.
Qed.

(* the ADDITIVE geometric sum over the exponent-count k equals the
   MULTIPLICATIVE per-prime factor p/(p-1) = the s=1 Euler factor *)
Theorem prime_euler_factor : forall p, 2 <= p ->
  Un_cv (fun K => sum_f_R0 (fun k => (/ p) ^ k) K) (p / (p - 1)).
Proof.
  intros p Hp.
  assert (Hlt : / p < 1) by (apply inv_prime_lt1; exact Hp).
  assert (H1p : 1 - / p <> 0) by lra.
  assert (Habs : Rabs (/ p) < 1)
    by (rewrite Rabs_right;
        [ exact Hlt | apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; lra ]).
  rewrite <- inv_1_sub_inv by exact Hp.
  apply (Un_cv_ext (fun K => / (1 - / p) - / (1 - / p) * (/ p) ^ (S K))).
  - intro K. rewrite (tech3 (/ p) K ltac:(lra)). field; lra.
  - assert (Hz : Un_cv (fun K => / (1 - / p) * (/ p) ^ (S K)) 0)
      by (apply Un_cv_scal_0; apply pow_shift_cv0; exact Habs).
    intros eps Heps. destruct (Hz eps Heps) as [N HN]. exists N. intros n Hn.
    specialize (HN n Hn). unfold R_dist in *.
    replace (/ (1 - / p) - / (1 - / p) * (/ p) ^ (S n) - / (1 - / p))
      with (- (/ (1 - / p) * (/ p) ^ (S n) - 0)) by ring.
    rewrite Rabs_Ropp. exact HN.
Qed.

(* ===== (D) the additive index: 1 + 1 + ... + 1 = the count ===== *)

Fixpoint ones (k : nat) : R := match k with 0 => 0 | S k' => 1 + ones k' end.

Lemma ones_eq : forall k, ones k = INR k.
Proof.
  induction k as [| k IH]; [ reflexivity | ].
  cbn [ones]. rewrite IH, S_INR. ring.
Qed.

Theorem index_cv_infty : cv_infty (fun k => ones k).
Proof.
  intro M. destruct (INR_unbounded M) as [N HN]. exists N. intros n Hn.
  rewrite ones_eq. assert (INR N <= INR n) by (apply le_INR; exact Hn). lra.
Qed.

(* ===== (C) primorial^inf: product over the first k primes ===== *)

Section Primorial.
Variable P : nat -> R.                 (* abstract prime enumeration, P i = i-th prime *)
Hypothesis HP : forall i, 2 <= P i.    (* each prime is >= 2 *)

Fixpoint primorial (k : nat) : R :=
  match k with 0 => 1 | S k' => P k' * primorial k' end.

(* each step multiplies in the next prime -- the prime-count indexing *)
Lemma primorial_S : forall k, primorial (S k) = P k * primorial k.
Proof. reflexivity. Qed.

Lemma primorial_ge_pow2 : forall k, 2 ^ k <= primorial k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rle_trans with (P k * 2 ^ k).
  - apply Rmult_le_compat_r; [ apply pow_le; lra | apply HP ].
  - apply Rmult_le_compat_l; [ pose proof (HP k); lra | exact IH ].
Qed.

(* primorial^inf: prod_{i<k} p_i -> +infinity *)
Theorem primorial_cv_infty : cv_infty primorial.
Proof.
  intro M. destruct (pow2_cv_infty M) as [N HN]. exists N. intros n Hn.
  pose proof (primorial_ge_pow2 n). pose proof (HN n Hn). lra.
Qed.

(* ===== the whole picture, for the i-th prime, bundled ===== *)
Theorem prime_infinity_picture : forall i,
  cv_infty (fun k => ones k)                                  (* additive index 1+1+...+1 -> inf *)
  /\ cv_infty (fun n => (P i) ^ n)                            (* prime^inf: p^n indexed by exponent-count *)
  /\ (forall c, Un_cv (fun n => c / (P i) ^ n) 0)             (* the collapse *)
  /\ Un_cv (fun K => sum_f_R0 (fun k => (/ P i) ^ k) K)
           (P i / (P i - 1))                                  (* reconciliation: add.-count sum -> per-prime factor *)
  /\ cv_infty primorial.                                      (* primorial^inf indexed by prime-count *)
Proof.
  intro i. pose proof (HP i) as Hpi.
  repeat split.
  - apply index_cv_infty.
  - apply prime_pow_cv_infty; exact Hpi.
  - intro c; apply over_prime_pow_cv0; exact Hpi.
  - apply prime_euler_factor; exact Hpi.
  - apply primorial_cv_infty.
Qed.

End Primorial.

Print Assumptions prime_pow_cv_infty.
Print Assumptions prime_euler_factor.
Print Assumptions prime_infinity_picture.
