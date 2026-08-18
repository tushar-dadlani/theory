(* ================================================================= *)
(*  EulerProductZetaS.v  —  the convergent s>1 Euler product -> zeta(s).  *)
(*                                                                    *)
(*  At s = 1 the primorial-indexed product of the per-prime factors      *)
(*  p/(p-1) DIVERGES (EulerProductAssembly; the harmonic/zeta(1)=inf     *)
(*  shadow).  For s > 1 the factor is 1/(1 - p^{-s}) and the product      *)
(*  CONVERGES to zeta(s).  Two pieces:                                    *)
(*                                                                    *)
(*   (depth, per prime)  euler_factor_s : the geometric sum over the      *)
(*        exponent-count k of the fugacity p^{-s} equals the factor       *)
(*          Sum_k (p^{-s})^k = 1/(1 - p^{-s})                           *)
(*        -- the s-generalization of prime_euler_factor (s=1: p/(p-1)).   *)
(*   (breadth, across primes)  the product over primes p <= B of those    *)
(*        factors converges to zeta(s)  (reusing the already-proven       *)
(*        EulerProductZetaCont.euler_product_zeta).                       *)
(*                                                                    *)
(*  convergent_euler_product_s bundles both: zeta(s) = prod_p sum_n       *)
(*  p^{-ns}, the depth axis (geometric per prime) times the breadth axis  *)
(*  (product over primes).  Axiom-clean.                                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import PrimeInfinities BaselZeta EulerProductZetaCont Ell2ZetaCont
        EulerProductZeta EulerProductR.
Open Scope R_scope.

(* the general geometric series (factored out of prime_euler_factor) *)
Lemma geom_sum_cv : forall q, Rabs q < 1 ->
  Un_cv (fun K => sum_f_R0 (fun k => q ^ k) K) (/ (1 - q)).
Proof.
  intros q Hq.
  assert (Hq1 : q <> 1) by (intro; subst; rewrite Rabs_R1 in Hq; lra).
  assert (H1q : 1 - q <> 0) by (intro H; apply Hq1; lra).
  apply (Un_cv_ext (fun K => / (1 - q) - / (1 - q) * q ^ (S K))).
  - intro K. rewrite (tech3 q K Hq1). field; exact H1q.
  - assert (Hz : Un_cv (fun K => / (1 - q) * q ^ (S K)) 0)
      by (apply Un_cv_scal_0; apply pow_shift_cv0; exact Hq).
    intros eps Heps. destruct (Hz eps Heps) as [N HN]. exists N. intros n Hn.
    specialize (HN n Hn). unfold R_dist in *.
    replace (/ (1 - q) - / (1 - q) * q ^ (S n) - / (1 - q))
      with (- (/ (1 - q) * q ^ (S n) - 0)) by ring.
    rewrite Rabs_Ropp. exact HN.
Qed.

Lemma Rpower_neg_pos_lt1 : forall s p, 0 < s -> 1 < p -> 0 < Rpower p (- s) < 1.
Proof.
  intros s p Hs Hp. split.
  - unfold Rpower; apply exp_pos.
  - unfold Rpower. rewrite <- exp_0. apply exp_increasing.
    assert (0 < ln p) by (rewrite <- ln_1; apply ln_increasing; lra). nra.
Qed.

(* the DEPTH-s per-prime factor: sum over the exponent-count of p^{-ns} *)
Theorem euler_factor_s : forall s p, 0 < s -> 2 <= p ->
  Un_cv (fun K => sum_f_R0 (fun k => (Rpower p (- s)) ^ k) K)
        (/ (1 - Rpower p (- s))).
Proof.
  intros s p Hs Hp. apply geom_sum_cv.
  pose proof (Rpower_neg_pos_lt1 s p Hs ltac:(lra)) as [Hlo Hhi].
  rewrite Rabs_right; [ exact Hhi | apply Rle_ge; lra ].
Qed.

(* at s = 1 the factor is the s=1 factor p/(p-1) of prime_euler_factor *)
Lemma Rpower_neg1 : forall p, 0 < p -> Rpower p (- 1) = / p.
Proof.
  intros p Hp. unfold Rpower.
  replace (-1 * ln p) with (- ln p) by ring.
  rewrite exp_Ropp, exp_ln by exact Hp. reflexivity.
Qed.

Lemma euler_factor_s_at_1 : forall p, 2 <= p -> / (1 - Rpower p (- 1)) = p / (p - 1).
Proof. intros p Hp. rewrite Rpower_neg1 by lra. field; split; lra. Qed.

(* ===== the convergent Euler product at s>1, bundled ===== *)
Theorem convergent_euler_product_s : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  (* depth: each per-prime factor is the geometric sum over the exponent-count *)
  (forall p, 2 <= p ->
     Un_cv (fun K => sum_f_R0 (fun k => (Rpower p (- s)) ^ k) K)
           (/ (1 - Rpower p (- s))))
  (* breadth: the product over primes p<=B of those factors -> zeta(s) *)
  /\ Un_cv (fun N => Zfactor (map (fun p => Rpower (IZR p) (- s)) (primes_upto (S N))))
           (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hs. split.
  - intros p Hp; apply euler_factor_s; [ lra | exact Hp ].
  - apply euler_product_zeta; exact Hs.
Qed.

Print Assumptions euler_factor_s.
Print Assumptions convergent_euler_product_s.
