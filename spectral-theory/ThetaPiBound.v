(* ================================================================= *)
(*  ThetaPiBound.v  —  the lower half of sharp PNT (Step 4b, easy dir). *)
(*                                                                    *)
(*  theta(N) = Sum_{p<=N} ln p <= Sum_{p<=N} ln N = pi(N) ln N, so       *)
(*      pi(N) >= theta(N)/ln N   (pi_count_ge_theta_div).              *)
(*  Combined with theta(N)/N -> 1 (ThetaLimit, from psi~N), this gives   *)
(*  the lower bound of the sharp prime number theorem:                  *)
(*      for all eps>0, eventually  (1-eps) * (N/ln N) <= pi(N)          *)
(*      (pi_lower_of_theta).                                            *)
(*  Abel-free.  (The matching sharp UPPER bound needs Abel summation.)  *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import Chebyshev ChebyshevBound PrimePowerReindex ChebyshevPrime.
Open Scope R_scope.

Lemma theta_le_picount_lnN : forall N, (2 <= N)%nat -> theta N <= pi_count N * ln (INR N).
Proof.
  intros N HN; apply Rle_trans with (psi N);
    [ apply theta_le_psi | apply psi_le_picount_lnN; exact HN ].
Qed.

Lemma pi_count_ge_theta_div : forall N, (2 <= N)%nat -> theta N / ln (INR N) <= pi_count N.
Proof.
  intros N HN.
  assert (Hln : 0 < ln (INR N)) by (apply ln_INR_pos; exact HN).
  apply Rmult_le_reg_r with (ln (INR N)); [ exact Hln | ].
  unfold Rdiv; rewrite Rmult_assoc.
  rewrite Rinv_l by lra.
  rewrite Rmult_1_r.
  apply theta_le_picount_lnN; exact HN.
Qed.

Theorem pi_lower_of_theta :
  Un_cv (fun N => theta N / INR N) 1 ->
  forall eps, 0 < eps -> exists N0, forall N, (N0 <= N)%nat ->
    (1 - eps) * (INR N / ln (INR N)) <= pi_count N.
Proof.
  intros Hth eps Heps.
  destruct (Hth eps Heps) as [N1 HN1].
  exists (Nat.max N1 2); intros N HN.
  assert (HN1' : (N1 <= N)%nat) by lia.
  assert (HN2 : (2 <= N)%nat) by lia.
  assert (Hn0 : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hln : 0 < ln (INR N)) by (apply ln_INR_pos; exact HN2).
  specialize (HN1 N HN1'); unfold R_dist in HN1; apply Rabs_def2 in HN1.
  destruct HN1 as [_ Hlo].
  assert (Hthlow : (1 - eps) * INR N <= theta N).
  { apply Rmult_le_reg_r with (/ INR N); [ apply Rinv_0_lt_compat; exact Hn0 | ].
    replace ((1 - eps) * INR N * / INR N) with (1 - eps) by (field; lra).
    replace (theta N * / INR N) with (theta N / INR N) by (unfold Rdiv; ring).
    lra. }
  apply Rle_trans with (theta N / ln (INR N)).
  - unfold Rdiv; rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hln | exact Hthlow ].
  - apply pi_count_ge_theta_div; exact HN2.
Qed.

Print Assumptions pi_lower_of_theta.

(* ================================================================= *)
(*  END ThetaPiBound.v  —  pi(N) >= theta(N)/ln N; eventually          *)
(*  pi(N) >= (1-eps) N/ln N  given theta~N.                             *)
(* ================================================================= *)
