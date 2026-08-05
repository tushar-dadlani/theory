(* ================================================================= *)
(*  ThetaLimit.v  —  psi(x) ~ x  =>  theta(x) ~ x   (Step 4a, limit form).*)
(*                                                                    *)
(*  From the tail bound 0 <= psi N - theta N <= sqrt N * ln N           *)
(*  (PsiThetaTail) and ln N / sqrt N -> 0 (via ln x <= 4 x^{1/4}), the    *)
(*  difference (psi N - theta N)/N -> 0, so                             *)
(*      Un_cv (psi/N) 1  ->  Un_cv (theta/N) 1   (theta_asymp_of_psi).  *)
(*  Uses only the existing convergence toolkit (squeeze, CV_minus,       *)
(*  cv_infty) -- no limsup machinery.  Axiom-clean.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import Chebyshev ChebyshevBound ChebyshevPrime PsiThetaTail
        GaussValue ImproperCv0 GammaFunction.
Open Scope R_scope.

Lemma div_le_div : forall a b c d, 0 < b -> 0 < d -> a * d <= c * b -> a / b <= c / d.
Proof.
  intros a b c d Hb Hd H.
  apply Rmult_le_reg_r with (b * d); [ apply Rmult_lt_0_compat; assumption | ].
  replace (a / b * (b * d)) with (a * d) by (field; lra).
  replace (c / d * (b * d)) with (c * b) by (field; lra).
  exact H.
Qed.

Lemma cv_infty_sqrtsqrt : cv_infty (fun k => sqrt (sqrt (INR k))).
Proof.
  intro M; destruct (Rle_or_lt M 0) as [HM | HM].
  - exists 1%nat; intros k Hk; apply Rle_lt_trans with 0; [ exact HM | ].
    apply sqrt_lt_R0; apply sqrt_lt_R0; apply lt_0_INR; lia.
  - destruct (cv_infty_sqrt ((M + 1) * (M + 1))) as [N HN].
    exists (Nat.max N 1); intros k Hk.
    assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
    apply Rlt_le_trans with (M + 1); [ lra | ].
    apply Rle_trans with (sqrt ((M + 1) * (M + 1))).
    + assert (Hs : sqrt ((M + 1) * (M + 1)) = M + 1)
        by (pose proof (sqrt_Rsqr (M + 1) ltac:(lra)) as H'; unfold Rsqr in H'; exact H').
      rewrite Hs; apply Rle_refl.
    + apply sqrt_le_1_alt; left; exact HN.
Qed.

Lemma inv_sqrtsqrt_cv0 : Un_cv (fun N => / sqrt (sqrt (INR N))) 0.
Proof.
  intros eps Heps.
  destruct (cv_infty_sqrtsqrt (/ eps)) as [N HN].
  exists (Nat.max N 1); intros k Hk.
  assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
  assert (Hpos : 0 < sqrt (sqrt (INR k)))
    by (apply sqrt_lt_R0; apply sqrt_lt_R0; apply lt_0_INR; lia).
  unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact Hpos).
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar;
    [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact Heps | exact Hpos ] | exact HN ].
Qed.

Lemma four_over_sqrtsqrt_cv0 : Un_cv (fun N => 4 / sqrt (sqrt (INR N))) 0.
Proof.
  apply (Un_cv_ext (fun N => 4 * / sqrt (sqrt (INR N))));
    [ intros n; unfold Rdiv; ring | ].
  replace 0 with (4 * 0) by ring.
  apply (CV_mult (fun _ => 4) (fun N => / sqrt (sqrt (INR N))) 4 0);
    [ apply Un_cv_const | apply inv_sqrtsqrt_cv0 ].
Qed.

Lemma ln_over_sqrt_cv0 : Un_cv (fun N => ln (INR N) / sqrt (INR N)) 0.
Proof.
  apply (Un_cv_squeeze0 (fun N => ln (INR N) / sqrt (INR N))
           (fun N => 4 / sqrt (sqrt (INR N)))); [ | apply four_over_sqrtsqrt_cv0 ].
  exists 1%nat; intros n Hn.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hs : 0 < sqrt (INR n)) by (apply sqrt_lt_R0; exact Hn0).
  assert (Hss : 0 < sqrt (sqrt (INR n))) by (apply sqrt_lt_R0; exact Hs).
  assert (Hln0 : 0 <= ln (INR n)) by (apply lpos; lia).
  assert (Hsq : sqrt (sqrt (INR n)) * sqrt (sqrt (INR n)) = sqrt (INR n))
    by (apply sqrt_sqrt; left; exact Hs).
  assert (Hlnb : ln (INR n) <= 4 * sqrt (sqrt (INR n))).
  { pose proof (ln_le_2sqrt (sqrt (INR n)) Hs) as H2.
    pose proof (ln_sqrt_half (INR n) Hn0) as Hh; lra. }
  split.
  - unfold Rdiv; apply Rmult_le_pos; [ exact Hln0 | left; apply Rinv_0_lt_compat; exact Hs ].
  - apply div_le_div; [ exact Hs | exact Hss | nra ].
Qed.

Lemma psi_theta_diff_cv0 : Un_cv (fun N => (psi N - theta N) / INR N) 0.
Proof.
  apply (Un_cv_squeeze0 (fun N => (psi N - theta N) / INR N)
           (fun N => ln (INR N) / sqrt (INR N))); [ | apply ln_over_sqrt_cv0 ].
  exists 2%nat; intros n Hn2.
  pose proof (psi_minus_theta_bound n Hn2) as [Hlo Hhi].
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hs : 0 < sqrt (INR n)) by (apply sqrt_lt_R0; exact Hn0).
  assert (Hsq : sqrt (INR n) * sqrt (INR n) = INR n) by (apply sqrt_sqrt; lra).
  split.
  - unfold Rdiv; apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; exact Hn0 ].
  - apply div_le_div; [ exact Hn0 | exact Hs | nra ].
Qed.

Theorem theta_asymp_of_psi :
  Un_cv (fun N => psi N / INR N) 1 -> Un_cv (fun N => theta N / INR N) 1.
Proof.
  intro Hpsi.
  apply (Un_cv_ext (fun N => psi N / INR N - (psi N - theta N) / INR N)).
  - intros n; destruct (Nat.eq_dec n 0) as [->|Hn].
    + replace (INR 0) with 0 by (simpl; ring); unfold Rdiv; rewrite Rinv_0; ring.
    + field; apply not_0_INR; exact Hn.
  - replace 1 with (1 - 0) by ring; apply CV_minus; [ exact Hpsi | apply psi_theta_diff_cv0 ].
Qed.

Print Assumptions theta_asymp_of_psi.

(* ================================================================= *)
(*  END ThetaLimit.v  —  psi ~ x  =>  theta ~ x.                        *)
(* ================================================================= *)
