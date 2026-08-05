(* ================================================================= *)
(*  LnLimits.v  —  reusable logarithmic limits (for the sharp PNT upper).*)
(*                                                                    *)
(*      ln N -> oo        (cv_infty_ln, from INR N -> oo)              *)
(*      / sqrt N -> 0     (inv_sqrt_cv0)                               *)
(*      / ln N -> 0       (inv_ln_cv0)                                 *)
(*      ln N / N -> 0     (ln_over_N_cv0, via ln x <= 2 sqrt x)         *)
(*  Uses only the existing convergence toolkit.  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ChebyshevBound ChebyshevPrime GaussValue GaussCauchy GammaFunction.
Open Scope R_scope.

Lemma div_le_div : forall a b c d, 0 < b -> 0 < d -> a * d <= c * b -> a / b <= c / d.
Proof.
  intros a b c d Hb Hd H.
  apply Rmult_le_reg_r with (b * d); [ apply Rmult_lt_0_compat; assumption | ].
  replace (a / b * (b * d)) with (a * d) by (field; lra).
  replace (c / d * (b * d)) with (c * b) by (field; lra).
  exact H.
Qed.

Lemma cv_infty_ln : cv_infty (fun N => ln (INR N)).
Proof.
  intro M.
  destruct (cv_infty_INR (exp M)) as [N HN].
  exists (Nat.max N 1); intros k Hk.
  assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
  rewrite <- (ln_exp M); apply ln_increasing; [ apply exp_pos | exact HN ].
Qed.

Lemma inv_sqrt_cv0 : Un_cv (fun N => / sqrt (INR N)) 0.
Proof.
  intros eps Heps; destruct (cv_infty_sqrt (/ eps)) as [N HN].
  exists (Nat.max N 1); intros k Hk.
  assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
  assert (Hpos : 0 < sqrt (INR k)) by (apply sqrt_lt_R0; apply lt_0_INR; lia).
  unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact Hpos).
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar;
    [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact Heps | exact Hpos ] | exact HN ].
Qed.

Lemma inv_ln_cv0 : Un_cv (fun N => / ln (INR N)) 0.
Proof.
  intros eps Heps; destruct (cv_infty_ln (/ eps)) as [N HN].
  exists (Nat.max N 1); intros k Hk.
  assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
  assert (Hpos : 0 < ln (INR k))
    by (apply Rlt_trans with (/ eps); [ apply Rinv_0_lt_compat; exact Heps | exact HN ]).
  unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact Hpos).
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar;
    [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact Heps | exact Hpos ] | exact HN ].
Qed.

Lemma ln_over_N_cv0 : Un_cv (fun N => ln (INR N) / INR N) 0.
Proof.
  apply (Un_cv_squeeze0 (fun N => ln (INR N) / INR N) (fun N => 2 * / sqrt (INR N)));
    [ | apply (Un_cv_ext (fun N => 2 * / sqrt (INR N)));
        [ intros n; reflexivity
        | replace 0 with (2 * 0) by ring;
          apply CV_mult; [ apply Un_cv_const | apply inv_sqrt_cv0 ] ] ].
  exists 1%nat; intros n Hn.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hs : 0 < sqrt (INR n)) by (apply sqrt_lt_R0; exact Hn0).
  assert (Hln0 : 0 <= ln (INR n)) by (apply lpos; lia).
  assert (Hsq : sqrt (INR n) * sqrt (INR n) = INR n) by (apply sqrt_sqrt; lra).
  pose proof (ln_le_2sqrt (INR n) Hn0) as Hlb.
  split.
  - unfold Rdiv; apply Rmult_le_pos; [ exact Hln0 | left; apply Rinv_0_lt_compat; exact Hn0 ].
  - replace (2 * / sqrt (INR n)) with (2 / sqrt (INR n)) by (unfold Rdiv; ring).
    apply div_le_div; [ exact Hn0 | exact Hs | nra ].
Qed.

Print Assumptions ln_over_N_cv0.

(* ================================================================= *)
(*  END LnLimits.v                                                    *)
(* ================================================================= *)
