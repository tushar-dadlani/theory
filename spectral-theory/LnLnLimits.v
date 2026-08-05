(* ================================================================= *)
(*  LnLnLimits.v  —  the double-log limits (for the sharp PNT upper).   *)
(*                                                                    *)
(*      sqrt(ln N) -> oo    (cv_infty_sqrt_ln)                         *)
(*      / sqrt(ln N) -> 0   (inv_sqrt_ln_cv0)                          *)
(*      ln(ln N) / ln N -> 0  (lnln_over_ln_cv0, via ln u <= 2 sqrt u)  *)
(*  These control the threshold N/(ln N)^2 in the sharp upper bound.    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ChebyshevBound ChebyshevPrime GaussValue GaussCauchy GammaFunction LnLimits.
Open Scope R_scope.

Lemma cv_infty_sqrt_ln : cv_infty (fun N => sqrt (ln (INR N))).
Proof.
  intro M; destruct (Rle_or_lt M 0) as [HM | HM].
  - exists 2%nat; intros k Hk; apply Rle_lt_trans with 0; [ exact HM | ].
    apply sqrt_lt_R0; apply ln_INR_pos; lia.
  - destruct (cv_infty_ln ((M + 1) * (M + 1))) as [N HN].
    exists (Nat.max N 1); intros k Hk.
    assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
    apply Rlt_le_trans with (M + 1); [ lra | ].
    apply Rle_trans with (sqrt ((M + 1) * (M + 1))).
    + assert (Hs : sqrt ((M + 1) * (M + 1)) = M + 1)
        by (pose proof (sqrt_Rsqr (M + 1) ltac:(lra)) as H'; unfold Rsqr in H'; exact H').
      rewrite Hs; apply Rle_refl.
    + apply sqrt_le_1_alt; left; exact HN.
Qed.

Lemma inv_sqrt_ln_cv0 : Un_cv (fun N => / sqrt (ln (INR N))) 0.
Proof.
  intros eps Heps; destruct (cv_infty_sqrt_ln (/ eps)) as [N HN].
  exists (Nat.max N 2); intros k Hk.
  assert (Hk1 : (N <= k)%nat) by lia; specialize (HN k Hk1).
  assert (Hpos : 0 < sqrt (ln (INR k)))
    by (apply Rlt_trans with (/ eps); [ apply Rinv_0_lt_compat; exact Heps | exact HN ]).
  unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact Hpos).
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar;
    [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact Heps | exact Hpos ] | exact HN ].
Qed.

Lemma lnln_over_ln_cv0 : Un_cv (fun N => ln (ln (INR N)) / ln (INR N)) 0.
Proof.
  apply (Un_cv_squeeze0 (fun N => ln (ln (INR N)) / ln (INR N))
           (fun N => 2 * / sqrt (ln (INR N))));
    [ | replace 0 with (2 * 0) by ring;
        apply (CV_mult (fun _ => 2) (fun N => / sqrt (ln (INR N))) 2 0);
        [ apply Un_cv_const | apply inv_sqrt_ln_cv0 ] ].
  destruct (cv_infty_ln 1) as [N0 HN0].
  exists N0; intros n Hn; specialize (HN0 n Hn).
  assert (Hlnpos : 0 < ln (INR n)) by lra.
  assert (Hlnlnpos : 0 <= ln (ln (INR n))) by (rewrite <- ln_1; apply ln_le; lra).
  assert (Hsln : 0 < sqrt (ln (INR n))) by (apply sqrt_lt_R0; exact Hlnpos).
  assert (Hsq : sqrt (ln (INR n)) * sqrt (ln (INR n)) = ln (INR n)) by (apply sqrt_sqrt; lra).
  pose proof (ln_le_2sqrt (ln (INR n)) Hlnpos) as Hlb.
  split.
  - unfold Rdiv; apply Rmult_le_pos; [ exact Hlnlnpos | left; apply Rinv_0_lt_compat; exact Hlnpos ].
  - replace (2 * / sqrt (ln (INR n))) with (2 / sqrt (ln (INR n))) by (unfold Rdiv; ring).
    apply div_le_div; [ exact Hlnpos | exact Hsln | nra ].
Qed.

Print Assumptions lnln_over_ln_cv0.

(* ================================================================= *)
(*  END LnLnLimits.v                                                  *)
(* ================================================================= *)
