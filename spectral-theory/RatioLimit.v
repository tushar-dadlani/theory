(* ================================================================= *)
(*  RatioLimit.v  —  ln N / (ln N - 2 ln ln N) -> 1  (sharp PNT upper). *)
(*                                                                    *)
(*  With s = ln ln N / ln N -> 0 (LnLnLimits), the ratio               *)
(*      R(N) = ln N / (ln N - 2 ln ln N) = 1/(1 - 2s)                   *)
(*  satisfies  0 <= R(N) - 1 <= 4 s(N)  once s <= 1/4, so R(N) -> 1      *)
(*  (squeeze on R-1, then shift).  This is the last limit needed for     *)
(*  the sharp upper bound of PNT.  Axiom-clean.                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ChebyshevBound ChebyshevPrime GammaFunction ZetaZero
        LnLimits LnLnLimits.
Open Scope R_scope.

Theorem ratio_cv1 :
  Un_cv (fun N => ln (INR N) / (ln (INR N) - 2 * ln (ln (INR N)))) 1.
Proof.
  apply Un_cv_shift0.
  apply (Un_cv_squeeze0
           (fun N => ln (INR N) / (ln (INR N) - 2 * ln (ln (INR N))) - 1)
           (fun N => 4 * ln (ln (INR N)) / ln (INR N)));
    [ | replace 0 with (4 * 0) by ring;
        apply (Un_cv_ext (fun N => 4 * (ln (ln (INR N)) / ln (INR N))));
          [ intros n; unfold Rdiv; ring
          | apply (CV_mult (fun _ => 4) (fun N => ln (ln (INR N)) / ln (INR N)) 4 0);
            [ apply Un_cv_const | apply lnln_over_ln_cv0 ] ] ].
  destruct (cv_infty_ln 1) as [N1 HN1].
  destruct (lnln_over_ln_cv0 (1 / 4) ltac:(lra)) as [N2 HN2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia; specialize (HN1 n Hn1).
  assert (Hn2 : (N2 <= n)%nat) by lia; specialize (HN2 n Hn2).
  unfold R_dist in HN2; rewrite Rminus_0_r in HN2.
  assert (Hlnpos : 0 < ln (INR n)) by lra.
  assert (Hlnln0 : 0 <= ln (ln (INR n))) by (rewrite <- ln_1; apply ln_le; lra).
  assert (Hs : 0 <= ln (ln (INR n)) / ln (INR n))
    by (unfold Rdiv; apply Rmult_le_pos;
        [ exact Hlnln0 | left; apply Rinv_0_lt_compat; exact Hlnpos ]).
  rewrite Rabs_right in HN2 by (apply Rle_ge; exact Hs).
  assert (H4 : 4 * ln (ln (INR n)) <= ln (INR n)).
  { apply Rmult_le_reg_r with (/ ln (INR n)); [ apply Rinv_0_lt_compat; exact Hlnpos | ].
    replace (4 * ln (ln (INR n)) * / ln (INR n))
      with (4 * (ln (ln (INR n)) / ln (INR n))) by (unfold Rdiv; ring).
    replace (ln (INR n) * / ln (INR n)) with 1 by (field; lra).
    lra. }
  assert (HL : 0 < ln (INR n) - 2 * ln (ln (INR n))) by lra.
  assert (HR1 : ln (INR n) / (ln (INR n) - 2 * ln (ln (INR n))) - 1
              = 2 * ln (ln (INR n)) / (ln (INR n) - 2 * ln (ln (INR n))))
    by (field; lra).
  split.
  - rewrite HR1; unfold Rdiv; apply Rmult_le_pos;
      [ lra | left; apply Rinv_0_lt_compat; exact HL ].
  - rewrite HR1; apply div_le_div; [ exact HL | exact Hlnpos | nra ].
Qed.

Print Assumptions ratio_cv1.

(* ================================================================= *)
(*  END RatioLimit.v                                                  *)
(* ================================================================= *)
