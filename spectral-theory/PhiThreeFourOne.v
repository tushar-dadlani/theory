(* ================================================================= *)
(*  PhiThreeFourOne.v  --  the 3-4-1 inequality in ADDITIVE form, on  *)
(*  Phi = -zeta'/zeta.                                                *)
(*                                                                    *)
(*    0 <= 3 Re Phi(sg) + 4 Re Phi(sg+it) + Re Phi(sg+2it)   (sg > 1) *)
(*                                                                    *)
(*  ThreeFourOne.tfo_zeta is the MULTIPLICATIVE form,                 *)
(*  |zeta(sg)|^3 |zeta(sg+it)|^4 |zeta(sg+2it)| >= 1, and that is      *)
(*  where the repo's zero-free region loses eight logarithms.  In the  *)
(*  multiplicative form a zero can only enter through                  *)
(*  |zeta(a+ig)| <= 2(a-b) max|zeta'| (CHorizMVT.horiz_mvt), so it is  *)
(*  raised to the FOURTH power along with max|zeta'| = O(ln^2 t),      *)
(*  giving Kg = 16 A M^4 ~ ln^9 t and a region of width 5e-16 at t=2.  *)
(*                                                                    *)
(*  In the additive form a zero enters LINEARLY, as -1/(sg-b), through *)
(*  the partial-fraction expansion of zeta'/zeta.  No fourth power and *)
(*  no max|zeta'|.  That is the de la Vallee Poussin shape c/ln t, and *)
(*  it is the only known route to it -- ln^9 -> ln^1 is not constant   *)
(*  chasing.                                                          *)
(*                                                                    *)
(*  The expansion itself is ALREADY BUILT and is not needed here:      *)
(*  XiLogDerivZeros.xi_logderiv_zeros (xi'/xi as a sum over zeros),    *)
(*  ExplicitFormulaXiLogDeriv.XiC_logderiv (the xi'/xi <-> zeta'/zeta  *)
(*  bridge), on top of XiHgrow.xi_sum_inv_sq_uncond and               *)
(*  XiSubQuadLog.xi_subquadlog.  This file supplies the inequality     *)
(*  that consumes them.                                               *)
(*                                                                    *)
(*  WHY IT IS SHORT.  Phi is a Dirichlet series with NONNEGATIVE       *)
(*  coefficients (CVonMangoldtSeries.Phi = sum Lam(n) n^{-s}), so the  *)
(*  inequality is termwise: each term contributes                     *)
(*      Lam(n) n^{-sg} [3 + 4 cos(t ln n) + cos(2 t ln n)]            *)
(*  and the bracket is 2(1 + cos)^2 >= 0 by                            *)
(*  EulerFactorLog.three_four_one.  Every partial sum is nonnegative;  *)
(*  Rle_cv_lim passes that to the limit.  No Euler product, no         *)
(*  logarithm of a complex number, nothing about primes.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus EulerFormula CexpFull CSeries
        CZetaTerm CDirichlet EulerFactorLog VonMangoldtGlobal Chebyshev
        CVonMangoldtSeries.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- real parts of the complex pieces.                        *)
(* ----------------------------------------------------------------- *)

Lemma Re_Cexpf : forall w, Re (Cexpf w) = exp (Re w) * cos (Im w).
Proof. intro w. unfold Cexpf, Cexp, RtoC, Cmul. cbn [Re Im]. ring. Qed.

Lemma Re_RtoC_mul : forall a z, Re (Cmul (RtoC a) z) = a * Re z.
Proof. intros a z. unfold Cmul, RtoC. cbn [Re Im]. ring. Qed.

(* the n-th von Mangoldt term, real part, at s = sg + i u *)
Lemma Re_pterm : forall sg u n,
  Re (pterm (mkC sg u) n)
  = Lam (S n) * (Rpower (INR (S n)) (- sg) * cos (u * ln (INR (S n)))).
Proof.
  intros sg u n. unfold pterm, cterm, gC, Cpw, Rpower.
  rewrite Re_RtoC_mul, Re_Cexpf.
  replace (Re (Cmul (Copp (mkC sg u)) (RtoC (ln (INR (S n))))))
    with (- sg * ln (INR (S n)))
    by (unfold Cmul, Copp, RtoC; cbn [Re Im]; ring).
  replace (Im (Cmul (Copp (mkC sg u)) (RtoC (ln (INR (S n))))))
    with (- (u * ln (INR (S n))))
    by (unfold Cmul, Copp, RtoC; cbn [Re Im]; ring).
  rewrite cos_neg. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the termwise inequality.                                 *)
(* ----------------------------------------------------------------- *)

Lemma comb_nonneg : forall sg t n,
  0 <= 3 * Re (pterm (mkC sg 0) n)
       + 4 * Re (pterm (mkC sg t) n)
       + Re (pterm (mkC sg (2 * t)) n).
Proof.
  intros sg t n. rewrite !Re_pterm.
  set (R := Rpower (INR (S n)) (- sg)).
  set (L := ln (INR (S n))).
  assert (HR : 0 < R) by (unfold R, Rpower; apply exp_pos).
  assert (HL : 0 <= Lam (S n)) by apply Lam_nonneg.
  replace (0 * L) with 0 by ring. rewrite cos_0.
  replace (2 * t * L) with (2 * (t * L)) by ring.
  assert (Hkey : 3 * 1 + 4 * cos (t * L) + cos (2 * (t * L))
                 = 2 * (1 + cos (t * L)) ^ 2)
    by (pose proof (three_four_one (t * L)); lra).
  replace (3 * (Lam (S n) * (R * 1)) + 4 * (Lam (S n) * (R * cos (t * L)))
           + Lam (S n) * (R * cos (2 * (t * L))))
    with (Lam (S n) * R * (3 * 1 + 4 * cos (t * L) + cos (2 * (t * L))))
    by ring.
  rewrite Hkey.
  apply Rmult_le_pos; [ nra | ].
  apply Rmult_le_pos; [ lra | apply pow2_ge_0 ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- partial sums.                                            *)
(* ----------------------------------------------------------------- *)

Lemma comb_sum : forall f g h N,
  3 * sum_f_R0 f N + 4 * sum_f_R0 g N + sum_f_R0 h N
  = sum_f_R0 (fun k => 3 * f k + 4 * g k + h k) N.
Proof.
  intros f g h N. induction N as [| N IH]; [ reflexivity | ].
  rewrite !tech5, <- IH. ring.
Qed.

Lemma sum_f_R0_nonneg : forall f N, (forall k, 0 <= f k) -> 0 <= sum_f_R0 f N.
Proof.
  intros f N H. induction N as [| N IH]; [ apply H | ].
  rewrite tech5. pose proof (H (S N)). lra.
Qed.

Lemma psum_nonneg : forall sg t N,
  0 <= 3 * Re (Cpsum (pterm (mkC sg 0)) N)
       + 4 * Re (Cpsum (pterm (mkC sg t)) N)
       + Re (Cpsum (pterm (mkC sg (2 * t))) N).
Proof.
  intros sg t N. rewrite !Re_Cpsum, comb_sum.
  apply sum_f_R0_nonneg. intro k. apply comb_nonneg.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part D -- to the limit.                                            *)
(* ----------------------------------------------------------------- *)

Lemma Un_cv_const0 : Un_cv (fun _ : nat => 0) 0.
Proof.
  intros eps He. exists 0%nat. intros n _. unfold R_dist.
  replace (0 - 0) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Lemma Un_cv_scal : forall (u : nat -> R) l c,
  Un_cv u l -> Un_cv (fun n => c * u n) (c * l).
Proof.
  intros u l c H eps He.
  destruct (Req_dec c 0) as [Hc0 | Hc0].
  - exists 0%nat. intros n _. unfold R_dist. rewrite Hc0.
    replace (0 * u n - 0 * l) with 0 by ring. rewrite Rabs_R0. exact He.
  - assert (Hc : 0 < Rabs c) by (apply Rabs_pos_lt; exact Hc0).
    destruct (H (eps / Rabs c) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    exists N. intros n Hn. unfold R_dist.
    replace (c * u n - c * l) with (c * (u n - l)) by ring.
    rewrite Rabs_mult.
    apply Rlt_le_trans with (Rabs c * (eps / Rabs c)).
    + apply Rmult_lt_compat_l; [ lra | apply HN; exact Hn ].
    + apply Req_le. field. lra.
Qed.

Lemma Re_psum_cv : forall s (H : 1 < Re s),
  Un_cv (fun N => Re (Cpsum (pterm s) N)) (Re (Phi s H)).
Proof.
  intros s H.
  pose proof (Phi_spec s H) as HS. unfold Cseries_cv in HS.
  rewrite CUn_cv_comp in HS. destruct HS as [HRe _]. exact HRe.
Qed.

(* ---- THE additive 3-4-1 ---- *)

Theorem tfo_phi : forall (sg t : R)
    (H0 : 1 < Re (mkC sg 0)) (H1 : 1 < Re (mkC sg t))
    (H2 : 1 < Re (mkC sg (2 * t))),
  0 <= 3 * Re (Phi (mkC sg 0) H0)
       + 4 * Re (Phi (mkC sg t) H1)
       + Re (Phi (mkC sg (2 * t)) H2).
Proof.
  intros sg t H0 H1 H2.
  apply Rle_cv_lim with
    (Un := fun _ : nat => 0)
    (Vn := fun N => 3 * Re (Cpsum (pterm (mkC sg 0)) N)
                    + 4 * Re (Cpsum (pterm (mkC sg t)) N)
                    + Re (Cpsum (pterm (mkC sg (2 * t))) N)).
  - intro N. apply psum_nonneg.
  - apply Un_cv_const0.
  - apply CV_plus;
      [ apply CV_plus;
        [ apply Un_cv_scal; apply Re_psum_cv
        | apply Un_cv_scal; apply Re_psum_cv ]
      | apply Re_psum_cv ].
Qed.

Print Assumptions tfo_phi.

(* ================================================================= *)
(*  END PhiThreeFourOne.v                                             *)
(* ================================================================= *)
