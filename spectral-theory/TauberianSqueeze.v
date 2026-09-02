(* ================================================================= *)
(*  TauberianSqueeze.v  --  Newman's Tauberian squeeze.                *)
(*                                                                    *)
(*  From the CAUCHY TAIL of the improper integral                      *)
(*      int_1^oo (psi(u) - u)/u^2 du                                   *)
(*  conclude  psi(x)/x -> 1.                                           *)
(*                                                                    *)
(*  The Cauchy tail is what Newman's contour argument delivers; it is  *)
(*  taken here as the hypothesis TintCauchy, so this file is the       *)
(*  REAL-ANALYSIS half of the route and is independent of the contour  *)
(*  work still outstanding (CNewman.v).                                *)
(*                                                                    *)
(*  Mechanism: an overshoot psiR x >= lam*x forces, by monotonicity of *)
(*  psi, a block of area >= lam - 1 - ln lam > 0 over [x, lam*x]       *)
(*  (TauberianBlock.block_lower).  That lower bound does not shrink    *)
(*  with x, so it contradicts the Cauchy tail.  Dually below.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV NewmanTauber NewmanBlock
        Chebyshev ChebyshevPsiR PsiRIntegrable TauberianBlock
        CIdentityProp SelbergEndgame SelbergAverage PsiAsymp
        PrimePowerReindex PNTConditional.
Open Scope R_scope.

(* the Cauchy criterion for the tail of int_1^oo tint *)
Definition TintCauchy : Prop :=
  forall eps, 0 < eps -> exists X, 1 <= X /\
    forall x y (Hx : X <= x) (Hxy : x <= y)
           (pr : Riemann_integrable tint x y),
      Rabs (RiemannInt pr) < eps.

(* ----------------------------------------------------------------- *)
(*  No sustained overshoot.                                           *)
(* ----------------------------------------------------------------- *)

Theorem tauberian_no_overshoot : TintCauchy ->
  forall lam, 1 < lam ->
  exists X, 0 < X /\ forall x, X <= x -> psiR x < lam * x.
Proof.
  intros HC lam Hlam.
  destruct (HC (lam - 1 - ln lam) (gap_pos_gt lam Hlam)) as [X [HX1 HXb]].
  exists X. split; [ lra | ].
  intros x Hx.
  assert (Hx0 : 0 < x) by lra.
  destruct (Rlt_or_le (psiR x) (lam * x)) as [Hlt | Hge]; [ exact Hlt | ].
  exfalso.
  assert (Hab : x <= lam * x) by nra.
  pose proof (tint_integrable x (lam * x) Hx0 Hab) as pr.
  pose proof (block_lower x lam Hx0 (Rlt_le _ _ Hlam) Hge pr) as Hlow.
  pose proof (HXb x (lam * x) Hx Hab pr) as Hsmall.
  apply Rabs_def2 in Hsmall.
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  No sustained undershoot.                                          *)
(* ----------------------------------------------------------------- *)

Theorem tauberian_no_undershoot : TintCauchy ->
  forall mu, 0 < mu -> mu < 1 ->
  exists X, 0 < X /\ forall x, X <= x -> mu * x < psiR x.
Proof.
  intros HC mu Hmu Hmu1.
  assert (Hgap : 0 < mu - 1 - ln mu) by (apply gap_pos; lra).
  destruct (HC (mu - 1 - ln mu) Hgap) as [X [HX1 HXb]].
  exists (X / mu). split; [ apply Rdiv_lt_0_compat; lra | ].
  intros x Hx.
  assert (Hx0 : 0 < x) by (apply Rlt_le_trans with (X / mu);
                           [ apply Rdiv_lt_0_compat; lra | exact Hx ]).
  destruct (Rlt_or_le (mu * x) (psiR x)) as [Hlt | Hle]; [ exact Hlt | ].
  exfalso.
  assert (Hax : X <= mu * x).
  { apply (Rmult_le_reg_r (/ mu)); [ apply Rinv_0_lt_compat; lra | ].
    replace (mu * x * / mu) with x by (field; lra).
    unfold Rdiv in Hx. exact Hx. }
  assert (Hab : mu * x <= x) by nra.
  pose proof (tint_integrable (mu * x) x ltac:(nra) Hab) as pr.
  pose proof (block_upper x mu Hx0 Hmu (Rlt_le _ _ Hmu1) Hle pr) as Hup.
  pose proof (HXb (mu * x) x Hax Hab pr) as Hsmall.
  apply Rabs_def2 in Hsmall.
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE SQUEEZE: psi(x)/x -> 1.                                        *)
(* ----------------------------------------------------------------- *)

Theorem tauberian_squeeze_real : TintCauchy ->
  forall eps, 0 < eps -> exists X, 0 < X /\
    forall x, X <= x -> Rabs (psiR x / x - 1) < eps.
Proof.
  intros HC eps He.
  assert (He0 : 0 < Rmin eps (/ 2)) by (apply Rmin_glb_lt; lra).
  assert (He1 : Rmin eps (/ 2) <= eps) by apply Rmin_l.
  assert (He2 : Rmin eps (/ 2) <= / 2) by apply Rmin_r.
  destruct (tauberian_no_overshoot HC (1 + Rmin eps (/ 2)) ltac:(lra))
    as [X1 [HX1 Hover]].
  destruct (tauberian_no_undershoot HC (1 - Rmin eps (/ 2)) ltac:(lra) ltac:(lra))
    as [X2 [HX2 Hunder]].
  exists (Rmax X1 X2). split.
  { apply Rlt_le_trans with X1; [ exact HX1 | apply Rmax_l ]. }
  intros x Hx.
  assert (Hx1 : X1 <= x)
    by (apply Rle_trans with (Rmax X1 X2); [ apply Rmax_l | exact Hx ]).
  assert (Hx2 : X2 <= x)
    by (apply Rle_trans with (Rmax X1 X2); [ apply Rmax_r | exact Hx ]).
  assert (Hx0 : 0 < x) by lra.
  pose proof (Hover x Hx1) as Hu.
  pose proof (Hunder x Hx2) as Hl.
  replace (psiR x / x - 1) with ((psiR x - x) / x) by (field; lra).
  apply Rlt_le_trans with (Rmin eps (/ 2)); [ | exact He1 ].
  apply Rabs_def1.
  - apply (Rmult_lt_reg_r x); [ exact Hx0 | ].
    replace ((psiR x - x) / x * x) with (psiR x - x) by (field; lra).
    lra.
  - apply (Rmult_lt_reg_r x); [ exact Hx0 | ].
    replace ((psiR x - x) / x * x) with (psiR x - x) by (field; lra).
    lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Bridge to the form PNT consumes: Un_cv Vrem 0.                     *)
(*  PsiAsymp.psi_asymp_cv then gives psi N / N -> 1, and               *)
(*  PNTConditional.pi_asymp_of_psi gives PNT.                          *)
(* ----------------------------------------------------------------- *)

Lemma psiR_at_nat : forall N : nat, psiR (INR N) = psi N.
Proof.
  intro N. apply psiR_step.
  split; [ apply Rle_refl | rewrite S_INR; lra ].
Qed.

Theorem tauberian_psi_cv : TintCauchy -> Un_cv Vrem 0.
Proof.
  intros HC eps He.
  destruct (tauberian_squeeze_real HC eps He) as [X [HX Hb]].
  destruct (exists_nat_gt X (Rlt_le _ _ HX)) as [N0 HN0].
  exists (Nat.max N0 1). intros n Hn.
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (HnN0 : (N0 <= n)%nat) by lia.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hxn : X <= INR n).
  { apply Rle_trans with (INR N0); [ lra | apply le_INR; exact HnN0 ]. }
  pose proof (Hb (INR n) Hxn) as Hbb.
  unfold R_dist. rewrite Rminus_0_r.
  rewrite Rabs_pos_eq by apply Vrem_nonneg.
  unfold Vrem, Rem.
  replace (Rabs (psi n - INR n) / INR n)
    with (Rabs (psiR (INR n) / INR n - 1)); [ exact Hbb | ].
  rewrite psiR_at_nat.
  replace (psi n / INR n - 1) with ((psi n - INR n) / INR n) by (field; lra).
  unfold Rdiv. rewrite Rabs_mult. f_equal.
  rewrite Rabs_right; [ reflexivity | ].
  apply Rle_ge, Rlt_le, Rinv_0_lt_compat; exact Hn0.
Qed.

(* ================================================================= *)
(*  CAPSTONE: PNT, conditional ONLY on the Cauchy tail of the Newman   *)
(*  integral -- i.e. on exactly what the contour argument delivers.    *)
(* ================================================================= *)

Theorem pnt_of_tint_cauchy : TintCauchy ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof.
  intro HC.
  apply pi_asymp_of_psi, psi_asymp_cv, tauberian_psi_cv, HC.
Qed.

Print Assumptions pnt_of_tint_cauchy.
Print Assumptions tauberian_psi_cv.
Print Assumptions tauberian_no_overshoot.
Print Assumptions tauberian_no_undershoot.
Print Assumptions tauberian_squeeze_real.
