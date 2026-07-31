(* ================================================================= *)
(*  GaussSelfDual.v  —  Leibniz-gap Phases 4 & 5: the UNCONDITIONAL    *)
(*  Gaussian Fourier self-duality.                                    *)
(*                                                                    *)
(*    fourier_self_dual : ∫_ℝ e^{−πx²}cos(2πxξ) dx = e^{−πξ²}.          *)
(*                                                                    *)
(*  Phase 4 (the ODE identity, integration by parts): the antiderivative*)
(*  P(x) = e^{−πx²}sin(2πxξ) has P'(x) = fsin ξ x + 2πξ·fcos ξ x, so    *)
(*  ∫_{−k}^k (fsin + 2πξ fcos) = P(k) − P(−k) = 2 e^{−πk²}sin(2πkξ)     *)
(*  (FTC + evenness of e^{−πx²}, oddness of sin).  Letting k→∞ (the      *)
(*  boundary → 0 since e^{−πk²} → 0, exp_pi_cv0) gives                  *)
(*      g(ξ) = −2πξ · F(ξ)   (fourier_ode).                            *)
(*  Phase 5: F' = g = −2πξ·F (fourier_deriv + fourier_ode) and F(0)=1   *)
(*  (gauss_pi) feed gaussian_ode_unique ⇒ F(ξ) = e^{−πξ²}.             *)
(*                                                                    *)
(*  The Leibniz gap flagged in GaussFourier is now CLOSED — the         *)
(*  self-duality is unconditional.  No new axioms (classical Reals).   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV GaussSubst GaussFull GaussPiValue GaussDeriv
  GaussTransform GaussDerivValue GaussFourier GaussSqrtStep GaussLeibnizCVU.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Linear/chain derivative helpers.                                 *)
(* ----------------------------------------------------------------- *)

Lemma dscal : forall c x, derivable_pt_lim (fun z => c * z) x c.
Proof.
  intros c x; pose proof (derivable_pt_lim_scal (fun z => z) c x 1 (derivable_pt_lim_id x)) as Hm.
  cbv beta in Hm; match type of Hm with derivable_pt_lim _ _ ?V => replace V with c in Hm by ring end.
  exact Hm.
Qed.

Lemma dlin2 : forall b x, derivable_pt_lim (fun z => 2 * PI * z * b) x (2 * PI * b).
Proof.
  intros b x.
  pose proof (derivable_pt_lim_mult (fun z => 2 * PI * z) (fct_cte b) x (2 * PI) 0
                (dscal (2 * PI) x) (derivable_pt_lim_const b x)) as Hm.
  cbv beta in Hm.
  match type of Hm with derivable_pt_lim _ _ ?V => replace V with (2 * PI * b) in Hm by (unfold fct_cte; ring) end.
  exact Hm.
Qed.

Lemma dsin_lin : forall b x, derivable_pt_lim (fun z => sin (2 * PI * z * b)) x (cos (2 * PI * x * b) * (2 * PI * b)).
Proof.
  intros b x.
  exact (derivable_pt_lim_comp (fun z => 2 * PI * z * b) sin x (2 * PI * b) (cos (2 * PI * x * b))
           (dlin2 b x) (derivable_pt_lim_sin (2 * PI * x * b))).
Qed.

(* ----------------------------------------------------------------- *)
(*  e^{−πk²} → 0.                                                    *)
(* ----------------------------------------------------------------- *)

Lemma exp_pi_cv0 : Un_cv (fun k => exp_pi (INR k)) 0.
Proof.
  intros eps He; pose proof PI_RGT_0 as HPI.
  destruct (INR_unbounded (Rmax 1 ((/ eps - 1) / PI))) as [N HN].
  exists N; intros k Hk.
  assert (Hbig : Rmax 1 ((/ eps - 1) / PI) < INR k)
    by (apply Rlt_le_trans with (INR N); [ exact HN | apply le_INR; exact Hk ]).
  assert (Hk1 : 1 <= INR k)
    by (apply Rlt_le; apply Rle_lt_trans with (Rmax 1 ((/ eps - 1) / PI)); [ apply Rmax_l | exact Hbig ]).
  assert (Hke : (/ eps - 1) / PI < INR k)
    by (apply Rle_lt_trans with (Rmax 1 ((/ eps - 1) / PI)); [ apply Rmax_r | exact Hbig ]).
  unfold R_dist; rewrite Rminus_0_r, Rabs_pos_eq by (left; unfold exp_pi; apply exp_pos).
  apply Rle_lt_trans with (/ (1 + PI * INR k)).
  - assert (Hkk : INR k <= INR k ^ 2) by (replace (INR k ^ 2) with (INR k * INR k) by ring; nra).
    unfold exp_pi; rewrite exp_Ropp; apply Rinv_le_contravar; [ nra | ].
    apply Rle_trans with (1 + PI * INR k ^ 2); [ nra | pose proof (exp_ineq1_le (PI * INR k ^ 2)); lra ].
  - assert (Hgt : / eps < 1 + PI * INR k).
    { pose proof (Rmult_lt_compat_r PI ((/ eps - 1) / PI) (INR k) HPI Hke) as Hm.
      replace ((/ eps - 1) / PI * PI) with (/ eps - 1) in Hm by (field; lra); lra. }
    apply Rlt_le_trans with (/ / eps); [ | rewrite Rinv_inv; apply Rle_refl ].
    apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact He | nra ] | exact Hgt ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Integration by parts on [−k,k].                                  *)
(* ----------------------------------------------------------------- *)

Lemma ibp_identity : forall xi k,
  S_deriv xi k + 2 * PI * xi * S_transform xi k = 2 * exp_pi (INR k) * sin (2 * PI * INR k * xi).
Proof.
  intros xi k.
  assert (HAA : - INR k <= INR k) by (pose proof (pos_INR k); lra).
  set (P := fun x => exp_pi x * sin (2 * PI * x * xi)).
  set (h := fun x => fsin xi x + 2 * PI * xi * fcos xi x).
  assert (dP : forall x, derivable_pt_lim P x (h x)).
  { intro x; unfold P, h.
    pose proof (derivable_pt_lim_mult exp_pi (fun z => sin (2 * PI * z * xi)) x
                  (- (2 * PI * x) * exp_pi x) (cos (2 * PI * x * xi) * (2 * PI * xi))
                  (dexp_pi x) (dsin_lin xi x)) as Hm.
    cbv beta in Hm.
    match type of Hm with derivable_pt_lim _ _ ?V =>
      replace V with (fsin xi x + 2 * PI * xi * fcos xi x) in Hm by (unfold fsin, fcos; ring) end.
    exact Hm. }
  assert (conth : forall x, - INR k <= x <= INR k -> continuity_pt h x)
    by (intros x _; unfold h; apply continuity_pt_plus;
        [ apply cont_fsin | apply (continuity_pt_scal (fcos xi) (2 * PI * xi) x); apply cont_fcos ]).
  assert (prh : Riemann_integrable h (- INR k) (INR k))
    by (apply continuity_implies_RiemannInt; [ exact HAA | exact conth ]).
  assert (Hanti : antiderivative h P (- INR k) (INR k))
    by (split; [ intros t Ht; exists (exist _ (h t) (dP t)); reflexivity | exact HAA ]).
  assert (Hftc : RiemannInt prh = P (INR k) - P (- INR k))
    by (apply (FTC_antideriv h P (- INR k) (INR k) HAA conth prh Hanti)).
  assert (Hbd : P (INR k) - P (- INR k) = 2 * exp_pi (INR k) * sin (2 * PI * INR k * xi)).
  { unfold P; rewrite exp_pi_even;
      replace (2 * PI * (- INR k) * xi) with (- (2 * PI * INR k * xi)) by ring;
      rewrite sin_neg; ring. }
  assert (Hlin : RiemannInt prh = S_deriv xi k + 2 * PI * xi * S_transform xi k).
  { unfold S_deriv, S_transform;
      exact (RiemannInt_P13 (fsin_int xi (- INR k) (INR k)) (fcos_int xi (- INR k) (INR k)) prh). }
  rewrite <- Hlin, Hftc; exact Hbd.
Qed.

(* ----------------------------------------------------------------- *)
(*  The ODE:  g(ξ) = −2πξ · F(ξ).                                    *)
(* ----------------------------------------------------------------- *)

Lemma fourier_ode : forall xi, g_deriv xi = - (2 * PI * xi) * F_transform xi.
Proof.
  intro xi.
  assert (bd_cv0 : Un_cv (fun k => 2 * exp_pi (INR k) * sin (2 * PI * INR k * xi)) 0).
  { intros eps He.
    assert (H2 : Un_cv (fun k => 2 * exp_pi (INR k)) 0).
    { replace 0 with (2 * 0) by ring;
        apply (CV_mult (fun _ => 2) (fun k => exp_pi (INR k)) 2 0);
        [ intros e He2; exists 0%nat; intros p _; unfold R_dist;
          replace (2 - 2) with 0 by ring; rewrite Rabs_R0; exact He2 | apply exp_pi_cv0 ]. }
    destruct (H2 eps He) as [N HN]; exists N; intros k Hk.
    pose proof (HN k Hk) as Ht; unfold R_dist in Ht |- *; rewrite Rminus_0_r in Ht |- *.
    apply Rle_lt_trans with (2 * exp_pi (INR k)).
    - rewrite Rabs_mult, (Rabs_pos_eq (2 * exp_pi (INR k)))
        by (apply Rmult_le_pos; [ lra | left; unfold exp_pi; apply exp_pos ]).
      apply Rle_trans with (2 * exp_pi (INR k) * 1); [ | rewrite Rmult_1_r; apply Rle_refl ].
      apply Rmult_le_compat_l;
        [ apply Rmult_le_pos; [ lra | left; unfold exp_pi; apply exp_pos ] | ].
      pose proof (SIN_bound (2 * PI * INR k * xi)); unfold Rabs;
        destruct (Rcase_abs (sin (2 * PI * INR k * xi))); lra.
    - apply Rle_lt_trans with (Rabs (2 * exp_pi (INR k))); [ apply Rle_abs | exact Ht ]. }
  apply (UL_sequence (S_deriv xi)); [ apply g_deriv_cv | ].
  apply (Un_cv_ext (fun k => 2 * exp_pi (INR k) * sin (2 * PI * INR k * xi) - 2 * PI * xi * S_transform xi k)
                   (S_deriv xi) (- (2 * PI * xi) * F_transform xi)).
  - intro k; pose proof (ibp_identity xi k); lra.
  - replace (- (2 * PI * xi) * F_transform xi) with (0 - 2 * PI * xi * F_transform xi) by ring.
    apply CV_minus; [ exact bd_cv0 | ].
    apply (CV_mult (fun _ => 2 * PI * xi) (S_transform xi) (2 * PI * xi) (F_transform xi));
      [ intros e He; exists 0%nat; intros p _; unfold R_dist;
        replace (2 * PI * xi - 2 * PI * xi) with 0 by ring; rewrite Rabs_R0; exact He
      | apply F_transform_cv ].
Qed.

(* ----------------------------------------------------------------- *)
(*  F(0) = 1, and the self-duality.                                  *)
(* ----------------------------------------------------------------- *)

Lemma S_transform_0 : forall k, S_transform 0 k = Dseq k.
Proof.
  intro k; unfold S_transform, Dseq; apply RiemannInt_P18;
    [ pose proof (pos_INR k); lra | intros x _; unfold fcos;
      replace (2 * PI * x * 0) with 0 by ring; rewrite cos_0; ring ].
Qed.

Lemma F_transform_0 : F_transform 0 = 1.
Proof.
  apply (UL_sequence (S_transform 0)); [ apply F_transform_cv | ].
  apply (Un_cv_ext Dseq (S_transform 0) 1);
    [ intro k; symmetry; apply S_transform_0 | exact D_cv' ].
Qed.

Theorem fourier_self_dual : forall xi, F_transform xi = exp (- (PI * xi ^ 2)).
Proof.
  apply gaussian_ode_unique.
  - intro x; rewrite <- fourier_ode; apply fourier_deriv.
  - exact F_transform_0.
Qed.

Print Assumptions fourier_self_dual.

(* ================================================================= *)
(*  END GaussSelfDual.v — the Leibniz gap is CLOSED.                 *)
(*  ∫_ℝ e^{−πx²}cos(2πxξ) dx = e^{−πξ²}, UNCONDITIONALLY (classical     *)
(*  Reals only).  The Gaussian is its own Fourier transform — the       *)
(*  analytic heart of Poisson summation and the θ functional equation.  *)
(* ================================================================= *)
