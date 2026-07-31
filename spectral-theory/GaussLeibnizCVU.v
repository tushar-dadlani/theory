(* ================================================================= *)
(*  GaussLeibnizCVU.v  —  Leibniz-gap Phase 3: F'(ξ) = g(ξ).           *)
(*                                                                    *)
(*  The improper transform F(ξ) = ∫_ℝ e^{−πx²}cos(2πxξ) is             *)
(*  differentiable with F'(ξ) = g(ξ) = ∫_ℝ −2πx e^{−πx²}sin(2πxξ),      *)
(*  by the stdlib interchange theorem derivable_pt_lim_CVU on a ball    *)
(*  around ξ, fed with everything Phases 1–2 produced:                *)
(*    • fn = S_transform, fn' = S_deriv derivable (leibniz_bounded);   *)
(*    • fn → F pointwise (F_transform_cv);                             *)
(*    • fn' → g uniformly (g_deriv_cvu, the CVU hypothesis);           *)
(*    • g continuous (CVU_continuity, needing each S_deriv·n            *)
(*      continuous — a Lipschitz bound via sin_lipschitz, same mbnd).  *)
(*                                                                    *)
(*    fourier_deriv : derivable_pt_lim F_transform ξ (g_deriv ξ).      *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 PSeries_reg Lra Lia.
Require Import GaussSubst GaussFull GaussPiValue GaussTaylor GaussTransform GaussDerivValue GaussLeibniz.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Lipschitz ⇒ continuity_pt.                                       *)
(* ----------------------------------------------------------------- *)

Lemma lipschitz_continuity : forall (f : R -> R) (y K : R), 0 <= K ->
  (forall x, Rabs (f x - f y) <= K * Rabs (x - y)) -> continuity_pt f y.
Proof.
  intros f y K HK Hlip eps He.
  exists (eps / (K + 1)); split; [ apply Rdiv_lt_0_compat; lra | ].
  intros x [_ Hdist]; unfold R_dist in *; simpl in *.
  apply Rle_lt_trans with (K * Rabs (x - y)); [ apply Hlip | ].
  apply Rle_lt_trans with ((K + 1) * Rabs (x - y));
    [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | ].
  pose proof (Rmult_lt_compat_l (K + 1) (Rabs (x - y)) (eps / (K + 1)) ltac:(lra) Hdist) as Hm.
  replace ((K + 1) * (eps / (K + 1))) with eps in Hm by (field; lra); exact Hm.
Qed.

(* ----------------------------------------------------------------- *)
(*  The Lipschitz constant integrand mbnd = e^{−πx²}(2πx)².          *)
(* ----------------------------------------------------------------- *)

Definition mbnd (x : R) : R := exp_pi x * (2 * PI * x) ^ 2.

Lemma cont_mbnd : continuity mbnd.
Proof.
  intro x; unfold mbnd; apply continuity_pt_mult; [ apply cont_exp_pi | ].
  apply (cont_pow (fun y => 2 * PI * y) 2); intro y;
    apply (continuity_pt_scal (fun z => z) (2 * PI) y); apply cont_id.
Qed.

Lemma mbnd_int : forall a b, Riemann_integrable mbnd a b.
Proof.
  intros a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_mbnd ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_mbnd ].
Qed.

Lemma fsin_diff_bound : forall y s x, Rabs (fsin s x - fsin y x) <= mbnd x * Rabs (s - y).
Proof.
  intros y s x; unfold fsin, mbnd.
  replace (- (2 * PI * x * exp_pi x) * sin (2 * PI * x * s)
           - - (2 * PI * x * exp_pi x) * sin (2 * PI * x * y))
    with (- (2 * PI * x * exp_pi x) * (sin (2 * PI * x * s) - sin (2 * PI * x * y))) by ring.
  rewrite Rabs_mult, Rabs_Ropp.
  apply Rle_trans with (Rabs (2 * PI * x * exp_pi x) * Rabs (2 * PI * x * s - 2 * PI * x * y)).
  - apply Rmult_le_compat_l; [ apply Rabs_pos | apply sin_lipschitz ].
  - replace (2 * PI * x * s - 2 * PI * x * y) with (2 * PI * x * (s - y)) by ring.
    rewrite (Rabs_mult (2 * PI * x) (exp_pi x)), (Rabs_mult (2 * PI * x) (s - y)),
            (Rabs_pos_eq (exp_pi x)) by (left; unfold exp_pi; apply exp_pos).
    apply Req_le.
    assert (Hsq : Rabs (2 * PI * x) * Rabs (2 * PI * x) = (2 * PI * x) ^ 2)
      by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring).
    replace (Rabs (2 * PI * x) * exp_pi x * (Rabs (2 * PI * x) * Rabs (s - y)))
      with (exp_pi x * (Rabs (2 * PI * x) * Rabs (2 * PI * x)) * Rabs (s - y)) by ring.
    rewrite Hsq; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  S_deriv · n is Lipschitz in the parameter, hence continuous.     *)
(* ----------------------------------------------------------------- *)

Lemma S_deriv_lip : forall n y s,
  Rabs (S_deriv s n - S_deriv y n) <= RiemannInt (mbnd_int (- INR n) (INR n)) * Rabs (s - y).
Proof.
  intros n y s.
  assert (HAA : - INR n <= INR n) by (pose proof (pos_INR n); lra).
  set (dd := fun x => fsin s x - fsin y x).
  assert (prdd : Riemann_integrable dd (- INR n) (INR n))
    by (apply continuity_implies_RiemannInt; [ exact HAA | intros x _; unfold dd;
        apply continuity_pt_minus; apply cont_fsin ]).
  assert (Hlin : S_deriv s n - S_deriv y n = RiemannInt prdd).
  { assert (prg : Riemann_integrable (fun x => fsin s x + (-1) * fsin y x) (- INR n) (INR n))
      by (apply continuity_implies_RiemannInt; [ exact HAA | intros x _; apply continuity_pt_plus;
          [ apply cont_fsin | apply (continuity_pt_scal (fsin y) (-1) x); apply cont_fsin ] ]).
    pose proof (RiemannInt_P13 (fsin_int s (- INR n) (INR n)) (fsin_int y (- INR n) (INR n)) prg) as HP.
    assert (Hdg : RiemannInt prdd = RiemannInt prg)
      by (apply RiemannInt_P18; [ exact HAA | intros x _; unfold dd; ring ]).
    unfold S_deriv; rewrite Hdg, HP; ring. }
  assert (prTM : Riemann_integrable (fun x => Rabs (s - y) * mbnd x) (- INR n) (INR n))
    by (apply continuity_implies_RiemannInt; [ exact HAA | intros x _;
        apply (continuity_pt_scal mbnd (Rabs (s - y)) x); apply cont_mbnd ]).
  rewrite Hlin.
  apply Rle_trans with (RiemannInt (RiemannInt_P16 prdd)); [ apply RiemannInt_P17; exact HAA | ].
  apply Rle_trans with (RiemannInt prTM).
  - apply RiemannInt_P19; [ exact HAA | intros x _; unfold dd ].
    apply Rle_trans with (mbnd x * Rabs (s - y)); [ apply fsin_diff_bound | apply Req_le; ring ].
  - rewrite (RInt_scal_cont mbnd (Rabs (s - y)) (- INR n) (INR n) HAA cont_mbnd (mbnd_int (- INR n) (INR n)) prTM).
    apply Req_le; ring.
Qed.

Lemma S_deriv_cont : forall n, continuity (fun s => S_deriv s n).
Proof.
  intros n y.
  apply (lipschitz_continuity (fun s => S_deriv s n) y (RiemannInt (mbnd_int (- INR n) (INR n)))).
  - apply (nonneg_int mbnd (- INR n) (INR n)); [ pose proof (pos_INR n); lra | intros x _; unfold mbnd;
      apply Rmult_le_pos; [ left; unfold exp_pi; apply exp_pos | nra ] ].
  - intro s; apply S_deriv_lip.
Qed.

(* ----------------------------------------------------------------- *)
(*  F'(ξ) = g(ξ).                                                    *)
(* ----------------------------------------------------------------- *)

Theorem fourier_deriv : forall xi, derivable_pt_lim F_transform xi (g_deriv xi).
Proof.
  intro xi; assert (Hr : 0 < 1) by lra.
  assert (Hcvu : CVU (fun n s => S_deriv s n) g_deriv xi (mkposreal 1 Hr)).
  { intros e He; destruct (g_deriv_cvu e He) as [N HN]; exists N; intros n y Hn _; apply HN; exact Hn. }
  apply (derivable_pt_lim_CVU (fun n s => S_transform s n) (fun n s => S_deriv s n)
           F_transform g_deriv xi xi (mkposreal 1 Hr)).
  - unfold Boule; simpl; replace (xi - xi) with 0 by ring; rewrite Rabs_R0; exact Hr.
  - intros y n _; exact (leibniz_bounded (INR n) y (pos_INR n)).
  - intros y _; exact (F_transform_cv y).
  - exact Hcvu.
  - apply (CVU_continuity (fun n s => S_deriv s n) g_deriv xi (mkposreal 1 Hr) Hcvu).
    intros n y _; apply S_deriv_cont.
Qed.

Print Assumptions fourier_deriv.

(* ================================================================= *)
(*  END GaussLeibnizCVU.v (Phase 3)                                 *)
(*  F'(ξ) = g(ξ): the improper Fourier cosine transform of the         *)
(*  Gaussian is differentiable with derivative the sin-transform.      *)
(*  Next (Phase 4): the ODE identity g(ξ) = −2πξ·F(ξ) (integration by   *)
(*  parts), then Phase 5 (gaussian_ode_unique) closes the self-duality.*)
(* ================================================================= *)
