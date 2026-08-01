(* ================================================================= *)
(*  GaussFourierCoeff.v  —  Poisson→θ P3 step 9: the Fourier cosine    *)
(*  coefficient of the 2π-rescaled periodization.                     *)
(*                                                                    *)
(*  acoef ftil m = (1/π) ∫_{−π}^{π} ftil(y) cos(m y) dy.               *)
(*  Substituting y = 2π x (cov_continuous, g = ·/2π) and using that    *)
(*  Θ_t(x)cos(2πx m) is 1-periodic (∫_{−1/2}^{1/2} = ∫₀¹) gives, with   *)
(*  coeff_true,   acoef ftil m = 2·(1/√t) e^{−πm²/t}.                  *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta GaussPeriodization GaussPeriodTotal GaussPeriodDeriv
        GaussPeriodDeriv2 GaussCoeffTrue ContinuousCoV GaussPiValue FourierKernelRep.
Open Scope R_scope.

Lemma RInt_bounds_eq : forall (f : R -> R) (a b a' b' : R)
  (pr : Riemann_integrable f a b) (pr' : Riemann_integrable f a' b'),
  a = a' -> b = b' -> RiemannInt pr = RiemannInt pr'.
Proof. intros f a b a' b' pr pr' Ha Hb; subst a' b'; apply RiemannInt_P5. Qed.

Section FourierCoeff.

Variable t : R.
Hypothesis Ht : 0 < t.

Notation Cft := (ftil_cont t Ht).

Definition fper (m : nat) (x : R) : R := GTheta t Ht x * cos (2 * PI * x * INR m).

Lemma cont_fper : forall m, continuity (fper m).
Proof.
  intros m x; unfold fper; apply continuity_pt_mult;
    [ apply (GTheta_cont t Ht) | apply cont_cosm ].
Qed.

Lemma fper_int : forall m a b, Riemann_integrable (fper m) a b.
Proof.
  intros m a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_fper ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_fper ].
Qed.

Lemma fper_per : forall m x, fper m (x + 1) = fper m x.
Proof.
  intros m x; unfold fper; rewrite (GTheta_periodic t Ht x); f_equal.
  replace (2 * PI * (x + 1) * INR m) with (2 * PI * x * INR m + 2 * INR m * PI) by ring.
  apply cos_period.
Qed.

Lemma twoPI_ne : 2 * PI <> 0. Proof. pose proof PI_RGT_0; apply Rgt_not_eq; lra. Qed.

Lemma cont_cosm' : forall m, continuity (fun x => cos (INR m * x)).
Proof.
  intros m x; apply (continuity_pt_comp (fun x => INR m * x) cos x).
  - apply (continuity_pt_scal (fun x => x) (INR m) x);
      apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - apply continuity_cos.
Qed.

(* --- the substitution map u ↦ u/(2π) as a C1_fun --- *)

Definition inv2pi : C1_fun :=
  mkC1 (c1 := fun u => u / (2 * PI))
       (diff0 := fun u => exist _ (/ (2 * PI)) (dcov u))
       (fun u => continuity_pt_const (fun _ => / (2 * PI)) u (fun a b => eq_refl)).
Lemma inv2pi_val : forall x, inv2pi x = x / (2 * PI). Proof. reflexivity. Qed.
Lemma inv2pi_der : forall x, derive inv2pi (diff0 inv2pi) x = / (2 * PI). Proof. reflexivity. Qed.

(* --- the change of variables:  ∫_{-π}^{π} ftil·cos = 2π ∫_{-1/2}^{1/2} Θ·cos --- *)

Lemma cov_step : forall m,
  RiemannInt (ri_fcos (ftil t Ht) Cft m) = 2 * PI * RiemannInt (fper_int m (- (1 / 2)) (1 / 2)).
Proof.
  intro m; pose proof PI_RGT_0 as HPI; pose proof twoPI_ne as Hne; assert (HPIne : PI <> 0) by (apply Rgt_not_eq; lra).
  assert (Hab : - PI <= PI) by lra.
  assert (Hmono : forall x, - PI <= x <= PI -> inv2pi (- PI) <= inv2pi x <= inv2pi (PI)).
  { intros x [Hx0 Hx1]; simpl; unfold Rdiv; split;
      apply Rmult_le_compat_r; try (left; apply Rinv_0_lt_compat; lra); lra. }
  assert (Hcont : forall u, inv2pi (- PI) <= u <= inv2pi (PI) -> continuity_pt (fper m) u)
    by (intros u _; apply cont_fper).
  assert (prL : Riemann_integrable
                  (fun x => fper m (inv2pi x) * derive inv2pi (diff0 inv2pi) x) (- PI) PI).
  { apply continuity_implies_RiemannInt; [ exact Hab | intros x _ ].
    apply continuity_pt_mult;
      [ apply (continuity_pt_comp inv2pi (fper m) x);
          [ apply derivable_continuous_pt; exists (/ (2 * PI)); apply dcov | apply cont_fper ]
      | apply continuity_pt_const; intros a b; reflexivity ]. }
  pose proof (cov_continuous inv2pi (fper m) (- PI) PI Hab Hmono Hcont prL (fper_int m (inv2pi (- PI)) (inv2pi (PI)))) as Hcov.
  (* RHS bounds: inv2pi (± PI) = ± 1/2 *)
  rewrite (RInt_bounds_eq (fper m) (inv2pi (- PI)) (inv2pi PI) (- (1 / 2)) (1 / 2)
             (fper_int m (inv2pi (- PI)) (inv2pi PI)) (fper_int m (- (1 / 2)) (1 / 2))
             ltac:(simpl; field; assumption) ltac:(simpl; field; assumption)) in Hcov.
  (* LHS: relate prL to /(2π)·ri_fcos *)
  assert (HL : RiemannInt prL = / (2 * PI) * RiemannInt (ri_fcos (ftil t Ht) Cft m)).
  { assert (prsc : Riemann_integrable
                     (fun x => / (2 * PI) * (ftil t Ht x * cos (INR m * x))) (- PI) PI)
      by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
          apply (continuity_pt_scal (fun x => ftil t Ht x * cos (INR m * x)) (/ (2 * PI)) x);
          apply continuity_pt_mult; [ apply Cft | apply cont_cosm' ] ]).
    assert (Heq : RiemannInt prL = RiemannInt prsc).
    { apply RiemannInt_P18; [ exact Hab | intros x _ ].
      rewrite inv2pi_der; unfold fper, ftil; rewrite !inv2pi_val.
      replace (2 * PI * (x / (2 * PI)) * INR m) with (INR m * x) by (field; assumption).
      field; assumption. }
    rewrite Heq.
    rewrite (RInt_scal_cont (fun x => ftil t Ht x * cos (INR m * x)) (/ (2 * PI)) (- PI) PI Hab
               ltac:(intro x; apply continuity_pt_mult; [ apply Cft | apply cont_cosm' ])
               (ri_fcos (ftil t Ht) Cft m) prsc); reflexivity. }
  rewrite HL in Hcov.
  (* Hcov : /(2π)·∫ftil·cos = ∫_{-1/2}^{1/2} Θ·cos ; solve for ∫ftil·cos *)
  apply Rmult_eq_reg_l with (/ (2 * PI)); [ | apply Rinv_neq_0_compat; exact Hne ].
  rewrite Hcov; field; assumption.
Qed.

(* --- the period shift  ∫_{-1/2}^{1/2} = ∫₀¹ --- *)

Lemma dshift : forall y, derivable_pt_lim (fun y => y - 1) y 1.
Proof.
  intro y; pose proof (derivable_pt_lim_minus (fun y => y) (fun _ => 1) y 1 0
    (derivable_pt_lim_id y) (derivable_pt_lim_const 1 y)) as H.
  replace (1 - 0) with 1 in H by ring; exact H.
Qed.

Definition shiftm1 : C1_fun :=
  mkC1 (c1 := fun y => y - 1) (diff0 := fun y => exist _ 1 (dshift y))
       (fun y => continuity_pt_const (fun _ => 1) y (fun a b => eq_refl)).
Lemma shiftm1_val : forall y, shiftm1 y = y - 1. Proof. reflexivity. Qed.
Lemma shiftm1_der : forall y, derive shiftm1 (diff0 shiftm1) y = 1. Proof. reflexivity. Qed.

Lemma shift_half : forall m,
  RiemannInt (fper_int m (- (1 / 2)) 0) = RiemannInt (fper_int m (1 / 2) 1).
Proof.
  intro m.
  assert (Hab : (1 / 2) <= 1) by lra.
  assert (Hmono : forall y, 1 / 2 <= y <= 1 -> shiftm1 (1 / 2) <= shiftm1 y <= shiftm1 1)
    by (intros y [Hy0 Hy1]; rewrite !shiftm1_val; lra).
  assert (Hcont : forall u, shiftm1 (1 / 2) <= u <= shiftm1 1 -> continuity_pt (fper m) u)
    by (intros u _; apply cont_fper).
  assert (prL : Riemann_integrable
                  (fun y => fper m (shiftm1 y) * derive shiftm1 (diff0 shiftm1) y) (1 / 2) 1).
  { apply continuity_implies_RiemannInt; [ lra | intros y _ ]; apply continuity_pt_mult;
      [ apply (continuity_pt_comp shiftm1 (fper m) y);
          [ apply derivable_continuous_pt; exists 1; apply dshift | apply cont_fper ]
      | apply continuity_pt_const; intros a b; reflexivity ]. }
  pose proof (cov_continuous shiftm1 (fper m) (1 / 2) 1 Hab Hmono Hcont prL
                (fper_int m (shiftm1 (1 / 2)) (shiftm1 1))) as Hcov.
  rewrite (RInt_bounds_eq (fper m) (shiftm1 (1 / 2)) (shiftm1 1) (- (1 / 2)) 0
             (fper_int m (shiftm1 (1 / 2)) (shiftm1 1)) (fper_int m (- (1 / 2)) 0)
             ltac:(rewrite shiftm1_val; lra) ltac:(rewrite shiftm1_val; lra)) in Hcov.
  assert (HL : RiemannInt prL = RiemannInt (fper_int m (1 / 2) 1)).
  { apply RiemannInt_P18; [ lra | intros y _ ].
    rewrite shiftm1_der, shiftm1_val, Rmult_1_r.
    rewrite <- (fper_per m (y - 1)); replace (y - 1 + 1) with y by ring; reflexivity. }
  rewrite <- Hcov; exact HL.
Qed.

Lemma period_shift : forall m,
  RiemannInt (fper_int m (- (1 / 2)) (1 / 2)) = RiemannInt (fper_int m 0 1).
Proof.
  intro m.
  pose proof (RiemannInt_P26 (fper_int m (- (1 / 2)) 0) (fper_int m 0 (1 / 2))
                (fper_int m (- (1 / 2)) (1 / 2))) as HA.
  pose proof (RiemannInt_P26 (fper_int m 0 (1 / 2)) (fper_int m (1 / 2) 1)
                (fper_int m 0 1)) as HB.
  pose proof (shift_half m) as HS; lra.
Qed.

(* --- the coefficient value --- *)

Theorem acoef_value : forall m,
  acoef (ftil t Ht) Cft m = 2 * (/ sqrt t * exp (- (PI * INR m ^ 2 / t))).
Proof.
  intro m; unfold acoef.
  rewrite cov_step, period_shift.
  assert (Hv : RiemannInt (fper_int m 0 1) = / sqrt t * exp (- (PI * INR m ^ 2 / t)))
    by exact (coeff_true t Ht m (fper_int m 0 1)).
  rewrite Hv; field; split;
    [ apply Rgt_not_eq; apply sqrt_lt_R0; exact Ht | apply Rgt_not_eq; apply PI_RGT_0 ].
Qed.

End FourierCoeff.

Print Assumptions acoef_value.

(* ================================================================= *)
(*  END GaussFourierCoeff.v                                          *)
(*  acoef ftil m = 2·(1/√t) e^{−πm²/t}.                              *)
(* ================================================================= *)
