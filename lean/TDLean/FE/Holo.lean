/-
  TDLean.FE.Holo -- cluster A14: `Λ` is holomorphic off `{0, 1}`.

  The tail transform `M(w) := ∫₁^∞ u^w·ψ(u) du` is **entire**, by differentiation under the
  integral sign. The `w`-derivative of `u^w` is `log u·u^w`, so the dominating function picks
  up a `log u` — absorbed by `log u ≤ u` on `[1,∞)`, which just shifts the exponent by one and
  lands back in `integrableOn_rpow_mul_exp_neg_pi`. The exponential decay of `ψ` then covers
  every exponent, so no half-plane restriction survives: `M` is entire, full stop.

  Since `Λ(s) = 1/(s−1) − 1/s + M(s/2−1) + M((1−s)/2−1)`, that makes `Λ` holomorphic on
  `ℂ \ {0,1}`. This is what the identity theorem needs in order to push
  `Λ(s) = π^{−s/2}Γ(s/2)ζ(s)` from `Re s > 1` down into the critical strip.
-/
import TDLean.FE.Strip
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace TDLean.FE

open Complex Real MeasureTheory Set

theorem log_le_self {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ u := by
  have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < u)
  linarith

theorem log_nonneg_of_one_le {u : ℝ} (hu : 1 ≤ u) : 0 ≤ Real.log u :=
  Real.log_nonneg hu

/-- The `log`-weighted decay integral. `log u ≤ u` on `[1,∞)` shifts the exponent by one. -/
theorem integrableOn_log_mul_rpow_mul_exp_neg_pi (σ : ℝ) :
    IntegrableOn (fun u : ℝ => Real.log u * (u ^ σ * Real.exp (-(π * u)))) (Ioi (1 : ℝ)) := by
  refine Integrable.mono' (integrableOn_rpow_mul_exp_neg_pi (σ + 1)) ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine ContinuousOn.mul (Real.continuousOn_log.mono ?_) ?_
    · intro u hu
      exact ne_of_gt (by linarith [mem_Ioi.mp hu] : (0 : ℝ) < u)
    · refine ContinuousOn.mul ?_ (Real.continuous_exp.comp (by fun_prop)).continuousOn
      exact ContinuousOn.rpow_const continuousOn_id fun u hu =>
        Or.inl (by linarith [mem_Ioi.mp hu])
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hu0 : (0 : ℝ) < u := by linarith
    have hlog : 0 ≤ Real.log u := log_nonneg_of_one_le hu1
    have hexp : (0 : ℝ) < Real.exp (-(π * u)) := Real.exp_pos _
    have hrpow : (0 : ℝ) < u ^ σ := Real.rpow_pos_of_pos hu0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.log u * (u ^ σ * Real.exp (-(π * u)))
        ≤ u * (u ^ σ * Real.exp (-(π * u))) := by
          exact mul_le_mul_of_nonneg_right (log_le_self hu1) (by positivity)
      _ = u ^ (σ + 1) * Real.exp (-(π * u)) := by
          rw [Real.rpow_add hu0, Real.rpow_one]
          ring

theorem aestronglyMeasurable_ofReal_log :
    AEStronglyMeasurable (fun u : ℝ => ((Real.log u : ℝ) : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) := by
  refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
  exact Complex.continuous_ofReal.comp_continuousOn
    (Real.continuousOn_log.mono fun u hu =>
      ne_of_gt (by linarith [mem_Ioi.mp hu] : (0 : ℝ) < u))

theorem aestronglyMeasurable_cpow_Ioi_one (w : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ w) (volume.restrict (Ioi (1 : ℝ))) := by
  refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
  refine ContinuousOn.cpow_const ?_ (fun u hu => Or.inl ?_)
  · exact Complex.continuous_ofReal.continuousOn.comp continuousOn_id fun _ _ => trivial
  · simpa using (by linarith [mem_Ioi.mp hu] : (0 : ℝ) < u)

/-- The complex form: `log u · u^w · ψ(u)` is integrable on `(1,∞)` for every `w`. -/
theorem integrableOn_log_mul_cpow_mul_psiTheta (w : ℂ) :
    IntegrableOn (fun u : ℝ => ((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ w * psiTheta u)
      (Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ w * psiTheta u)
      (volume.restrict (Ioi (1 : ℝ))) :=
    (aestronglyMeasurable_ofReal_log.mul (aestronglyMeasurable_cpow_Ioi_one w)).mul
      (aestronglyMeasurable_psiTheta.mono_set (Ioi_subset_Ioi (by norm_num)))
  refine Integrable.mono'
    ((integrableOn_log_mul_rpow_mul_exp_neg_pi w.re).const_mul psiBound) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
  have hu0 : (0 : ℝ) < u := by linarith
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (log_nonneg_of_one_le hu1)]
  calc Real.log u * u ^ w.re * ‖psiTheta u‖
      ≤ Real.log u * u ^ w.re * (psiBound * Real.exp (-(π * u))) := by
        refine mul_le_mul_of_nonneg_left (norm_psiTheta_le hu1) ?_
        exact mul_nonneg (log_nonneg_of_one_le hu1) (Real.rpow_nonneg hu0.le _)
    _ = psiBound * (Real.log u * (u ^ w.re * Real.exp (-(π * u)))) := by ring

/-! ### The tail transform and its derivative -/

/-- `M(w) = ∫₁^∞ u^w·ψ(u) du`. -/
noncomputable def mellinTail (w : ℂ) : ℂ := ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ w * psiTheta u

/-- **Differentiation under the integral sign.** -/
theorem hasDerivAt_mellinTail (w : ℂ) :
    HasDerivAt mellinTail
      (∫ u in Ioi (1 : ℝ), ((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ w * psiTheta u) w := by
  have hball : Metric.ball w 1 ∈ nhds w := Metric.ball_mem_nhds w one_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (u : ℝ) => (u : ℂ) ^ x * psiTheta u)
    (F' := fun (x : ℂ) (u : ℝ) => ((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ x * psiTheta u)
    (bound := fun u : ℝ =>
      psiBound * (Real.log u * (u ^ (w.re + 1) * Real.exp (-(π * u)))))
    hball ?_ (integrableOn_cpow_mul_psiTheta w)
    (integrableOn_log_mul_cpow_mul_psiTheta w).aestronglyMeasurable ?_
    ((integrableOn_log_mul_rpow_mul_exp_neg_pi (w.re + 1)).const_mul psiBound) ?_).2
  · filter_upwards with x
    exact (integrableOn_cpow_mul_psiTheta x).aestronglyMeasurable
  · -- the uniform bound on `ball w 1`
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x hx
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hu0 : (0 : ℝ) < u := by linarith
    have hre : x.re ≤ w.re + 1 := by
      have hd : ‖x - w‖ < 1 := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hx
      have := abs_re_le_norm (x - w)
      simp only [Complex.sub_re] at this
      have h2 : |x.re - w.re| < 1 := lt_of_le_of_lt this hd
      linarith [abs_lt.mp h2]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (log_nonneg_of_one_le hu1)]
    calc Real.log u * u ^ x.re * ‖psiTheta u‖
        ≤ Real.log u * u ^ (w.re + 1) * (psiBound * Real.exp (-(π * u))) := by
          refine mul_le_mul ?_ (norm_psiTheta_le hu1) (norm_nonneg _) ?_
          · exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hu1 hre) (log_nonneg_of_one_le hu1)
          · exact mul_nonneg (log_nonneg_of_one_le hu1) (Real.rpow_nonneg hu0.le _)
      _ = psiBound * (Real.log u * (u ^ (w.re + 1) * Real.exp (-(π * u)))) := by ring
  · -- the pointwise derivative
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x _
    have hu0 : (0 : ℝ) < u := by linarith [mem_Ioi.mp hu]
    have hne : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have hcpow : HasDerivAt (fun x : ℂ => ((u : ℝ) : ℂ) ^ x)
        (((u : ℝ) : ℂ) ^ x * Complex.log ((u : ℝ) : ℂ)) x := by
      simpa using (hasDerivAt_id x).const_cpow (Or.inl hne)
    have h2 := hcpow.mul_const (psiTheta u)
    have heq : ((u : ℝ) : ℂ) ^ x * Complex.log ((u : ℝ) : ℂ) * psiTheta u
        = ((Real.log u : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ x * psiTheta u := by
      rw [Complex.ofReal_log hu0.le]; ring
    rwa [heq] at h2

theorem differentiable_mellinTail : Differentiable ℂ mellinTail :=
  fun w => (hasDerivAt_mellinTail w).differentiableAt

/-! ### Hence `Λ` -/

/-- `Λ` in terms of the tail transform. -/
theorem completedZeta_eq_mellinTail (s : ℂ) :
    completedZeta s = 1 / (s - 1) - 1 / s + (mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1))
    := by
  rw [completedZeta, mellinTail, mellinTail,
    ← MeasureTheory.integral_add (integrableOn_cpow_mul_psiTheta (s / 2 - 1))
      (integrableOn_cpow_mul_psiTheta ((1 - s) / 2 - 1))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

/-- **`Λ` is holomorphic off `{0, 1}`.** -/
theorem differentiableAt_completedZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ completedZeta s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => 1 / (z - 1) - 1 / z
        + (mellinTail (z / 2 - 1) + mellinTail ((1 - z) / 2 - 1))) s := by
    refine DifferentiableAt.add (DifferentiableAt.sub ?_ ?_) (DifferentiableAt.add ?_ ?_)
    · exact (differentiableAt_const 1).div (differentiableAt_id.sub_const 1) hsub
    · exact (differentiableAt_const 1).div differentiableAt_id h0
    · -- pin `g` and `f` via the stated type: otherwise the elaborator unfolds `mellinTail`
      -- to its integral and tries to split the composition there
      have h : DifferentiableAt ℂ (mellinTail ∘ fun z : ℂ => z / 2 - 1) s :=
        DifferentiableAt.comp s (differentiable_mellinTail _)
          ((differentiableAt_id.div_const 2).sub_const 1)
      exact h
    · have h : DifferentiableAt ℂ (mellinTail ∘ fun z : ℂ => (1 - z) / 2 - 1) s :=
        DifferentiableAt.comp s (differentiable_mellinTail _)
          ((((differentiableAt_const 1).sub differentiableAt_id).div_const 2).sub_const 1)
      exact h
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall completedZeta_eq_mellinTail)

end TDLean.FE
