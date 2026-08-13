/-
  TDLean.FE.Mellin.Integrable -- cluster A11: the integrability bookkeeping.

  The assembly of the functional equation needs three integrability facts, and only the
  third is more than routine:

  * `integrableOn_rpow_mul_exp_neg_pi` — `u^σ e^{−πu}` on `(1,∞)` for **every** real `σ`.
    The `σ ≤ 0` case is not covered by `Mellin/Term.lean`'s `Re s > 1` machinery, so the
    proof dominates `u^σ` by `u^{max σ 0}` — valid precisely because `u ≥ 1`.
  * `integrableOn_cpow_mul_psiTheta` — `u^w ψ(u)` on `(1,∞)` for **every** complex `w`,
    by the decay bound. This is the one the reflected exponent `(1−s)/2 − 1` needs.
  * `integrableOn_mellin_Ioi_zero` — the original Mellin integrand on `(0,∞)` for `Re s > 1`,
    which is what lets the integral be split at `t = 1` at all.
-/
import TDLean.FE.Theta.Decay
import TDLean.FE.Mellin.Split

namespace TDLean.FE

open Complex Real MeasureTheory Set

/-- `u^σ·e^{−πu}` is integrable on `(1,∞)` for **every** real `σ` — including negative `σ`,
    where the `Re s > 1` Gamma machinery does not apply. -/
theorem integrableOn_rpow_mul_exp_neg_pi (σ : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ σ * Real.exp (-(π * u))) (Ioi (1 : ℝ)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set σ' : ℝ := max σ 0 with hσ'
  have hσ'0 : 0 ≤ σ' := le_max_right _ _
  have hmaj : IntegrableOn (fun u : ℝ => u ^ σ' * Real.exp (-(π * u))) (Ioi (1 : ℝ)) := by
    have h := integrableOn_real_term (σ := σ' + 1) (by linarith) hπ
    have h1 : IntegrableOn (fun t : ℝ => t ^ (σ' + 1 - 1) * Real.exp (-(π * t)))
        (Ioi (1 : ℝ)) := h.mono_set (Ioi_subset_Ioi (by norm_num))
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
    norm_num
  refine Integrable.mono' hmaj ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine ContinuousOn.mul ?_ (Real.continuous_exp.comp (by fun_prop)).continuousOn
    exact ContinuousOn.rpow_const continuousOn_id fun u hu =>
      Or.inl (by linarith [mem_Ioi.mp hu])
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hexp : (0 : ℝ) < Real.exp (-(π * u)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hu1 (le_max_left _ _))
      hexp.le

/-- **The key integrability fact.** `u^w·ψ(u)` is integrable on `(1,∞)` for **every** complex
    `w`. This is where the exponential decay of `ψ` earns its keep: no growth condition on
    `w` is needed, which is what the reflected exponent `(1−s)/2 − 1` requires. -/
theorem integrableOn_cpow_mul_psiTheta (w : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ w * psiTheta u) (Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ w * psiTheta u)
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine AEStronglyMeasurable.mul ?_
      (aestronglyMeasurable_psiTheta.mono_set (Ioi_subset_Ioi (by norm_num)))
    refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine ContinuousOn.cpow_const ?_ (fun u hu => Or.inl ?_)
    · exact Complex.continuous_ofReal.continuousOn.comp continuousOn_id fun _ _ => trivial
    · simpa using (by linarith [mem_Ioi.mp hu] : (0 : ℝ) < u)
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg_pi w.re).const_mul psiBound) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
  have hu0 : (0 : ℝ) < u := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  calc u ^ w.re * ‖psiTheta u‖
      ≤ u ^ w.re * (psiBound * Real.exp (-(π * u))) :=
        mul_le_mul_of_nonneg_left (norm_psiTheta_le hu1) (Real.rpow_nonneg hu0.le _)
    _ = psiBound * (u ^ w.re * Real.exp (-(π * u))) := by ring

/-! ### The folded integrand

    On `(1,∞)` the folded integrand splits, via `psiTheta_transform`, into the two elementary
    pole powers and one copy of the good integrand with the exponent reflected. Both halves
    are integrable — the second only because of the decay bound. -/

/-- The pointwise split of the folded integrand. -/
theorem folded_integrand_eq {s : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    (u : ℂ) ^ (-s / 2 - 1) * psiTheta (1 / u)
      = ((((Real.sqrt u : ℝ)) : ℂ) - 1) / 2 * (u : ℂ) ^ (-s / 2 - 1)
        + (u : ℂ) ^ ((1 - s) / 2 - 1) * psiTheta u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hne : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have h1 : (u : ℂ) ^ (1 / 2 : ℂ) * (u : ℂ) ^ (-s / 2 - 1) = (u : ℂ) ^ ((1 - s) / 2 - 1) := by
    rw [← Complex.cpow_add _ _ hne]
    congr 1
    ring
  rw [psiTheta_transform hu0, sqrt_eq_cpow_half hu0, ← h1]
  ring

/-- The elementary pole part is integrable on `(1,∞)` for `Re s > 1`. -/
theorem integrableOn_pole {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((((Real.sqrt u : ℝ)) : ℂ) - 1) / 2 * (u : ℂ) ^ (-s / 2 - 1))
      (Ioi (1 : ℝ)) := by
  have hre1 : (-s / 2 - 1 / 2).re < -1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
    linarith
  have hre2 : (-s / 2 - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
    linarith
  have hi1 := integrableOn_Ioi_cpow_of_lt hre1 (by norm_num : (0 : ℝ) < 1)
  have hi2 := integrableOn_Ioi_cpow_of_lt hre2 (by norm_num : (0 : ℝ) < 1)
  refine MeasureTheory.IntegrableOn.congr_fun
    ((hi1.const_mul (1 / 2 : ℂ)).sub (hi2.const_mul (1 / 2 : ℂ))) ?_ measurableSet_Ioi
  intro u hu
  exact (pole_integrand_eq (s := s) (by linarith [mem_Ioi.mp hu])).symm

/-- The folded integrand is integrable on `(1,∞)` for `Re s > 1`. -/
theorem integrableOn_folded {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s / 2 - 1) * psiTheta (1 / u)) (Ioi (1 : ℝ)) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_pole hs).add (integrableOn_cpow_mul_psiTheta ((1 - s) / 2 - 1)))
    ?_ measurableSet_Ioi
  intro u hu
  exact (folded_integrand_eq (s := s) (mem_Ioi.mp hu).le).symm

/-- Hence the Mellin integrand is integrable on `(0,1)` — obtained by transporting
    `integrableOn_folded` back along `u ↦ 1/u`, the same substitution as `Split.lean`. -/
theorem integrableOn_mellin_Ioo {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * psiTheta t) (Ioo (0 : ℝ) 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun y : ℝ => 1 / y)
    (f' := fun u : ℝ => -(u ^ 2)⁻¹) measurableSet_Ioi
    (fun u hu => hasDerivWithinAt_inv_Ioi_one hu) injOn_inv_Ioi_one
    (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * psiTheta t)
  rw [inv_image_Ioi_one] at h
  refine h.mpr (MeasureTheory.IntegrableOn.congr_fun (integrableOn_folded hs) ?_
    measurableSet_Ioi)
  intro u hu
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hne : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  -- the `EqOn` goal arrives with unreduced beta-redexes, which `rw` cannot see through
  dsimp only
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (u ^ 2)⁻¹)]
  change (u : ℂ) ^ (-s / 2 - 1) * psiTheta (1 / u)
      = (((u ^ 2)⁻¹ : ℝ) : ℂ) * (((1 / u : ℝ) : ℂ) ^ (s / 2 - 1) * psiTheta (1 / u))
  rw [inv_cpow_ofReal hu0, ofReal_sq_inv_eq_cpow hu0, ← mul_assoc,
    ← Complex.cpow_add _ _ hne]
  congr 2
  ring

end TDLean.FE
