/-
  TDLean.PNT.GNewman -- C10, part 7: `g z = ∫₀^∞ f(t) e^{−zt} dt`, Newman's Laplace pair.

  Assembles `LS_LamC_eq_mellin`, `mellin_change_of_variable`, `psi_exp_eq` and
  `integral_cexp_neg_Ioi` into the two hypotheses Newman needs about `g`:
  it is the Laplace transform of `f` on `Re z > 0`, and (next file) it extends past the axis.

  The algebra, with `s = z+1` and `Φ⁻(s) = −ζ′/ζ(s) − 1/(s−1)`:

      Φ(s) = s·(g(s−1) + 1/(s−1))   ⟹   g(z) = (Φ⁻(z+1) − 1)/(z+1)

  so the pole at `s = 1` cancels exactly, which is the whole point.
-/
import TDLean.PNT.NewmanInput
import TDLean.Zeta.PhiHolo

namespace TDLean.PNT

open MeasureTheory TDLean.Zeta

/-! ### Measurability and integrability of `f(t)e^{−zt}` -/

theorem measurable_fNewman : Measurable fNewman := by
  have h1 : Measurable (fun t : ℝ => psi (Real.exp t)) :=
    measurable_psi.comp Real.continuous_exp.measurable
  have h2 : Measurable (fun t : ℝ => Real.exp (-t)) := by fun_prop
  exact (h1.mul h2).sub measurable_const

theorem measurable_fNewmanC : Measurable fNewmanC :=
  Complex.measurable_ofReal.comp measurable_fNewman

/-- **Newman's integrability hypothesis**, discharged. -/
theorem integrableOn_fNewman_exp {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => fNewmanC t * Complex.exp (-z * (t : ℂ))) (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => fNewmanC t * Complex.exp (-z * (t : ℂ))) (volume.restrict (Set.Ioi 0)) := by
    refine (measurable_fNewmanC.aestronglyMeasurable).mul ?_
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hdom : IntegrableOn
      (fun t : ℝ => (Ccheb + 1) * ‖Complex.exp (-z * (t : ℂ))‖) (Set.Ioi 0) :=
    ((integrableOn_cexp_neg hz).norm).const_mul _
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_fNewmanC_le (le_of_lt (Set.mem_Ioi.mp ht)))
    (norm_nonneg _)

/-! ### Splitting off the `+1` -/

theorem laplace_pointwise (z : ℂ) (t : ℝ) :
    Complex.exp (-(z + 1) * (t : ℂ)) * ((psi (Real.exp t) : ℝ) : ℂ)
      = fNewmanC t * Complex.exp (-z * (t : ℂ)) + Complex.exp (-z * (t : ℂ)) := by
  rw [psi_exp_eq]
  have hre : Complex.exp (-(z + 1) * (t : ℂ)) * ((fNewmanC t + 1) * Complex.exp ((t : ℂ)))
      = (fNewmanC t + 1) * (Complex.exp (-(z + 1) * (t : ℂ)) * Complex.exp ((t : ℂ))) := by
    ring
  rw [hre, ← Complex.exp_add]
  have harg : -(z + 1) * (t : ℂ) + (t : ℂ) = -z * (t : ℂ) := by ring
  rw [harg]
  ring

theorem mellin_eq_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(z + 1) * (t : ℂ)) * ((psi (Real.exp t) : ℝ) : ℂ))
      = (∫ t in Set.Ioi (0 : ℝ), fNewmanC t * Complex.exp (-z * (t : ℂ))) + 1 / z := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => laplace_pointwise z t),
    integral_add (integrableOn_fNewman_exp hz) (integrableOn_cexp_neg hz),
    integral_cexp_neg_Ioi hz]

/-! ### The Laplace pair -/

/-- Newman's `g`: the analytic continuation of the Laplace transform of `f`. -/
noncomputable def gNewman (z : ℂ) : ℂ := (PhiMinus (z + 1) - 1) / (z + 1)

/-- **`g` is the Laplace transform of `f` on the right half-plane.** -/
theorem gNewman_eq {z : ℂ} (hz : 0 < z.re) :
    gNewman z = ∫ t in Set.Ioi (0 : ℝ), fNewmanC t * Complex.exp (-z * (t : ℂ)) := by
  have hs : 1 < (z + 1).re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    rw [this] at hs; linarith
  have hmellin := LS_LamC_eq_mellin hs
  rw [mellin_change_of_variable, mellin_eq_laplace hz] at hmellin
  have hphi := PhiMinus_eq hs
  rw [show (z + 1) - 1 = z by ring] at hphi
  rw [gNewman, hphi, hmellin]
  field_simp
  ring

end TDLean.PNT
