/-
  TDLean.PNT.Substitution -- C10, part 4: the change of variable `x = eᵗ`.

  `∫₁^∞ ψ(x) x^{−s−1} dx = ∫₀^∞ ψ(eᵗ) e^{−st} dt`, which turns the Mellin representation
  into a Laplace transform and so lets Newman's theorem apply.

  **Why the Jacobian form.** The natural tool, `integral_comp_smul_deriv_Ioi`, requires
  `ContinuousOn g (f '' Ioi a)` — and `ψ` is a *step* function, so that hypothesis fails.
  `integral_image_eq_integral_abs_deriv_smul` (`MeasureTheory/Function/JacobianOneDim.lean:66`)
  asks nothing of `g` at all, which is exactly what a step function needs. This is the same
  obstruction that forced Newman itself off `Continuous f` in Phase 0.
-/
import TDLean.PNT.Mellin
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace TDLean.PNT

open MeasureTheory TDLean.Zeta

theorem exp_image_Ioi_zero : Real.exp '' (Set.Ioi (0 : ℝ)) = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using Real.exp_lt_exp.mpr (Set.mem_Ioi.mp ht)
  · intro hx
    have hx1 : (1 : ℝ) < x := Set.mem_Ioi.mp hx
    exact ⟨Real.log x, Real.log_pos hx1, Real.exp_log (by linarith)⟩

/-- `(eᵗ : ℂ)^w = exp(t·w)`. -/
theorem ofReal_exp_cpow (t : ℝ) (w : ℂ) :
    (((Real.exp t : ℝ)) : ℂ) ^ w = Complex.exp ((t : ℂ) * w) := by
  have ht0 : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hne : (((Real.exp t : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hlog : Complex.log (((Real.exp t : ℝ)) : ℂ) = (t : ℂ) := by
    rw [Complex.log, Complex.arg_ofReal_of_nonneg ht0.le]
    simp [Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero hne, hlog]

/-- **Change of variable.** -/
theorem mellin_change_of_variable (s : ℂ) :
    (∫ x in Set.Ioi (1 : ℝ), ((x : ℂ) ^ (-s - 1)) * ((psi x : ℝ) : ℂ))
      = ∫ t in Set.Ioi (0 : ℝ),
          Complex.exp (-s * (t : ℂ)) * ((psi (Real.exp t) : ℝ) : ℂ) := by
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt Real.exp (Real.exp t) (Set.Ioi (0 : ℝ)) t :=
    fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.Ioi (0 : ℝ)) := Real.exp_injective.injOn
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    measurableSet_Ioi hderiv hinj
    (fun x : ℝ => ((x : ℂ) ^ (-s - 1)) * ((psi x : ℝ) : ℂ))
  rw [exp_image_Ioi_zero] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have ht0 : (0 : ℝ) < Real.exp t := Real.exp_pos t
  rw [abs_of_pos ht0]
  show ((Real.exp t : ℝ) : ℂ)
      * ((((Real.exp t : ℝ)) : ℂ) ^ (-s - 1) * ((psi (Real.exp t) : ℝ) : ℂ))
    = Complex.exp (-s * (t : ℂ)) * ((psi (Real.exp t) : ℝ) : ℂ)
  rw [ofReal_exp_cpow, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  have harg : (t : ℂ) + (t : ℂ) * (-s - 1) = -s * (t : ℂ) := by ring
  rw [harg]

end TDLean.PNT
