/-
  TDLean.FE.Mellin.Split -- cluster A9: the change of variable `t ↦ 1/u` on `(0,1)`.

      ∫₀¹ ψ(t)·t^{s/2−1} dt = ∫₁^∞ ψ(1/u)·u^{−s/2−1} du

  This is the step that folds the half of the Mellin integral near `0` — where `ψ` blows up
  and nothing converges — onto `(1,∞)`, where `ψ` decays like `e^{−πt}`. Combined with
  `psiTheta_transform` it turns the bad half into the pole terms plus an `s ↦ 1−s` copy of
  the good half, which is the whole content of the functional equation.

  **Why the Jacobian form.** `integral_comp_smul_deriv_Ioi` wants `ContinuousOn g` on the
  image; here `g` involves `psiTheta`, whose continuity is not in hand. As in
  `PNT/Substitution.lean`, `integral_image_eq_integral_abs_deriv_smul` asks nothing of `g`.
-/
import TDLean.FE.Mellin.Completed
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace TDLean.FE

open Complex Real MeasureTheory Set

/-- Inversion carries `(1,∞)` onto `(0,1)`. -/
theorem inv_image_Ioi_one : (fun u : ℝ => 1 / u) '' (Ioi (1 : ℝ)) = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := by linarith
    exact ⟨by positivity, by rw [div_lt_one hu0]; linarith⟩
  · rintro ⟨hx0, hx1⟩
    refine ⟨1 / x, ?_, ?_⟩
    · simp only [Set.mem_Ioi]
      rw [lt_div_iff₀ hx0]
      linarith
    · field_simp

/-- `(1/u)^w = u^{−w}` for `u > 0`: no branch conditions, because the base is a positive real
    and `cpow_pos_eq_exp` reduces both sides to `exp` of a real logarithm. -/
theorem inv_cpow_ofReal {u : ℝ} (hu : 0 < u) (w : ℂ) :
    ((1 / u : ℝ) : ℂ) ^ w = ((u : ℝ) : ℂ) ^ (-w) := by
  have hinv : (0 : ℝ) < 1 / u := by positivity
  rw [cpow_pos_eq_exp hinv, cpow_pos_eq_exp hu]
  congr 1
  rw [one_div, Real.log_inv]
  push_cast
  ring

/-- The Jacobian `1/u²` as a complex power. -/
theorem ofReal_sq_inv_eq_cpow {u : ℝ} (hu : 0 < u) :
    (((u ^ 2)⁻¹ : ℝ) : ℂ) = ((u : ℝ) : ℂ) ^ (-2 : ℂ) := by
  have hne : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  ring

/-- The derivative of `u ↦ 1/u` on `(1,∞)`. Exposed because both the integral identity and
    the integrability transfer need it. -/
theorem hasDerivWithinAt_inv_Ioi_one {u : ℝ} (hu : u ∈ Ioi (1 : ℝ)) :
    HasDerivWithinAt (fun y : ℝ => 1 / y) (-(u ^ 2)⁻¹) (Ioi (1 : ℝ)) u := by
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu1; linarith
  simp only [one_div]
  exact (hasDerivAt_inv hu0).hasDerivWithinAt

theorem injOn_inv_Ioi_one : Set.InjOn (fun u : ℝ => 1 / u) (Ioi (1 : ℝ)) := by
  intro a _ b _ hab
  simp only [one_div] at hab
  exact inv_injective hab

/-- **The change of variable.** The Mellin integral over `(0,1)` equals an integral over
    `(1,∞)` of `ψ(1/u)`, with the exponent reflected from `s/2−1` to `−s/2−1`. -/
theorem integral_Ioo_eq_integral_Ioi_inv (s : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (s / 2 - 1) * psiTheta t)
      = ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-s / 2 - 1) * psiTheta (1 / u) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun y : ℝ => 1 / y)
    (f' := fun u : ℝ => -(u ^ 2)⁻¹) measurableSet_Ioi
    (fun u hu => hasDerivWithinAt_inv_Ioi_one hu) injOn_inv_Ioi_one
    (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * psiTheta t)
  rw [inv_image_Ioi_one] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hne : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (u ^ 2)⁻¹)]
  -- `Complex.real_smul` will not `rw` here: the `SMul ℝ ℂ` instance the Jacobian lemma
  -- produces is defeq to, but not syntactically, the one the lemma is stated with.
  -- `show` lets defeq do the work instead.
  change (((u ^ 2)⁻¹ : ℝ) : ℂ) * (((1 / u : ℝ) : ℂ) ^ (s / 2 - 1) * psiTheta (1 / u))
      = (u : ℂ) ^ (-s / 2 - 1) * psiTheta (1 / u)
  rw [inv_cpow_ofReal hu0, ofReal_sq_inv_eq_cpow hu0, ← mul_assoc,
    ← Complex.cpow_add _ _ hne]
  congr 2
  ring

end TDLean.FE
