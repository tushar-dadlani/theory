/-
  TDLean.Newman.Winding -- Brick C5.

  ORACLE: spectral-theory/CTruncWind.v : trunc_winding
  Claim: `∮_C dz/z = 2πi` over Zagier's truncated contour `C` (arc from `-α` to `α` on
  `|z| = R`, then the chord back), for `α ∈ (π/2, π)`.

  ## Why this does not need the keystone C4

  The planned route was to deform `C` to the full circle, which needs a Cauchy theorem on a
  convex region (brick C4). That is unnecessary here. On the chord, `Re z = R cos α < 0`,
  and on the half-plane `Re z < 0` the function `log (-z)` is a genuine primitive of `1/z`:
  `-z` then has positive real part, so it lies in mathlib's `slitPlane` and the principal
  branch is holomorphic there. The chord never meets the branch cut.

  So C5 follows from C3 (the loop FTC) alone:
    * arc:   the integrand collapses to the constant `I`, giving `2αi`;
    * chord: FTC with the primitive `log (-·)`, giving `log(-bot) - log(-top) = 2(π-α)i`.
  Total `2αi + 2(π-α)i = 2πi`.

  The Coq proof (254 lines) computes the chord with `arctan` antiderivatives precisely
  because it has no complex `log`. Recorded in LEDGER.md.
-/
import TDLean.Newman.Contour
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TDLean.Newman

open Complex Set intervalIntegral Real

/-! ### A primitive of `1/z` on the left half-plane -/

/-- On `Re z < 0`, `log (-z)` is a primitive of `z⁻¹`. The point of the sign: `-z` has
    positive real part, hence lies in `slitPlane`, so the principal branch is holomorphic
    at `-z` and the chord never meets the branch cut. -/
theorem hasDerivAt_logNeg {z : ℂ} (hz : z.re < 0) :
    HasDerivAt (fun w : ℂ => Complex.log (-w)) z⁻¹ z := by
  have hmem : (-z) ∈ Complex.slitPlane := by
    refine Or.inl ?_
    simpa using hz
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have := hneg.clog (by simpa using hmem)
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  simpa [neg_div_neg_eq, one_div] using this

/-! ### The arc contributes `2αi` -/

/-- On the arc the integrand `γ' · (1/γ)` collapses to the constant `I`. -/
theorem arcIntegral_inv {R : ℝ} (hR : R ≠ 0) (α : ℝ) :
    arcIntegral (fun z => z⁻¹) R α = (2 * α : ℝ) * I := by
  have hne : ∀ θ : ℝ, circleMap 0 R θ ≠ 0 := fun θ => circleMap_ne_center hR
  have : ∀ θ : ℝ, deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹ = I := by
    intro θ
    rw [deriv_circleMap, mul_comm (circleMap 0 R θ) I, mul_assoc,
      mul_inv_cancel₀ (hne θ), mul_one]
  rw [arcIntegral]
  simp only [this]
  rw [intervalIntegral.integral_const]
  -- `intervalIntegral.integral_const` produces the `ℝ`-on-`ℂ` action through
  -- `SMulZeroClass.toSMul`, which neither `rw` nor `simp` will unify with
  -- `Complex.real_smul`. The two actions are definitionally equal, so `show` cuts through.
  change ((α - -α : ℝ) : ℂ) * I = _
  push_cast
  ring

/-! ### The chord contributes `2(π-α)i` -/

/-- The real part of a point on the circle. -/
theorem circleMap_re (R θ : ℝ) : (circleMap 0 R θ).re = R * Real.cos θ := by
  simp [circleMap, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- Both chord endpoints have real part `R cos α`, so the whole chord does. -/
theorem chord_re_eq {R α : ℝ} (t : ℝ) :
    (chord (arcTop R α) (arcBot R α) t).re = R * Real.cos α := by
  have htop : (arcTop R α).re = R * Real.cos α := circleMap_re R α
  have hbot : (arcBot R α).re = R * Real.cos α := by
    rw [arcBot, circleMap_re, Real.cos_neg]
  simp [chord, chordC, Complex.add_re, Complex.mul_re, htop, hbot]

/-- `-arcTop R α = R e^{i(α-π)}`. -/
theorem neg_arcTop {R α : ℝ} : -arcTop R α = circleMap 0 R (α - π) := by
  have h : Complex.exp (((α : ℂ) - (π : ℂ)) * I) = -Complex.exp ((α : ℂ) * I) := by
    rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]
  simp only [arcTop, circleMap, Complex.ofReal_sub, zero_add]
  rw [h]; ring

/-- `-arcBot R α = R e^{i(π-α)}`. -/
theorem neg_arcBot {R α : ℝ} : -arcBot R α = circleMap 0 R (π - α) := by
  have h : Complex.exp (((π : ℂ) - (α : ℂ)) * I) = -Complex.exp ((-(α : ℂ)) * I) := by
    rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I, neg_mul, Complex.exp_neg]
    simp [div_eq_mul_inv]
  simp only [arcBot, circleMap, Complex.ofReal_sub, Complex.ofReal_neg, zero_add]
  rw [h]; ring

/-- `arg (R e^{iθ}) = θ` for `R > 0` and `θ ∈ (-π, π]`. -/
theorem arg_circleMap {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioc (-π) π) :
    (circleMap 0 R θ).arg = θ := by
  have : circleMap 0 R θ = (R : ℂ) * (Complex.cos θ + Complex.sin θ * I) := by
    simp [circleMap, Complex.exp_mul_I]
  rw [this, Complex.arg_real_mul _ hR, Complex.arg_cos_add_sin_mul_I hθ]

theorem chordIntegral_inv {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π) :
    chordIntegral (fun z => z⁻¹) (arcTop R α) (arcBot R α) = (2 * (π - α) : ℝ) * I := by
  have hcos : Real.cos α < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hα (by linarith [Real.pi_pos])
  have hre : ∀ z ∈ chordSet (arcTop R α) (arcBot R α), z.re < 0 := by
    rintro z ⟨t, -, rfl⟩
    rw [chord_re_eq]
    exact mul_neg_of_pos_of_neg hR hcos
  have hne : ∀ z ∈ chordSet (arcTop R α) (arcBot R α), z ≠ 0 := by
    intro z hz h
    have hlt := hre z hz
    rw [h] at hlt
    simp at hlt
  -- FTC with the primitive `log (-·)`
  have hF : ∀ z ∈ chordSet (arcTop R α) (arcBot R α),
      HasDerivAt (fun w : ℂ => Complex.log (-w)) z⁻¹ z := fun z hz => hasDerivAt_logNeg (hre z hz)
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) (chordSet (arcTop R α) (arcBot R α)) :=
    fun z hz => (continuousAt_inv₀ (hne z hz)).continuousWithinAt
  rw [chordIntegral_eq_sub hF hcont]
  -- evaluate the two logs
  have hπ := Real.pi_pos
  have h1 : Complex.log (-arcTop R α) = Real.log R + ((α - π : ℝ) : ℂ) * I := by
    rw [neg_arcTop, Complex.log, arg_circleMap hR ⟨by linarith, by linarith⟩,
      norm_circleMap_zero, abs_of_pos hR]
  have h2 : Complex.log (-arcBot R α) = Real.log R + ((π - α : ℝ) : ℂ) * I := by
    rw [neg_arcBot, Complex.log, arg_circleMap hR ⟨by linarith, by linarith⟩,
      norm_circleMap_zero, abs_of_pos hR]
  rw [h1, h2]
  push_cast
  ring

/-! ### The winding number -/

/-- ORACLE: CTruncWind.v : trunc_winding.
    `∮_C dz/z = 2πi` over the truncated contour. -/
theorem trunc_winding {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π) :
    truncContour (fun z => z⁻¹) R α = 2 * π * I := by
  rw [truncContour, arcIntegral_inv hR.ne' α, chordIntegral_inv hR hα hα2]
  push_cast
  ring

/-- Non-vacuity: the hypotheses are satisfiable (`R = 1`, `α = 3π/4`). -/
theorem trunc_winding_nonvacuous :
    ∃ R α : ℝ, 0 < R ∧ π / 2 < α ∧ α < π := by
  refine ⟨1, 3 * π / 4, one_pos, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

end TDLean.Newman
