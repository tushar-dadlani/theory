/-
  TDLean.Newman.Tauberian -- Brick C8, part 1: the contour identity.

  NO COQ ORACLE. `CNewman.v` does not exist: `docs/route_b_C4_newman_plan.md` lists brick 8
  as open, and `docs/newman_route_status.md` repeats it. Everything here is an *overtake* --
  Lean proving something the Rocq development does not have -- not a cross-verification.
  Nothing in this file may be described as "verified against Coq".

  Newman's analytic theorem (Zagier's form) runs:

      2πi (g(0) − g_T(0)) = ∮_C (g(z) − g_T(z)) e^{zT} (1/z + z/R²) dz

  followed by three ML estimates (right semicircle, left semicircle for `g_T`, left part
  for `g` as `T → ∞`) and an `ε`-chase in `R`.

  This file proves the **identity**. It is exactly where the earlier bricks pay off:
    * the `1/z` half is C6 (`trunc_cauchy`), which needed C4 and C5;
    * the `z/R²` half is C4 directly -- that summand is holomorphic, so its loop vanishes.

  The three estimates and the limit argument are still to come; `norm_laplaceTail_le`
  (brick C7) is the first of them.
-/
import TDLean.Newman.TruncCauchy
import TDLean.Newman.Kernel
import TDLean.Newman.Laplace

namespace TDLean.Newman

open Complex Set Metric Real

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The `z/R²` half of the Newman kernel contributes nothing: the integrand is holomorphic
    on the region, so C4 applies. -/
theorem truncContour_kernelPoly_eq_zero {R α : ℝ} (hU : IsOpen U) (hstar : StarAboutZero U)
    (hF : DifferentiableOn ℂ F U) (hsubset : contourSet R α ⊆ U) :
    truncContour (fun z => F z * (z / (R ^ 2 : ℝ))) R α = 0 := by
  refine truncContour_eq_zero_of_starAboutZero hU hstar ?_ hsubset
  exact hF.mul (differentiableOn_id.div_const _)

/-- **Newman's contour identity.** For `F` holomorphic on an open star-shaped region
    containing the contour and `0`,

      `∮_C F(z) (1/z + z/R²) dz = 2πi · F(0)`.

    In the application `F z = (g z − g_T z) e^{zT}`, so `F 0 = g 0 − g_T 0` and this is the
    identity Newman's argument starts from.

    OVERTAKE: no Coq counterpart (`CNewman.v` does not exist). -/
theorem newman_contour_identity {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α < π)
    (hU : IsOpen U) (hstar : StarAboutZero U) (h0 : (0 : ℂ) ∈ U)
    (hF : DifferentiableOn ℂ F U) (hsubset : contourSet R α ⊆ U)
    (hzero : (0 : ℂ) ∉ contourSet R α) :
    truncContour (fun z => F z * newmanKernel R z) R α = 2 * π * I * F 0 := by
  have hne : ∀ z ∈ contourSet R α, z ≠ 0 := fun z hz h => hzero (h ▸ hz)
  -- split the kernel
  have hsplit : truncContour (fun z => F z * newmanKernel R z) R α
      = truncContour (fun z => F z / z + F z * (z / (R ^ 2 : ℝ))) R α := by
    unfold truncContour arcIntegral chordIntegral
    congr 1
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      dsimp only
      rw [newmanKernel]
      field_simp [hne _ (Or.inl (arcSet_mem hθ))]
    · refine intervalIntegral.integral_congr fun t ht => ?_
      dsimp only
      rw [newmanKernel]
      field_simp [hne _ (Or.inr (chordSet_mem ht))]
  have hcont₁ : ContinuousOn (fun z : ℂ => F z / z) (contourSet R α) := by
    intro z hz
    exact ((hF.continuousOn.mono hsubset z hz).div
      (continuousAt_id.continuousWithinAt) (hne z hz))
  have hcont₂ : ContinuousOn (fun z : ℂ => F z * (z / (R ^ 2 : ℝ))) (contourSet R α) :=
    (hF.continuousOn.mono hsubset).mul (continuousOn_id.div_const _)
  rw [hsplit, truncContour_add hcont₁ hcont₂,
    trunc_cauchy hR hα hα2 hU hstar h0 hF hsubset hzero,
    truncContour_kernelPoly_eq_zero hU hstar hF hsubset, add_zero]

/-! ### The right-semicircle estimate

    This is where the two halves of the design meet. On `‖z‖ = R` with `Re z > 0`:

      ‖g − g_T‖ ≤ B e^{−(Re z)T} / Re z      (C7, `norm_laplaceTail_le`)
      ‖e^{zT}‖  = e^{(Re z)T}
      ‖K_R(z)‖  = 2 (Re z) / R²              (C2, `norm_newmanKernel`)

    The exponentials cancel and so does `Re z`, leaving the constant `2B/R²` — which is
    exactly why Newman's argument closes. -/

/-- **The Newman right-semicircle estimate, pointwise.** Every `z`-dependence cancels.

    OVERTAKE: no Coq counterpart. -/
theorem norm_newman_integrand_right {R T B : ℝ} {G : ℂ → ℂ} {z : ℂ}
    (hR : 0 < R) (hnorm : ‖z‖ = R) (hz : 0 < z.re)
    (hG : ‖G z‖ ≤ B * Real.exp (-z.re * T) / z.re) :
    ‖G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖ ≤ 2 * B / R ^ 2 := by
  have hB : 0 ≤ B := by
    by_contra hcon
    push_neg at hcon
    have h2 : 0 < Real.exp (-z.re * T) := Real.exp_pos _
    have hneg : B * Real.exp (-z.re * T) / z.re < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcon h2) hz
    linarith [norm_nonneg (G z), hG]
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hker : ‖newmanKernel R z‖ = 2 * z.re / R ^ 2 := by
    rw [norm_newmanKernel hR hnorm, abs_of_pos hz]
  have hcancel : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖
      = ‖G z‖ * Real.exp (z.re * T) * (2 * z.re / R ^ 2) := by
        rw [norm_mul, norm_mul, hexp, hker]
    _ ≤ (B * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) * (2 * z.re / R ^ 2) := by
        gcongr
    _ = B * (Real.exp (-z.re * T) * Real.exp (z.re * T)) * 2 / R ^ 2 := by
        have ha : z.re ≠ 0 := ne_of_gt hz
        field_simp
    _ = 2 * B / R ^ 2 := by rw [hcancel]; ring

/-- Non-vacuity: the right-semicircle hypotheses are satisfiable. -/
theorem norm_newman_integrand_right_nonvacuous :
    ∃ (R : ℝ) (z : ℂ), 0 < R ∧ ‖z‖ = R ∧ 0 < z.re :=
  ⟨1, 1, one_pos, by rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by norm_num, Complex.norm_real]; simp,
    by simp⟩

end TDLean.Newman
