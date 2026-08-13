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
import TDLean.Newman.Split
import TDLean.Newman.LeftLimit

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
theorem newman_contour_identity {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π)
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

/-- **The Newman left-semicircle estimate, pointwise.** Same constant `2B/R²`, now driven
    by the bound on `g_T` itself (C7 `norm_gT_le_of_re_neg`) rather than on `g − g_T`.
    Again every `z`-dependence cancels.

    OVERTAKE: no Coq counterpart. -/
theorem norm_newman_integrand_left {R T B : ℝ} {G : ℂ → ℂ} {z : ℂ}
    (hR : 0 < R) (hnorm : ‖z‖ = R) (hz : z.re < 0)
    (hG : ‖G z‖ ≤ B * Real.exp (-z.re * T) / (-z.re)) :
    ‖G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖ ≤ 2 * B / R ^ 2 := by
  have ha : (0 : ℝ) < -z.re := neg_pos.mpr hz
  have hB : 0 ≤ B := by
    by_contra hcon
    push_neg at hcon
    have h2 : 0 < Real.exp (-z.re * T) := Real.exp_pos _
    have hneg : B * Real.exp (-z.re * T) / (-z.re) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcon h2) ha
    linarith [norm_nonneg (G z), hG]
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hker : ‖newmanKernel R z‖ = 2 * (-z.re) / R ^ 2 := by
    rw [norm_newmanKernel hR hnorm, abs_of_neg hz]
  have hcancel : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖
      = ‖G z‖ * Real.exp (z.re * T) * (2 * (-z.re) / R ^ 2) := by
        rw [norm_mul, norm_mul, hexp, hker]
    _ ≤ (B * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) * (2 * (-z.re) / R ^ 2) := by
        gcongr
    _ = B * (Real.exp (-z.re * T) * Real.exp (z.re * T)) * 2 / R ^ 2 := by
        have hane : z.re ≠ 0 := ne_of_lt hz
        have hR0 : R ≠ 0 := ne_of_gt hR
        field_simp
    _ = 2 * B / R ^ 2 := by rw [hcancel]; ring

/-! ### The deformation of the left part

    For an ENTIRE `F` (in the application `F = g_T e^{zT}`, with `g_T` entire by C7), the
    contour integral of `F · K_R` is `2πi F(0)` for *every* admissible `α`, in particular
    for `α` and for `π`. Since the right semicircles coincide, the left parts coincide --
    and at `α = π` the left part is the left semicircle. -/

/-- `F · K_R` is continuous on the contour, which avoids `0`. -/
theorem continuousOn_kernel_mul {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π)
    (hF : Continuous F) :
    ContinuousOn (fun z => F z * newmanKernel R z) (contourSet R α) := by
  have hne : ∀ z ∈ contourSet R α, z ≠ 0 := fun z hz h =>
    zero_not_mem_contourSet hR hα hα2 (h ▸ hz)
  intro z hz
  refine (hF.continuousWithinAt).mul ?_
  refine ContinuousWithinAt.add ?_ ?_
  · exact (continuousAt_inv₀ (hne z hz)).continuousWithinAt
  · exact (continuousAt_id.div_const _).continuousWithinAt

/-- **Zagier's deformation, obtained from C6 alone.** For entire `F`, the left part of the
    contour at angle `α` equals the left part at `α = π` -- i.e. the left semicircle.

    OVERTAKE: no Coq counterpart. -/
theorem leftPart_kernel_deform {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π)
    (hF : Differentiable ℂ F) :
    leftPart (fun z => F z * newmanKernel R z) R α
      = leftPart (fun z => F z * newmanKernel R z) R π := by
  have hπ2 : π / 2 < π := by linarith [Real.pi_pos]
  set R' : ℝ := R + 1 with hR'
  have hRR : R < R' := by linarith
  have hR'0 : 0 < R' := by linarith
  have hUopen : IsOpen (Metric.ball (0 : ℂ) R') := isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R' := mem_ball_self hR'0
  have hFd : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) R') := hF.differentiableOn
  have hcα := newman_contour_identity hR hα hα2 hUopen starAboutZero_ball h0 hFd
    (contourSet_subset_ball hR hRR) (zero_not_mem_contourSet hR hα hα2)
  have hcπ := newman_contour_identity hR hπ2 le_rfl hUopen starAboutZero_ball h0 hFd
    (contourSet_subset_ball hR hRR) (zero_not_mem_contourSet hR hπ2 le_rfl)
  exact leftPart_eq_of_truncContour_eq hα.le
    (continuousOn_kernel_mul hR hα hα2 hF.continuous)
    (continuousOn_kernel_mul hR hπ2 le_rfl hF.continuous)
    (by rw [hcα, hcπ])

/-! ### From pointwise to integral: the two `2πB/R` bounds

    `R · (2B/R²) · π = 2πB/R` on each semicircle. Both go through the a.e. ML bound, since
    the pointwise estimates need `Re z ≠ 0` and the endpoints `θ = ±π/2` have `Re z = 0`. -/

/-- The right semicircle contributes at most `R · (2B/R²) · π`. -/
theorem norm_rightSemi_le {R B : ℝ} {h : ℂ → ℂ} (hR : 0 < R)
    (hb : ∀ z : ℂ, ‖z‖ = R → 0 < z.re → ‖h z‖ ≤ 2 * B / R ^ 2) :
    ‖rightSemi h R‖ ≤ R * (2 * B / R ^ 2) * π := by
  have hhalf : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have key : ∀ θ ∈ Ioo (min (-(π / 2)) (π / 2)) (max (-(π / 2)) (π / 2)),
      ‖h (circleMap 0 R θ)‖ ≤ 2 * B / R ^ 2 := by
    intro θ hθ
    rw [min_eq_left hhalf, max_eq_right hhalf] at hθ
    refine hb _ (by rw [norm_circleMap_zero, abs_of_pos hR]) ?_
    rw [circleMap_re]
    exact mul_pos hR (Real.cos_pos_of_mem_Ioo hθ)
  have hml := norm_arcIntegralOn_le_of_ae (f := h) (R := R) key
  rw [abs_of_pos hR] at hml
  calc ‖rightSemi h R‖ ≤ R * (2 * B / R ^ 2) * |π / 2 - -(π / 2)| := hml
    _ = R * (2 * B / R ^ 2) * π := by
        rw [show π / 2 - -(π / 2) = π by ring, abs_of_pos Real.pi_pos]

/-- An arc piece lying in the left half-plane contributes at most `R · (2B/R²) · |b − a|`. -/
theorem norm_leftArc_le {R B a b : ℝ} {h : ℂ → ℂ} (hR : 0 < R)
    (hab : ∀ θ ∈ Ioo (min a b) (max a b), Real.cos θ < 0)
    (hb : ∀ z : ℂ, ‖z‖ = R → z.re < 0 → ‖h z‖ ≤ 2 * B / R ^ 2) :
    ‖arcIntegralOn h R a b‖ ≤ R * (2 * B / R ^ 2) * |b - a| := by
  have key : ∀ θ ∈ Ioo (min a b) (max a b), ‖h (circleMap 0 R θ)‖ ≤ 2 * B / R ^ 2 := by
    intro θ hθ
    refine hb _ (by rw [norm_circleMap_zero, abs_of_pos hR]) ?_
    rw [circleMap_re]
    exact mul_neg_of_pos_of_neg hR (hab θ hθ)
  have hml := norm_arcIntegralOn_le_of_ae (f := h) (R := R) key
  rwa [abs_of_pos hR] at hml

/-- The left semicircle (the `α = π` left part, where the chord degenerates) contributes at
    most `R · (2B/R²) · π` -- the same as the right semicircle. -/
theorem norm_leftPart_pi_le {R B : ℝ} {h : ℂ → ℂ} (hR : 0 < R)
    (hb : ∀ z : ℂ, ‖z‖ = R → z.re < 0 → ‖h z‖ ≤ 2 * B / R ^ 2) :
    ‖leftPart h R π‖ ≤ R * (2 * B / R ^ 2) * π := by
  have hπ := Real.pi_pos
  rw [leftPart_pi]
  have h1 : ‖arcIntegralOn h R (-π) (-(π / 2))‖ ≤ R * (2 * B / R ^ 2) * |(-(π / 2)) - (-π)| := by
    refine norm_leftArc_le hR (fun θ hθ => ?_) hb
    rw [min_eq_left (by linarith : -π ≤ -(π / 2)),
      max_eq_right (by linarith : -π ≤ -(π / 2))] at hθ
    exact cos_neg_on_lower hθ
  have h2 : ‖arcIntegralOn h R (π / 2) π‖ ≤ R * (2 * B / R ^ 2) * |π - π / 2| := by
    refine norm_leftArc_le hR (fun θ hθ => ?_) hb
    rw [min_eq_left (by linarith : π / 2 ≤ π), max_eq_right (by linarith : π / 2 ≤ π)] at hθ
    exact cos_neg_on_upper hθ
  rw [show (-(π / 2)) - (-π) = π / 2 by ring, abs_of_pos (by linarith : (0:ℝ) < π / 2)] at h1
  rw [show π - π / 2 = π / 2 by ring, abs_of_pos (by linarith : (0:ℝ) < π / 2)] at h2
  calc ‖arcIntegralOn h R (-π) (-(π / 2)) + arcIntegralOn h R (π / 2) π‖
      ≤ ‖arcIntegralOn h R (-π) (-(π / 2))‖ + ‖arcIntegralOn h R (π / 2) π‖ := norm_add_le _ _
    _ ≤ R * (2 * B / R ^ 2) * (π / 2) + R * (2 * B / R ^ 2) * (π / 2) := by linarith
    _ = R * (2 * B / R ^ 2) * π := by ring

/-- Non-vacuity: the right-semicircle hypotheses are satisfiable. -/
theorem norm_newman_integrand_right_nonvacuous :
    ∃ (R : ℝ) (z : ℂ), 0 < R ∧ ‖z‖ = R ∧ 0 < z.re :=
  ⟨1, 1, one_pos, by rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by norm_num, Complex.norm_real]; simp,
    by simp⟩


/-! ### The quantitative core of Newman's theorem -/

/-- **The Newman inequality.** For every `T ≥ 0` and every admissible contour radius `R`,

      `2π ‖g(0) − g_T(0)‖ ≤ 2·(R·(2B/R²)·π) + ‖leftPart(g·e^{zT}·K_R)‖`.

    The first term is `4πB/R`, which is small for large `R`; the second tends to `0` as
    `T → ∞` at fixed `R` (`tendsto_leftPart_g_zero`). Those two facts together are Newman's
    theorem.

    OVERTAKE: no Coq counterpart. -/
theorem newman_inequality {f : ℝ → ℂ} {g : ℂ → ℂ} {B R α T : ℝ} {U : Set ℂ}
    (hfi : IntervalIntegrable f MeasureTheory.volume 0 T)
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) (hT : 0 ≤ T)
    (hint : ∀ z : ℂ, 0 < z.re →
      MeasureTheory.IntegrableOn (fun t : ℝ => f t * Complex.exp (-z * (t : ℂ))) (Ioi 0))
    (hgL : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * Complex.exp (-z * (t : ℂ)))
    (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π)
    (hU : IsOpen U) (hstar : StarAboutZero U) (h0 : (0 : ℂ) ∈ U)
    (hsub : contourSet R α ⊆ U) (hgd : DifferentiableOn ℂ g U) :
    2 * π * ‖g 0 - gT f T 0‖ ≤ 2 * (R * (2 * B / R ^ 2) * π)
      + ‖leftPart (fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) R α‖ := by
  have hπ := Real.pi_pos
  have hfM : ∀ t ∈ uIcc (0 : ℝ) T, ‖f t‖ ≤ B := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hB t ht.1
  have hgTd : Differentiable ℂ (gT f T) := differentiable_gT hfi hfM
  have hexpd : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (T : ℂ))) :=
    Complex.differentiable_exp.comp (differentiable_id.mul_const _)
  -- the two integrands
  set A : ℂ → ℂ := fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z with hA
  set Bf : ℂ → ℂ := fun z => gT f T z * Complex.exp (z * (T : ℂ)) * newmanKernel R z with hBf
  set F : ℂ → ℂ := fun z => (g z - gT f T z) * Complex.exp (z * (T : ℂ)) with hF
  have hFd : DifferentiableOn ℂ F U :=
    (hgd.sub hgTd.differentiableOn).mul hexpd.differentiableOn
  have hzero := zero_not_mem_contourSet hR hα hα2
  have hne : ∀ z ∈ contourSet R α, z ≠ 0 := fun z hz h => hzero (h ▸ hz)
  have hKc : ContinuousOn (fun z : ℂ => newmanKernel R z) (contourSet R α) := by
    intro z hz
    exact ((continuousAt_inv₀ (hne z hz)).continuousWithinAt).add
      ((continuousAt_id.div_const _).continuousWithinAt)
  have hAc : ContinuousOn A (contourSet R α) :=
    ((hgd.continuousOn.mono hsub).mul (by fun_prop)).mul hKc
  have hBc : ContinuousOn Bf (contourSet R α) :=
    ((hgTd.continuous.continuousOn).mul (by fun_prop)).mul hKc
  -- the contour identity, then the split
  have hid := newman_contour_identity hR hα hα2 hU hstar h0 hFd hsub hzero
  have hF0 : F 0 = g 0 - gT f T 0 := by simp [hF]
  have hFK : (fun z => F z * newmanKernel R z) = fun z => A z - Bf z := by
    funext z; simp only [hA, hBf, hF]; ring
  rw [hFK, hF0] at hid
  have hsplit := truncContour_split (f := fun z => A z - Bf z) hα.le (hAc.sub hBc)
  rw [hsplit, leftPart_sub hα.le hAc hBc] at hid
  -- deform the `g_T` left part to the left semicircle
  have hdeform : leftPart Bf R α = leftPart Bf R π := by
    have : Bf = fun z => (gT f T z * Complex.exp (z * (T : ℂ))) * newmanKernel R z := by
      funext z; simp [hBf]
    rw [this]
    exact leftPart_kernel_deform hR hα hα2 (hgTd.mul hexpd)
  rw [hdeform] at hid
  -- bound the right semicircle
  have hright : ‖rightSemi (fun z => A z - Bf z) R‖ ≤ R * (2 * B / R ^ 2) * π := by
    refine norm_rightSemi_le hR fun z hznorm hzre => ?_
    have hsubg : A z - Bf z = (g z - gT f T z) * Complex.exp (z * (T : ℂ)) *
        newmanKernel R z := by simp only [hA, hBf]; ring
    rw [hsubg]
    refine norm_newman_integrand_right (G := fun w => g w - gT f T w) hR hznorm hzre ?_
    dsimp only
    rw [sub_gT_eq_tail hT (hgL z hzre) (hint z hzre)]
    exact norm_laplaceTail_le hB hzre hT ((hint z hzre).mono_set (Ioi_subset_Ioi hT))
  -- bound the left semicircle
  have hleft : ‖leftPart Bf R π‖ ≤ R * (2 * B / R ^ 2) * π := by
    refine norm_leftPart_pi_le hR fun z hznorm hzre => ?_
    have hsubg : Bf z = gT f T z * Complex.exp (z * (T : ℂ)) * newmanKernel R z := rfl
    rw [hsubg]
    exact norm_newman_integrand_left (G := gT f T) hR hznorm hzre
      (norm_gT_le_of_re_neg hT hfi hB hzre)
  -- assemble
  have hnorm : ‖(2 : ℂ) * π * I * (g 0 - gT f T 0)‖ = 2 * π * ‖g 0 - gT f T 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ]
    norm_num
  calc 2 * π * ‖g 0 - gT f T 0‖ = ‖(2 : ℂ) * π * I * (g 0 - gT f T 0)‖ := hnorm.symm
    _ = ‖rightSemi (fun z => A z - Bf z) R + (leftPart A R α - leftPart Bf R π)‖ := by rw [hid]
    _ ≤ ‖rightSemi (fun z => A z - Bf z) R‖ + (‖leftPart A R α‖ + ‖leftPart Bf R π‖) := by
        refine le_trans (norm_add_le _ _) ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ R * (2 * B / R ^ 2) * π + (‖leftPart A R α‖ + R * (2 * B / R ^ 2) * π) := by
        gcongr
    _ = 2 * (R * (2 * B / R ^ 2) * π) + ‖leftPart A R α‖ := by ring


/-! ### Newman's analytic theorem -/

/-- **Newman's analytic Tauberian theorem** (Zagier's form).

    If `f` is continuous and bounded by `B` on `[0,∞)`, `g` is its Laplace transform on
    `Re z > 0`, and `g` extends holomorphically past the imaginary axis (encoded by
    `hregion`: for each contour radius `R` there is an admissible star-shaped region), then

        `∫₀ᵀ f(t) dt → g(0)`  as  `T → ∞`,

    i.e. the improper integral `∫₀^∞ f` converges to `g(0)`.

    OVERTAKE: no Coq counterpart -- `CNewman.v` does not exist, and
    `docs/newman_route_status.md` lists this as brick 8, open. -/
theorem newman_tauberian {f : ℝ → ℂ} {g : ℂ → ℂ} {B : ℝ}
    (hfi : ∀ T : ℝ, IntervalIntegrable f MeasureTheory.volume 0 T)
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B)
    (hint : ∀ z : ℂ, 0 < z.re →
      MeasureTheory.IntegrableOn (fun t : ℝ => f t * Complex.exp (-z * (t : ℂ))) (Ioi 0))
    (hgL : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * Complex.exp (-z * (t : ℂ)))
    (hregion : ∀ R : ℝ, 0 < R → ∃ α U, π / 2 < α ∧ α ≤ π ∧ IsOpen U ∧ StarAboutZero U ∧
      (0 : ℂ) ∈ U ∧ contourSet R α ⊆ U ∧ DifferentiableOn ℂ g U) :
    Filter.Tendsto (fun T : ℝ => gT f T 0) Filter.atTop (nhds (g 0)) := by
  have hπ := Real.pi_pos
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 le_rfl)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the contour radius so that the `4πB/R` term is below `πε`
  set R : ℝ := 4 * B / ε + 1 with hRdef
  have hR : 0 < R := by positivity
  have hRbig : 2 * B / R < ε / 2 := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hRval : ε / 2 * R = 2 * B + ε / 2 := by rw [hRdef]; field_simp; ring
    rw [div_lt_iff₀ hR, hRval]
    linarith
  obtain ⟨α, U, hα, hα2, hU, hstar, h0, hsub, hgd⟩ := hregion R hR
  have hgc : ContinuousOn g (contourSet R α) := hgd.continuousOn.mono hsub
  -- the left part vanishes as `T → ∞`
  have hlim := (tendsto_leftPart_g_zero hR hα hα2 hgc).norm
  simp only [norm_zero] at hlim
  have hev : ∀ᶠ T : ℝ in Filter.atTop,
      ‖leftPart (fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) R α‖ < π * ε :=
    hlim.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨N, hN⟩ := (hev.and (Filter.eventually_ge_atTop (0 : ℝ))).exists_forall_of_atTop
  refine ⟨N, fun T hT => ?_⟩
  obtain ⟨hTleft, hT0⟩ := hN T hT
  have hineq := newman_inequality (hfi T) hB hT0 hint hgL hR hα hα2 hU hstar h0 hsub hgd
  -- `2 * (R * (2B/R²) * π) = 2π * (2B/R)`
  have hrw : 2 * (R * (2 * B / R ^ 2) * π) = 2 * π * (2 * B / R) := by
    field_simp
  rw [hrw] at hineq
  have hstep : 2 * π * ‖g 0 - gT f T 0‖ < 2 * π * ε := by
    calc 2 * π * ‖g 0 - gT f T 0‖
        ≤ 2 * π * (2 * B / R) + ‖leftPart
            (fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) R α‖ := hineq
      _ < 2 * π * (ε / 2) + π * ε := by gcongr
      _ = 2 * π * ε := by ring
  have hfin : ‖g 0 - gT f T 0‖ < ε := by
    have h2π : 0 < 2 * π := by linarith
    exact lt_of_mul_lt_mul_left (by linarith [hstep]) (le_of_lt h2π)
  rw [dist_eq_norm, ← norm_neg]
  simpa using hfin


/-- Non-vacuity for `newman_tauberian`. The hypothesis set is elaborate -- in particular
    `hregion` -- so it is worth exhibiting a point where all of it holds simultaneously.
    Taking `f = 0`, `g = 0`, `B = 0`: `g` is entire, so any ball around `0` serves as the
    region. (This says only that the hypotheses are consistent, not that they are weak.) -/
theorem newman_tauberian_nonvacuous :
    ∃ (f : ℝ → ℂ) (g : ℂ → ℂ) (B : ℝ),
      (∀ T : ℝ, IntervalIntegrable f MeasureTheory.volume 0 T) ∧
      (∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B) ∧
      (∀ z : ℂ, 0 < z.re →
        MeasureTheory.IntegrableOn (fun t : ℝ => f t * Complex.exp (-z * (t : ℂ))) (Ioi 0)) ∧
      (∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * Complex.exp (-z * (t : ℂ))) ∧
      (∀ R : ℝ, 0 < R → ∃ α U, π / 2 < α ∧ α ≤ π ∧ IsOpen U ∧ StarAboutZero U ∧
        (0 : ℂ) ∈ U ∧ contourSet R α ⊆ U ∧ DifferentiableOn ℂ g U) := by
  have hπ := Real.pi_pos
  refine ⟨fun _ => 0, fun _ => 0, 0, fun _ => intervalIntegrable_const,
    fun t _ => by simp, ?_, ?_, ?_⟩
  · intro z _; simp
  · intro z _; simp
  · intro R hR
    refine ⟨π, Metric.ball (0 : ℂ) (R + 1), by linarith, le_rfl, isOpen_ball,
      starAboutZero_ball, mem_ball_self (by linarith), ?_, differentiableOn_const 0⟩
    exact contourSet_subset_ball hR (by linarith)

end TDLean.Newman
