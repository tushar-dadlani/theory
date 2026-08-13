/-
  TDLean.Newman.LeftLimit -- Brick C8, item 2: the `T → ∞` step.

  NO COQ ORACLE (brick 8 is open on the Coq side).

  At fixed `R`, the `g`-part of the left contour integral vanishes as `T → ∞`:

      leftPart (fun z => g z · e^{zT} · K_R z) R α  →  0.

  The mechanism is that `‖e^{zT}‖ = e^{(Re z)T}`, and `Re z < 0` on the left part (strictly,
  except at the two endpoints `θ = ±π/2`, a null set). So the integrand tends to `0`
  pointwise a.e. and is dominated by a constant -- `‖e^{zT}‖ ≤ 1` there for `T ≥ 0`, `g` is
  bounded on the compact contour, and `‖K_R‖` is bounded off `0`.
-/
import TDLean.Newman.Split
import TDLean.Newman.Kernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace TDLean.Newman

open Complex Set Filter Topology intervalIntegral Real
open scoped Interval

/-! ### A dominated-convergence helper -/

/-- If a family of interval integrands is eventually uniformly bounded and tends to `0`
    a.e., the integrals tend to `0`. -/
theorem tendsto_intervalIntegral_zero {a b C : ℝ} {F : ℝ → ℝ → ℂ}
    (hmeas : ∀ T : ℝ, MeasureTheory.AEStronglyMeasurable (F T)
      (MeasureTheory.volume.restrict (Ι a b)))
    (hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ θ, θ ∈ Ι a b → ‖F T θ‖ ≤ C)
    (hlim : ∀ᵐ θ, θ ∈ Ι a b → Tendsto (fun T : ℝ => F T θ) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ θ in a..b, F T θ) atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (f := fun _ : ℝ => (0 : ℂ)) (bound := fun _ : ℝ => C)
    (Eventually.of_forall hmeas) hbound _root_.intervalIntegrable_const hlim
  simpa using h

/-- `e^{zT} → 0` as `T → ∞`, when `Re z < 0`. -/
theorem tendsto_expT_zero {z : ℂ} (hz : z.re < 0) :
    Tendsto (fun T : ℝ => Complex.exp (z * (T : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ T : ℝ, ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    intro T; rw [Complex.norm_exp]; congr 1; simp
  simp only [hnorm]
  exact Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hz).mpr tendsto_id)

/-- `‖e^{zT}‖ ≤ 1` when `Re z ≤ 0` and `T ≥ 0`. -/
theorem norm_expT_le_one {z : ℂ} (hz : z.re ≤ 0) {T : ℝ} (hT : 0 ≤ T) :
    ‖Complex.exp (z * (T : ℂ))‖ ≤ 1 := by
  have : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [this, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hz hT)

/-! ### The kernel is bounded on the contour -/

/-- On `‖z‖ = R`, `‖K_R z‖ ≤ 2/R`. -/
theorem norm_newmanKernel_le_arc {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R) :
    ‖newmanKernel R z‖ ≤ 2 / R := by
  rw [norm_newmanKernel hR hz]
  have h1 : |z.re| ≤ R := by rw [← hz]; exact Complex.abs_re_le_norm z
  calc 2 * |z.re| / R ^ 2 ≤ 2 * R / R ^ 2 := by gcongr
    _ = 2 / R := by field_simp

/-! ### The arc pieces vanish -/

/-- On an arc piece where `cos < 0`, the `g`-part tends to `0` as `T → ∞`. -/
theorem tendsto_arcIntegralOn_g_zero {R a b M : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : ContinuousOn g (arcSetOn R a b))
    (hM : ∀ z ∈ arcSetOn R a b, ‖g z‖ ≤ M)
    (hcos : ∀ θ ∈ Ioo (min a b) (max a b), Real.cos θ < 0)
    (hcosle : ∀ θ ∈ Ι a b, Real.cos θ ≤ 0) :
    Tendsto (fun T : ℝ => arcIntegralOn
      (fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) R a b) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := by
    have : circleMap 0 R a ∈ arcSetOn R a b := arcSetOn_mem left_mem_uIcc
    exact le_trans (norm_nonneg _) (hM _ this)
  have hnormz : ∀ θ : ℝ, ‖circleMap 0 R θ‖ = R := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hR]
  refine tendsto_intervalIntegral_zero (C := R * M * 1 * (2 / R)) ?_ ?_ ?_
  · -- measurability
    intro T
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine (arcIntegrandOn_continuousOn (f := fun z =>
      g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) ?_).mono uIoc_subset_uIcc
    refine (hg.mul (by fun_prop)).mul ?_
    intro z hz
    have hzne : z ≠ 0 := by
      intro h; rw [h] at hz
      obtain ⟨θ, -, hθ⟩ := hz
      have := hnormz θ; rw [hθ] at this; simp at this; linarith
    exact ((continuousAt_inv₀ hzne).continuousWithinAt).add
      ((continuousAt_id.div_const _).continuousWithinAt)
  · -- uniform bound, for `T ≥ 0`
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    filter_upwards with θ hθ
    have hmem : circleMap 0 R θ ∈ arcSetOn R a b := arcSetOn_mem (uIoc_subset_uIcc hθ)
    have hre : (circleMap 0 R θ).re ≤ 0 := by
      rw [circleMap_re]
      exact mul_nonpos_of_nonneg_of_nonpos hR.le (hcosle θ hθ)
    calc ‖deriv (circleMap 0 R) θ * (g (circleMap 0 R θ) *
            Complex.exp (circleMap 0 R θ * (T : ℂ)) * newmanKernel R (circleMap 0 R θ))‖
        = R * (‖g (circleMap 0 R θ)‖ * ‖Complex.exp (circleMap 0 R θ * (T : ℂ))‖ *
            ‖newmanKernel R (circleMap 0 R θ)‖) := by
          rw [norm_mul, norm_deriv_circleMap, abs_of_pos hR, norm_mul, norm_mul]
      _ ≤ R * (M * 1 * (2 / R)) := by
          gcongr
          · exact hM _ hmem
          · exact norm_expT_le_one hre hT
          · exact norm_newmanKernel_le_arc hR (hnormz θ)
      _ = R * M * 1 * (2 / R) := by ring
  · -- pointwise limit off the null endpoint set
    have hmax : ∀ᵐ θ : ℝ, θ ≠ max a b := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hmax] with θ hθ hmem
    have hIoo : θ ∈ Ioo (min a b) (max a b) :=
      ⟨(hmem : θ ∈ Ioc (min a b) (max a b)).1,
        lt_of_le_of_ne (hmem : θ ∈ Ioc (min a b) (max a b)).2 hθ⟩
    have hre : (circleMap 0 R θ).re < 0 := by
      rw [circleMap_re]; exact mul_neg_of_pos_of_neg hR (hcos θ hIoo)
    have := (tendsto_expT_zero hre).const_mul
      (deriv (circleMap 0 R) θ * g (circleMap 0 R θ))
    have heq : ∀ T : ℝ,
        deriv (circleMap 0 R) θ * (g (circleMap 0 R θ) *
            Complex.exp (circleMap 0 R θ * (T : ℂ)) * newmanKernel R (circleMap 0 R θ))
          = (deriv (circleMap 0 R) θ * g (circleMap 0 R θ)) *
              Complex.exp (circleMap 0 R θ * (T : ℂ)) * newmanKernel R (circleMap 0 R θ) :=
      fun T => by ring
    simp only [heq]
    simpa using (this.mul_const (newmanKernel R (circleMap 0 R θ)))


/-! ### The chord piece vanishes -/

/-- On the chord (where `Re z = R cos α < 0` throughout) the `g`-part tends to `0`. -/
theorem tendsto_chordIntegral_g_zero {R α C₀ : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hcos : Real.cos α < 0)
    (hg : ContinuousOn g (chordSet (arcTop R α) (arcBot R α)))
    (hK : ContinuousOn (fun z : ℂ => newmanKernel R z) (chordSet (arcTop R α) (arcBot R α)))
    (hC : ∀ z ∈ chordSet (arcTop R α) (arcBot R α), ‖g z‖ * ‖newmanKernel R z‖ ≤ C₀) :
    Tendsto (fun T : ℝ => chordIntegral
      (fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z)
      (arcTop R α) (arcBot R α)) atTop (𝓝 0) := by
  set P := arcTop R α
  set Q := arcBot R α
  have hre : ∀ t : ℝ, (chord P Q t).re < 0 := fun t => by
    rw [chord_re_eq]; exact mul_neg_of_pos_of_neg hR hcos
  refine tendsto_intervalIntegral_zero (C := ‖Q - P‖ * C₀ * 1) ?_ ?_ ?_
  · intro T
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine (chordIntegrand_continuousOn (f := fun z =>
      g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) ((hg.mul (by fun_prop)).mul hK)).mono
      uIoc_subset_uIcc
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    filter_upwards with t ht
    have hmem : chord P Q t ∈ chordSet P Q := chordSet_mem (uIoc_subset_uIcc ht)
    calc ‖(Q - P) * (g (chord P Q t) * Complex.exp (chord P Q t * (T : ℂ)) *
            newmanKernel R (chord P Q t))‖
        = ‖Q - P‖ * (‖g (chord P Q t)‖ * ‖newmanKernel R (chord P Q t)‖ *
            ‖Complex.exp (chord P Q t * (T : ℂ))‖) := by
          rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ ‖Q - P‖ * (C₀ * 1) := by
          have h1 : ‖g (chord P Q t)‖ * ‖newmanKernel R (chord P Q t)‖ ≤ C₀ := hC _ hmem
          have hC0 : 0 ≤ C₀ := le_trans (by positivity) h1
          have h2 : ‖Complex.exp (chord P Q t * (T : ℂ))‖ ≤ 1 :=
            norm_expT_le_one (hre t).le hT
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (norm_nonneg _) hC0) (norm_nonneg _)
      _ = ‖Q - P‖ * C₀ * 1 := by ring
  · filter_upwards with t _
    have := (tendsto_expT_zero (hre t)).const_mul ((Q - P) * g (chord P Q t))
    have heq : ∀ T : ℝ, (Q - P) * (g (chord P Q t) *
          Complex.exp (chord P Q t * (T : ℂ)) * newmanKernel R (chord P Q t))
        = ((Q - P) * g (chord P Q t)) * Complex.exp (chord P Q t * (T : ℂ)) *
            newmanKernel R (chord P Q t) := fun T => by ring
    simp only [heq]
    simpa using this.mul_const (newmanKernel R (chord P Q t))


/-! ### Assembling: the whole left part vanishes -/

/-- **The `T → ∞` step.** At fixed `R`, the `g`-part of the left contour integral vanishes.

    OVERTAKE: no Coq counterpart. -/
theorem tendsto_leftPart_g_zero {R α : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hα : π / 2 < α) (hα2 : α ≤ π) (hg : ContinuousOn g (contourSet R α)) :
    Tendsto (fun T : ℝ => leftPart
      (fun z => g z * Complex.exp (z * (T : ℂ)) * newmanKernel R z) R α) atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hcos : Real.cos α < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hα (by linarith)
  obtain ⟨t1, t2, t3⟩ := leftPart_subsets hα.le
  -- kernel is continuous on the contour (which avoids `0`)
  have hne : ∀ z ∈ contourSet R α, z ≠ 0 := fun z hz h =>
    zero_not_mem_contourSet hR hα hα2 (h ▸ hz)
  have hKc : ContinuousOn (fun z : ℂ => newmanKernel R z) (contourSet R α) := by
    intro z hz
    exact ((continuousAt_inv₀ (hne z hz)).continuousWithinAt).add
      ((continuousAt_id.div_const _).continuousWithinAt)
  -- bounds by compactness
  obtain ⟨Mg, hMg⟩ := (isCompact_contourSet R α).exists_bound_of_continuousOn hg
  obtain ⟨MK, hMK⟩ := (isCompact_contourSet R α).exists_bound_of_continuousOn hKc
  have harc1 := tendsto_arcIntegralOn_g_zero (M := Mg) hR (hg.mono t1)
    (fun z hz => hMg z (t1 hz))
    (fun θ hθ => by
      rw [min_eq_left (by linarith : -α ≤ -(π / 2)),
        max_eq_right (by linarith : -α ≤ -(π / 2))] at hθ
      exact cos_neg_on_lower ⟨by linarith [hθ.1], hθ.2⟩)
    (fun θ hθ => cos_nonpos_of_mem_lower hα hα2 hθ)
  have harc2 := tendsto_arcIntegralOn_g_zero (M := Mg) hR (hg.mono t2)
    (fun z hz => hMg z (t2 hz))
    (fun θ hθ => by
      rw [min_eq_left (by linarith : π / 2 ≤ α), max_eq_right (by linarith : π / 2 ≤ α)] at hθ
      exact cos_neg_on_upper ⟨hθ.1, by linarith [hθ.2]⟩)
    (fun θ hθ => cos_nonpos_of_mem_upper hα hα2 hθ)
  have hchord := tendsto_chordIntegral_g_zero (C₀ := Mg * MK) hR hcos (hg.mono t3) (hKc.mono t3)
    (fun z hz => mul_le_mul (hMg z (t3 hz)) (hMK z (t3 hz)) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hMg z (t3 hz))))
  have := (harc1.add harc2).add hchord
  simpa [leftPart] using this

end TDLean.Newman
