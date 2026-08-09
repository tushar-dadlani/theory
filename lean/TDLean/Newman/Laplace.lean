/-
  TDLean.Newman.Laplace -- Brick C7.

  ORACLE: spectral-theory/CLaplace.v : gT_holo (178 Coq lines)
  Claim: the truncated Laplace transform `g_T(z) = ∫₀ᵀ f(t) e^{−zt} dt` is entire in `z`,
  with `g_T'(z) = ∫₀ᵀ f(t)(−t) e^{−zt} dt`.

  The Coq proof differentiates directly rather than by a Leibniz rule: it expands the
  increment as `f(t)·e^{−zt}·(e^u − 1 − u)` with `u = −h t`, bounds `|e^u − 1 − u| ≤
  3|u|²e^{|u|}` (`CexpRemainder.Cexpf_remainder`), and concludes `O(|h|²) = o(|h|)` by an
  ML estimate. Here the same differentiation-under-the-integral machinery used for the
  keystone C4 applies, with a constant dominating bound on `[0,T]`.

  This file also proves the **tail bound** that brick C8 needs: for `Re z > 0` and `‖f‖ ≤ B`
  on `[0,∞)`,

      ‖∫₀^∞ f e^{−zt} dt − g_T(z)‖ ≤ B e^{−(Re z) T} / Re z.

  In the Coq plan that estimate is listed as part of the still-open brick 8 (`CNewman.v`,
  which does not exist), so it has no Coq oracle.
-/
import TDLean.Newman.StarPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace TDLean.Newman

open Complex Set MeasureTheory intervalIntegral Metric
open scoped Interval

variable {f : ℝ → ℂ} {T : ℝ}

/-- The truncated Laplace transform. ORACLE: CLaplace.v : g_T -/
noncomputable def gT (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, f t * Complex.exp (-z * (t : ℂ))

/-- Its derivative. ORACLE: CLaplace.v : g_T' -/
noncomputable def gT' (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, f t * (-(t : ℂ) * Complex.exp (-z * (t : ℂ)))

/-- `d/dz e^{−zt} = −t e^{−zt}`. -/
theorem hasDerivAt_expNeg (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-w * (t : ℂ)))
      (-(t : ℂ) * Complex.exp (-z * (t : ℂ))) z := by
  have hinner : HasDerivAt (fun w : ℂ => -w * (t : ℂ)) (-(t : ℂ)) z := by
    simpa using ((hasDerivAt_id z).neg).mul_const (t : ℂ)
  have := (Complex.hasDerivAt_exp (-z * (t : ℂ))).comp z hinner
  rw [Function.comp_def] at this
  convert this using 1
  ring

/-- `‖e^{−zt}‖ = e^{−(Re z) t}`. -/
theorem norm_expNeg (t : ℝ) (z : ℂ) :
    ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- The integrand and its `z`-derivative are continuous on `[0,T]`. -/
theorem laplaceIntegrand_continuousOn (hf : ContinuousOn f (uIcc (0 : ℝ) T)) (z : ℂ) :
    ContinuousOn (fun t : ℝ => f t * Complex.exp (-z * (t : ℂ))) (uIcc (0 : ℝ) T) :=
  hf.mul (by fun_prop)

theorem laplaceDerivIntegrand_continuousOn (hf : ContinuousOn f (uIcc (0 : ℝ) T)) (z : ℂ) :
    ContinuousOn (fun t : ℝ => f t * (-(t : ℂ) * Complex.exp (-z * (t : ℂ))))
      (uIcc (0 : ℝ) T) :=
  hf.mul ((by fun_prop : ContinuousOn (fun t : ℝ => -(t : ℂ)) (uIcc (0:ℝ) T)).mul
    (by fun_prop))

/-- ORACLE: CLaplace.v : gT_holo. The truncated Laplace transform is entire. -/
theorem hasDerivAt_gT (hf : ContinuousOn f (uIcc (0 : ℝ) T)) (z : ℂ) :
    HasDerivAt (gT f T) (gT' f T z) z := by
  -- bound `‖f‖` on the (compact) interval
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hf
  set ρ : ℝ := 1 with hρdef
  have hρ : (0 : ℝ) < ρ := one_pos
  -- a constant dominating bound for `x` in `ball z ρ`
  set C : ℝ := |T| with hC
  set E : ℝ := Real.exp ((|z.re| + ρ) * |T|) with hE
  set bound : ℝ := M * C * E with hbound
  have hsub : Ι (0 : ℝ) T ⊆ uIcc (0 : ℝ) T := uIoc_subset_uIcc
  have habs : ∀ t ∈ uIcc (0 : ℝ) T, |t| ≤ |T| := by
    intro t ht
    rcases le_total (0 : ℝ) T with h | h
    · rw [uIcc_of_le h] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h]; exact ht.2
    · rw [uIcc_of_ge h] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h]; linarith [ht.1]
  have hdom : ∀ t ∈ Ι (0 : ℝ) T, ∀ x ∈ ball z ρ,
      ‖f t * (-(t : ℂ) * Complex.exp (-x * (t : ℂ)))‖ ≤ bound := by
    intro t ht x hx
    have ht' : t ∈ uIcc (0 : ℝ) T := hsub ht
    have hMt : ‖f t‖ ≤ M := hM t ht'
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hMt
    have hxre : |x.re - z.re| < ρ := by
      have hd : ‖x - z‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hx
      calc |x.re - z.re| = |(x - z).re| := by simp
        _ ≤ ‖x - z‖ := Complex.abs_re_le_norm _
        _ < ρ := hd
    have hexp : ‖Complex.exp (-x * (t : ℂ))‖ ≤ E := by
      rw [norm_expNeg]
      apply Real.exp_le_exp.mpr
      have h1 : -x.re * t ≤ |x.re| * |t| := by
        calc -x.re * t ≤ |(-x.re) * t| := le_abs_self _
          _ = |x.re| * |t| := by rw [abs_mul, abs_neg]
      have h2 : |x.re| ≤ |z.re| + ρ := by
        calc |x.re| ≤ |z.re| + |x.re - z.re| := by
              have := abs_sub_abs_le_abs_sub x.re z.re; linarith [abs_nonneg (x.re - z.re)]
          _ ≤ |z.re| + ρ := by linarith
      calc -x.re * t ≤ |x.re| * |t| := h1
        _ ≤ (|z.re| + ρ) * |T| := by
            apply mul_le_mul h2 (habs t ht') (abs_nonneg t)
            positivity
    calc ‖f t * (-(t : ℂ) * Complex.exp (-x * (t : ℂ)))‖
        = ‖f t‖ * |t| * ‖Complex.exp (-x * (t : ℂ))‖ := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      _ ≤ M * C * E := by
          have hE0 : (0 : ℝ) ≤ E := (Real.exp_pos _).le
          gcongr
          · exact habs t ht'
    -- `bound` is `M * C * E`
  have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => f t * Complex.exp (-x * (t : ℂ)))
    (F' := fun x t => f t * (-(t : ℂ) * Complex.exp (-x * (t : ℂ))))
    (x₀ := z) (bound := fun _ => bound) (s := ball z ρ)
    (μ := MeasureTheory.volume) (a := 0) (b := T)
    (ball_mem_nhds z hρ)
    (Filter.Eventually.of_forall fun x =>
      ((laplaceIntegrand_continuousOn hf x).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (laplaceIntegrand_continuousOn hf z).intervalIntegrable
    (((laplaceDerivIntegrand_continuousOn hf z).mono hsub).aestronglyMeasurable
      measurableSet_uIoc)
    (Filter.Eventually.of_forall hdom)
    _root_.intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => (hasDerivAt_expNeg t x).const_mul (f t))
  exact hres.2

/-- ORACLE: CLaplace.v : gT_holo (the `Differentiable` packaging). -/
theorem differentiable_gT (hf : ContinuousOn f (uIcc (0 : ℝ) T)) :
    Differentiable ℂ (gT f T) := fun z => (hasDerivAt_gT hf z).differentiableAt

/-! ### `g_T` on the left half-plane

    Newman needs a bound on `g_T` itself (not on `g − g_T`) where `Re z < 0`. The integral
    `∫₀ᵀ e^{−(Re z)t} dt` is what supplies the `1/|Re z|` that cancels the kernel's
    numerator. mathlib has no `∫₀ᵀ e^{at} dt`, so it is proved here by FTC. -/

/-- `∫₀ᵀ e^{at} dt = (e^{aT} − 1)/a`. -/
theorem integral_exp_mul_zero {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (a * t)) = (Real.exp (a * T) - 1) / a := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => Real.exp (a * s) / a) (Real.exp (a * t)) t := by
    intro t _
    have h : HasDerivAt (fun s : ℝ => Real.exp (a * s)) (Real.exp (a * t) * a) t := by
      simpa using (Real.hasDerivAt_exp (a * t)).comp t ((hasDerivAt_id t).const_mul a)
    simpa [mul_div_assoc, mul_div_cancel_right₀ _ ha] using h.div_const a
  have hcont : ContinuousOn (fun t : ℝ => Real.exp (a * t)) (uIcc (0 : ℝ) T) := by fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [sub_div]

/-- For `Re z < 0`, `‖g_T(z)‖ ≤ B e^{−(Re z)T} / (−Re z)`. -/
theorem norm_gT_le_of_re_neg {B : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (uIcc (0 : ℝ) T)) (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B)
    {z : ℂ} (hz : z.re < 0) :
    ‖gT f T z‖ ≤ B * Real.exp (-z.re * T) / (-z.re) := by
  have ha : (0 : ℝ) < -z.re := neg_pos.mpr hz
  have hIcc : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT
  have hB0 : 0 ≤ B := by
    have := hB 0 le_rfl
    exact le_trans (norm_nonneg _) this
  -- bound the integrand pointwise
  have hpt : ∀ t ∈ Icc (0 : ℝ) T,
      ‖f t * Complex.exp (-z * (t : ℂ))‖ ≤ B * Real.exp (-z.re * t) := by
    intro t ht
    rw [norm_mul, norm_expNeg]
    exact mul_le_mul_of_nonneg_right (hB t ht.1) (Real.exp_pos _).le
  have hcont1 : ContinuousOn (fun t : ℝ => ‖f t * Complex.exp (-z * (t : ℂ))‖)
      (uIcc (0 : ℝ) T) := (laplaceIntegrand_continuousOn hf z).norm
  have hcont2 : ContinuousOn (fun t : ℝ => B * Real.exp (-z.re * t)) (uIcc (0 : ℝ) T) := by
    fun_prop
  calc ‖gT f T z‖
      ≤ ∫ t in (0 : ℝ)..T, ‖f t * Complex.exp (-z * (t : ℂ))‖ := by
        rw [gT]
        exact intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ t in (0 : ℝ)..T, B * Real.exp (-z.re * t) := by
        refine intervalIntegral.integral_mono_on hT hcont1.intervalIntegrable
          hcont2.intervalIntegrable fun t ht => hpt t ht
    _ = B * ((Real.exp (-z.re * T) - 1) / (-z.re)) := by
        have h := intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := T)
          (μ := MeasureTheory.volume) B (fun t : ℝ => Real.exp (-z.re * t))
        rw [h, integral_exp_mul_zero (ne_of_gt ha)]
    _ = (B * Real.exp (-z.re * T) - B) / (-z.re) := by
        field_simp
    _ ≤ B * Real.exp (-z.re * T) / (-z.re) := by
        gcongr
        linarith

/-! ### The tail bound

    No Coq oracle: in `docs/route_b_C4_newman_plan.md` this estimate is part of the still
    open brick 8 (`CNewman.v`, which does not exist). -/

/-- For `Re z > 0` and `‖f‖ ≤ B` on `[0,∞)`, the Laplace tail past `T` is `O(e^{−(Re z)T})`:

      `‖∫_{t>T} f(t) e^{−zt} dt‖ ≤ B e^{−(Re z) T} / Re z`.

    This is the estimate that drives Newman's `g − g_T` bound on the right semicircle. -/
theorem norm_laplaceTail_le {B : ℝ} {z : ℂ} (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) (hz : 0 < z.re)
    (hT : 0 ≤ T)
    (hint : IntegrableOn (fun t : ℝ => f t * Complex.exp (-z * (t : ℂ))) (Ioi T)) :
    ‖∫ t in Ioi T, f t * Complex.exp (-z * (t : ℂ))‖ ≤ B * Real.exp (-z.re * T) / z.re := by
  have hneg : -z.re < 0 := neg_neg_iff_pos.mpr hz
  have hboundInt : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul B
  have hb : ∀ t ∈ Ioi T, ‖f t * Complex.exp (-z * (t : ℂ))‖ ≤ B * Real.exp (-z.re * t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hT (mem_Ioi.mp ht))
    rw [norm_mul, norm_expNeg]
    exact mul_le_mul_of_nonneg_right (hB t ht0) (Real.exp_pos _).le
  calc ‖∫ t in Ioi T, f t * Complex.exp (-z * (t : ℂ))‖
      ≤ ∫ t in Ioi T, ‖f t * Complex.exp (-z * (t : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, B * Real.exp (-z.re * t) :=
        setIntegral_mono_on hint.norm hboundInt measurableSet_Ioi hb
    _ = B * ∫ t in Ioi T, Real.exp (-z.re * t) := MeasureTheory.integral_const_mul _ _
    _ = B * Real.exp (-z.re * T) / z.re := by
        rw [integral_exp_mul_Ioi hneg T]
        field_simp

end TDLean.Newman
