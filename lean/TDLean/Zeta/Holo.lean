/-
  TDLean.Zeta.Holo -- Brick C9, part 3: the continuation is holomorphic.

  NO COQ ORACLE. From-scratch rule in force (see `TDLean.Zeta.Basic`).

  Each difference term is holomorphic in `s` -- the `m^{-s}` half directly, the integral
  half by differentiation under the integral sign (the same machinery as C4 and C7) -- and
  the series is locally uniformly dominated, so the sum is holomorphic on `Re s > 0` by
  `differentiableOn_tsum_of_summable_norm`.

  Note the bound `‖zetaDiff s n‖ ≤ ‖s‖ (n+1)^{-Re s-1}` carries a `‖s‖`, so it is uniform
  only on BOUNDED sets. Hence the tsum lemma is applied on balls and differentiability is
  concluded pointwise.
-/
import TDLean.Zeta.Continuation
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

namespace TDLean.Zeta

open Complex Filter Topology intervalIntegral Metric

/-! ### `d/ds x^{-s} = -(log x) x^{-s}` -/

theorem hasDerivAt_cpow_neg_exponent {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun t : ℂ => (x : ℂ) ^ (-t)) (-(Real.log x : ℂ) * (x : ℂ) ^ (-s)) s := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h := (hasStrictDerivAt_const_cpow (x := ((x : ℝ) : ℂ)) (y := -s) (Or.inl hx0)).hasDerivAt
  have hneg : HasDerivAt (fun t : ℂ => -t) (-1) s := (hasDerivAt_id s).neg
  have hc := h.comp s hneg
  rw [Function.comp_def] at hc
  rw [Complex.ofReal_log hx.le]
  convert hc using 1
  ring

/-- On `[m, m+1]` with `m ≥ 1` and `Re t > 0`, the `s`-derivative of the integrand is
    bounded by `log (m+1)`. -/
theorem norm_dcpow_le {n : ℕ} {x : ℝ} (hx : ((n : ℝ) + 1) ≤ x) (hx2 : x ≤ (n : ℝ) + 2)
    {t : ℂ} (ht : 0 < t.re) :
    ‖-(Real.log x : ℂ) * (x : ℂ) ^ (-t)‖ ≤ Real.log ((n : ℝ) + 2) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hx1), norm_cpow_neg_of_pos hxpos]
  have h1 : x ^ (-t.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have h2 : Real.log x ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hxpos hx2
  calc Real.log x * x ^ (-t.re) ≤ Real.log x * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.log_nonneg hx1)
    _ = Real.log x := mul_one _
    _ ≤ Real.log ((n : ℝ) + 2) := h2

/-! ### Differentiating the integral term -/

theorem hasDerivAt_intCpow (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun t : ℂ => ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), (x : ℂ) ^ (-t))
      (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), -(Real.log x : ℂ) * (x : ℂ) ^ (-s)) s := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := one_le_idx n
  have hle : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by linarith
  set ρ : ℝ := s.re / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hball : ∀ t ∈ ball s ρ, 0 < t.re := by
    intro t ht
    have : |t.re - s.re| < ρ := by
      have hd : ‖t - s‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp ht
      calc |t.re - s.re| = |(t - s).re| := by simp
        _ ≤ ‖t - s‖ := Complex.abs_re_le_norm _
        _ < ρ := hd
    have := abs_lt.mp this
    simp only [hρdef] at this ⊢
    linarith [this.1]
  have hsub : Set.uIoc ((n : ℝ) + 1) ((n : ℝ) + 2) ⊆ Set.uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) :=
    Set.uIoc_subset_uIcc
  have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => (x : ℂ) ^ (-t))
    (F' := fun t x => -(Real.log x : ℂ) * (x : ℂ) ^ (-t))
    (x₀ := s) (bound := fun _ => Real.log ((n : ℝ) + 2)) (s := ball s ρ)
    (μ := MeasureTheory.volume) (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (ball_mem_nhds s hρ)
    (Filter.Eventually.of_forall fun t =>
      ((continuousOn_cpow_neg_uIcc hm hle t).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (continuousOn_cpow_neg_uIcc hm hle s).intervalIntegrable
    (by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine ContinuousOn.mono ?_ hsub
      refine ContinuousOn.mul ?_ (continuousOn_cpow_neg_uIcc hm hle s)
      rw [Set.uIcc_of_le hle]
      refine (Complex.continuous_ofReal.comp_continuousOn ?_).neg
      exact Real.continuousOn_log.mono (fun u hu => by
        have : (0 : ℝ) < u := lt_of_lt_of_le hm hu.1
        simpa using this.ne'))
    (Filter.Eventually.of_forall fun x hx t ht => by
      rw [Set.uIoc_of_le hle] at hx
      exact norm_dcpow_le hx.1.le hx.2 (hball t ht))
    _root_.intervalIntegrable_const
    (Filter.Eventually.of_forall fun x hx t _ => by
      rw [Set.uIoc_of_le hle] at hx
      exact hasDerivAt_cpow_neg_exponent (lt_of_lt_of_le hm hx.1.le) t)
  exact hres.2


/-! ### Each term, then the sum -/

theorem differentiableAt_zetaDiff (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun t => zetaDiff t n) s := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := one_le_idx n
  have h1 := hasDerivAt_cpow_neg_exponent hm s
  have h2 := hasDerivAt_intCpow n hs
  exact (h1.sub h2).differentiableAt

/-- The difference series, summed. -/
noncomputable def zetaDiffSum (s : ℂ) : ℂ := ∑' n : ℕ, zetaDiff s n

/-- **The difference series is holomorphic on `Re s > 0`.**

    Applied on a ball, because the term bound carries a `‖s‖` and so is uniform only on
    bounded sets. -/
theorem differentiableAt_zetaDiffSum {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ zetaDiffSum s₀ := by
  set σ₀ : ℝ := s₀.re / 2 with hσ₀
  have hσ₀pos : 0 < σ₀ := by positivity
  set ρ : ℝ := min (s₀.re / 2) 1 with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) one_pos
  set M : ℝ := ‖s₀‖ + ρ with hM
  have hmem : s₀ ∈ ball s₀ ρ := mem_ball_self hρ
  -- properties of points of the ball
  have hball_re : ∀ w ∈ ball s₀ ρ, σ₀ ≤ w.re := by
    intro w hw
    have hd : ‖w - s₀‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hw
    have : |w.re - s₀.re| < ρ := by
      calc |w.re - s₀.re| = |(w - s₀).re| := by simp
        _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
        _ < ρ := hd
    have h2 := (abs_lt.mp this).1
    have hρle : ρ ≤ s₀.re / 2 := min_le_left _ _
    simp only [hσ₀]
    linarith
  have hball_norm : ∀ w ∈ ball s₀ ρ, ‖w‖ ≤ M := by
    intro w hw
    have hd : ‖w - s₀‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hw
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ M := by simp only [hM]; linarith
  -- the uniform bound
  have hbd : ∀ (n : ℕ) (w : ℂ), w ∈ ball s₀ ρ →
      ‖zetaDiff w n‖ ≤ M * ((n : ℝ) + 1) ^ (-σ₀ - 1) := by
    intro n w hw
    have hwre : 0 < w.re := lt_of_lt_of_le hσ₀pos (hball_re w hw)
    have h1 : ((n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-σ₀ - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le (by simp) ?_
      linarith [hball_re w hw]
    calc ‖zetaDiff w n‖ ≤ ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) := norm_zetaDiff_le hwre n
      _ ≤ M * ((n : ℝ) + 1) ^ (-σ₀ - 1) := by
          refine mul_le_mul (hball_norm w hw) h1 (by positivity) ?_
          simp only [hM]; positivity
  have hsummable : Summable (fun n : ℕ => M * ((n : ℝ) + 1) ^ (-σ₀ - 1)) :=
    (summable_rpow_shift hσ₀pos).mul_left _
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun t => zetaDiff t n) (ball s₀ ρ) := by
    intro n w hw
    have hw0 : 0 < w.re := lt_of_lt_of_le hσ₀pos (hball_re w hw)
    exact (differentiableAt_zetaDiff n hw0).differentiableWithinAt
  have hsum := differentiableOn_tsum_of_summable_norm hsummable hdiff isOpen_ball hbd
  exact hsum.differentiableAt (isOpen_ball.mem_nhds hmem)

/-- Hence holomorphic on the whole half-plane. -/
theorem differentiableOn_zetaDiffSum :
    DifferentiableOn ℂ zetaDiffSum {s : ℂ | 0 < s.re} := fun _ hs =>
  (differentiableAt_zetaDiffSum hs).differentiableWithinAt

end TDLean.Zeta
