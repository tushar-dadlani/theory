/-
  TDLean.Zeta.Telescope -- Brick C9, part 4: the continuation agrees with the series.

  NO COQ ORACLE. From-scratch rule in force.

  For `Re s > 1` the integrals telescope:

      ∫ₘ^{m+1} x^{−s} dx = (m^{1−s} − (m+1)^{1−s})/(s−1),

  so the partial sums collapse to `(1 − (N+1)^{1−s})/(s−1) → 1/(s−1)`. Hence

      1/(s−1) + ∑ zetaDiff s n = ∑ m^{−s} = ζ(s)   on  Re s > 1,

  and since the left side is holomorphic on `Re s > 0` (part 3), it continues `ζ` with the
  pole isolated in the explicit `1/(s−1)` term.
-/
import TDLean.Zeta.Holo

namespace TDLean.Zeta

open Complex Filter Topology intervalIntegral

/-- Closed form of the block integral, for `s ≠ 1`. -/
theorem intCpow_eq {m : ℝ} (hm : 0 < m) {s : ℂ} (hs : s ≠ 1) :
    (∫ x in m..(m + 1), (x : ℂ) ^ (-s))
      = ((m : ℂ) ^ (1 - s) - ((m + 1 : ℝ) : ℂ) ^ (1 - s)) / (s - 1) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hle : m ≤ m + 1 := by linarith
  -- antiderivative `x^{1-s}/(1-s)`
  have hderiv : ∀ x ∈ Set.uIcc m (m + 1),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s)) ((x : ℂ) ^ (-s)) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : x ≠ 0 := by
      have : 0 < x := lt_of_lt_of_le hm hx.1
      exact this.ne'
    have h := hasDerivAt_ofReal_cpow_const hx0 h1s
    have := h.div_const (1 - s)
    convert this using 1
    field_simp
    congr 1
    ring
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.uIcc m (m + 1)) :=
    continuousOn_cpow_neg_uIcc hm hle s
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  field_simp
  ring

/-- The block integral in the indexed form used by `zetaDiff`. -/
theorem intCpow_idx (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), (x : ℂ) ^ (-s))
      = ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (1 - s) / (s - 1) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := one_le_idx n
  have h := intCpow_eq hm hs
  rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring] at h
  rw [h, sub_div]


/-! ### Telescoping -/

/-- The telescoping antiderivative term, `m^{1−s}/(s−1)` with `m = n+1`. -/
noncomputable def zetaT (s : ℂ) (n : ℕ) : ℂ := ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (1 - s) / (s - 1)

theorem zetaT_zero (s : ℂ) : zetaT s 0 = 1 / (s - 1) := by
  simp [zetaT]

theorem intCpow_eq_T (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), (x : ℂ) ^ (-s)) = zetaT s n - zetaT s (n + 1) := by
  rw [intCpow_idx n hs, zetaT, zetaT]
  push_cast
  ring_nf

/-- `zetaDiff` in telescoping form. -/
theorem zetaDiff_eq_T (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaDiff s n = ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (zetaT s n - zetaT s (n + 1)) := by
  rw [zetaDiff, intCpow_eq_T n hs]

/-- `‖zetaT s n‖ → 0` for `Re s > 1`. -/
theorem tendsto_zetaT_zero {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun n : ℕ => zetaT s n) Filter.atTop (nhds 0) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h => by rw [h] at hs; simp at hs)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖zetaT s n‖ = ((n : ℝ) + 1) ^ (1 - s.re) / ‖s - 1‖ := by
    intro n
    have hm : (0 : ℝ) < (n : ℝ) + 1 := one_le_idx n
    rw [zetaT, norm_div, norm_cpow_of_pos hm]
    congr 2
  simp only [hnorm]
  have hy : 0 < s.re - 1 := by linarith
  have hcomp : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - s.re)) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hy).comp hcomp
    simpa [Function.comp_def, show -(s.re - 1) = 1 - s.re by ring] using h
  simpa using h1.div_const ‖s - 1‖


/-! ### The continuation agrees with the Dirichlet series on `Re s > 1` -/

theorem sum_zetaDiff_range {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, zetaDiff s n
      = (∑ n ∈ Finset.range N, ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s))
        - (zetaT s 0 - zetaT s N) := by
  have hcongr : ∀ n ∈ Finset.range N, zetaDiff s n
      = ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (zetaT s n - zetaT s (n + 1)) :=
    fun n _ => zetaDiff_eq_T n hs
  rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, Finset.sum_range_sub' (zetaT s) N]

/-- The shifted Dirichlet term, in the form `zetaDiff` uses. -/
theorem shifted_term (s : ℂ) (n : ℕ) :
    (1 : ℂ) / (((n + 1 : ℕ) : ℂ)) ^ s = ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
  rw [Complex.cpow_neg, one_div]
  congr 2
  push_cast
  ring

/-- **The continuation.** `1/(s−1) + ∑ zetaDiff s n = ζ(s)` on `Re s > 1`. -/
theorem zetaDiffSum_eq {s : ℂ} (hs : 1 < s.re) :
    zetaDiffSum s = zetaSeries s - 1 / (s - 1) := by
  have hs0re : (0 : ℝ) < s.re := by linarith
  have hsne : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  -- partial sums of `zetaDiff` converge to the sum
  have hpart : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, zetaDiff s n) Filter.atTop
      (nhds (zetaDiffSum s)) := (summable_zetaDiff hs0re).hasSum.tendsto_sum_nat
  -- partial sums of the Dirichlet series converge to `zetaSeries s`
  have hz : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (1 : ℂ) / (n : ℂ) ^ s)
      Filter.atTop (nhds (zetaSeries s)) := (summable_zetaTerm hs).hasSum.tendsto_sum_nat
  -- the `n = 0` term vanishes, so the shifted partial sums are the same sequence shifted
  have hzero : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ s = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow hs0]; simp
  have hshift : ∀ N : ℕ, (∑ n ∈ Finset.range N, ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s))
      = ∑ n ∈ Finset.range (N + 1), (1 : ℂ) / (n : ℂ) ^ s := by
    intro N
    rw [Finset.sum_range_succ' (fun n => (1 : ℂ) / (n : ℂ) ^ s) N, hzero, add_zero]
    exact (Finset.sum_congr rfl fun n _ => (shifted_term s n).symm)
  have hz' : Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N, ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s))
      Filter.atTop (nhds (zetaSeries s)) := by
    simp only [hshift]
    exact hz.comp (Filter.tendsto_add_atTop_nat 1)
  -- take the limit in the telescoped partial sum
  have hlim : Filter.Tendsto
      (fun N => (∑ n ∈ Finset.range N, ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s))
        - (zetaT s 0 - zetaT s N)) Filter.atTop (nhds (zetaSeries s - (zetaT s 0 - 0))) :=
    hz'.sub (tendsto_const_nhds.sub (tendsto_zetaT_zero hs))
  simp only [sub_zero] at hlim
  have heq := tendsto_nhds_unique (hpart.congr (fun N => sum_zetaDiff_range hsne N)) hlim
  rw [heq, zetaT_zero]

/-- The analytic continuation of `ζ` to `Re s > 0`, with the pole isolated. -/
noncomputable def zetaCont (s : ℂ) : ℂ := 1 / (s - 1) + zetaDiffSum s

/-- **`zetaCont` continues `ζ`.** -/
theorem zetaCont_eq_zetaSeries {s : ℂ} (hs : 1 < s.re) : zetaCont s = zetaSeries s := by
  rw [zetaCont, zetaDiffSum_eq hs]
  ring

/-- **`zetaCont` is holomorphic away from `s = 1` on `Re s > 0`** -- the pole is entirely in
    the explicit `1/(s−1)` term. -/
theorem differentiableAt_zetaCont {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ zetaCont s := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - 1)) s := by
    exact DifferentiableAt.div (differentiableAt_const (1 : ℂ))
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ))) (sub_ne_zero.mpr hs1)
  exact h1.add (differentiableAt_zetaDiffSum hs)

end TDLean.Zeta
