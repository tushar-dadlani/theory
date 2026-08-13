/-
  TDLean.Zeta.Continuation -- Brick C9, part 2: the difference series.

  NO COQ ORACLE. From-scratch rule in force (see `TDLean.Zeta.Basic`).

  The classical route to continuing `ζ` past `Re s = 1` without the functional equation:
  for `Re s > 1`,

      ζ(s) = 1/(s−1) + ∑_{m≥1} ( m^{−s} − ∫ₘ^{m+1} x^{−s} dx )

  because `∑_m ∫ₘ^{m+1} x^{−s} dx = ∫₁^∞ x^{−s} dx = 1/(s−1)`. The point is that the
  difference series converges for `Re s > 0`, so the right-hand side continues `ζ` to the
  larger half-plane, with the pole visibly isolated in the `1/(s−1)` term.

  This file defines the difference terms and proves the estimate and summability that make
  that work; each term is `O(‖s‖ m^{−Re s−1})` by the increment bound from `Basic`.
-/
import TDLean.Zeta.Basic

namespace TDLean.Zeta

open Complex Filter Topology intervalIntegral

/-- The `n`-th difference term, with classical index `m = n + 1`:
    `m^{−s} − ∫ₘ^{m+1} x^{−s} dx`. -/
noncomputable def zetaDiff (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), (x : ℂ) ^ (-s)

theorem one_le_idx (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity

/-- `x ↦ x^{−s}` is continuous on `[m, m+1]` for `m > 0`. -/
theorem continuousOn_cpow_neg_uIcc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  refine ContinuousOn.cpow_const ?_ ?_
  · exact Complex.continuous_ofReal.continuousOn.comp continuousOn_id (fun u _ => trivial)
  · intro u hu
    exact Or.inl (by simpa using lt_of_lt_of_le ha hu.1)

/-- The difference term written as a single integral, which is what the estimate needs. -/
theorem zetaDiff_eq_integral (s : ℂ) (n : ℕ) :
    zetaDiff s n = ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
      ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (x : ℂ) ^ (-s) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := one_le_idx n
  have hle : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by linarith
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      ((n : ℝ) + 1) ((n : ℝ) + 2) := (continuousOn_cpow_neg_uIcc hm hle s).intervalIntegrable
  rw [zetaDiff, intervalIntegral.integral_sub _root_.intervalIntegrable_const hint,
    intervalIntegral.integral_const]
  norm_num

/-- **The term estimate.** `‖zetaDiff s n‖ ≤ ‖s‖ · (n+1)^{−Re s−1}` for `Re s > 0`. -/
theorem norm_zetaDiff_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖zetaDiff s n‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := one_le_idx n
  have hle : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by linarith
  rw [zetaDiff_eq_integral]
  have hbd : ∀ x ∈ Set.uIoc ((n : ℝ) + 1) ((n : ℝ) + 2),
      ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖
        ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hmx : ((n : ℝ) + 1) ≤ x := hx.1.le
    have hx1 : x - ((n : ℝ) + 1) ≤ 1 := by linarith [hx.2]
    calc ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖
        ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) * (x - ((n : ℝ) + 1)) :=
          norm_cpow_sub_le hm hmx hs
      _ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) * 1 := by
          have hpos : 0 ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by positivity
          exact mul_le_mul_of_nonneg_left hx1 hpos
      _ = ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := mul_one _
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  calc ‖∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
        ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) * |((n : ℝ) + 2) - ((n : ℝ) + 1)| := this
    _ = ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by norm_num

/-! ### Summability of the bound -/

/-- `∑ (n+1)^{−σ−1}` converges for `σ > 0`. -/
theorem summable_rpow_shift {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ - 1)) := by
  have hp : 1 < σ + 1 := by linarith
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (σ + 1)) :=
    Real.summable_one_div_nat_rpow.mpr hp
  rw [← summable_nat_add_iff 1] at hs
  refine hs.congr fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast
  rw [show (-σ - 1 : ℝ) = -(σ + 1) by ring, Real.rpow_neg hn.le, one_div]

/-- The `zetaDiff` bound is summable for `Re s > 0`. -/
theorem summable_zetaDiff_bound {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
  (summable_rpow_shift hs).mul_left _

/-- Hence the difference series converges absolutely for `Re s > 0`. -/
theorem summable_zetaDiff {s : ℂ} (hs : 0 < s.re) : Summable (zetaDiff s) :=
  Summable.of_norm_bounded (summable_zetaDiff_bound hs) (norm_zetaDiff_le hs)

end TDLean.Zeta
