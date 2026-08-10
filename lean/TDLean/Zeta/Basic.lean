/-
  TDLean.Zeta.Basic -- Brick C9, foundations.

  NO COQ ORACLE for this cluster. C9 is the Coq route's own gating blocker:
  `docs/newman_route_status.md` records "holomorphy of PhiMinus at s = 1" as ABSENT,
  because the complex continuation `zetaC` there has no Laurent/pole structure at `1`.

  **From-scratch rule in force.** mathlib's `riemannZeta`, `riemannZeta_residue_one`,
  `riemannZeta_ne_zero_of_one_le_re` and the whole `NumberTheory.LSeries` zeta /
  von-Mangoldt API are BANNED. Everything here is built from `Complex.cpow`, summability,
  and locally-uniform limits.

  This file fixes the Dirichlet series and the elementary estimates that the analytic
  continuation rests on.
-/
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TDLean.Zeta

open Complex Filter Topology intervalIntegral

/-- The Dirichlet series `∑ 1/nˢ`. The `n = 0` term is `1/0ˢ = 0` for `s ≠ 0`, matching
    mathlib's indexing convention so `Complex.summable_one_div_nat_cpow` applies directly. -/
noncomputable def zetaSeries (s : ℂ) : ℂ := ∑' n : ℕ, 1 / (n : ℂ) ^ s

theorem summable_zetaTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
  Complex.summable_one_div_nat_cpow.mpr hs

/-! ### Norms of complex powers of positive reals -/

/-- `‖xˢ‖ = x^(Re s)` for real `x > 0`. -/
theorem norm_cpow_of_pos {x : ℝ} (hx : 0 < x) (s : ℂ) : ‖(x : ℂ) ^ s‖ = x ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx s

@[simp] theorem norm_cpow_neg_of_pos {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ (-s)‖ = x ^ (-s.re) := by
  rw [norm_cpow_of_pos hx]; simp

/-- `u ↦ u^e` is antitone in the base for `e ≤ 0`. -/
theorem rpow_le_rpow_base {m u e : ℝ} (hm : 0 < m) (hmu : m ≤ u) (he : e ≤ 0) :
    u ^ e ≤ m ^ e := Real.rpow_le_rpow_of_nonpos hm hmu he

/-! ### The derivative of `x ↦ x^(-s)` on the positive reals -/

/-- `d/dx x^(-s) = -s · x^(-s-1)` for `x ≠ 0` and `s ≠ 0`. -/
theorem hasDerivAt_cpow_neg {x : ℝ} (hx : x ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
  hasDerivAt_ofReal_cpow_const hx (neg_ne_zero.mpr hs)

/-! ### The key increment estimate

    `‖m^(-s) − x^(-s)‖ ≤ ‖s‖ · m^(-Re s - 1) · (x − m)` for `m ≤ x`, which is what makes the
    difference series `∑ (m^(-s) − ∫ₘ^{m+1} x^(-s) dx)` converge for `Re s > 0`. -/

/-- `‖m^(-s) − x^(-s)‖ ≤ ‖s‖ · m^(-Re s - 1) · (x − m)` for `0 < m ≤ x`. -/
theorem norm_cpow_sub_le {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) {s : ℂ} (hs : 0 < s.re) :
    ‖((m : ℂ) ^ (-s) - (x : ℂ) ^ (-s))‖ ≤ ‖s‖ * m ^ (-s.re - 1) * (x - m) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  -- FTC on `[m, x]`
  have hderiv : ∀ u ∈ Set.uIcc m x, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
      (-s * (u : ℂ) ^ (-s - 1)) u := by
    intro u hu
    rw [Set.uIcc_of_le hmx] at hu
    exact hasDerivAt_cpow_neg (by linarith [hu.1] : u ≠ 0) hs0
  have hcont : ContinuousOn (fun u : ℝ => -s * (u : ℂ) ^ (-s - 1)) (Set.uIcc m x) := by
    rw [Set.uIcc_of_le hmx]
    refine continuousOn_const.mul (ContinuousOn.cpow_const ?_ ?_)
    · exact Complex.continuous_ofReal.continuousOn.comp continuousOn_id (fun u _ => trivial)
    · intro u hu
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hm hu.1
      exact Or.inl (by simpa using hu0)
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  -- bound the integral
  have hbound : ∀ u ∈ Set.uIoc m x, ‖-s * (u : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * m ^ (-s.re - 1) := by
    intro u hu
    rw [Set.uIoc_of_le hmx] at hu
    have hu0 : 0 < u := lt_of_lt_of_le hm hu.1.le
    rw [norm_mul, norm_neg, show (-s - 1 : ℂ) = -(s + 1) by ring,
      norm_cpow_neg_of_pos hu0]
    have : u ^ (-(s + 1).re) ≤ m ^ (-(s + 1).re) :=
      rpow_le_rpow_base hm hu.1.le (by simp; linarith)
    calc ‖s‖ * u ^ (-(s + 1).re) ≤ ‖s‖ * m ^ (-(s + 1).re) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg s)
      _ = ‖s‖ * m ^ (-s.re - 1) := by
            congr 2
            simp [Complex.add_re]
            ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hFTC] at this
  calc ‖((m : ℂ) ^ (-s) - (x : ℂ) ^ (-s))‖ = ‖(x : ℂ) ^ (-s) - (m : ℂ) ^ (-s)‖ :=
        (norm_sub_rev _ _)
    _ ≤ ‖s‖ * m ^ (-s.re - 1) * |x - m| := this
    _ = ‖s‖ * m ^ (-s.re - 1) * (x - m) := by rw [abs_of_nonneg (by linarith)]

end TDLean.Zeta
