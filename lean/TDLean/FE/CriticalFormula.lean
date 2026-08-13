/-
  TDLean.FE.CriticalFormula -- cluster A21: the critical line as one real function.

  The numerical route to existence needs a sign change of `ξ` along `Re s = 1/2`. `A18`/`A19`
  give one endpoint (`ξ(1/2) > 0`, real). This file reduces the *whole* line to a single
  explicit real-valued function of a real variable:

      Z(t) := 1/2 − (t² + 1/4)·Re M(−3/4 + i·t/2),        ξ(1/2 + it) = Z(t)

  Two things make this collapse. First `mellinTail_conj`: `M(w̄) = conj(M(w))`, because `ψ` is
  real on `ℝ`. Second, at `s = 1/2 + it` the two exponents in `ξ` are **conjugates** of each
  other — `s/2 − 1 = −3/4 + it/2` and `(1−s)/2 − 1` is its conjugate — so the pair sums to
  `2·Re M`, and the prefactor `s(s−1)/2 = −(t²+1/4)/2` is real. Everything imaginary cancels
  structurally rather than numerically.

  **What remains, precisely.** Existence of a nontrivial zero below height `T` is now exactly
  `∃ t ∈ (0,T), Z(t) < 0`, with `Z(0) > 0` already proved. `Z` is one real integral,

      Re M(−3/4 + it/2) = ∫₁^∞ u^{−3/4}·cos((t/2)·log u)·ψ(u) du,

  and the first zero sits at `t ≈ 14.13`, where `Z` is of size `~10⁻³` against a leading term
  of `1/2`. Deciding its sign therefore needs `Re M` to roughly five significant figures — a
  rigorous oscillatory quadrature with no interval-arithmetic infrastructure in this
  development. **No sign change is proved here, and no nontrivial zero is exhibited.**
-/
import TDLean.FE.Growth

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-- `M(w̄) = conj(M(w))`, because `ψ` is real on the positive reals. -/
theorem mellinTail_conj (w : ℂ) :
    mellinTail ((starRingEnd ℂ) w) = (starRingEnd ℂ) (mellinTail w) := by
  rw [mellinTail, mellinTail,
    show (starRingEnd ℂ) (∫ u in Ioi (1 : ℝ), (u : ℂ) ^ w * psiTheta u)
      = ∫ u in Ioi (1 : ℝ), (starRingEnd ℂ) ((u : ℂ) ^ w * psiTheta u) from integral_conj.symm]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := by linarith [mem_Ioi.mp hu]
  rw [map_mul, conj_psiTheta, conj_cpow_ofReal_pos hu0]

/-- **`Z`, the critical line as a real function.** -/
noncomputable def Zline (t : ℝ) : ℝ :=
  1 / 2 - (t ^ 2 + 1 / 4) * (mellinTail (-3 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I)).re

/-- **The reduction.** `ξ` on the critical line *is* `Z`, with no imaginary part left over. -/
theorem xi_critical_formula (t : ℝ) :
    xi (1 / 2 + (t : ℂ) * Complex.I) = ((Zline t : ℝ) : ℂ) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  set w : ℂ := -3 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I with hw
  have hw1 : (1 / 2 + (t : ℂ) * Complex.I) / 2 - 1 = w := by
    rw [hw]; push_cast; ring
  have hw2 : (1 - (1 / 2 + (t : ℂ) * Complex.I)) / 2 - 1 = (starRingEnd ℂ) w := by
    rw [hw]
    simp only [map_add, map_div₀, map_neg, map_mul, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    push_cast
    ring
  have hpre : (1 / 2 + (t : ℂ) * Complex.I) * ((1 / 2 + (t : ℂ) * Complex.I) - 1) / 2
      = ((-(t ^ 2 + 1 / 4) / 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination ((t : ℂ) ^ 2 / 2) * hI
  -- fold the `Zline` unfolding back to `w` before `push_cast`: otherwise `push_cast`
  -- rewrites `↑(t/2)` *inside* `mellinTail`'s argument and the two sides stop matching
  rw [xi, hw1, hw2, mellinTail_conj, Complex.add_conj, hpre, Zline, ← hw]
  push_cast
  ring

/-- Consistency at `t = 0`: the formula reproduces `ξ(1/2)`. -/
theorem xi_critical_formula_zero : xi (1 / 2 : ℂ) = ((Zline 0 : ℝ) : ℂ) := by
  have h := xi_critical_formula 0
  simpa using h

/-- **`Z(0) > 0`** — one endpoint of the intermediate-value argument, from `A19`. -/
theorem Zline_zero_pos : 0 < Zline 0 := by
  have h := xi_half_re_pos
  rw [xi_critical_formula_zero] at h
  simpa using h

/-- **Existence of a nontrivial zero on the critical line below height `T`, reduced.**

    `Z` is continuous nowhere-proved here, so this is stated as the implication that a sign
    change *plus* continuity would give a zero — not as a completed argument. What it records
    is that the analytic content is now entirely in the sign of one real integral. -/
theorem xi_eq_zero_of_Zline_eq_zero {t : ℝ} (h : Zline t = 0) :
    xi (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
  rw [xi_critical_formula, h]
  norm_num

/-- And such a zero lies on the critical line, as `xi_zeros_in_strip` would then place it. -/
theorem re_eq_half_of_Zline_eq_zero (t : ℝ) :
    (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
  simp

end TDLean.FE
