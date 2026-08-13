/-
  TDLean.Zeta.Conj -- conjugation symmetry of the zeta continuation.

      ζ(s̄) = conj(ζ(s))

  so the zero set is closed under conjugation: **symmetric about the real axis**. This needs
  **no functional equation** — only that the Dirichlet coefficients are real.

  ## Why this is an overtake, not a re-proof

  A repo-wide search finds **zero** Coq results connecting `Cconj` to `zetaC`. Every
  conjugation result in `spectral-theory/` is about `XiC`, the theta-tail function
  (`ZetaZeroQuadruple.v:71 TC_conj`, `:111 XiC_conj`, `:125 XiC_zero_conj`) — and
  `ZetaXiLink.v:18` ties `XiC` to ζ only on the **real ray `s > 1`**. So none of them
  constrains a zero of ζ off that ray. mathlib has no `riemannZeta (conj s) = conj (riemannZeta s)`
  either; `Complex.Gamma_conj` (`Gamma/Basic.lean:359`) is the closest model.

  ## The one thing that made this easy

  Root-level `integral_conj` (`MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:175`) is
  **unconditional** — no integrability hypothesis — and `intervalIntegral` unfolds to a
  difference of set integrals. So conjugation passes through the interval integral in one
  `simp only`, with no side goals and no `IsScalarTower ℝ ℂ ℂ` diamond to dodge.
-/
import TDLean.Zeta.Telescope

namespace TDLean.Zeta

open Complex

/-! ### Conjugation passes through each ingredient -/

/-- For a positive real base, `x^w = exp(log x · w)` — reducing `cpow` to `exp` of a *real*
    logarithm, where conjugation is transparent. -/
theorem cpow_ofReal_pos_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  have hne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log, Complex.arg_ofReal_of_nonneg hx.le]
  simp

theorem conj_cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (starRingEnd ℂ) (((x : ℝ) : ℂ) ^ w) = ((x : ℝ) : ℂ) ^ ((starRingEnd ℂ) w) := by
  rw [cpow_ofReal_pos_eq_exp hx, cpow_ofReal_pos_eq_exp hx, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal]

/-- **Conjugation through an interval integral**, unconditionally. -/
theorem conj_intervalIntegral (f : ℝ → ℂ) (a b : ℝ) :
    (starRingEnd ℂ) (∫ x in a..b, f x) = ∫ x in a..b, (starRingEnd ℂ) (f x) := by
  simp only [intervalIntegral, map_sub]
  congr 1 <;> exact (_root_.integral_conj).symm

/-! ### …hence through the whole continuation -/

theorem zetaDiff_conj (s : ℂ) (n : ℕ) :
    zetaDiff ((starRingEnd ℂ) s) n = (starRingEnd ℂ) (zetaDiff s n) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by linarith
  have hneg : -((starRingEnd ℂ) s) = (starRingEnd ℂ) (-s) := (map_neg _ _).symm
  rw [zetaDiff, zetaDiff, map_sub, conj_intervalIntegral, hneg,
    ← conj_cpow_ofReal_pos hpos]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hle] at hx
  have hx0 : (0 : ℝ) < x := by linarith [hx.1]
  exact (conj_cpow_ofReal_pos hx0 (-s)).symm

theorem zetaDiffSum_conj (s : ℂ) :
    zetaDiffSum ((starRingEnd ℂ) s) = (starRingEnd ℂ) (zetaDiffSum s) := by
  rw [zetaDiffSum, zetaDiffSum, Complex.conj_tsum]
  exact tsum_congr fun n => zetaDiff_conj s n

/-- **`ζ(s̄) = conj(ζ(s))`.** -/
theorem zetaCont_conj (s : ℂ) :
    zetaCont ((starRingEnd ℂ) s) = (starRingEnd ℂ) (zetaCont s) := by
  rw [zetaCont, zetaCont, map_add, zetaDiffSum_conj]
  congr 1
  rw [map_div₀, map_one, map_sub, map_one]

/-- **The zero set is symmetric about the real axis.** -/
theorem zetaCont_eq_zero_conj {s : ℂ} (h : zetaCont s = 0) :
    zetaCont ((starRingEnd ℂ) s) = 0 := by
  rw [zetaCont_conj, h, map_zero]

/-- Non-vacuity: `ζ` is real on the real axis, so conjugation acts trivially there. -/
theorem zetaCont_conj_nonvacuous (x : ℝ) :
    zetaCont ((starRingEnd ℂ) ((x : ℝ) : ℂ)) = (starRingEnd ℂ) (zetaCont ((x : ℝ) : ℂ)) :=
  zetaCont_conj _

end TDLean.Zeta
