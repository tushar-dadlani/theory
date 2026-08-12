/-
  TDLean.FE.Mellin.Term -- cluster A3: the single-term Mellin integral.

      ∫₀^∞ t^{s/2−1} e^{−πn²t} dt  =  π^{−s/2} · n^{−s} · Γ(s/2)

  Summing this over `n ≥ 1` is what turns `ψ(t) = ∑_{n≥1} e^{−πn²t}` into
  `π^{−s/2}Γ(s/2)ζ(s)` — the completed zeta. This file does the single term; the interchange
  of sum and integral is the next brick.

  ORACLE: `MellinTail.v:143 T_exists` / `:183 T_spec` define `T(s) = ∫₁^∞ t^{s/2−1}ψ(t)dt`
  as a convergent improper integral, and `MellinTailSeries.v:214 tail_series` gives its
  term-by-term expansion. The Coq side works with the *tail* `∫₁^∞`; this is the full
  `∫₀^∞` of a single term, which is where the `Γ` comes from.

  `Gamma.Basic` is not gate-banned (only `Gamma.Deligne` is), so `Complex.Gamma` and
  `integral_cpow_mul_exp_neg_mul_Ioi` are available.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace TDLean.FE

open Complex Real MeasureTheory Set

/-- For a positive real base, `x^w = exp(log x · w)`. -/
theorem cpow_pos_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  have hne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log, Complex.arg_ofReal_of_nonneg hx.le]
  simp

/-- `(1/(πn²))^{s/2} = π^{−s/2}·n^{−s}`. -/
theorem scale_factor {s : ℂ} (n : ℕ+) :
    (1 / ((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) ^ (s / 2)
      = ((π : ℝ) : ℂ) ^ (-s / 2) * (((n : ℕ) : ℝ) : ℂ) ^ (-s) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hprod : (0 : ℝ) < π * ((n : ℕ) : ℝ) ^ 2 := by positivity
  have hinv : (0 : ℝ) < 1 / (π * ((n : ℕ) : ℝ) ^ 2) := by positivity
  have hcast : (1 / ((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      = ((1 / (π * ((n : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, cpow_pos_eq_exp hinv, cpow_pos_eq_exp hpi, cpow_pos_eq_exp hn, ← Complex.exp_add]
  congr 1
  have hlog : Real.log (1 / (π * ((n : ℕ) : ℝ) ^ 2))
      = -(Real.log π) - 2 * Real.log ((n : ℕ) : ℝ) := by
    rw [one_div, Real.log_inv, Real.log_mul hpi.ne' (by positivity), Real.log_pow]
    push_cast; ring
  rw [hlog]
  push_cast
  ring

/-- **The single-term Mellin integral.** -/
theorem mellin_gaussian_term {s : ℂ} (hs : 0 < s.re) (n : ℕ+) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1)
        * Complex.exp (-(((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * ((t : ℝ) : ℂ))))
      = ((π : ℝ) : ℂ) ^ (-s / 2) * (((n : ℕ) : ℝ) : ℂ) ^ (-s) * Complex.Gamma (s / 2) := by
  have hhalf : s / 2 = ((1 / 2 : ℝ) : ℂ) * s := by push_cast; ring
  have hs2 : 0 < (s / 2).re := by
    rw [hhalf, Complex.re_ofReal_mul]; linarith
  have hr : (0 : ℝ) < π * ((n : ℕ) : ℝ) ^ 2 := by
    have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    positivity
  have hmain := integral_cpow_mul_exp_neg_mul_Ioi (a := s / 2)
    (r := π * ((n : ℕ) : ℝ) ^ 2) hs2 hr
  rw [hmain, scale_factor n]

end TDLean.FE
