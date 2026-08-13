/-
  TDLean.Zeta.LogDeriv -- Brick C9 item 2, part 1: `−ζ′(s) = ∑ log(n)·n^{−s}`.

  ORACLE STATUS -- read this before believing the cluster header.

  I previously said C9 item 2 has a Coq oracle in `Ell2Zeta.v : vonmangoldt_zeta_trace`.
  That is only half right, and the weaker half:

    * `Ell2Zeta.v:149 energy_eq_divisor_sum : Hlog n = dsum Lam n`  (`log n = ∑_{d∣n} Λ(d)`)
      IS substantive, and is a genuine oracle for the arithmetic identity.
    * `Ell2Zeta.v:133 vonmangoldt_zeta_trace` is NOT an oracle for `∑Λ(n)n^{−s} = −ζ′/ζ`,
      despite its name and its section header (`:127`) claiming exactly that. The theorem is
      `diag_trace (fun n => Lam n * z s n) N = dvmzeta s N` -- a FINITE trace equals a FINITE
      sum -- and the proof is `apply diag_trace_eq`, i.e. "the trace of a diagonal operator
      is the sum of its diagonal entries". The file's own header (`:22`) is honest about it:
      *"Convergence of the partial traces to the analytic ζ(s) (Re s>1) is a separate
      analytic step."*

  So the analytic half of item 2 is an **overtake**, not cross-verification. Recorded in
  LEDGER.md.

  ## Ban boundary

  `Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt` (the definition of `Λ` and the
  elementary convolution `Λ ∗ 1 = log`) is treated as FOUNDATIONS: it is pure arithmetic
  with no analysis, in the same category as `MonoidAlgebra` or `Complex.Gamma`.
  `Mathlib.NumberTheory.LSeries.*` -- which contains
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, i.e. the headline itself -- stays BANNED.

  This file proves the analytic half's first ingredient by termwise differentiation.
-/
import TDLean.Zeta.Telescope
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace TDLean.Zeta

open Complex Filter Topology Metric

/-- `∑ log(n)·n^{−s}`, the series that is `−ζ′`. -/
noncomputable def logZetaSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, (Real.log n : ℂ) * (1 / (n : ℂ) ^ s)

/-- Termwise derivative of the Dirichlet series. The `n = 0` term is constantly `0` near any
    `s` with `Re s > 0` (since then `s ≠ 0`), and `Real.log 0 = 0`, so the formula holds
    uniformly in `n`. -/
theorem hasDerivAt_zetaTerm (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun w : ℂ => 1 / (n : ℂ) ^ w)
      (-(Real.log n : ℂ) * (1 / (n : ℂ) ^ s)) s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the zero term is locally constant `0`
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hzero : (fun w : ℂ => (1 : ℂ) / ((0 : ℕ) : ℂ) ^ w) =ᶠ[nhds s] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds hs] with w hw
      have hwne : w ≠ 0 := by
        intro h; rw [h] at hw; simp at hw
      rw [Nat.cast_zero, Complex.zero_cpow hwne]; simp
    have h2 : HasDerivAt (fun w : ℂ => (1 : ℂ) / ((0 : ℕ) : ℂ) ^ w) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq hzero
    simpa using h2
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h := hasDerivAt_cpow_neg_exponent hn0 s
    have hcast : (((n : ℕ) : ℝ) : ℂ) = ((n : ℕ) : ℂ) := by push_cast; ring
    rw [hcast] at h
    have heq : ∀ w : ℂ, ((n : ℕ) : ℂ) ^ (-w) = 1 / ((n : ℕ) : ℂ) ^ w := fun w => by
      rw [Complex.cpow_neg, one_div]
    simp only [heq] at h
    exact h

/-- Each term is holomorphic. -/
theorem differentiableOn_zetaTerm (n : ℕ) {U : Set ℂ} (hU : U ⊆ {w : ℂ | 0 < w.re}) :
    DifferentiableOn ℂ (fun w : ℂ => 1 / (n : ℂ) ^ w) U := fun _ hw =>
  (hasDerivAt_zetaTerm n (hU hw)).differentiableAt.differentiableWithinAt

/-- **`ζ′(s) = −∑ log(n)·n^{−s}` on `Re s > 1`.**

    OVERTAKE: no Coq counterpart (`Ell2Zeta.v`'s trace identity is finite-level; see the
    file header). -/
theorem hasSum_deriv_zetaSeries {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => -(Real.log n : ℂ) * (1 / (n : ℂ) ^ s)) (deriv zetaSeries s) := by
  -- work on a small ball where `Re w` is bounded below by `σ₀ > 1`
  set σ₀ : ℝ := (1 + s.re) / 2 with hσ₀
  have hσ₀1 : 1 < σ₀ := by simp only [hσ₀]; linarith
  set ρ : ℝ := (s.re - 1) / 2 with hρdef
  have hρ : 0 < ρ := by simp only [hρdef]; linarith
  have hmem : s ∈ ball s ρ := mem_ball_self hρ
  have hball_re : ∀ w ∈ ball s ρ, σ₀ ≤ w.re := by
    intro w hw
    have hd : ‖w - s‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hw
    have habs : |w.re - s.re| < ρ := by
      calc |w.re - s.re| = |(w - s).re| := by simp
        _ ≤ ‖w - s‖ := Complex.abs_re_le_norm _
        _ < ρ := hd
    have := (abs_lt.mp habs).1
    simp only [hσ₀, hρdef] at this ⊢
    linarith
  have hsub : ball s ρ ⊆ {w : ℂ | 0 < w.re} := fun w hw =>
    lt_of_lt_of_le (by linarith : (0:ℝ) < σ₀) (hball_re w hw)
  -- uniform bound by the convergent `p`-series at `σ₀`
  have hbd : ∀ (n : ℕ) (w : ℂ), w ∈ ball s ρ →
      ‖(1 : ℂ) / (n : ℂ) ^ w‖ ≤ ‖(1 : ℂ) / (n : ℂ) ^ (σ₀ : ℂ)‖ := by
    intro n w hw
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hwne : w ≠ 0 := by
        intro h; rw [h] at hw; have := hball_re 0 hw; simp at this; linarith
      have hσne : (σ₀ : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]; intro h; rw [h] at hσ₀1; linarith
      simp [Complex.zero_cpow hwne, Complex.zero_cpow hσne]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [norm_div, norm_div, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0, norm_one]
      simp only [Complex.ofReal_re]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hn0 _)
      exact Real.rpow_le_rpow_of_exponent_le hn1 (hball_re w hw)
  have hsummable : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ (σ₀ : ℂ)‖) :=
    summable_norm_iff.mpr (summable_zetaTerm (by simpa using hσ₀1))
  have hres := hasSum_deriv_of_summable_norm hsummable
    (fun n => differentiableOn_zetaTerm n hsub) isOpen_ball hbd hmem
  have hderiv : ∀ n : ℕ, deriv (fun w : ℂ => 1 / (n : ℂ) ^ w) s
      = -(Real.log n : ℂ) * (1 / (n : ℂ) ^ s) :=
    fun n => (hasDerivAt_zetaTerm n (by linarith)).deriv
  simpa only [hderiv, zetaSeries] using hres

end TDLean.Zeta
