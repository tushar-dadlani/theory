/-
  TDLean.Zeta.Mertens -- C9 item 3, phase 1: the Mertens "3 + 4cos + cos 2" inequality.

  NO COQ ORACLE. From-scratch rule in force.

  For `σ > 1` and any real `t`, with `F = −ζ′/ζ = L(Λ)`:

      3·Re F(σ) + 4·Re F(σ+it) + Re F(σ+2it)
        = ∑ₙ Λ(n)·n^(−σ)·[3 + 4cos(t log n) + cos(2t log n)]  ≥ 0

  since `Λ(n) ≥ 0` and `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`.

  ## No Euler product

  mathlib derives this via `log ζ` and the Euler product
  (`LSeries/Nonvanishing.lean:220 re_log_comb_nonneg'` -- banned, and `private` besides).
  Working with `−ζ′/ζ` instead avoids that entirely: its Dirichlet series is already in hand
  (`LS_vonMangoldt_eq`) and its coefficients `Λ(n)` are already non-negative. So this file
  needs no Euler product, no `log ζ`, and no Taylor series of `log`.
-/
import TDLean.Zeta.VonMangoldt

namespace TDLean.Zeta

open Complex Filter Topology

/-! ### The trig identity -/

theorem three_add_four_cos_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h : 3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
    rw [Real.cos_two_mul]; ring
  rw [h]
  positivity

/-! ### Real part of `n^(−s)` -/

theorem cpow_neg_re {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (((n : ℂ)) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
  have hcast : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by push_cast; ring
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [hcast, Complex.log, Complex.arg_ofReal_of_nonneg hn0.le]
    simp
  rw [hlog, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.neg_re, Complex.neg_im]
  congr 1
  · rw [Real.rpow_def_of_pos hn0]
  · rw [show Real.log n * -s.im = -(s.im * Real.log n) by ring, Real.cos_neg]


/-! ### Real part of the von Mangoldt series -/

/-- Real part of a single term. -/
theorem re_LS_LamC_term (n : ℕ+) (s : ℂ) :
    (LamC (n : ℕ) / ((n : ℕ) : ℂ) ^ s).re
      = ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-s.re)
          * Real.cos (s.im * Real.log (n : ℕ)) := by
  have hdiv : LamC (n : ℕ) / ((n : ℕ) : ℂ) ^ s = LamC (n : ℕ) * (((n : ℕ) : ℂ)) ^ (-s) := by
    rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [hdiv, LamC, Complex.re_ofReal_mul, cpow_neg_re n.pos]
  ring

/-- The summand, as a real function. -/
noncomputable def mertensTerm (σ θscale : ℝ) (n : ℕ+) : ℝ :=
  ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ)
    * Real.cos (θscale * Real.log (n : ℕ))

theorem summable_mertensTerm {σ : ℝ} (hσ : 1 < σ) (θscale : ℝ) :
    Summable (mertensTerm σ θscale) := by
  have hs : (1 : ℝ) < (((σ : ℂ) + θscale * Complex.I)).re := by simpa using hσ
  have h : Summable (fun n : ℕ+ =>
      (LamC (n : ℕ) / ((n : ℕ) : ℂ) ^ ((σ : ℂ) + θscale * Complex.I)).re) :=
    (Complex.hasSum_re ((summable_norm_LamC hs).of_norm).hasSum).summable
  refine h.congr fun n => ?_
  rw [re_LS_LamC_term, mertensTerm]
  simp

theorem re_LS_LamC {s : ℂ} (hs : 1 < s.re) :
    (LS LamC s).re = ∑' n : ℕ+, mertensTerm s.re s.im n := by
  rw [LS, Complex.re_tsum ((summable_norm_LamC hs).of_norm)]
  exact tsum_congr fun n => re_LS_LamC_term n s

/-! ### The inequality -/

/-- **Mertens' inequality.** For `σ > 1` and any real `t`,
    `3·Re F(σ) + 4·Re F(σ+it) + Re F(σ+2it) ≥ 0`, where `F = L(Λ) = −ζ′/ζ`. -/
theorem mertens_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (LS LamC (σ : ℂ)).re + 4 * (LS LamC ((σ : ℂ) + t * Complex.I)).re
      + (LS LamC ((σ : ℂ) + 2 * t * Complex.I)).re := by
  have h0 : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have h1 : (1 : ℝ) < (((σ : ℂ) + t * Complex.I)).re := by simpa using hσ
  have h2 : (1 : ℝ) < (((σ : ℂ) + 2 * t * Complex.I)).re := by simpa using hσ
  have e0 : (LS LamC (σ : ℂ)).re = ∑' n : ℕ+, mertensTerm σ 0 n := by
    rw [re_LS_LamC h0]; simp
  have e1 : (LS LamC ((σ : ℂ) + t * Complex.I)).re = ∑' n : ℕ+, mertensTerm σ t n := by
    rw [re_LS_LamC h1]; simp
  have e2 : (LS LamC ((σ : ℂ) + 2 * t * Complex.I)).re
      = ∑' n : ℕ+, mertensTerm σ (2 * t) n := by
    rw [re_LS_LamC h2]; simp
  rw [e0, e1, e2, ← tsum_mul_left, ← tsum_mul_left,
    ← (summable_mertensTerm hσ 0).mul_left 3 |>.tsum_add ((summable_mertensTerm hσ t).mul_left 4),
    ← ((summable_mertensTerm hσ 0).mul_left 3 |>.add
        ((summable_mertensTerm hσ t).mul_left 4)).tsum_add (summable_mertensTerm hσ (2 * t))]
  refine tsum_nonneg fun n => ?_
  have hn1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.one_le
  have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := by linarith
  set θ : ℝ := t * Real.log (n : ℕ) with hθ
  have hkey : 3 * mertensTerm σ 0 n + 4 * mertensTerm σ t n + mertensTerm σ (2 * t) n
      = ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ)
          * (3 + 4 * Real.cos θ + Real.cos (2 * θ)) := by
    simp only [mertensTerm, hθ, zero_mul, Real.cos_zero]
    rw [show 2 * t * Real.log (n : ℕ) = 2 * (t * Real.log (n : ℕ)) by ring]
    ring
  rw [hkey]
  have hnn : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hn0.le _)
  exact mul_nonneg hnn (three_add_four_cos_nonneg θ)

/-! ### Non-vacuity -/

/-- The hypotheses of `summable_mertensTerm` are satisfiable: the series really exists. -/
theorem summable_mertensTerm_nonvacuous : Summable (mertensTerm 2 1) :=
  summable_mertensTerm (by norm_num) 1

end TDLean.Zeta
