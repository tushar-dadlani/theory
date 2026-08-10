/-
  TDLean.PNT.Chebyshev -- C10, part 1: the Chebyshev functions and the bound `θ(x) ≤ x·log 4`.

  ORACLE: `spectral-theory/ChebyshevPrime.v` (`theta`, `psi`, `theta_le_psi`,
  `chebyshev_theorem`). This is genuine cross-verification, unlike cluster C9.

  **Built from scratch on purpose.** `Mathlib.NumberTheory.Chebyshev` has `Chebyshev.psi`,
  `Chebyshev.theta` and `psi_le_const_mul_self` ready-made, and its import closure is free of
  the `LSeries` tree -- but `scripts/check_sorry.sh` has banned
  `Mathlib.NumberTheory.(Chebyshev|PrimeCounting)` since the first scaffold commit, precisely
  because `ChebyshevPrime.v` is a Coq oracle and importing would destroy the cross-check.
  Only `Mathlib.NumberTheory.Primorial` (elementary, no prime-counting content) is used.

  The route: `θ(x) = log(⌊x⌋#)` and `n# ≤ 4ⁿ`, hence `θ(x) ≤ x·log 4`.
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TDLean.PNT

open Finset

/-- Chebyshev's `θ(x) = ∑_{p ≤ x} log p`. -/
noncomputable def theta (x : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p

/-- Chebyshev's `ψ(x) = ∑_{n ≤ x} Λ(n)`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ n ∈ range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n

theorem theta_nonneg (x : ℝ) : 0 ≤ theta x := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp' : Nat.Prime p := (mem_filter.mp hp).2
  exact Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)

theorem psi_nonneg (x : ℝ) : 0 ≤ psi x :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- `θ(x)` is the logarithm of the primorial of `⌊x⌋`. -/
theorem theta_eq_log_primorial (x : ℝ) :
    theta x = Real.log (primorial ⌊x⌋₊) := by
  rw [primorial, Nat.cast_prod, Real.log_prod]
  · rfl
  · intro p hp
    have hp' : Nat.Prime p := (mem_filter.mp hp).2
    exact_mod_cast hp'.ne_zero

/-- **Chebyshev's bound.** `θ(x) ≤ x · log 4`, from `n# ≤ 4ⁿ`. -/
theorem theta_le_mul_log4 {x : ℝ} (hx : 0 ≤ x) : theta x ≤ x * Real.log 4 := by
  have hpos : (0 : ℝ) < (primorial ⌊x⌋₊ : ℝ) := by exact_mod_cast primorial_pos ⌊x⌋₊
  have hle : (primorial ⌊x⌋₊ : ℝ) ≤ (4 : ℝ) ^ (⌊x⌋₊ : ℕ) := by
    exact_mod_cast primorial_le_4_pow ⌊x⌋₊
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc theta x = Real.log (primorial ⌊x⌋₊) := theta_eq_log_primorial x
    _ ≤ Real.log ((4 : ℝ) ^ (⌊x⌋₊ : ℕ)) := Real.log_le_log hpos hle
    _ = (⌊x⌋₊ : ℝ) * Real.log 4 := by rw [Real.log_pow]
    _ ≤ x * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (Nat.floor_le hx) hlog4

end TDLean.PNT
