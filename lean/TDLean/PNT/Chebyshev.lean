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
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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


/-! ### `ψ − θ`: the prime-power correction

    Every `n ≤ x` with `Λ n ≠ 0` that is not prime is `p^k` with `k ≥ 2`, hence `p ≤ √x` and
    `k ≤ log₂ x`. So the correction has at most `(√x+1)(log₂x+1)` terms, each at most `log x`.
    That is `O(√x·log²x) = o(x)`, which is all the Chebyshev bound needs. -/

/-- `θ` is the prime part of `ψ`. -/
theorem theta_eq_sum_vonMangoldt (x : ℝ) :
    theta x = ∑ n ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n := by
  refine Finset.sum_congr rfl fun p hp => ?_
  exact (ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2).symm

/-- The non-prime part. -/
noncomputable def psiErr (x : ℝ) : ℝ :=
  ∑ n ∈ (range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime),
    ArithmeticFunction.vonMangoldt n

theorem psi_eq_theta_add (x : ℝ) : psi x = theta x + psiErr x := by
  rw [theta_eq_sum_vonMangoldt, psiErr, psi]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The set carrying the correction: non-prime prime powers up to `x`. -/
noncomputable def ppSet (x : ℝ) : Finset ℕ :=
  (range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n)

theorem psiErr_eq_sum_ppSet (x : ℝ) :
    psiErr x = ∑ n ∈ ppSet x, ArithmeticFunction.vonMangoldt n := by
  rw [psiErr]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [ppSet, mem_filter] at hn
    exact mem_filter.mpr ⟨hn.1, hn.2.1⟩
  · intro n hn hn'
    rw [mem_filter] at hn
    rw [ppSet, mem_filter] at hn'
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact fun hpp => hn' ⟨hn.1, hn.2, hpp⟩

/-- **The counting bound.** `ppSet x` injects into `√x × log₂x` via `n ↦ (minFac n, exponent)`. -/
theorem card_ppSet_le (x : ℝ) :
    (ppSet x).card ≤ (Nat.sqrt ⌊x⌋₊ + 1) * (Nat.log 2 ⌊x⌋₊ + 1) := by
  classical
  have hcard : (ppSet x).card
      ≤ ((range (Nat.sqrt ⌊x⌋₊ + 1)) ×ˢ (range (Nat.log 2 ⌊x⌋₊ + 1))).card := by
    refine Finset.card_le_card_of_injOn
      (fun n => (n.minFac, n.factorization n.minFac)) ?_ ?_
    · intro n hn
      simp only [ppSet, Finset.mem_coe, mem_filter, mem_range] at hn
      obtain ⟨hlt, hnp, hpp⟩ := hn
      have hle : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp hlt
      have hp : (n.minFac).Prime := Nat.minFac_prime hpp.ne_one
      have hrec : n.minFac ^ n.factorization n.minFac = n := hpp.minFac_pow_factorization_eq
      have hk2 : 2 ≤ n.factorization n.minFac := by
        by_contra hcon
        push_neg at hcon
        have hcases : n.factorization n.minFac = 0 ∨ n.factorization n.minFac = 1 := by omega
        rcases hcases with h0 | h1
        · rw [h0, pow_zero] at hrec; exact hpp.ne_one hrec.symm
        · rw [h1, pow_one] at hrec; exact hnp (hrec ▸ hp)
      refine Finset.mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩
      · have hsq : n.minFac * n.minFac ≤ ⌊x⌋₊ := by
          calc n.minFac * n.minFac = n.minFac ^ 2 := by ring
            _ ≤ n.minFac ^ (n.factorization n.minFac) := Nat.pow_le_pow_right hp.pos hk2
            _ = n := hrec
            _ ≤ ⌊x⌋₊ := hle
        exact Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hsq)
      · have h2k : 2 ^ (n.factorization n.minFac) ≤ ⌊x⌋₊ := by
          calc 2 ^ (n.factorization n.minFac)
              ≤ n.minFac ^ (n.factorization n.minFac) := Nat.pow_le_pow_left hp.two_le _
            _ = n := hrec
            _ ≤ ⌊x⌋₊ := hle
        exact Nat.lt_succ_iff.mpr (Nat.le_log_of_pow_le one_lt_two h2k)
    · intro m hm n hn hmn
      simp only [ppSet, Finset.mem_coe, mem_filter] at hm hn
      have hrm : m.minFac ^ m.factorization m.minFac = m := hm.2.2.minFac_pow_factorization_eq
      have hrn : n.minFac ^ n.factorization n.minFac = n := hn.2.2.minFac_pow_factorization_eq
      rw [Prod.mk.injEq] at hmn
      rw [← hrm, ← hrn, hmn.2, hmn.1]
  simpa using hcard

/-! ### From the counting bound to `ψ(x) = O(x)` -/

theorem vonMangoldt_le_log_of_mem {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ ppSet x) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
  simp only [ppSet, mem_filter, mem_range] at hn
  have hle : (n : ℝ) ≤ x :=
    le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hn.1) (Nat.floor_le (by linarith))
  have hn2 : 2 ≤ n := hn.2.2.two_le
  calc ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    _ ≤ Real.log x := Real.log_le_log (by positivity) hle

theorem psiErr_le_card_mul {x : ℝ} (hx : 1 ≤ x) :
    psiErr x ≤ (ppSet x).card * Real.log x := by
  rw [psiErr_eq_sum_ppSet]
  calc ∑ n ∈ ppSet x, ArithmeticFunction.vonMangoldt n
      ≤ ∑ _n ∈ ppSet x, Real.log x :=
        Finset.sum_le_sum fun n hn => vonMangoldt_le_log_of_mem hx hn
    _ = (ppSet x).card * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]

theorem natSqrt_le_sqrt {x : ℝ} (hx : 0 ≤ x) : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x := by
  have h1 : ((Nat.sqrt ⌊x⌋₊ : ℝ)) ^ 2 ≤ x := by
    have hnat : Nat.sqrt ⌊x⌋₊ ^ 2 ≤ ⌊x⌋₊ := Nat.sqrt_le' ⌊x⌋₊
    calc ((Nat.sqrt ⌊x⌋₊ : ℝ)) ^ 2 = ((Nat.sqrt ⌊x⌋₊ ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnat
      _ ≤ x := Nat.floor_le hx
  calc (Nat.sqrt ⌊x⌋₊ : ℝ) = Real.sqrt (((Nat.sqrt ⌊x⌋₊ : ℝ)) ^ 2) :=
        (Real.sqrt_sq (Nat.cast_nonneg _)).symm
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h1

theorem natLog2_mul_log2_le {x : ℝ} (hx : 1 ≤ x) :
    (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ Real.log x := by
  have hm : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx).ne'
  have hpow : (2 : ℕ) ^ (Nat.log 2 ⌊x⌋₊) ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 hm
  have hr : ((2 : ℝ)) ^ (Nat.log 2 ⌊x⌋₊) ≤ x := by
    calc ((2 : ℝ)) ^ (Nat.log 2 ⌊x⌋₊) = (((2 : ℕ) ^ (Nat.log 2 ⌊x⌋₊) : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hpow
      _ ≤ x := Nat.floor_le (by linarith)
  have h := Real.log_le_log (by positivity) hr
  rwa [Real.log_pow] at h

/-- `log x ≤ 4·x^(1/4)`, written with nested square roots so no `rpow` is needed. -/
theorem log_le_four_mul_sqrt_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  set R : ℝ := Real.sqrt (Real.sqrt x) with hR
  have hS0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hx4 : R ^ 4 = x := by
    have h1 : R ^ 2 = Real.sqrt x := Real.sq_sqrt hS0
    have h2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    calc R ^ 4 = (R ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by rw [h1]
      _ = x := h2
  have hRpos : 0 < R := by
    rcases hR0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hx4; simp at hx4; linarith [hx4 ▸ hx]
  have hlog : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos hRpos
  calc Real.log x = Real.log (R ^ 4) := by rw [hx4]
    _ = 4 * Real.log R := by rw [Real.log_pow]; norm_num
    _ ≤ 4 * (R - 1) := by linarith
    _ ≤ 4 * R := by linarith

/-- **The correction is `O(x)`.** -/
theorem psiErr_mul_log2_le {x : ℝ} (hx : 1 ≤ x) :
    psiErr x * Real.log 2 ≤ 40 * x := by
  set S : ℝ := Real.sqrt x with hSdef
  set R : ℝ := Real.sqrt S with hRdef
  set L : ℝ := Real.log x with hLdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hS1 : 1 ≤ S := by rw [hSdef]; exact Real.one_le_sqrt.mpr hx
  have hR1 : 1 ≤ R := by rw [hRdef]; exact Real.one_le_sqrt.mpr hS1
  have hRS : R ^ 2 = S := Real.sq_sqrt (by linarith)
  have hL4R : L ≤ 4 * R := log_le_four_mul_sqrt_sqrt hx
  have hS2 : S ^ 2 = x := Real.sq_sqrt (by linarith)
  -- card bound, pushed to the reals
  have hNs : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ S := natSqrt_le_sqrt (by linarith)
  have hNl : (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ L := natLog2_mul_log2_le hx
  have hNs0 : (0 : ℝ) ≤ (Nat.sqrt ⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hNl0 : (0 : ℝ) ≤ (Nat.log 2 ⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hcard : ((ppSet x).card : ℝ)
      ≤ ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) := by
    have := card_ppSet_le x
    calc ((ppSet x).card : ℝ)
        ≤ (((Nat.sqrt ⌊x⌋₊ + 1) * (Nat.log 2 ⌊x⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) := by push_cast; ring
  have hstep : psiErr x ≤ ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * L :=
    le_trans (psiErr_le_card_mul hx) (by gcongr)
  -- multiply through by `log 2` and use `Nl · log 2 ≤ L`, `log 2 ≤ 1`
  have hmain : ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * L * Real.log 2
      ≤ (S + 1) * (L + 1) * L := by
    have hexp : ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * Real.log 2
        = (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 + Real.log 2 := by ring
    have h1 : ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * Real.log 2 ≤ L + 1 := by rw [hexp]; linarith
    have h2 : (Nat.sqrt ⌊x⌋₊ : ℝ) + 1 ≤ S + 1 := by linarith
    have heq : ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * L * Real.log 2
        = ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * (((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * Real.log 2) * L := by ring
    rw [heq]
    have hnn1 : (0 : ℝ) ≤ ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * Real.log 2 := by positivity
    have hS1' : (0 : ℝ) ≤ S + 1 := by linarith
    refine mul_le_mul (mul_le_mul h2 h1 hnn1 hS1') (le_refl L) hL0 ?_
    positivity
  have hfin : (S + 1) * (L + 1) * L ≤ 40 * x := by
    have hb1 : S + 1 ≤ 2 * S := by linarith
    have hb2 : L + 1 ≤ 5 * R := by linarith
    have hcalc : (S + 1) * (L + 1) * L ≤ (2 * S) * (5 * R) * (4 * R) := by
      apply mul_le_mul _ hL4R hL0 (by positivity)
      exact mul_le_mul hb1 hb2 (by linarith) (by linarith)
    calc (S + 1) * (L + 1) * L ≤ (2 * S) * (5 * R) * (4 * R) := hcalc
      _ = 40 * S * R ^ 2 := by ring
      _ = 40 * S * S := by rw [hRS]
      _ = 40 * S ^ 2 := by ring
      _ = 40 * x := by rw [hS2]
  calc psiErr x * Real.log 2
      ≤ ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊x⌋₊ : ℝ) + 1) * L * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right hstep hlog2.le
    _ ≤ (S + 1) * (L + 1) * L := hmain
    _ ≤ 40 * x := hfin

/-- **Chebyshev's bound (headline).** `ψ(x) ≤ C·x` with `C = log 4 + 40/log 2`.
    ORACLE: `ChebyshevPrime.v:268 chebyshev_theorem`. -/
theorem psi_le_const_mul {x : ℝ} (hx : 1 ≤ x) :
    psi x ≤ (Real.log 4 + 40 / Real.log 2) * x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : theta x ≤ x * Real.log 4 := theta_le_mul_log4 (by linarith)
  have h2 : psiErr x ≤ 40 / Real.log 2 * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    linarith [psiErr_mul_log2_le hx]
  rw [psi_eq_theta_add]
  nlinarith

end TDLean.PNT

