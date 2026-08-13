/-
  TDLean.PNT.PiCount -- C10, part 12: the prime-counting function and `θ ≤ π·log`.

  `Mathlib.NumberTheory.PrimeCounting` is on the declared ban list, so `π` is defined here
  from scratch, matching the `theta`/`psi` conventions of `Chebyshev.lean`.

  ORACLE for the transfer as a whole: `PNTConditional.v:52 pi_asymp_of_psi`
  (`ψ(N)/N → 1 → π(N)/(N/log N) → 1`) — the *assembled* conditional theorem, not the two
  half-bounds `PiUpperAssembly.v:83` / `ThetaPiBound.v:35` that feed it.
-/
import TDLean.PNT.Transfer

namespace TDLean.PNT

open Finset

/-- `π(x) = #{p ≤ x : p prime}`. -/
noncomputable def piCount (x : ℝ) : ℝ :=
  (((range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ)

theorem piCount_nonneg (x : ℝ) : 0 ≤ piCount x := Nat.cast_nonneg _

/-- **`θ(x) ≤ π(x)·log x`.** Each of the `π(x)` primes `p ≤ x` contributes `log p ≤ log x`.
    ORACLE: `PrimePowerReindex.v:377 psi_le_picount_lnN` (the `ψ` analogue). -/
theorem theta_le_piCount_mul_log {x : ℝ} (hx : 1 ≤ x) :
    theta x ≤ piCount x * Real.log x := by
  have hbound : ∀ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p ≤ Real.log x := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.one_lt.le
    have hple : (p : ℝ) ≤ x :=
      le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hp.1) (Nat.floor_le (by linarith))
    exact Real.log_le_log (by linarith) hple
  calc theta x = ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p := rfl
    _ ≤ ∑ _p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log x := Finset.sum_le_sum hbound
    _ = piCount x * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul, piCount]

/-- The lower half of the transfer: `θ(x)/x ≤ (π(x)·log x)/x`. -/
theorem theta_div_le {x : ℝ} (hx : 1 ≤ x) :
    theta x / x ≤ piCount x * Real.log x / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  exact div_le_div_of_nonneg_right (theta_le_piCount_mul_log hx) hx0.le


/-! ### The upper bound -/

/-- Primes below `y` are at most `y + 1` in number. -/
theorem card_small_primes_le {y : ℝ} (hy : 0 ≤ y) (A : Finset ℕ) :
    ((A.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ y + 1 := by
  have hsub : A.filter (fun p : ℕ => (p : ℝ) ≤ y) ⊆ range (⌊y⌋₊ + 1) := by
    intro p hp
    rw [mem_filter] at hp
    exact mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hp.2))
  have hcard := Finset.card_le_card hsub
  rw [card_range] at hcard
  calc ((A.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = (⌊y⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ y + 1 := by linarith [Nat.floor_le hy]

/-- **`π(x) ≤ x^α + 1 + θ(x)/(α·log x)`** for `0 < α < 1`. The primes in `(x^α, x]` each
    contribute more than `α·log x` to `θ(x)`, and there are at most `x^α + 1` below `x^α`. -/
theorem piCount_le {x α : ℝ} (hx : 1 < x) (hα0 : 0 < α) :
    piCount x ≤ x ^ α + 1 + theta x / (α * Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hden : 0 < α * Real.log x := by positivity
  set A : Finset ℕ := (range (⌊x⌋₊ + 1)).filter Nat.Prime with hA
  set T : Finset ℕ := A.filter (fun p : ℕ => (p : ℝ) ≤ x ^ α) with hT
  set S : Finset ℕ := A.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ x ^ α)) with hS
  have hsplit : (T.card : ℝ) + (S.card : ℝ) = piCount x := by
    rw [hT, hS, piCount, ← hA]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_filter_add_card_filter_not
      (p := fun p : ℕ => (p : ℝ) ≤ x ^ α))
  have hTle : (T.card : ℝ) ≤ x ^ α + 1 :=
    card_small_primes_le (Real.rpow_nonneg hx0.le α) A
  -- every prime in `S` contributes more than `α log x`
  have hSbound : (S.card : ℝ) * (α * Real.log x) ≤ theta x := by
    have hsubset : S ⊆ A := Finset.filter_subset _ _
    have hnn : ∀ p ∈ A, p ∉ S → 0 ≤ Real.log p := by
      intro p hp _
      rw [hA, mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    have hlow : ∀ p ∈ S, α * Real.log x ≤ Real.log p := by
      intro p hp
      rw [hS, mem_filter] at hp
      push_neg at hp
      have hgt : x ^ α < (p : ℝ) := hp.2
      have hrp : Real.log (x ^ α) = α * Real.log x := Real.log_rpow hx0 α
      rw [← hrp]
      exact (Real.log_le_log (Real.rpow_pos_of_pos hx0 α) hgt.le)
    calc (S.card : ℝ) * (α * Real.log x)
        = ∑ _p ∈ S, (α * Real.log x) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ S, Real.log p := Finset.sum_le_sum hlow
      _ ≤ ∑ p ∈ A, Real.log p := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnn
      _ = theta x := rfl
  have hScard : (S.card : ℝ) ≤ theta x / (α * Real.log x) := by
    rw [le_div_iff₀ hden]; exact hSbound
  linarith [hsplit, hTle, hScard]

end TDLean.PNT
