/-
  TDLean.FE.Strip -- cluster A13: the critical strip and the trivial zeros.

  What the functional equation buys, now that `completedZeta_symm` and `completedZeta_eq`
  are both in hand:

  * `completedZeta_ne_zero_of_one_lt_re` — `Λ(s) ≠ 0` for `Re s > 1`, because each of the
    three factors `π^{−s/2}`, `Γ(s/2)`, `ζ(s)` is nonzero there.
  * `completedZeta_ne_zero_of_re_lt_zero` — hence `Λ(s) ≠ 0` for `Re s < 0`, **by symmetry
    alone**. This is the step that was unavailable before the functional equation.
  * `completedZeta_zeros_in_strip` — so every zero of `Λ` has `0 ≤ Re s ≤ 1`.

  **On the trivial zeros, stated honestly.** `zetaFE` continues `ζ` to `Re s < 0` by
  `ζ(s) := Λ(s)·π^{s/2}/Γ(s/2)`, and `zetaFE_trivial_zero` says it vanishes at `s = −2n`.
  That statement is *partly conventional*: mathlib assigns `Γ` the junk value `0` at its
  poles, so `Λ/Γ` there is `Λ/0 = 0` by Lean's division convention rather than by a limit.
  The mathematical content is the companion theorem
  `completedZeta_ne_zero_at_trivial` — `Λ(−2n) ≠ 0` — which says the zero comes **entirely
  from the Γ-factor's pole and not from `Λ`**. That one is a real theorem, and it is the
  reason the trivial zeros are where they are.

  ORACLE for the confinement: `XiTwoSided.v`. Note the earlier ledger finding that Coq's
  `XiC_zeros_in_strip` sits under two `Hypothesis` declarations (`H_compl`, `H_gamma`);
  the statements here are unconditional.
-/
import TDLean.FE.Mellin.FunctionalEquation
import TDLean.Zeta.NonVanishing
import TDLean.Zeta.Conj
import TDLean.Zeta.CriticalLine
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

theorem pi_cpow_ne_zero (w : ℂ) : ((π : ℝ) : ℂ) ^ w ≠ 0 := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [Ne, Complex.cpow_eq_zero_iff]
  tauto

theorem gamma_half_ne_zero {s : ℂ} (hs : 0 < s.re) : Complex.Gamma (s / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  rw [Complex.div_ofNat_re]
  linarith

/-- **`Λ(s) ≠ 0` for `Re s > 1`:** all three factors are nonzero there. -/
theorem completedZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : completedZeta s ≠ 0 := by
  rw [completedZeta_eq hs]
  exact mul_ne_zero (mul_ne_zero (pi_cpow_ne_zero _) (gamma_half_ne_zero (by linarith)))
    (zetaSeries_ne_zero hs)

/-- **`Λ(s) ≠ 0` for `Re s < 0`, by symmetry alone.** This is the half that the functional
    equation supplies and that nothing before it could reach. -/
theorem completedZeta_ne_zero_of_re_lt_zero {s : ℂ} (hs : s.re < 0) : completedZeta s ≠ 0 := by
  rw [← completedZeta_symm s]
  refine completedZeta_ne_zero_of_one_lt_re ?_
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- **The zeros of `Λ` lie in the closed strip `0 ≤ Re s ≤ 1`.** -/
theorem completedZeta_zeros_in_strip {s : ℂ} (h : completedZeta s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra hc
    exact completedZeta_ne_zero_of_re_lt_zero (not_le.mp hc) h
  · by_contra hc
    exact completedZeta_ne_zero_of_one_lt_re (not_le.mp hc) h

/-- The strip is nonempty as a constraint: `Λ` is nonzero at `2`, off the strip. -/
theorem completedZeta_ne_zero_nonvacuous : completedZeta 2 ≠ 0 :=
  completedZeta_ne_zero_of_one_lt_re (by norm_num)

/-! ### The continuation of `ζ`, and the trivial zeros -/

/-- `ζ` continued by the functional equation: `ζ(s) = Λ(s)·π^{s/2}/Γ(s/2)`. -/
noncomputable def zetaFE (s : ℂ) : ℂ :=
  completedZeta s * ((π : ℝ) : ℂ) ^ (s / 2) / Complex.Gamma (s / 2)

/-- On `Re s > 1` the continuation agrees with the Dirichlet series, so `zetaFE` really does
    extend `ζ` rather than defining something new. -/
theorem zetaFE_eq_zetaSeries {s : ℂ} (hs : 1 < s.re) : zetaFE s = zetaSeries s := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := gamma_half_ne_zero (by linarith)
  rw [zetaFE, completedZeta_eq hs,
    show ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaSeries s * ((π : ℝ) : ℂ) ^ (s / 2)
      = (((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ (s / 2))
        * (Complex.Gamma (s / 2) * zetaSeries s) by ring,
    ← Complex.cpow_add _ _ hπ, show (-s / 2 + s / 2 : ℂ) = 0 by ring, Complex.cpow_zero,
    one_mul, mul_comm (Complex.Gamma (s / 2)) (zetaSeries s), mul_div_assoc, div_self hΓ,
    mul_one]

theorem gamma_neg_two_nat_half (n : ℕ) : Complex.Gamma ((-(2 * (n : ℂ))) / 2) = 0 := by
  rw [show (-(2 * (n : ℂ))) / 2 = -(n : ℂ) by ring]
  exact Complex.Gamma_neg_nat_eq_zero n

/-- **The trivial zeros.** `ζ(−2n) = 0`.

    Read the caveat in the module docstring: mathlib assigns `Γ` the junk value `0` at its
    poles, so this follows from Lean's `x/0 = 0` convention. The theorem with content is
    `completedZeta_ne_zero_at_trivial` below. -/
theorem zetaFE_trivial_zero (n : ℕ) : zetaFE (-(2 * (n : ℂ))) = 0 := by
  rw [zetaFE, gamma_neg_two_nat_half, div_zero]

/-- **The content of the trivial zeros:** `Λ(−2n) ≠ 0` for `n ≥ 1`, so the zero of `ζ` at
    `−2n` comes entirely from the pole of the `Γ`-factor, not from `Λ`. -/
theorem completedZeta_ne_zero_at_trivial {n : ℕ} (hn : 1 ≤ n) :
    completedZeta (-(2 * (n : ℂ))) ≠ 0 := by
  refine completedZeta_ne_zero_of_re_lt_zero ?_
  have hre : (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) := by simp
  rw [hre]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-! ### Conjugation, and the Klein four-group on the zeros

    `ψ` is real on the positive reals, so `Λ` commutes with conjugation. Combined with
    `completedZeta_symm` this closes the four-group `{s, 1−s, s̄, 1−s̄}` acting on the zero
    set of `Λ`. Both generators are now theorems rather than hypotheses. -/

/-- `ψ` is real-valued on `ℝ`: every term `e^{−πn²u}` has a real argument. -/
theorem conj_psiTheta (u : ℝ) : (starRingEnd ℂ) (psiTheta u) = psiTheta u := by
  rw [psiTheta, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/-- **`Λ(s̄) = conj(Λ(s))`.** -/
theorem completedZeta_conj (s : ℂ) :
    completedZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedZeta s) := by
  have e1 : (starRingEnd ℂ) (s / 2 - 1) = (starRingEnd ℂ) s / 2 - 1 := by simp [map_ofNat]
  have e2 : (starRingEnd ℂ) ((1 - s) / 2 - 1) = (1 - (starRingEnd ℂ) s) / 2 - 1 := by
    simp [map_ofNat]
  rw [completedZeta, completedZeta]
  simp only [map_add, map_sub, map_div₀, map_one]
  congr 1
  -- `rw [← integral_conj]` fails on an `RCLike ℂ` instance mismatch; stating the rewrite
  -- with its expected type lets elaboration bridge the defeq instead.
  rw [show (starRingEnd ℂ) (∫ u in Ioi (1 : ℝ),
        ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * psiTheta u)
      = ∫ u in Ioi (1 : ℝ), (starRingEnd ℂ)
        (((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * psiTheta u)
      from integral_conj.symm]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := by linarith [mem_Ioi.mp hu]
  rw [map_mul, map_add, conj_psiTheta, conj_cpow_ofReal_pos hu0, conj_cpow_ofReal_pos hu0,
    e1, e2]

/-- **The Klein four-group.** The zero set of `Λ` is closed under `s ↦ 1−s`, `s ↦ s̄`, and
    hence under their composite `s ↦ 1−s̄` — the reflection whose fixed-point set is exactly
    the critical line (`Zeta.refl_fixed_iff`). -/
theorem completedZeta_zero_quadruple {s : ℂ} (h : completedZeta s = 0) :
    completedZeta (1 - s) = 0 ∧ completedZeta ((starRingEnd ℂ) s) = 0
      ∧ completedZeta (1 - (starRingEnd ℂ) s) = 0 := by
  have h1 : completedZeta (1 - s) = 0 := by rw [completedZeta_symm s]; exact h
  have h2 : completedZeta ((starRingEnd ℂ) s) = 0 := by
    rw [completedZeta_conj, h, map_zero]
  exact ⟨h1, h2, by rw [completedZeta_symm ((starRingEnd ℂ) s)]; exact h2⟩

/-- The composite generator is exactly `Zeta.refl`, whose fixed points are the critical
    line. So: **the zero set of `Λ` is invariant under an antiholomorphic involution whose
    fixed-point set is `Re s = 1/2`** — and RH is the statement that the zeros in the strip
    are precisely its fixed points. Stating it does not prove it. -/
theorem completedZeta_zeros_refl_invariant {s : ℂ} (h : completedZeta s = 0) :
    completedZeta (TDLean.Zeta.refl s) = 0 :=
  (completedZeta_zero_quadruple h).2.2

end TDLean.FE
