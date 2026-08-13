/-
  TDLean.FE.Continuation -- cluster A16: `ζ` continued to `ℂ \ {0,1}`, and the trivial zeros
  made genuine.

  `zetaFE s = Λ(s)·π^{s/2}/Γ(s/2)` was defined in `Strip.lean` but nothing was known about its
  regularity, and `zetaFE_trivial_zero` was proved by Lean's `x/0 = 0` convention — true, but
  the proof was not the mathematics.

  **What fixes it is that `1/Γ` is entire** (`Complex.differentiable_one_div_Gamma`). mathlib
  assigns `Γ` the value `0` at its poles, and that assignment is not arbitrary: it is exactly
  the one making `s ↦ (Γ s)⁻¹` differentiable on all of `ℂ`. Writing `zetaFE` as a *product*
  with `(Γ(s/2))⁻¹` rather than a quotient therefore gives:

  * `differentiableAt_zetaFE` — `ζ` is holomorphic on `ℂ \ {0,1}`, the first statement in this
    development that it continues past `Re s > 0` at all;
  * `zetaFE_eq_zetaCont` — and it agrees with `zetaCont` where both are defined, so it really
    is *the* continuation rather than a rival function;
  * `zetaFE_trivial_zero_genuine` — so `ζ(−2n) = 0` is now the vanishing of a **holomorphic
    function at a point**, not a division by zero;
  * `zetaFE_eq_zero_iff_of_re_lt_zero` — and off the strip those are the **only** zeros.

  `s = 0` is a removable singularity (`Λ`'s pole there is cancelled by `1/Γ`'s zero, which is
  why `ζ(0) = −1/2` is finite). That cancellation is not proved here; `0` is excluded rather
  than silently claimed.
-/
import TDLean.FE.Transfer

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-- **The honesty carrier.** `s ↦ (Γ(s/2))⁻¹` is entire. mathlib's junk value `Γ(−n) = 0` is
    pinned by this: it is the unique assignment making the reciprocal differentiable. -/
theorem differentiable_inv_Gamma_half :
    Differentiable ℂ (fun z : ℂ => (Complex.Gamma (z / 2))⁻¹) := by
  intro s
  have h : DifferentiableAt ℂ ((fun w : ℂ => (Complex.Gamma w)⁻¹) ∘ fun z : ℂ => z / 2) s :=
    DifferentiableAt.comp s (Complex.differentiable_one_div_Gamma _)
      (differentiableAt_id.div_const 2)
  exact h

theorem zetaFE_eq_mul_inv (s : ℂ) :
    zetaFE s = completedZeta s * ((π : ℝ) : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ := by
  rw [zetaFE, div_eq_mul_inv]

/-- **`ζ` is holomorphic on `ℂ \ {0,1}`.** -/
theorem differentiableAt_zetaFE {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ zetaFE s := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfun : zetaFE = fun z : ℂ =>
      completedZeta z * ((π : ℝ) : ℂ) ^ (z / 2) * (Complex.Gamma (z / 2))⁻¹ := by
    funext z
    exact zetaFE_eq_mul_inv z
  rw [hfun]
  exact ((differentiableAt_completedZeta h0 h1).mul
    ((differentiableAt_id.div_const 2).const_cpow (Or.inl hπ))).mul
    (differentiable_inv_Gamma_half s)

/-- **It really is the continuation:** `zetaFE` agrees with `zetaCont` wherever the latter is
    defined. -/
theorem zetaFE_eq_zetaCont {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) : zetaFE s = zetaCont s := by
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := gamma_half_ne_zero hs
  rw [zetaFE, completedZeta_eq_zetaCont hs h1,
    show ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaCont s * ((π : ℝ) : ℂ) ^ (s / 2)
      = (((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ (s / 2))
        * (Complex.Gamma (s / 2) * zetaCont s) by ring,
    pi_cpow_neg_mul_self, one_mul, mul_comm (Complex.Gamma (s / 2)) (zetaCont s),
    mul_div_assoc, div_self hΓ, mul_one]

/-! ### The trivial zeros, as zeros of a holomorphic function -/

theorem neg_two_nat_ne_zero {n : ℕ} (hn : 1 ≤ n) : (-(2 * (n : ℂ))) ≠ 0 := by
  intro hc
  have hre : (-(2 * (n : ℂ))).re = (0 : ℂ).re := by rw [hc]
  simp only [Complex.zero_re, Complex.neg_re, Complex.mul_re] at hre
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp at hre
  linarith

theorem neg_two_nat_ne_one {n : ℕ} (hn : 1 ≤ n) : (-(2 * (n : ℂ))) ≠ 1 := by
  intro hc
  have hre : (-(2 * (n : ℂ))).re = (1 : ℂ).re := by rw [hc]
  simp only [Complex.one_re] at hre
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp at hre
  linarith

/-- **The trivial zeros, genuinely.** For `n ≥ 1`, the continued `ζ` is holomorphic at `−2n`
    **and** vanishes there. The vanishing factor is `(Γ(s/2))⁻¹`, a value of the *entire*
    function `1/Γ` — not a division by zero. -/
theorem zetaFE_trivial_zero_genuine {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableAt ℂ zetaFE (-(2 * (n : ℂ))) ∧ zetaFE (-(2 * (n : ℂ))) = 0 :=
  ⟨differentiableAt_zetaFE (neg_two_nat_ne_zero hn) (neg_two_nat_ne_one hn),
    zetaFE_trivial_zero n⟩

/-- **Off the strip the trivial zeros are the only zeros.** For `Re s < 0`,
    `ζ(s) = 0` exactly when `s = −2n`. Both `Λ(s)` and `π^{s/2}` are nonvanishing there, so
    every zero comes from `Γ`'s poles — and `Γ`'s poles are the non-positive integers. -/
theorem zetaFE_eq_zero_iff_of_re_lt_zero {s : ℂ} (hs : s.re < 0) :
    zetaFE s = 0 ↔ ∃ n : ℕ, s = -(2 * (n : ℂ)) := by
  rw [zetaFE_eq_mul_inv]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' (completedZeta_ne_zero_of_re_lt_zero hs)
      · exact absurd h'' (pi_cpow_ne_zero _)
    · rw [inv_eq_zero] at h'
      obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff _).mp h'
      exact ⟨m, by linear_combination 2 * hm⟩
  · rintro ⟨m, rfl⟩
    rw [inv_eq_zero.mpr (by
      rw [show (-(2 * (m : ℂ))) / 2 = -(m : ℂ) by ring]
      exact Complex.Gamma_neg_nat_eq_zero m), mul_zero]

end TDLean.FE
