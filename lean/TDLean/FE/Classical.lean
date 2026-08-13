/-
  TDLean.FE.Classical -- cluster A17: the functional equation in its classical shape.

      ζ(1−s) = 2·(2π)^{−s}·cos(πs/2)·Γ(s)·ζ(s)

  The `Λ(s) = Λ(1−s)` form is the one the theta integral produces; this is the one everybody
  recognises. Getting from one to the other is pure Γ-arithmetic: Euler's reflection formula
  turns `1/Γ((1−s)/2)` into `cos(πs/2)·Γ((1+s)/2)/π`, and Legendre duplication collapses
  `Γ(s/2)·Γ((1+s)/2)` into `Γ(s)·2^{1−s}·√π`.

  **The delicate point is the odd integers.** At `s = 2m+1` the factor `Γ((1−s)/2) = Γ(−m)`
  has a pole, so the reflection step cannot be run by dividing. But `cos(πs/2)` vanishes at
  exactly those points, so the identity still holds — both sides are `0`. The reflection lemma
  `inv_Gamma_half_sub` is therefore proved with an explicit case split rather than assuming
  the Γ-factor invertible, and the resulting functional equation is valid on all of
  `Re s > 1`, odd integers included.

  That gives a **third, independent route to the trivial zeros**: `ζ(−2m) = ζ(1−(2m+1)) = 0`
  because `cos(π(2m+1)/2) = 0`. Compare `completedZeta_ne_zero_at_trivial` (the zero is the
  Γ-pole, not `Λ`) and `zetaFE_trivial_zero_genuine` (a holomorphic function vanishing).
-/
import TDLean.FE.Continuation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

theorem pi_ne_zero_C : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-! ### Reflection, including at the poles -/

/-- Where `cos(πz)` vanishes and `Re z > 0`, the Γ-factor vanishes too. This is what makes
    the reflection step survive the odd integers. -/
theorem gamma_half_sub_eq_zero_of_cos_eq_zero {z : ℂ} (hz : 0 < z.re)
    (hc : Complex.cos ((π : ℝ) * z) = 0) : Complex.Gamma (1 / 2 - z) = 0 := by
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
  have hzv : z = (2 * (k : ℂ) + 1) / 2 := by
    refine mul_left_cancel₀ pi_ne_zero_C ?_
    rw [hk]
    ring
  have hzr : z = (((2 * (k : ℝ) + 1) / 2 : ℝ) : ℂ) := by rw [hzv]; push_cast; ring
  have hre : z.re = (2 * (k : ℝ) + 1) / 2 := by rw [hzr, Complex.ofReal_re]
  have hk0 : (0 : ℤ) ≤ k := by
    by_contra hcon
    push_neg at hcon
    have hkz : k ≤ -1 := by omega
    have hkl : (k : ℝ) ≤ -1 := by exact_mod_cast hkz
    rw [hre] at hz
    linarith
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  rw [show (1 : ℂ) / 2 - z = -(m : ℂ) by rw [hzv]; push_cast; ring]
  exact Complex.Gamma_neg_nat_eq_zero m

/-- **Euler reflection, in reciprocal form.** Valid for `Re z > 0` *including* the points
    where `Γ(1/2 − z)` has a pole, where both sides are `0`. -/
theorem inv_Gamma_half_sub {z : ℂ} (hz : 0 < z.re) :
    (Complex.Gamma (1 / 2 - z))⁻¹
      = Complex.cos ((π : ℝ) * z) * Complex.Gamma (1 / 2 + z) / ((π : ℝ) : ℂ) := by
  by_cases hc : Complex.cos ((π : ℝ) * z) = 0
  · rw [hc, zero_mul, zero_div, inv_eq_zero]
    exact gamma_half_sub_eq_zero_of_cos_eq_zero hz hc
  · have hsin : Complex.sin (((π : ℝ) : ℂ) * (1 / 2 + z)) = Complex.cos (((π : ℝ) : ℂ) * z) := by
      rw [show (((π : ℝ) : ℂ) * (1 / 2 + z)) = ((π : ℝ) : ℂ) / 2 + ((π : ℝ) : ℂ) * z by ring,
        Complex.sin_add]
      simp
    have hrefl := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + z)
    rw [show (1 : ℂ) - (1 / 2 + z) = 1 / 2 - z by ring, hsin] at hrefl
    have hrefl' : Complex.Gamma (1 / 2 + z) * Complex.Gamma (1 / 2 - z)
        * Complex.cos (((π : ℝ) : ℂ) * z) = ((π : ℝ) : ℂ) := by
      rw [hrefl]
      field_simp
    -- `field_simp` normalises inside the `Γ` arguments (`1/2 - z` becomes `(1-2z)/2`), which
    -- defeats `linear_combination`. Build the product identity directly instead.
    have hnum : Complex.Gamma (1 / 2 - z)
        * (Complex.cos (((π : ℝ) : ℂ) * z) * Complex.Gamma (1 / 2 + z)) = ((π : ℝ) : ℂ) := by
      linear_combination hrefl'
    have hprod : Complex.Gamma (1 / 2 - z)
        * (Complex.cos (((π : ℝ) : ℂ) * z) * Complex.Gamma (1 / 2 + z) / ((π : ℝ) : ℂ)) = 1 := by
      rw [← mul_div_assoc, hnum, div_self pi_ne_zero_C]
    exact inv_eq_of_mul_eq_one_right hprod

/-! ### The combined Γ-factor -/

/-- `Γ(s/2)/Γ((1−s)/2) = cos(πs/2)·Γ(s)·2^{1−s}·√π/π`, by reflection then duplication. -/
theorem gamma_ratio {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma (s / 2) * (Complex.Gamma ((1 - s) / 2))⁻¹
      = Complex.cos (((π : ℝ) : ℂ) * s / 2) * Complex.Gamma s * (2 : ℂ) ^ (1 - s)
        * ((Real.sqrt π : ℝ) : ℂ) / ((π : ℝ) : ℂ) := by
  have hz : 0 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have hhalf : (1 - s) / 2 = 1 / 2 - s / 2 := by ring
  rw [hhalf, inv_Gamma_half_sub hz]
  have hdup := Complex.Gamma_mul_Gamma_add_half (s / 2)
  rw [show s / 2 + 1 / 2 = 1 / 2 + s / 2 by ring, show 2 * (s / 2) = s by ring] at hdup
  have hcos : ((π : ℝ) : ℂ) * (s / 2) = ((π : ℝ) : ℂ) * s / 2 := by ring
  rw [hcos, ← mul_div_assoc]
  congr 1
  linear_combination (Complex.cos (((π : ℝ) : ℂ) * s / 2)) * hdup

/-! ### Collapsing the powers -/

theorem pi_power_collapse (s : ℂ) :
    ((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ ((1 - s) / 2) * ((Real.sqrt π : ℝ) : ℂ)
        / ((π : ℝ) : ℂ)
      = ((π : ℝ) : ℂ) ^ (-s) := by
  have hsq : ((Real.sqrt π : ℝ) : ℂ) = ((π : ℝ) : ℂ) ^ (1 / 2 : ℂ) :=
    sqrt_eq_cpow_half Real.pi_pos
  have hinv : (((π : ℝ) : ℂ))⁻¹ = ((π : ℝ) : ℂ) ^ (-1 : ℂ) := by
    rw [Complex.cpow_neg, Complex.cpow_one]
  rw [hsq, div_eq_mul_inv, hinv, ← Complex.cpow_add _ _ pi_ne_zero_C,
    ← Complex.cpow_add _ _ pi_ne_zero_C, ← Complex.cpow_add _ _ pi_ne_zero_C]
  congr 1
  ring

theorem two_pi_cpow (s : ℂ) :
    (2 : ℂ) ^ (1 - s) * ((π : ℝ) : ℂ) ^ (-s) = 2 * (((2 * π : ℝ)) : ℂ) ^ (-s) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hcast2 : (((2 * π : ℝ)) : ℂ) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) := by push_cast; ring
  have hsplit : (((2 * π : ℝ)) : ℂ) ^ (-s)
      = (((2 : ℝ)) : ℂ) ^ (-s) * (((π : ℝ)) : ℂ) ^ (-s) := by
    rw [hcast2]
    exact Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le _
  have hcast : (((2 : ℝ)) : ℂ) = (2 : ℂ) := by norm_num
  rw [hsplit, hcast, show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ h2,
    Complex.cpow_one]
  ring

/-! ### The functional equation -/

/-- **`ζ(1−s) = 2·(2π)^{−s}·cos(πs/2)·Γ(s)·ζ(s)` for `Re s > 1`.**

    Valid at the odd integers too, where both sides vanish: `cos(πs/2) = 0` on the right and
    `Γ((1−s)/2)` has a pole on the left. -/
theorem zetaFE_functional_equation {s : ℂ} (hs : 1 < s.re) :
    zetaFE (1 - s)
      = 2 * (((2 * π : ℝ)) : ℂ) ^ (-s) * Complex.cos (((π : ℝ) : ℂ) * s / 2)
        * Complex.Gamma s * zetaSeries s := by
  have hs0 : 0 < s.re := by linarith
  rw [zetaFE_eq_mul_inv, completedZeta_symm s, completedZeta_eq hs]
  rw [show ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaSeries s
        * ((π : ℝ) : ℂ) ^ ((1 - s) / 2) * (Complex.Gamma ((1 - s) / 2))⁻¹
      = (((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ ((1 - s) / 2))
        * (Complex.Gamma (s / 2) * (Complex.Gamma ((1 - s) / 2))⁻¹) * zetaSeries s by ring,
    gamma_ratio hs0]
  rw [show (((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ ((1 - s) / 2))
        * (Complex.cos (((π : ℝ) : ℂ) * s / 2) * Complex.Gamma s * (2 : ℂ) ^ (1 - s)
            * ((Real.sqrt π : ℝ) : ℂ) / ((π : ℝ) : ℂ)) * zetaSeries s
      = (((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ ((1 - s) / 2) * ((Real.sqrt π : ℝ) : ℂ)
            / ((π : ℝ) : ℂ))
        * ((2 : ℂ) ^ (1 - s) * (Complex.cos (((π : ℝ) : ℂ) * s / 2) * Complex.Gamma s
            * zetaSeries s)) by ring,
    pi_power_collapse]
  rw [show ((π : ℝ) : ℂ) ^ (-s)
        * ((2 : ℂ) ^ (1 - s) * (Complex.cos (((π : ℝ) : ℂ) * s / 2) * Complex.Gamma s
            * zetaSeries s))
      = ((2 : ℂ) ^ (1 - s) * ((π : ℝ) : ℂ) ^ (-s))
        * (Complex.cos (((π : ℝ) : ℂ) * s / 2) * Complex.Gamma s * zetaSeries s) by ring,
    two_pi_cpow]
  ring

/-- **The trivial zeros, a third way.** `ζ(−2m) = 0` because `cos(π(2m+1)/2) = 0`. This is
    independent of both earlier routes: `completedZeta_ne_zero_at_trivial` located the zero in
    the Γ-pole, `zetaFE_trivial_zero_genuine` exhibited it as a holomorphic function vanishing,
    and this one reads it straight off the classical functional equation. -/
theorem zetaFE_trivial_zero_via_cos (m : ℕ) (hm : 1 ≤ m) :
    zetaFE (-(2 * (m : ℂ))) = 0 := by
  have hs : (1 : ℝ) < ((2 * (m : ℂ) + 1)).re := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re]
    simp
    linarith
  have hcos : Complex.cos (((π : ℝ) : ℂ) * (2 * (m : ℂ) + 1) / 2) = 0 := by
    rw [Complex.cos_eq_zero_iff]
    exact ⟨m, by push_cast; ring⟩
  have h := zetaFE_functional_equation hs
  rw [hcos] at h
  rw [show (-(2 * (m : ℂ))) = 1 - (2 * (m : ℂ) + 1) by ring, h]
  ring

end TDLean.FE
