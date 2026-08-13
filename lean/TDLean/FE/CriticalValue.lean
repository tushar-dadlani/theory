/-
  TDLean.FE.CriticalValue -- cluster A18: `Λ` is real on the critical line, and `Λ(1/2) < 0`.

  Chaining the two symmetries gives a **function** identity, not just a statement about zeros:

      Λ(refl s) = Λ(1 − s̄) = Λ(s̄) = conj(Λ(s))

  and `refl s = s` exactly on `Re s = 1/2` (`Zeta.refl_fixed_iff`). So `Λ` is real-valued on
  the critical line. This is the first statement in the development about `ζ`'s **values**
  there rather than about symmetries of its zero set.

  ORACLE: `spectral-theory/CoherenceSingularity.v:45 coherence_line`, which is exactly
  `Re z = /2 -> Im (XiC z) = 0`. A genuine two-development cross-check rather than an overtake
  — though note the usual caveat that Coq's `XiC` is symmetric by construction and tied to
  `zetaC` only on the real ray.

  Then `Λ(1/2) = −4 + ∫₁^∞ 2·u^{−3/4}·ψ(u) du`, and the decay bound from A10 controls the
  integral by `2·(1−e^{−π})⁻¹·e^{−1} < 4/3`. So `Λ(1/2) < 0`.

  **What this is and is not.** It is non-vacuity: `Λ` is not identically zero on the critical
  line, and the value at the centre is negative. It is *half* of an intermediate-value
  argument. The other half needs `Λ(1/2 + it) > 0` for some `t`, and the first zero is at
  `t ≈ 14.13` — rigorous numerics at that height, not a corollary of anything here. **No
  nontrivial zero is exhibited by this file.**
-/
import TDLean.FE.Classical
import TDLean.Zeta.CriticalLine
import Mathlib.Analysis.Real.Pi.Bounds

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-! ### `Λ` is real on the critical line -/

/-- The two symmetries compose to a conjugation law for the reflection `refl s = 1 − s̄`. -/
theorem completedZeta_refl (s : ℂ) :
    completedZeta (TDLean.Zeta.refl s) = (starRingEnd ℂ) (completedZeta s) := by
  rw [TDLean.Zeta.refl, completedZeta_symm ((starRingEnd ℂ) s), completedZeta_conj]

/-- **`Λ` is real on the critical line.** -/
theorem completedZeta_conj_eq_self {s : ℂ} (hs : s.re = 1 / 2) :
    (starRingEnd ℂ) (completedZeta s) = completedZeta s := by
  rw [← completedZeta_refl s, (TDLean.Zeta.refl_fixed_iff s).mpr hs]

/-- The same, as the vanishing of the imaginary part. This is the exact form of Coq's
    `CoherenceSingularity.v:45 coherence_line`. -/
theorem completedZeta_im_eq_zero {s : ℂ} (hs : s.re = 1 / 2) : (completedZeta s).im = 0 := by
  have h := completedZeta_conj_eq_self hs
  rw [Complex.ext_iff] at h
  have := h.2
  simp only [Complex.conj_im] at this
  linarith

/-! ### The value at the centre -/

theorem exp_neg_pi_le_quarter : Real.exp (-π) ≤ 1 / 4 := by
  have hπ : (3 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hle : π + 1 ≤ Real.exp π := Real.add_one_le_exp π
  have hpos : (0 : ℝ) < Real.exp π := Real.exp_pos π
  rw [Real.exp_neg]
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

theorem psiBound_le_two : psiBound ≤ 2 := by
  rw [psiBound]
  have h := exp_neg_pi_le_quarter
  have hpos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith [exp_neg_pi_lt_one]
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- The two exponents in `Λ`'s integrand collapse to `−3/4` at `s = 1/2`: the self-dual point
    is exactly where they coincide. -/
theorem half_exponents : ((1 / 2 : ℂ) / 2 - 1) = (-3 / 4 : ℂ)
    ∧ ((1 - (1 / 2 : ℂ)) / 2 - 1) = (-3 / 4 : ℂ) := by
  constructor <;> ring

/-- The tail integral at `s = 1/2` is small: bounded by `2·psiBound·e^{−1} < 4/3`. -/
theorem norm_integral_half_le :
    ‖∫ u in Ioi (1 : ℝ),
        (((u : ℂ) ^ ((1 / 2 : ℂ) / 2 - 1) + (u : ℂ) ^ ((1 - (1 / 2 : ℂ)) / 2 - 1))
          * psiTheta u)‖
      ≤ 2 * psiBound * Real.exp (-1) := by
  have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  -- the dominating function
  have hgint : IntegrableOn (fun u : ℝ => 2 * psiBound * Real.exp (-u)) (Ioi (1 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 1).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hgint ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hu0 : (0 : ℝ) < u := by linarith
    have hcast : ((1 / 2 : ℂ) / 2 - 1) = (-3 / 4 : ℂ) := by ring
    have hcast2 : ((1 - (1 / 2 : ℂ)) / 2 - 1) = (-3 / 4 : ℂ) := by ring
    rw [hcast, hcast2, norm_mul]
    have hre : ((-3 / 4 : ℂ)).re = (-3 / 4 : ℝ) := by norm_num
    have hpow : ‖(u : ℂ) ^ (-3 / 4 : ℂ)‖ = u ^ (-3 / 4 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    have hpowle : u ^ (-3 / 4 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (-3 / 4 : ℝ) ≤ 0)
    have hsum : ‖(u : ℂ) ^ (-3 / 4 : ℂ) + (u : ℂ) ^ (-3 / 4 : ℂ)‖ ≤ 2 := by
      calc ‖(u : ℂ) ^ (-3 / 4 : ℂ) + (u : ℂ) ^ (-3 / 4 : ℂ)‖
          ≤ ‖(u : ℂ) ^ (-3 / 4 : ℂ)‖ + ‖(u : ℂ) ^ (-3 / 4 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by rw [hpow]; linarith
        _ = 2 := by norm_num
    -- `e^{−πu} ≤ e^{−u}` because `π ≥ 1` and `u ≥ 1 > 0`
    have hexp : Real.exp (-(π * u)) ≤ Real.exp (-u) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc ‖(u : ℂ) ^ (-3 / 4 : ℂ) + (u : ℂ) ^ (-3 / 4 : ℂ)‖ * ‖psiTheta u‖
        ≤ 2 * (psiBound * Real.exp (-(π * u))) := by
          refine mul_le_mul hsum (norm_psiTheta_le hu1) (norm_nonneg _) (by norm_num)
      _ ≤ 2 * (psiBound * Real.exp (-u)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hexp psiBound_pos.le
      _ = 2 * psiBound * Real.exp (-u) := by ring
  · rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]

/-- **`Λ(1/2) < 0`.** The pole terms contribute `−4` and the tail is bounded by `4/3`. -/
theorem completedZeta_half_re_lt_zero : (completedZeta (1 / 2 : ℂ)).re < 0 := by
  have hpole : (1 : ℂ) / ((1 / 2 : ℂ) - 1) - 1 / (1 / 2 : ℂ) = -4 := by norm_num
  have hbound := norm_integral_half_le
  set I : ℂ := ∫ u in Ioi (1 : ℝ),
      (((u : ℂ) ^ ((1 / 2 : ℂ) / 2 - 1) + (u : ℂ) ^ ((1 - (1 / 2 : ℂ)) / 2 - 1))
        * psiTheta u) with hI
  have hval : completedZeta (1 / 2 : ℂ) = -4 + I := by
    rw [completedZeta, hI, hpole]
  -- `e^{−1} ≤ 1/2`, so the tail is at most `2·2·(1/2) = 2 < 4`
  have hexp1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hsmall : ‖I‖ ≤ 2 := by
    refine hbound.trans ?_
    have h1 : 2 * psiBound ≤ 4 := by linarith [psiBound_le_two]
    have h2 : (0 : ℝ) ≤ 2 * psiBound := by linarith [psiBound_pos]
    calc 2 * psiBound * Real.exp (-1 : ℝ) ≤ 4 * (1 / 2 : ℝ) := by
          refine mul_le_mul h1 hexp1 (Real.exp_pos _).le (by norm_num)
      _ = 2 := by norm_num
  have hre : I.re ≤ 2 :=
    le_trans (le_trans (le_abs_self I.re) (Complex.abs_re_le_norm I)) hsmall
  rw [hval]
  simp only [Complex.add_re, Complex.neg_re]
  norm_num
  linarith

end TDLean.FE
