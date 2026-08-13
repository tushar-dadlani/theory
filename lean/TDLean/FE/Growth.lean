/-
  TDLean.FE.Growth -- cluster A20: growth bounds on the tail transform and on `ξ`.

  **Why this file exists, stated plainly.** The Hadamard-factorisation route to *existence* of
  nontrivial zeros needs `ξ` entire (A19, done) **of finite order**. mathlib has Hadamard's
  *three-lines* theorem (`Analysis/Complex/Hadamard.lean`) but **not** the factorisation
  theorem: there are no Weierstrass products, no genus, no order-of-growth theory anywhere in
  `Mathlib/Analysis/`. Building that is a large independent project. This file supplies the
  analytic input it would consume, and nothing beyond it.

  The bound is in Γ-form:

      ‖M(w)‖ ≤ psiBound · π^{−(σ+1)} · Γ(σ+1)      for  σ = Re w ≥ 0

  because `∫₁^∞ u^σ e^{−πu} du ≤ ∫₀^∞ u^σ e^{−πu} du = Γ(σ+1)/π^{σ+1}`. For `σ ≤ 0` the tail
  is simply bounded, `‖M(w)‖ ≤ psiBound·e^{−1}`, since `u^σ ≤ 1` on `[1,∞)`.

  Converting `Γ(σ+1)` into the literal order-1 statement `‖ξ(s)‖ ≤ exp(C|s| log|s|)` needs
  Stirling, which is a separate step and is **not** done here. What is proved is the bound
  itself, which is the reusable object.
-/
import TDLean.FE.Xi

namespace TDLean.FE

open Complex Real MeasureTheory Set

/-! ### The Gamma integral -/

theorem integrableOn_rpow_mul_exp_neg_pi_Ioi_zero {σ : ℝ} (hσ : -1 < σ) :
    IntegrableOn (fun u : ℝ => u ^ σ * Real.exp (-(π * u))) (Ioi (0 : ℝ)) := by
  have h := integrableOn_real_term (σ := σ + 1) (by linarith) Real.pi_pos
  refine MeasureTheory.IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  norm_num

/-- `∫₀^∞ u^σ e^{−πu} du = Γ(σ+1)/π^{σ+1}`. -/
theorem integral_rpow_mul_exp_neg_pi {σ : ℝ} (hσ : -1 < σ) :
    (∫ u in Ioi (0 : ℝ), u ^ σ * Real.exp (-(π * u)))
      = (1 / π) ^ (σ + 1) * Real.Gamma (σ + 1) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsre : ((((2 * (σ + 1) : ℝ)) : ℂ)).re = 2 * (σ + 1) := Complex.ofReal_re _
  have hs : (0 : ℝ) < ((((2 * (σ + 1) : ℝ)) : ℂ)).re := by rw [hsre]; linarith
  have h := integral_norm_term (s := (((2 * (σ + 1) : ℝ)) : ℂ)) hs hπ
  rw [hsre, show 2 * (σ + 1) / 2 = σ + 1 by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hexp : (((2 * (σ + 1) : ℝ)) : ℂ) / 2 - 1 = ((σ : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re,
    Complex.norm_exp]
  congr 1
  simp

/-! ### The tail transform -/

/-- **The Γ-form growth bound**, for exponents of nonnegative real part. -/
theorem norm_mellinTail_le_gamma {w : ℂ} (hw : 0 ≤ w.re) :
    ‖mellinTail w‖ ≤ psiBound * ((1 / π) ^ (w.re + 1) * Real.Gamma (w.re + 1)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hw' : (-1 : ℝ) < w.re := by linarith
  have hgint : IntegrableOn (fun u : ℝ => psiBound * (u ^ w.re * Real.exp (-(π * u))))
      (Ioi (1 : ℝ)) := (integrableOn_rpow_mul_exp_neg_pi w.re).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hgint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hu0 : (0 : ℝ) < u := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    calc u ^ w.re * ‖psiTheta u‖
        ≤ u ^ w.re * (psiBound * Real.exp (-(π * u))) :=
          mul_le_mul_of_nonneg_left (norm_psiTheta_le hu1) (Real.rpow_nonneg hu0.le _)
      _ = psiBound * (u ^ w.re * Real.exp (-(π * u))) := by ring
  · rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ psiBound_pos.le
    rw [← integral_rpow_mul_exp_neg_pi hw']
    refine MeasureTheory.setIntegral_mono_set
      (integrableOn_rpow_mul_exp_neg_pi_Ioi_zero hw') ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      positivity
    · exact Filter.Eventually.of_forall (fun u hu => lt_trans zero_lt_one hu)

/-- For exponents of nonpositive real part the tail is simply bounded: `u^σ ≤ 1` on `[1,∞)`. -/
theorem norm_mellinTail_le_of_nonpos {w : ℂ} (hw : w.re ≤ 0) :
    ‖mellinTail w‖ ≤ psiBound * Real.exp (-1) := by
  have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hgint : IntegrableOn (fun u : ℝ => psiBound * Real.exp (-u)) (Ioi (1 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 1).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hgint ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hu0 : (0 : ℝ) < u := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hpow : u ^ w.re ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hu1 hw
    have hexp : Real.exp (-(π * u)) ≤ Real.exp (-u) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc u ^ w.re * ‖psiTheta u‖
        ≤ 1 * (psiBound * Real.exp (-(π * u))) := by
          refine mul_le_mul hpow (norm_psiTheta_le hu1) (norm_nonneg _) (by norm_num)
      _ ≤ psiBound * Real.exp (-u) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hexp psiBound_pos.le
  · rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]

/-! ### Hence `ξ` -/

/-- **A growth bound for `ξ` on `Re s ≥ 2`.** The `M(s/2−1)` term carries the Γ-factor; the
    reflected term `M((1−s)/2−1)` has very negative exponent there and is merely bounded.

    This is the analytic input a Hadamard-factorisation argument would consume. Turning
    `Γ(Re s/2)` into `exp(C|s| log|s|)` — the literal statement that `ξ` has order `1` —
    requires Stirling and is **not** proved here. -/
theorem norm_xi_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖xi s‖ ≤ 1 / 2 + ‖s * (s - 1) / 2‖
      * (psiBound * ((1 / π) ^ (s.re / 2) * Real.Gamma (s.re / 2))
        + psiBound * Real.exp (-1)) := by
  have h1 : (0 : ℝ) ≤ (s / 2 - 1).re := by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have h1' : (s / 2 - 1).re + 1 = s.re / 2 := by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    ring
  have h2 : ((1 - s) / 2 - 1).re ≤ 0 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hb1 := norm_mellinTail_le_gamma h1
  rw [h1'] at hb1
  have hb2 := norm_mellinTail_le_of_nonpos h2
  calc ‖xi s‖
      ≤ ‖(1 / 2 : ℂ)‖ + ‖s * (s - 1) / 2
          * (mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1))‖ := by
        rw [xi]; exact norm_add_le _ _
    _ ≤ 1 / 2 + ‖s * (s - 1) / 2‖
          * (psiBound * ((1 / π) ^ (s.re / 2) * Real.Gamma (s.re / 2))
            + psiBound * Real.exp (-1)) := by
        gcongr
        · norm_num
        · rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (norm_add_le _ _).trans (add_le_add hb1 hb2)

end TDLean.FE
