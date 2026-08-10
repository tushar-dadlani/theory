/-
  TDLean.Zeta.VonMangoldt -- Brick C9 item 2, part 3: assembly.

  Targets, all on `Re s > 1`:
    * `zetaSeries s ≠ 0`, via `μ ∗ 1 = δ` -- note this needs NO Euler product, so it does
      not drag item 3's work forward;
    * `L(Λ, s) · ζ(s) = −ζ′(s)`, from `Λ ∗ 1 = log`;
    * hence `L(Λ, s) = −ζ′(s)/ζ(s)`.

  ORACLE (arithmetic half only): `Ell2Zeta.v:149 energy_eq_divisor_sum` (`log n = ∑_{d∣n} Λ(d)`).
  The analytic half is an overtake -- see `TDLean/Zeta/LogDeriv.lean`'s header for why
  `vonmangoldt_zeta_trace` does *not* cover it.

  Ban boundary: `ArithmeticFunction.{VonMangoldt, Moebius}` are FOUNDATIONS (elementary
  arithmetic, no analysis). `NumberTheory.LSeries.*` stays banned.
-/
import TDLean.Zeta.DirichletMul
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace TDLean.Zeta

open Complex Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ### Bridging `ℕ`-indexed and `ℕ⁺`-indexed series -/

/-- For `s ≠ 0` the `n = 0` term vanishes (`(0:ℂ)^s = 0`), so the two indexings agree. -/
theorem LS_eq_tsum_nat (f : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) :
    LS f s = ∑' n : ℕ, f n / (n : ℂ) ^ s := by
  refine Function.Injective.tsum_eq (f := fun n : ℕ => f n / (n : ℂ) ^ s)
    (PNat.coe_injective) ?_
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (by rw [Nat.cast_zero, Complex.zero_cpow hs]; simp) hn
  · exact ⟨⟨n, hpos⟩, rfl⟩

/-- The constant-one Dirichlet series is `ζ`. -/
theorem LS_one_eq_zetaSeries {s : ℂ} (hs : s ≠ 0) :
    LS (fun _ => (1 : ℂ)) s = zetaSeries s := by
  rw [LS_eq_tsum_nat _ hs, zetaSeries]

/-! ### `ζ ≠ 0` on `Re s > 1`, from `μ ∗ 1 = δ` -/

/-- The Möbius function, complex-valued. -/
noncomputable def muC (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)

/-- The arithmetic-function `ζ` (i.e. `1` for `n ≥ 1`, `0` at `0`), complex-valued. -/
noncomputable def zetaC (n : ℕ) : ℂ := (ArithmeticFunction.zeta n : ℂ)

theorem norm_muC_le (n : ℕ) : ‖muC n‖ ≤ 1 := by
  rw [muC, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `μ ∗ 1 = δ`, transported to `ℂ`-valued functions and `dconv`. -/
theorem dconv_muC_zetaC (n : ℕ) : dconv muC zetaC n = if n = 1 then 1 else 0 := by
  have h : (((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℤ) n : ℤ) : ℂ)
      = (((1 : ArithmeticFunction ℤ) n : ℤ) : ℂ) := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply] at h
  simp only [ArithmeticFunction.natCoe_apply] at h
  push_cast at h
  simp only [dconv, muC, zetaC]
  rw [h, ArithmeticFunction.one_apply]
  split <;> simp

/-- `L(δ, s) = 1`. -/
theorem LS_delta (s : ℂ) : LS (fun n => if n = 1 then (1 : ℂ) else 0) s = 1 := by
  rw [LS]
  rw [tsum_eq_single 1 (fun n hn => by
    have : (n : ℕ) ≠ 1 := fun h => hn (PNat.coe_injective (by simpa using h))
    simp [this])]
  norm_num


/-! ### Summability of the log-weighted series

    `log x ≤ x^ε/ε` for `x > 0, ε > 0` -- elementary, from `log y ≤ y − 1` at `y = x^ε`.
    No asymptotics needed. -/

theorem log_le_rpow_div {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) : Real.log x ≤ x ^ ε / ε := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx ε)
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hε]
  nlinarith [h]

theorem summable_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-σ)) := by
  set ε : ℝ := (σ - 1) / 2 with hε
  have hεpos : 0 < ε := by simp only [hε]; linarith
  have hexp : 1 < σ - ε := by simp only [hε]; linarith
  have hbound : Summable (fun n : ℕ => (1 / ε) * (1 / (n : ℝ) ^ (σ - ε))) :=
    (Real.summable_one_div_nat_rpow.mpr hexp).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbound
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact mul_nonneg (Real.log_nonneg hn1) (Real.rpow_nonneg hn0.le _)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.log_zero, zero_mul]
      positivity
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlog : Real.log n ≤ (n : ℝ) ^ ε / ε := log_le_rpow_div hn0 hεpos
      have hcomb : (n : ℝ) ^ ε * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (ε - σ) := by
        rw [← Real.rpow_add hn0]; ring_nf
      calc Real.log n * (n : ℝ) ^ (-σ)
          ≤ ((n : ℝ) ^ ε / ε) * (n : ℝ) ^ (-σ) := by
            exact mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hn0.le _)
        _ = (1 / ε) * ((n : ℝ) ^ ε * (n : ℝ) ^ (-σ)) := by ring
        _ = (1 / ε) * (n : ℝ) ^ (ε - σ) := by rw [hcomb]
        _ = (1 / ε) * (1 / (n : ℝ) ^ (σ - ε)) := by
            congr 1
            rw [show ε - σ = -(σ - ε) by ring, Real.rpow_neg hn0.le, one_div]

/-! ### Summability of the Dirichlet series we need -/

theorem summable_norm_recip {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => ‖(1 : ℂ) / ((n : ℕ) : ℂ) ^ s‖) :=
  (summable_norm_iff.mpr (summable_zetaTerm hs)).comp_injective PNat.coe_injective

theorem norm_LS_term {f : ℕ → ℂ} {s : ℂ} (n : ℕ+) :
    ‖f n / ((n : ℕ) : ℂ) ^ s‖ = ‖f n‖ * ‖(1 : ℂ) / ((n : ℕ) : ℂ) ^ s‖ := by
  rw [norm_div, norm_div, norm_one]
  ring

theorem summable_norm_muC {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => ‖muC n / ((n : ℕ) : ℂ) ^ s‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_recip hs)
  rw [norm_LS_term]
  calc ‖muC n‖ * ‖(1 : ℂ) / ((n : ℕ) : ℂ) ^ s‖
      ≤ 1 * ‖(1 : ℂ) / ((n : ℕ) : ℂ) ^ s‖ :=
        mul_le_mul_of_nonneg_right (norm_muC_le _) (norm_nonneg _)
    _ = ‖(1 : ℂ) / ((n : ℕ) : ℂ) ^ s‖ := one_mul _

/-! ### `ζ ≠ 0` on `Re s > 1` -/

theorem LS_zetaC_eq {s : ℂ} (hs : s ≠ 0) : LS zetaC s = zetaSeries s := by
  rw [← LS_one_eq_zetaSeries hs, LS, LS]
  refine tsum_congr fun n => ?_
  have : zetaC (n : ℕ) = 1 := by
    simp only [zetaC, ArithmeticFunction.zeta_apply]
    have : (n : ℕ) ≠ 0 := n.ne_zero
    simp [this]
  rw [this]

/-- **`ζ(s) ≠ 0` for `Re s > 1`**, from `μ ∗ 1 = δ`. No Euler product. -/
theorem zetaSeries_ne_zero {s : ℂ} (hs : 1 < s.re) : zetaSeries s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hmul : LS muC s * LS zetaC s = 1 := by
    rw [LS_mul (summable_norm_muC hs) (by
      simpa only [LS_zetaC_eq hs0] using
        (summable_norm_recip hs).congr fun n => by rw [norm_LS_term]; simp [zetaC,
          ArithmeticFunction.zeta_apply, n.ne_zero])]
    rw [show dconv muC zetaC = fun n => if n = 1 then (1 : ℂ) else 0 from
      funext dconv_muC_zetaC]
    exact LS_delta s
  rw [LS_zetaC_eq hs0] at hmul
  intro hz
  rw [hz, mul_zero] at hmul
  exact one_ne_zero hmul.symm


/-! ### `L(Λ)·ζ = −ζ′`, and the quotient -/

/-- The von Mangoldt function, complex-valued. -/
noncomputable def LamC (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

/-- `log`, complex-valued. -/
noncomputable def logC (n : ℕ) : ℂ := (Real.log n : ℂ)

theorem norm_recip_eq {s : ℂ} (n : ℕ+) :
    ‖(1 : ℂ) / ((n : ℕ) : ℂ) ^ s‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn, one_div,
    ← Real.rpow_neg hn.le]

theorem summable_norm_zetaC {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => ‖zetaC (n : ℕ) / ((n : ℕ) : ℂ) ^ s‖) := by
  refine (summable_norm_recip hs).congr fun n => ?_
  have hz : zetaC (n : ℕ) = 1 := by
    simp only [zetaC, ArithmeticFunction.zeta_apply]
    simp [n.ne_zero]
  rw [hz]

theorem summable_norm_logC {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => ‖logC (n : ℕ) / ((n : ℕ) : ℂ) ^ s‖) := by
  have hbase : Summable (fun n : ℕ+ => Real.log ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_log_rpow hs).comp_injective PNat.coe_injective
  refine hbase.congr fun n => ?_
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  rw [norm_LS_term, norm_recip_eq, logC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast n.one_le))]

theorem summable_norm_LamC {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => ‖LamC (n : ℕ) / ((n : ℕ) : ℂ) ^ s‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (summable_norm_logC hs)
  rw [norm_LS_term, norm_LS_term]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [LamC, logC, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast n.one_le))]
  exact ArithmeticFunction.vonMangoldt_le_log

/-- ORACLE: `Ell2Zeta.v:149 energy_eq_divisor_sum` (`log n = ∑_{d∣n} Λ(d)`). -/
theorem dconv_LamC_zetaC (n : ℕ) : dconv LamC zetaC n = logC n := by
  have h : (((ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta :
        ArithmeticFunction ℝ) n : ℝ) : ℂ)
      = ((ArithmeticFunction.log n : ℝ) : ℂ) := by
    rw [ArithmeticFunction.vonMangoldt_mul_zeta]
  rw [ArithmeticFunction.mul_apply] at h
  simp only [ArithmeticFunction.natCoe_apply] at h
  push_cast at h
  simp only [dconv, LamC, zetaC]
  rw [h, logC, ArithmeticFunction.log_apply]

/-- `L(log, s) = −ζ′(s)` on `Re s > 1`. -/
theorem LS_logC_eq {s : ℂ} (hs : 1 < s.re) : LS logC s = -deriv zetaSeries s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h := (hasSum_deriv_zetaSeries hs).tsum_eq
  rw [LS_eq_tsum_nat _ hs0, ← h, ← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [logC, div_eq_mul_one_div]
  ring

/-- **`L(Λ,s)·ζ(s) = −ζ′(s)`** on `Re s > 1`. -/
theorem LS_vonMangoldt_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    LS LamC s * zetaSeries s = -deriv zetaSeries s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  rw [← LS_zetaC_eq hs0, LS_mul (summable_norm_LamC hs) (summable_norm_zetaC hs),
    show dconv LamC zetaC = logC from funext dconv_LamC_zetaC, LS_logC_eq hs]

/-- **`∑ Λ(n) n^{−s} = −ζ′(s)/ζ(s)`** on `Re s > 1`. The headline of C9 item 2. -/
theorem LS_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    LS LamC s = -deriv zetaSeries s / zetaSeries s := by
  rw [← LS_vonMangoldt_mul_zeta hs, mul_div_assoc, div_self (zetaSeries_ne_zero hs), mul_one]

end TDLean.Zeta
