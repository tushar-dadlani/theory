/-
  TDLean.PNT.Mellin -- C10, part 2: `−ζ′/ζ` as a Mellin/Stieltjes integral of `ψ`.

  For `Re s > 1`,

      ∑_{n} Λ(n) n^{−s}  =  s · ∫₁^∞ ψ(x) x^{−s−1} dx

  which is what turns the Dirichlet series into a Laplace transform after `x = eᵗ`.

  The banned `Mathlib/NumberTheory/LSeries/SumCoeff.lean:137 LSeries_eq_mul_integral` is this
  exact statement; its proof rests entirely on `Mathlib.NumberTheory.AbelSummation`, which is
  clean (no `LSeries` in its import closure), so that file is used here directly.

  This file proves the *finite* Abel identity; the passage to `∞` is separate.
-/
import TDLean.Zeta.VonMangoldt
import TDLean.PNT.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace TDLean.PNT

open Finset MeasureTheory TDLean.Zeta

theorem Icc_zero_eq_range (m : ℕ) : Finset.Icc 0 m = Finset.range (m + 1) := by
  ext n; simp

/-- `ψ` viewed in `ℂ`, in the shape Abel summation produces. -/
theorem sum_LamC_eq_psi (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, LamC n = ((psi x : ℝ) : ℂ) := by
  rw [Icc_zero_eq_range, psi, Complex.ofReal_sum]
  rfl

theorem LamC_zero : LamC 0 = 0 := by simp [LamC]

/-! ### The derivative of the kernel -/

theorem hasDerivAt_kernel {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t :=
  hasDerivAt_cpow_neg ht hs

theorem deriv_kernel_eqOn {s : ℂ} (hs : s ≠ 0) {b : ℝ} :
    Set.EqOn (deriv (fun y : ℝ => (y : ℂ) ^ (-s)))
      (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Set.Icc 1 b) := by
  intro t ht
  exact (hasDerivAt_kernel hs (by linarith [ht.1] : t ≠ 0)).deriv

theorem continuousOn_deriv_kernel (s : ℂ) {b : ℝ} :
    ContinuousOn (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Set.Icc 1 b) := by
  refine continuousOn_const.mul (ContinuousOn.cpow_const ?_ ?_)
  · exact Complex.continuous_ofReal.continuousOn.comp continuousOn_id (fun u _ => trivial)
  · intro u hu
    exact Or.inl (by simpa using (by linarith [hu.1] : (0:ℝ) < u))

/-! ### The finite Abel identity -/

/-- **Abel summation.** For `s ≠ 0` and `b ≥ 0`,
    `∑_{n ≤ b} Λ(n) n^{−s} = b^{−s} ψ(b) + s ∫₁^b ψ(t) t^{−s−1} dt`. -/
theorem abel_finite {s : ℂ} (hs : s ≠ 0) (b : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, ((k : ℂ) ^ (-s)) * LamC k
      = (b : ℂ) ^ (-s) * ((psi b : ℝ) : ℂ)
        + s * ∫ t in Set.Ioc (1 : ℝ) b, ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ) := by
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) b, DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-s)) t := by
    intro t ht
    exact (hasDerivAt_kernel hs (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hint : IntegrableOn (deriv (fun y : ℝ => (y : ℂ) ^ (-s))) (Set.Icc 1 b) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_deriv_kernel s)).congr_fun ?_ measurableSet_Icc
    exact fun t ht => (deriv_kernel_eqOn hs ht).symm
  have habel := sum_mul_eq_sub_integral_mul₀ (𝕜 := ℂ) LamC LamC_zero b hdiff hint
  rw [sum_LamC_eq_psi] at habel
  have hcast : ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-s) * LamC k
      = ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, ((k : ℂ)) ^ (-s) * LamC k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hcast] at habel
  have key : (∫ t in Set.Ioc (1 : ℝ) b,
      deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LamC k)
        = -s * ∫ t in Set.Ioc (1 : ℝ) b, ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ) := by
    have h1 : (∫ t in Set.Ioc (1 : ℝ) b,
        deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LamC k)
          = ∫ t in Set.Ioc (1 : ℝ) b, -s * (((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [sum_LamC_eq_psi, deriv_kernel_eqOn hs ⟨ht.1.le, ht.2⟩]
      ring
    rw [h1]
    exact integral_const_mul _ _
  have hgoal : (b : ℂ) ^ (-s) * ((psi b : ℝ) : ℂ)
      + s * ∫ t in Set.Ioc (1 : ℝ) b, ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ)
      = (b : ℂ) ^ (-s) * ((psi b : ℝ) : ℂ)
        - ∫ t in Set.Ioc (1 : ℝ) b,
            deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, LamC k := by
    rw [key]; ring
  rw [hgoal]
  exact habel

/-! ### Passing to `b → ∞` -/

theorem measurable_psi : Measurable psi := psi_mono.measurable

theorem norm_mellin_integrand_le {s : ℂ} (_hs : 1 < s.re) {t : ℝ} (ht : 1 ≤ t) :
    ‖((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ)‖ ≤ Ccheb * t ^ (-s.re) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hnorm1 : ‖((t : ℂ) ^ (-s - 1))‖ = t ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    congr 1
  have hnorm2 : ‖((psi t : ℝ) : ℂ)‖ = psi t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (psi_nonneg t)]
  have hpsi : psi t ≤ Ccheb * t := psi_le_Ccheb ht
  have hrpow : t ^ (-s.re - 1) * t = t ^ (-s.re) := by
    rw [show (-s.re - 1 : ℝ) = -s.re + (-1) by ring, Real.rpow_add ht0]
    rw [Real.rpow_neg_one]
    field_simp
  calc ‖((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ)‖
      = t ^ (-s.re - 1) * psi t := by rw [norm_mul, hnorm1, hnorm2]
    _ ≤ t ^ (-s.re - 1) * (Ccheb * t) := by
        exact mul_le_mul_of_nonneg_left hpsi (Real.rpow_nonneg ht0.le _)
    _ = Ccheb * (t ^ (-s.re - 1) * t) := by ring
    _ = Ccheb * t ^ (-s.re) := by rw [hrpow]

theorem integrableOn_mellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ)) (Set.Ioi 1) := by
  have hcont : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (-s - 1))) (Set.Ioi (1 : ℝ)) := by
    refine ContinuousOn.cpow_const ?_ ?_
    · exact Complex.continuous_ofReal.continuousOn.comp continuousOn_id (fun u _ => trivial)
    · intro u hu
      exact Or.inl (by simpa using (by linarith [Set.mem_Ioi.mp hu] : (0:ℝ) < u))
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ)) (volume.restrict (Set.Ioi 1)) :=
    (hcont.aestronglyMeasurable measurableSet_Ioi).mul
      (Complex.measurable_ofReal.comp measurable_psi).aestronglyMeasurable
  have hdom : IntegrableOn (fun t : ℝ => Ccheb * t ^ (-s.re)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_mellin_integrand_le hs (le_of_lt (Set.mem_Ioi.mp ht))

theorem tendsto_boundary {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun b : ℝ => (b : ℂ) ^ (-s) * ((psi b : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun b : ℝ => Ccheb * b ^ (1 - s.re)) Filter.atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith))
    simpa [show -(s.re - 1) = 1 - s.re by ring] using this.const_mul Ccheb
  refine squeeze_zero_norm' ?_ (by simpa using hlim)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with b hb
  have hb0 : (0 : ℝ) < b := by linarith
  have h1 : ‖(b : ℂ) ^ (-s)‖ = b ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0]; congr 1
  have h2 : ‖((psi b : ℝ) : ℂ)‖ = psi b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (psi_nonneg b)]
  have hrpow : b ^ (-s.re) * b = b ^ (1 - s.re) := by
    rw [show (1 - s.re : ℝ) = -s.re + 1 by ring, Real.rpow_add hb0, Real.rpow_one]
  calc ‖(b : ℂ) ^ (-s) * ((psi b : ℝ) : ℂ)‖ = b ^ (-s.re) * psi b := by
        rw [norm_mul, h1, h2]
    _ ≤ b ^ (-s.re) * (Ccheb * b) :=
        mul_le_mul_of_nonneg_left (psi_le_Ccheb hb) (Real.rpow_nonneg hb0.le _)
    _ = Ccheb * (b ^ (-s.re) * b) := by ring
    _ = Ccheb * b ^ (1 - s.re) := by rw [hrpow]

theorem summable_LamC_nat {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => LamC n / (n : ℂ) ^ s) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_log_rpow hs))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LamC]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [norm_div, LamC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn, Real.rpow_neg hn0.le,
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
      (by positivity)

theorem tendsto_partial {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun b : ℝ => ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, ((k : ℂ) ^ (-s)) * LamC k)
      Filter.atTop (nhds (LS LamC s)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hterm : ∀ k : ℕ, ((k : ℂ) ^ (-s)) * LamC k = LamC k / (k : ℂ) ^ s := by
    intro k
    rw [Complex.cpow_neg, div_eq_mul_inv]
    ring
  have hnat : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, LamC k / (k : ℂ) ^ s)
      Filter.atTop (nhds (LS LamC s)) := by
    rw [LS_eq_tsum_nat LamC hs0]
    exact (summable_LamC_nat hs).hasSum.tendsto_sum_nat
  have hfl : Filter.Tendsto (fun b : ℝ => ⌊b⌋₊ + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun b => Nat.le_succ _) tendsto_nat_floor_atTop
  have := hnat.comp hfl
  refine this.congr fun b => ?_
  simp only [Function.comp_apply, Icc_zero_eq_range]
  exact (Finset.sum_congr rfl fun k _ => hterm k).symm

/-- **The Mellin representation.** For `Re s > 1`,
    `∑ Λ(n) n^{−s} = s · ∫₁^∞ ψ(t) t^{−s−1} dt`. -/
theorem LS_LamC_eq_mellin {s : ℂ} (hs : 1 < s.re) :
    LS LamC s = s * ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hI : Filter.Tendsto
      (fun b : ℝ => ∫ t in Set.Ioc (1 : ℝ) b, ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ))
      Filter.atTop (nhds (∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ))) := by
    have h := intervalIntegral_tendsto_integral_Ioi (1 : ℝ) (integrableOn_mellin hs)
      Filter.tendsto_id
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with b hb
    exact intervalIntegral.integral_of_le hb
  have hRHS : Filter.Tendsto
      (fun b : ℝ => (b : ℂ) ^ (-s) * ((psi b : ℝ) : ℂ)
        + s * ∫ t in Set.Ioc (1 : ℝ) b, ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ))
      Filter.atTop
      (nhds (0 + s * ∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) ^ (-s - 1)) * ((psi t : ℝ) : ℂ))) :=
    (tendsto_boundary hs).add (hI.const_mul s)
  have heq := tendsto_nhds_unique (tendsto_partial hs)
    (hRHS.congr fun b => (abel_finite hs0 b).symm)
  simpa using heq

end TDLean.PNT

