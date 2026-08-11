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

end TDLean.PNT
