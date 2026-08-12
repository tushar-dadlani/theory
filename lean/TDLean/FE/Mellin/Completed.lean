/-
  TDLean.FE.Mellin.Completed -- cluster A5: the completed zeta as a Mellin transform.

      ∫₀^∞ ψ(t)·t^{s/2−1} dt = π^{−s/2}·Γ(s/2)·ζ(s)      for `Re s > 1`

  with `ψ(t) = ∑_{n≥1} e^{−πn²t}`. This is the identity that turns the theta function into the
  completed zeta, and it is what the split at `t = 1` will act on.

  ORACLE: `ZetaCompleted.v:58 zeta_completed_eq_J` proves the same identification — but only
  for **real `s > 1`**, and against the tail object `J`. This is the full `∫₀^∞` at complex `s`.
-/
import TDLean.FE.Mellin.Term
import TDLean.Zeta.VonMangoldt
import TDLean.FE.Theta.Transform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-- `ψ(t) = ∑_{n≥1} e^{−πn²t}`. -/
noncomputable def psiTheta (t : ℝ) : ℂ :=
  ∑' n : ℕ+, Complex.exp (-(((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * (t : ℂ)))

/-- The `n`-th Mellin term as a function of `t`. -/
private noncomputable def term (s : ℂ) (n : ℕ+) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s / 2 - 1) * Complex.exp (-(((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * (t : ℂ)))

private theorem tsum_term (s : ℂ) (t : ℝ) :
    ∑' n : ℕ+, term s n t = (t : ℂ) ^ (s / 2 - 1) * psiTheta t := by
  rw [psiTheta, ← tsum_mul_left]
  rfl

private theorem measurable_term {s : ℂ} (hs : 1 < s.re) (n : ℕ+) :
    AEStronglyMeasurable (term s n) (volume.restrict (Ioi (0 : ℝ))) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hr : (0 : ℝ) < π * ((n : ℕ) : ℝ) ^ 2 := by positivity
  have hs2 : 0 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  exact (integrableOn_gaussian_term hs2 hr).aestronglyMeasurable

/-- **The completed zeta as a Mellin transform.** -/
theorem mellin_psiTheta {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) * psiTheta t)
      = ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaSeries s := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  -- interchange
  have hswap : (∫ t in Ioi (0 : ℝ), ∑' n : ℕ+, term s n t)
      = ∑' n : ℕ+, ∫ t in Ioi (0 : ℝ), term s n t :=
    integral_tsum (measurable_term hs) (lintegral_norm_summable hs)
  have hlhs : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) * psiTheta t)
      = ∫ t in Ioi (0 : ℝ), ∑' n : ℕ+, term s n t :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => (tsum_term s t).symm
  rw [hlhs, hswap]
  -- evaluate each term
  have hterm : ∀ n : ℕ+, (∫ t in Ioi (0 : ℝ), term s n t)
      = (((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) * (((n : ℕ) : ℂ)) ^ (-s) := by
    intro n
    simp only [term]
    rw [mellin_gaussian_term hs0 n]
    have hcast : ((((n : ℕ) : ℝ)) : ℂ) = ((n : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]; ring
  rw [tsum_congr hterm, tsum_mul_left]
  congr 1
  -- `∑' n : ℕ+, n^{−s} = ζ(s)`
  rw [← LS_one_eq_zetaSeries hsne, LS]
  refine tsum_congr fun n => ?_
  rw [Complex.cpow_neg, one_div]


/-! ### Reconciling the two indexings

    `mellin_psiTheta` is stated with `psiTheta`, indexed over `ℕ⁺`; the theta bridge produces
    `psiNat`, indexed over `ℕ` by `n ↦ n+1`. They are the same sum. -/

theorem psiTheta_eq_psiNat (t : ℝ) : psiTheta t = psiNat t := by
  rw [psiTheta, psiNat]
  have hinj : Function.Injective (fun n : ℕ => n.succPNat) := by
    intro x y hxy
    simpa using hxy
  have hsupp : Function.support
      (fun m : ℕ+ => Complex.exp (-(((π * ((m : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * (t : ℂ))))
      ⊆ Set.range (fun n : ℕ => n.succPNat) := by
    intro m _
    refine ⟨(m : ℕ) - 1, ?_⟩
    apply PNat.coe_injective
    simp only [Nat.succPNat_coe]
    exact Nat.succ_pred_eq_of_pos m.pos
  refine (hinj.tsum_eq hsupp).symm.trans (tsum_congr fun n => ?_)
  congr 1
  simp only [Nat.succPNat_coe]
  push_cast
  ring

/-- **The transformation law, in the form the split needs.** -/
theorem psiTheta_transform {t : ℝ} (ht : 0 < t) :
    psiTheta (1 / t) = (((Real.sqrt t : ℝ) : ℂ) - 1) / 2
      + ((Real.sqrt t : ℝ) : ℂ) * psiTheta t := by
  rw [psiTheta_eq_psiNat, psiTheta_eq_psiNat, psiNat_transform ht]


/-! ### The elementary pole terms

    `∫₁^∞ (√u−1)/2 · u^{−s/2−1} du = 1/(s−1) − 1/s`. These two terms are what survive the
    `(√u−1)/2` part of `psiTheta_transform`, and they are exactly the pole structure of the
    completed zeta: a simple pole at `s = 1` and one at `s = 0`, swapped by `s ↦ 1−s`. -/

theorem sqrt_eq_cpow_half {u : ℝ} (hu : 0 < u) :
    (((Real.sqrt u : ℝ)) : ℂ) = (u : ℂ) ^ (1 / 2 : ℂ) := (cpow_half_eq_sqrt hu.le).symm

/-- The integrand splits into two pure powers. -/
theorem pole_integrand_eq {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ((((Real.sqrt u : ℝ)) : ℂ) - 1) / 2 * (u : ℂ) ^ (-s / 2 - 1)
      = (1 / 2) * (u : ℂ) ^ (-s / 2 - 1 / 2) - (1 / 2) * (u : ℂ) ^ (-s / 2 - 1) := by
  have hne : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hsplit : (u : ℂ) ^ (1 / 2 : ℂ) * (u : ℂ) ^ (-s / 2 - 1)
      = (u : ℂ) ^ (-s / 2 - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hne]
    congr 1
    ring
  rw [sqrt_eq_cpow_half hu, ← hsplit]
  ring

theorem integral_pole_terms {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (1 : ℝ), ((((Real.sqrt u : ℝ)) : ℂ) - 1) / 2 * (u : ℂ) ^ (-s / 2 - 1))
      = 1 / (s - 1) - 1 / s := by
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at hs; simp at hs
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    exact hs1 (by linear_combination -h)
  have hre1 : (-s / 2 - 1 / 2).re < -1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
    linarith
  have hre2 : (-s / 2 - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
    linarith
  have hi1 := integrableOn_Ioi_cpow_of_lt hre1 (by norm_num : (0:ℝ) < 1)
  have hi2 := integrableOn_Ioi_cpow_of_lt hre2 (by norm_num : (0:ℝ) < 1)
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun u hu => pole_integrand_eq (s := s) (by linarith [Set.mem_Ioi.mp hu]))]
  have e1 : (∫ a in Ioi (1 : ℝ), (1 / 2 : ℂ) * (a : ℂ) ^ (-s / 2 - 1 / 2))
      = (1 / 2 : ℂ) * ∫ a in Ioi (1 : ℝ), (a : ℂ) ^ (-s / 2 - 1 / 2) :=
    MeasureTheory.integral_const_mul _ _
  have e2 : (∫ a in Ioi (1 : ℝ), (1 / 2 : ℂ) * (a : ℂ) ^ (-s / 2 - 1))
      = (1 / 2 : ℂ) * ∫ a in Ioi (1 : ℝ), (a : ℂ) ^ (-s / 2 - 1) :=
    MeasureTheory.integral_const_mul _ _
  rw [integral_sub (hi1.const_mul _) (hi2.const_mul _), e1, e2,
    integral_Ioi_cpow_of_lt hre1 (by norm_num), integral_Ioi_cpow_of_lt hre2 (by norm_num)]
  have hA : (-s / 2 - 1 / 2) + 1 ≠ 0 := fun h => h1s (by linear_combination 2 * h)
  have hB : (-s / 2 - 1) + 1 ≠ 0 := fun h => hsne (by linear_combination -2 * h)
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hA' : (1 - s) * (1 - s)⁻¹ = 1 := mul_inv_cancel₀ h1s
  have hB' : s * s⁻¹ = 1 := mul_inv_cancel₀ hsne
  rw [div_sub_div _ _ hs1 hsne]
  field_simp
  linear_combination s * hA' + (1 - s) * hB'

end TDLean.FE
