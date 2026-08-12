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

end TDLean.FE
