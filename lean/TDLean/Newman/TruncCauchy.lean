/-
  TDLean.Newman.TruncCauchy -- Brick C6.

  ORACLE: spectral-theory/CTruncCauchy.v : trunc_cauchy
  Claim: `∮_C F(z)/z dz = 2πi · F(0)` over Zagier's truncated contour, for `F` holomorphic
  on an open star-shaped region containing the contour and `0`.

  ## This is STRICTLY STRONGER than the Coq oracle

  The Coq `trunc_cauchy` is a `Section` theorem that *takes as hypotheses* the whole
  exceptional-point interface for the removable quotient `φ = (F - F 0)/z`: global `CcontC`
  continuity, holomorphy off `0`, boundedness and continuity near `0`, and agreement with
  `(F - F 0)/z` on the contour. `docs/newman_route_status.md` lists discharging that
  interface -- "the g-extension / discharge φ" -- as one of the *deep remaining blockers*,
  because the Coq integral infrastructure demands GLOBAL continuity while `g` is only
  holomorphic near the truncated disk.

  Here the theorem is **unconditional**. mathlib's `dslope F 0` is *defined* to be
  `(F z - F 0)/(z - 0)` away from `0` and `deriv F 0` at `0`, and
  `differentiableOn_dslope` says it is differentiable on any neighbourhood of `0` on which
  `F` is. No continuity side condition survives, because Bochner integrals carry none.

  So that Coq blocker is an artifact of the bespoke `ComplexField` development, not
  mathematics. Recorded in LEDGER.md.

  Proof: `F z / z = dslope F 0 z + F 0 * z⁻¹` off `0`; C4 kills the first summand
  (`dslope F 0` is holomorphic on the region), C5 evaluates the second.
-/
import TDLean.Newman.StarPrimitive
import TDLean.Newman.Winding
import Mathlib.Analysis.Complex.RemovableSingularity

namespace TDLean.Newman

open Complex Set Metric Real

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- Off `0`, the Cauchy integrand splits into the removable quotient plus the pole. -/
theorem div_eq_dslope_add {z : ℂ} (hz : z ≠ 0) (F : ℂ → ℂ) :
    F z / z = dslope F 0 z + F 0 * z⁻¹ := by
  rw [dslope_of_ne F hz, slope_def_field, sub_zero]
  field_simp
  ring

/-- ORACLE: CTruncCauchy.v : trunc_cauchy -- but **unconditional** here, where the Coq
    version takes φ's global-continuity interface as hypotheses. -/
theorem trunc_cauchy {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α < π)
    (hU : IsOpen U) (hstar : StarAboutZero U) (h0 : (0 : ℂ) ∈ U)
    (hF : DifferentiableOn ℂ F U) (hsubset : contourSet R α ⊆ U)
    (hzero : (0 : ℂ) ∉ contourSet R α) :
    truncContour (fun z => F z / z) R α = 2 * π * I * F 0 := by
  -- the contour avoids `0`
  have hne : ∀ z ∈ contourSet R α, z ≠ 0 := fun z hz h => hzero (h ▸ hz)
  -- `dslope F 0` is holomorphic on `U`
  have hds : DifferentiableOn ℂ (dslope F 0) U :=
    (differentiableOn_dslope (hU.mem_nhds h0)).mpr hF
  -- rewrite the integrand on the contour
  have hsplit : truncContour (fun z => F z / z) R α
      = truncContour (fun z => dslope F 0 z + F 0 * z⁻¹) R α := by
    unfold truncContour arcIntegral chordIntegral
    congr 1
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      dsimp only
      rw [div_eq_dslope_add (hne _ (Or.inl (arcSet_mem hθ))) F]
    · refine intervalIntegral.integral_congr fun t ht => ?_
      dsimp only
      rw [div_eq_dslope_add (hne _ (Or.inr (chordSet_mem ht))) F]
  -- split, then apply C4 to the removable part and C5 to the pole
  have hcont₁ : ContinuousOn (dslope F 0) (contourSet R α) := hds.continuousOn.mono hsubset
  have hcont₂ : ContinuousOn (fun z : ℂ => F 0 * z⁻¹) (contourSet R α) := by
    intro z hz
    exact (continuousAt_const.mul (continuousAt_inv₀ (hne z hz))).continuousWithinAt
  rw [hsplit, truncContour_add hcont₁ hcont₂,
    truncContour_eq_zero_of_starAboutZero hU hstar hds hsubset,
    truncContour_const_mul (F 0) (fun z => z⁻¹) R α,
    trunc_winding hR hα hα2]
  ring

end TDLean.Newman
