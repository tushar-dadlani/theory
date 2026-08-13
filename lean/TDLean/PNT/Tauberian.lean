/-
  TDLean.PNT.Tauberian -- C10, part 9: feeding everything into Newman's theorem.

  Every hypothesis of `newman_tauberian` is now available:

    regularity  `intervalIntegrable_fNewmanC`   (NOT continuity -- `f` is a step function)
    bound       `norm_fNewmanC_le`              (from Chebyshev, `ψ(x) ≤ Ccheb·x`)
    integrable  `integrableOn_fNewman_exp`
    Laplace     `gNewman_eq`                    (via Mellin + change of variable)
    region      `hregion_gNewman`               (via `Φ⁻` holomorphic on `Re s ≥ 1`,
                                                 i.e. C9 items 3 and 4)

  so `∫₀^T f → g(0)`: the improper integral `∫₀^∞ (ψ(eᵗ)e^{−t} − 1) dt` converges.
-/
import TDLean.PNT.Region
import TDLean.Newman.Tauberian

namespace TDLean.PNT

open MeasureTheory TDLean.Zeta TDLean.Newman

/-- **The Tauberian conclusion.** `∫₀^T (ψ(eᵗ)e^{−t} − 1) dt` converges as `T → ∞`. -/
theorem tendsto_integral_fNewman :
    Filter.Tendsto (fun T : ℝ => gT fNewmanC T 0) Filter.atTop (nhds (gNewman 0)) := by
  refine newman_tauberian (B := Ccheb + 1) intervalIntegrable_fNewmanC
    (fun t ht => norm_fNewmanC_le ht) (fun z hz => integrableOn_fNewman_exp hz)
    (fun z hz => gNewman_eq hz) ?_
  intro R hR
  obtain ⟨α, U, hα, hα2, hU, hstar, h0, hsub, hgd⟩ := hregion_gNewman hR
  exact ⟨α, U, hα, hα2, hU, hstar, h0, hsub, hgd⟩

/-- Unwinding `gT … 0`: the conclusion really is about `∫₀^T f`. -/
theorem gT_zero (T : ℝ) : gT fNewmanC T 0 = ∫ t in (0 : ℝ)..T, fNewmanC t := by
  rw [gT]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

/-- **The improper integral converges.** -/
theorem tendsto_integral_fNewman' :
    Filter.Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, fNewmanC t) Filter.atTop
      (nhds (gNewman 0)) :=
  tendsto_integral_fNewman.congr gT_zero

end TDLean.PNT
