/-
  TDLean.Newman.Kernel -- Brick C2.

  ORACLE: spectral-theory/CNewmanKernel.v : newman_kernel_on_circle, Cmod_newman_kernel
  Claim: on the circle `‖z‖ = R`, Zagier/Newman's kernel `K_R z = z⁻¹ + z/R²` collapses to
  the REAL value `2 (Re z)/R²`, hence `‖K_R z‖ = 2|Re z|/R²`. This is what powers Newman's
  right-semicircle `O(B/R)` estimate.

  The mechanism: on `‖z‖ = R` we have `z⁻¹ = conj z / R²`, so `K_R z = (conj z + z)/R²`
  and `conj z + z = 2 Re z` is real.
-/
import Mathlib.Analysis.Complex.Norm

namespace TDLean.Newman

open Complex

/-- Zagier/Newman's kernel. ORACLE: CNewmanKernel.v : newman_kernel -/
noncomputable def newmanKernel (R : ℝ) (z : ℂ) : ℂ := z⁻¹ + z / (R ^ 2 : ℝ)

/-- ORACLE: CNewmanKernel.v : newman_kernel_on_circle.
    On `‖z‖ = R` the kernel is the real number `2 (Re z)/R²`. -/
theorem newmanKernel_of_norm_eq {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R) :
    newmanKernel R z = ((2 * z.re / R ^ 2 : ℝ) : ℂ) := by
  -- `normSq z = R²`, the only place the circle hypothesis is used
  have hnormSq : Complex.normSq z = R ^ 2 := by rw [← Complex.sq_norm, hz]
  have hR2 : (R : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hR.ne'
  -- `z⁻¹ = conj z * (R²)⁻¹`, so the kernel is `(conj z + z) * (R²)⁻¹`
  rw [newmanKernel, Complex.inv_def, hnormSq, div_eq_mul_inv]
  have : (starRingEnd ℂ) z * ((R ^ 2 : ℝ) : ℂ)⁻¹ + z * ((R ^ 2 : ℝ) : ℂ)⁻¹
      = (z + (starRingEnd ℂ) z) * ((R ^ 2 : ℝ) : ℂ)⁻¹ := by ring
  push_cast at this ⊢
  rw [this, Complex.add_conj]
  push_cast
  ring

/-- ORACLE: CNewmanKernel.v : Cmod_newman_kernel.
    `‖z⁻¹ + z/R²‖ = 2|Re z|/R²` on `‖z‖ = R`. -/
theorem norm_newmanKernel {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R) :
    ‖newmanKernel R z‖ = 2 * |z.re| / R ^ 2 := by
  rw [newmanKernel_of_norm_eq hR hz, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos (by positivity : (0:ℝ) < R ^ 2), abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- Non-vacuity: the hypotheses are satisfiable. -/
theorem newmanKernel_nonvacuous : ∃ (R : ℝ) (z : ℂ), 0 < R ∧ ‖z‖ = R :=
  ⟨1, Complex.I, one_pos, Complex.norm_I⟩

end TDLean.Newman
