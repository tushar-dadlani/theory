/-
  TDLean.Newman.Region -- Brick C1.

  ORACLE: spectral-theory/CTruncDisk.v : TruncDisk_convex, TruncDisk_open
  Claim: Zagier's truncated disk `U = {|z| < R} ∩ {Re z > -δ}` is convex and open.

  This is the region on which the whole Newman contour argument runs. Zagier uses the
  truncated disk rather than a full disk because Newman's `g = Φ - 1/(s-1)` is holomorphic
  only on `{0 < Re z, z ≠ 1, ζ ≠ 0}`, so a full circle of radius `R → ∞` leaves the domain
  (see docs/route_b_C4_newman_plan.md, "the key architectural finding").

  Convexity is the hypothesis brick C4 needs: mathlib has Cauchy's theorem on rectangles
  and circles only, so the truncated-disk Cauchy theorem must be built, and convexity is
  what makes `Analysis/Complex/HasPrimitives.lean`'s wedge-integral machinery apply.
-/
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex

namespace TDLean.Newman

open Complex Set Metric

/-- Zagier's truncated disk. ORACLE: CTruncDisk.v : TruncDisk -/
def truncDisk (R δ : ℝ) : Set ℂ := ball 0 R ∩ {z : ℂ | -δ < z.re}

/-- ORACLE: CTruncDisk.v : TruncDisk_convex -/
theorem convex_truncDisk (R δ : ℝ) : Convex ℝ (truncDisk R δ) :=
  (convex_ball (0 : ℂ) R).inter (convex_halfSpace_re_gt (-δ))

/-- ORACLE: CTruncDisk.v : TruncDisk_open -/
theorem isOpen_truncDisk (R δ : ℝ) : IsOpen (truncDisk R δ) :=
  (isOpen_ball).inter (isOpen_lt continuous_const Complex.continuous_re)

/-- `0` lies in the region -- needed by brick C4/C6, where the Cauchy formula is taken at
    the centre `0` and `dslope F 0` must be differentiable on a neighbourhood of it. -/
theorem zero_mem_truncDisk {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    (0 : ℂ) ∈ truncDisk R δ :=
  ⟨mem_ball_self hR, by simpa using neg_neg_iff_pos.mpr hδ⟩

/-- Non-vacuity: the region is inhabited for positive parameters. -/
theorem truncDisk_nonvacuous : ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ (truncDisk R δ).Nonempty :=
  ⟨1, 1, one_pos, one_pos, ⟨0, zero_mem_truncDisk one_pos one_pos⟩⟩

end TDLean.Newman
