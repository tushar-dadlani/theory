/-
  TDLean.Newman.StarPrimitive -- Brick C4, the keystone.

  ORACLE: spectral-theory/CGoursatConv.v (region Goursat, 428 lines)
        + spectral-theory/CPrimConv.v    (convex primitive + loop-zero, 271 lines)
        + spectral-theory/CGoursatExcept.v (exceptional-point primitive, 417 lines)

  Claim: a holomorphic function on an open, star-shaped-about-`0` region has a primitive
  there. Combined with C3 (`truncContour_eq_zero_of_primitive`), every closed-loop integral
  over the truncated contour vanishes -- which is the Cauchy theorem the Newman argument
  needs, and which mathlib does not provide (it has Cauchy on rectangles and circles only,
  with no convex / star-shaped / simply-connected version and no homotopy invariance).

  ## Why not adapt mathlib's `Analysis/Complex/HasPrimitives.lean`

  That file proves `DifferentiableOn.isExactOn_ball` by Morera, via `wedgeIntegral`. Two
  obstacles, both discovered by trying:

  1. Its route needs the *rectangle* spanned by pairs of points to stay in the region, and
     **balls are not rectangle-closed** -- take `z = 0.9`, `w = 0.9i` in `ball 0 1`: the
     corner `0.9 + 0.9i` has modulus `1.27 > 1`. mathlib's proof only ever moves a
     coordinate *toward the centre*, which is why it works for a ball and does not
     generalise for free.
  2. Every supporting lemma (`re_add_im_mul_mem_ball`, `mem_ball_of_map_re_aux`,
     `hasDerivAt_wedgeIntegral_re_aux`, ...) is `private`, so an adaptation must re-prove
     them rather than reuse them.

  So this file uses the self-contained **radial** argument instead:

      F z := ∫₀¹ z · f (t z) dt

  and the identity that makes it work,

      ∂/∂z [ z f(tz) ] = f(tz) + t z f'(tz) = d/dt [ t f(tz) ],

  so differentiating under the integral and then applying FTC-2 in `t` telescopes to
  `[t f(tz)]₀¹ = f(z)`.

  Note the `(t : ℂ) * z` spelling rather than `t • z` throughout: the real-on-complex
  scalar action runs into the instance diamond documented in `Contour.lean`'s header.
-/
import TDLean.Newman.Contour
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TDLean.Newman

open Complex Set MeasureTheory intervalIntegral Metric

variable {f : ℂ → ℂ} {U : Set ℂ}

/-- The region is star-shaped about `0`, written multiplicatively to avoid the `ℝ`-on-`ℂ`
    scalar-action diamond. -/
def StarAboutZero (U : Set ℂ) : Prop := ∀ z ∈ U, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (t : ℂ) * z ∈ U

/-- The radial primitive `F z = ∫₀¹ z f(tz) dt`. -/
noncomputable def radialPrimitive (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, z * f ((t : ℂ) * z)

/-! ### The radial cone over a compact set stays in `U` -/

/-- The set swept by radii from `0` to points of `s`. -/
def radialCone (s : Set ℂ) : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' (Icc (0 : ℝ) 1 ×ˢ s)

theorem isCompact_radialCone {s : Set ℂ} (hs : IsCompact s) : IsCompact (radialCone s) :=
  (isCompact_Icc.prod hs).image (by fun_prop)

theorem radialCone_subset (hstar : StarAboutZero U) {s : Set ℂ} (hs : s ⊆ U) :
    radialCone s ⊆ U := by
  rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  exact hstar x (hs hx) t ht

theorem mem_radialCone {s : Set ℂ} {x : ℂ} (hx : x ∈ s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * x ∈ radialCone s := ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩

/-! ### The integrand and its `z`-derivative -/

/-- `∂/∂z [ z · f (t z) ] = f(tz) + t·z·f'(tz)`. -/
theorem hasDerivAt_radialIntegrand (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} {x : ℂ} (hmem : (t : ℂ) * x ∈ U) :
    HasDerivAt (fun w : ℂ => w * f ((t : ℂ) * w))
      (f ((t : ℂ) * x) + x * ((t : ℂ) * deriv f ((t : ℂ) * x))) x := by
  have hfd : HasDerivAt f (deriv f ((t : ℂ) * x)) ((t : ℂ) * x) :=
    ((hf.differentiableAt (hU.mem_nhds hmem))).hasDerivAt
  have hinner : HasDerivAt (fun w : ℂ => (t : ℂ) * w) (t : ℂ) x := by
    simpa using (hasDerivAt_id x).const_mul (t : ℂ)
  have hcomp := hfd.comp x hinner
  rw [Function.comp_def] at hcomp
  have := (hasDerivAt_id x).mul hcomp
  convert this using 1
  simp only [id_eq]
  ring

/-- `d/dt [ t · f (t z) ] = f(tz) + z·t·f'(tz)` -- the same expression, which is the whole
    trick. Proved through the `ofReal` factorisation from `Contour.lean`. -/
theorem hasDerivAt_radialAntiderivative (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z : ℂ} {t : ℝ} (hmem : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * f ((s : ℂ) * z))
      (f ((t : ℂ) * z) + z * ((t : ℂ) * deriv f ((t : ℂ) * z))) t := by
  have hg : HasDerivAt (fun w : ℂ => w * f (w * z))
      (f ((t : ℂ) * z) + (t : ℂ) * (z * deriv f ((t : ℂ) * z))) (t : ℂ) := by
    have hfd : HasDerivAt f (deriv f ((t : ℂ) * z)) ((t : ℂ) * z) :=
      ((hf.differentiableAt (hU.mem_nhds hmem))).hasDerivAt
    have hinner : HasDerivAt (fun w : ℂ => w * z) z (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const z
    have hcomp := hfd.comp (t : ℂ) hinner
    rw [Function.comp_def] at hcomp
    have := (hasDerivAt_id (t : ℂ)).mul hcomp
    convert this using 1
    simp only [id_eq]
    ring
  have := hg.comp_ofReal
  convert this using 1
  ring

end TDLean.Newman
