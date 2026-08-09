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
import TDLean.Newman.Region
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TDLean.Newman

open Complex Set MeasureTheory intervalIntegral Metric
open scoped Interval

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

/-! ### The keystone: a primitive exists -/

/-- The `z`-derivative of the radial integrand, as a function of `(x, t)`. -/
noncomputable def radialDeriv (f : ℂ → ℂ) (x : ℂ) (t : ℝ) : ℂ :=
  f ((t : ℂ) * x) + x * ((t : ℂ) * deriv f ((t : ℂ) * x))

/-- ORACLE: CPrimConv.v : the convex-region primitive (with CGoursatConv.v behind it).
    On an open, star-shaped-about-`0` region, `radialPrimitive f` is a primitive of `f`. -/
theorem hasDerivAt_radialPrimitive (hU : IsOpen U) (hstar : StarAboutZero U)
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (radialPrimitive f) (f z) z := by
  -- a closed ball around `z` inside `U`
  obtain ⟨r, hr, hball⟩ : ∃ r, 0 < r ∧ closedBall z r ⊆ U := by
    obtain ⟨ρ, hρ, h⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨ρ / 2, by linarith, fun w hw => h ?_⟩
    have hd : dist w z ≤ ρ / 2 := mem_closedBall.mp hw
    exact mem_ball.mpr (by linarith)
  have hzr : z ∈ closedBall z r := mem_closedBall_self hr.le
  have hKc : IsCompact (radialCone (closedBall z r)) :=
    isCompact_radialCone (isCompact_closedBall z r)
  have hKU : radialCone (closedBall z r) ⊆ U := radialCone_subset hstar hball
  have hfc : ContinuousOn f U := hf.continuousOn
  have hdc : ContinuousOn (deriv f) U := (hf.deriv hU).continuousOn
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hfc.mono hKU)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hdc.mono hKU)
  have hpathU : ∀ x ∈ closedBall z r, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * x ∈ U :=
    fun x hx t ht => hKU (mem_radialCone hx ht)
  have huIcc : uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := uIcc_of_le zero_le_one
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [← huIcc]; exact uIoc_subset_uIcc
  have hpathcont : ∀ x : ℂ, Continuous (fun t : ℝ => (t : ℂ) * x) := by intro x; fun_prop
  have hFc : ∀ x ∈ closedBall z r,
      ContinuousOn (fun t : ℝ => x * f ((t : ℂ) * x)) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact continuousOn_const.mul
      (hfc.comp (hpathcont x).continuousOn fun t ht => hpathU x hx t ht)
  have hF'c : ∀ x ∈ closedBall z r,
      ContinuousOn (radialDeriv f x) (Icc (0 : ℝ) 1) := by
    intro x hx
    refine ContinuousOn.add
      (hfc.comp (hpathcont x).continuousOn fun t ht => hpathU x hx t ht)
      (continuousOn_const.mul (ContinuousOn.mul ?_ ?_))
    · exact Complex.continuous_ofReal.continuousOn
    · exact hdc.comp (hpathcont x).continuousOn fun t ht => hpathU x hx t ht
  have hxbound : ∀ x ∈ closedBall z r, ‖x‖ ≤ ‖z‖ + r := by
    intro x hx
    have hd : ‖x - z‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    calc ‖x‖ = ‖z + (x - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖x - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + r := by linarith
  set B : ℝ := M₁ + (‖z‖ + r) * M₂ with hB
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1, ∀ x ∈ ball z r, ‖radialDeriv f x t‖ ≤ B := by
    intro t ht x hx
    have hxc : x ∈ closedBall z r := ball_subset_closedBall hx
    have ht' : t ∈ Icc (0 : ℝ) 1 := hsub ht
    have hmem : (t : ℂ) * x ∈ radialCone (closedBall z r) := mem_radialCone hxc ht'
    have h1 : ‖f ((t : ℂ) * x)‖ ≤ M₁ := hM₁ _ hmem
    have h2 : ‖deriv f ((t : ℂ) * x)‖ ≤ M₂ := hM₂ _ hmem
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
    have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) h2
    have hxn : ‖x‖ ≤ ‖z‖ + r := hxbound x hxc
    have hkey : ‖x * ((t : ℂ) * deriv f ((t : ℂ) * x))‖ ≤ (‖z‖ + r) * M₂ := by
      rw [norm_mul, norm_mul]
      calc ‖x‖ * (‖(t : ℂ)‖ * ‖deriv f ((t : ℂ) * x)‖)
          ≤ (‖z‖ + r) * (1 * M₂) := by gcongr
        _ = (‖z‖ + r) * M₂ := by ring
    calc ‖radialDeriv f x t‖
        ≤ ‖f ((t : ℂ) * x)‖ + ‖x * ((t : ℂ) * deriv f ((t : ℂ) * x))‖ := norm_add_le _ _
      _ ≤ B := by rw [hB]; linarith
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => x * f ((t : ℂ) * x)) (F' := radialDeriv f) (x₀ := z)
    (bound := fun _ => B) (s := ball z r) (μ := MeasureTheory.volume) (a := 0) (b := 1)
    (ball_mem_nhds z hr)
    (by
      filter_upwards [ball_mem_nhds z hr] with x hx
      exact ((hFc x (ball_subset_closedBall hx)).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
    (by have := hFc z hzr; rw [← huIcc] at this; exact this.intervalIntegrable)
    (((hF'c z hzr).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall hbound)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht x hx =>
      hasDerivAt_radialIntegrand hU hf (hpathU x (ball_subset_closedBall hx) t (hsub ht)))
  -- the `t`-integral of the derivative telescopes to `f z`
  have hFTC : (∫ t in (0 : ℝ)..1, radialDeriv f z t) = f z := by
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => (s : ℂ) * f ((s : ℂ) * z)) (radialDeriv f z t) t := by
      intro t ht
      rw [huIcc] at ht
      exact hasDerivAt_radialAntiderivative hU hf (hpathU z hzr t ht)
    have hint : IntervalIntegrable (radialDeriv f z) MeasureTheory.volume 0 1 := by
      have := hF'c z hzr; rw [← huIcc] at this; exact this.intervalIntegrable
    rw [integral_eq_sub_of_hasDerivAt hderiv hint]
    push_cast
    ring_nf
  rw [hFTC] at hmain
  exact hmain.2

/-- ORACLE: CPrimConv.v : pathint_loop_conv (region loop-zero).
    The Cauchy theorem the Newman argument needs: the loop integral over the truncated
    contour of a function holomorphic on an open star-shaped region containing the contour
    vanishes. C4 composed with C3. -/
theorem truncContour_eq_zero_of_starAboutZero {R α : ℝ} (hU : IsOpen U)
    (hstar : StarAboutZero U) (hf : DifferentiableOn ℂ f U)
    (hsubset : contourSet R α ⊆ U) :
    truncContour f R α = 0 :=
  truncContour_eq_zero_of_primitive
    (fun _ hz => hasDerivAt_radialPrimitive hU hstar hf (hsubset hz))
    (hf.continuousOn.mono hsubset)

/-- The truncated disk is star-shaped about `0`, so C4 applies to it. -/
theorem starAboutZero_truncDisk {R δ : ℝ} (hδ : 0 < δ) :
    StarAboutZero (truncDisk R δ) := by
  rintro z ⟨hz1, hz2⟩ t ⟨ht0, ht1⟩
  simp only [Set.mem_setOf_eq] at hz2
  refine ⟨?_, ?_⟩
  · have hnorm : ‖(t : ℂ) * z‖ ≤ ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      nlinarith [norm_nonneg z]
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hnorm (mem_ball_zero_iff.mp hz1))
  · simp only [Set.mem_setOf_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rcases le_or_gt 0 z.re with h | h
    · nlinarith [mul_nonneg ht0 h]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt (neg_pos.mpr h))]

end TDLean.Newman
