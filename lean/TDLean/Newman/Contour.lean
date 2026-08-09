/-
  TDLean.Newman.Contour -- Brick C3.

  Zagier's truncated contour `C = arc + chord`, and the piecewise-loop fundamental theorem
  of calculus for it: if `f` has a primitive `F` along the contour, the loop integral
  vanishes.

  ORACLE: this brick has no single Coq counterpart. The Coq development builds a general
  path-integral calculus first (`CPathIntegral.v`, `CPathFTC.v`, `CSegInt.v`) because Rocq's
  stdlib has no complex analysis; `pathint_FTC` / `pathint_primitive_loop` are the
  corresponding engine. mathlib has interval integrals and FTC-2 but no path-integral
  abstraction, so this file supplies exactly the minimum the truncated contour needs.

  The contour is the boundary of `truncDisk R δ` (see Region.lean) with `δ = -R cos α`:
  the arc `θ ∈ [-α, α]` of `|z| = R` counterclockwise, then the chord from `top = R e^{iα}`
  back to `bot = R e^{-iα}`.

  With a primitive `F` the arc contributes `F top - F bot` and the chord `F bot - F top`,
  so the loop is `0` -- for ANY `α`, with no holomorphy hypothesis beyond the pointwise
  existence of `F` along the contour. Holomorphy enters only in C4, which *produces* `F`.

  ## A note on the chain rule (worth recording)

  The obvious route -- `(hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt` -- does NOT
  work here. For a concrete `ℂ → ℂ` function Lean resolves `NormedSpace ℝ ℂ` through
  `instInnerProductSpaceRealComplex`, and the resulting `SMul ℝ ℂ` does not match the
  algebra tower, so `IsScalarTower ℝ ℂ ℂ` fails to synthesise even though it is provable
  standalone. (mathlib's own uses of that idiom are in contexts where the codomain is an
  abstract `E`, which dodges the diamond.)

  The fix used below: factor every path as a genuinely `ℂ → ℂ` map precomposed with
  `Complex.ofReal`. Then the chain rule stays inside `ℂ` (`HasDerivAt.comp`, no scalar
  tower) and the real restriction is handled by mathlib's `HasDerivAt.comp_ofReal`.
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv

namespace TDLean.Newman

open Complex Set intervalIntegral

/-! ### Paths, as `ℂ → ℂ` maps restricted to `ℝ` -/

/-- The circle map as a genuinely complex-analytic function, so that the chain rule can be
    applied inside `ℂ`. Agrees with `circleMap` on reals (`circleMapC_ofReal`). -/
noncomputable def circleMapC (c : ℂ) (R : ℝ) (z : ℂ) : ℂ := c + R * Complex.exp (z * I)

@[simp] theorem circleMapC_ofReal (c : ℂ) (R : ℝ) (θ : ℝ) :
    circleMapC c R (θ : ℂ) = circleMap c R θ := rfl

theorem hasDerivAt_circleMapC (c : ℂ) (R : ℝ) (z : ℂ) :
    HasDerivAt (circleMapC c R) ((R : ℂ) * Complex.exp (z * I) * I) z := by
  unfold circleMapC
  have h : HasDerivAt (fun z : ℂ => Complex.exp (z * I)) (Complex.exp (z * I) * I) z := by
    simpa using (Complex.hasDerivAt_exp (z * I)).comp z ((hasDerivAt_id z).mul_const I)
  simpa [mul_assoc] using ((h.const_mul (R : ℂ)).const_add c)

/-- The straight chord from `P` to `Q`, as a complex-analytic function. -/
noncomputable def chordC (P Q : ℂ) (z : ℂ) : ℂ := P + z * (Q - P)

/-- The straight chord from `P` to `Q`, parametrised on `[0,1]`. -/
noncomputable def chord (P Q : ℂ) (t : ℝ) : ℂ := chordC P Q (t : ℂ)

theorem hasDerivAt_chordC (P Q : ℂ) (z : ℂ) : HasDerivAt (chordC P Q) (Q - P) z := by
  unfold chordC
  simpa using (((hasDerivAt_id z).mul_const (Q - P)).const_add P)

theorem continuous_chord (P Q : ℂ) : Continuous (chord P Q) := by
  unfold chord chordC; fun_prop

theorem continuous_arc (R : ℝ) : Continuous (circleMap 0 R) := continuous_circleMap 0 R

/-- The chain rule for `F ∘ γ` where `γ = g ∘ ofReal` and both `F, g : ℂ → ℂ`.

    Composing inside `ℂ` first sidesteps the `IsScalarTower ℝ ℂ ℂ` diamond described in the
    file header. -/
theorem hasDerivAt_comp_ofReal_path {F g : ℂ → ℂ} {w v : ℂ} {t : ℝ}
    (hF : HasDerivAt F w (g (t : ℂ))) (hg : HasDerivAt g v (t : ℂ)) :
    HasDerivAt (fun s : ℝ => F (g (s : ℂ))) (v * w) t := by
  have h : HasDerivAt (F ∘ g) (w * v) (t : ℂ) := hF.comp (t : ℂ) hg
  simpa [Function.comp_def, mul_comm] using h.comp_ofReal

/-! ### The contour -/

/-- The upper endpoint of the arc, `R e^{iα}`. -/
noncomputable def arcTop (R α : ℝ) : ℂ := circleMap 0 R α

/-- The lower endpoint of the arc, `R e^{-iα}`. -/
noncomputable def arcBot (R α : ℝ) : ℂ := circleMap 0 R (-α)

/-- `∫` over the circular arc `θ ∈ [-α, α]`. -/
noncomputable def arcIntegral (f : ℂ → ℂ) (R α : ℝ) : ℂ :=
  ∫ θ in (-α)..α, deriv (circleMap 0 R) θ * f (circleMap 0 R θ)

/-- `∫` over the chord from `P` to `Q`. -/
noncomputable def chordIntegral (f : ℂ → ℂ) (P Q : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (Q - P) * f (chord P Q t)

/-- Zagier's truncated contour: arc then chord.
    ORACLE: the contour of CTruncWind.v : trunc_winding and CTruncCauchy.v : trunc_cauchy -/
noncomputable def truncContour (f : ℂ → ℂ) (R α : ℝ) : ℂ :=
  arcIntegral f R α + chordIntegral f (arcTop R α) (arcBot R α)

/-- The points traced by the arc. -/
def arcSet (R α : ℝ) : Set ℂ := circleMap 0 R '' uIcc (-α) α

/-- The points traced by the chord. -/
def chordSet (P Q : ℂ) : Set ℂ := chord P Q '' uIcc (0:ℝ) 1

/-- The whole contour, as a set of points. -/
def contourSet (R α : ℝ) : Set ℂ := arcSet R α ∪ chordSet (arcTop R α) (arcBot R α)

/-! ### Integrability of the two pieces -/

theorem arcSet_mem {R α : ℝ} {θ : ℝ} (hθ : θ ∈ uIcc (-α) α) :
    circleMap 0 R θ ∈ arcSet R α := ⟨θ, hθ, rfl⟩

theorem chordSet_mem {P Q : ℂ} {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) :
    chord P Q t ∈ chordSet P Q := ⟨t, ht, rfl⟩

theorem arcIntegrand_continuousOn {f : ℂ → ℂ} {R α : ℝ} (hf : ContinuousOn f (arcSet R α)) :
    ContinuousOn (fun θ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ)) (uIcc (-α) α) := by
  have hderivEq : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * I :=
    funext fun θ => deriv_circleMap 0 R θ
  have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap 0 R) θ) (uIcc (-α) α) := by
    rw [hderivEq]; exact ((continuous_arc R).continuousOn).mul continuousOn_const
  exact h1.mul (hf.comp (continuous_arc R).continuousOn fun θ hθ => arcSet_mem hθ)

theorem arcIntegrable {f : ℂ → ℂ} {R α : ℝ} (hf : ContinuousOn f (arcSet R α)) :
    IntervalIntegrable (fun θ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ))
      MeasureTheory.volume (-α) α :=
  (arcIntegrand_continuousOn hf).intervalIntegrable

theorem chordIntegrand_continuousOn {f : ℂ → ℂ} {P Q : ℂ} (hf : ContinuousOn f (chordSet P Q)) :
    ContinuousOn (fun t => (Q - P) * f (chord P Q t)) (uIcc (0 : ℝ) 1) :=
  continuousOn_const.mul (hf.comp (continuous_chord P Q).continuousOn fun _ ht => chordSet_mem ht)

theorem chordIntegrable {f : ℂ → ℂ} {P Q : ℂ} (hf : ContinuousOn f (chordSet P Q)) :
    IntervalIntegrable (fun t => (Q - P) * f (chord P Q t)) MeasureTheory.volume 0 1 :=
  (chordIntegrand_continuousOn hf).intervalIntegrable

/-! ### Linearity of the contour integral -/

theorem truncContour_const_mul (c : ℂ) (f : ℂ → ℂ) (R α : ℝ) :
    truncContour (fun z => c * f z) R α = c * truncContour f R α := by
  have harc : (fun θ : ℝ => deriv (circleMap 0 R) θ * (c * f (circleMap 0 R θ)))
      = fun θ : ℝ => c * (deriv (circleMap 0 R) θ * f (circleMap 0 R θ)) :=
    funext fun θ => by ring
  have hch : (fun t : ℝ => (arcBot R α - arcTop R α) * (c * f (chord (arcTop R α) (arcBot R α) t)))
      = fun t : ℝ =>
          c * ((arcBot R α - arcTop R α) * f (chord (arcTop R α) (arcBot R α) t)) :=
    funext fun t => by ring
  -- `rw`/`simp` cannot unify `integral_const_mul` here (higher-order pattern), but the
  -- fully-applied term elaborates fine, so state each instance concretely.
  have h1 : (∫ θ in (-α)..α, c * (deriv (circleMap 0 R) θ * f (circleMap 0 R θ)))
      = c * ∫ θ in (-α)..α, deriv (circleMap 0 R) θ * f (circleMap 0 R θ) :=
    intervalIntegral.integral_const_mul c _
  have h2 : (∫ t in (0 : ℝ)..1,
        c * ((arcBot R α - arcTop R α) * f (chord (arcTop R α) (arcBot R α) t)))
      = c * ∫ t in (0 : ℝ)..1,
        (arcBot R α - arcTop R α) * f (chord (arcTop R α) (arcBot R α) t) :=
    intervalIntegral.integral_const_mul c _
  unfold truncContour arcIntegral chordIntegral
  rw [harc, hch, h1, h2]
  ring

theorem truncContour_add {f g : ℂ → ℂ} {R α : ℝ}
    (hf : ContinuousOn f (contourSet R α)) (hg : ContinuousOn g (contourSet R α)) :
    truncContour (fun z => f z + g z) R α = truncContour f R α + truncContour g R α := by
  have harcS : arcSet R α ⊆ contourSet R α := subset_union_left
  have hchS : chordSet (arcTop R α) (arcBot R α) ⊆ contourSet R α := subset_union_right
  have harc : (fun θ : ℝ =>
        deriv (circleMap 0 R) θ * (f (circleMap 0 R θ) + g (circleMap 0 R θ)))
      = fun θ : ℝ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ)
          + deriv (circleMap 0 R) θ * g (circleMap 0 R θ) :=
    funext fun θ => by ring
  have hch : (fun t : ℝ => (arcBot R α - arcTop R α) *
          (f (chord (arcTop R α) (arcBot R α) t) + g (chord (arcTop R α) (arcBot R α) t)))
      = fun t : ℝ => (arcBot R α - arcTop R α) * f (chord (arcTop R α) (arcBot R α) t)
          + (arcBot R α - arcTop R α) * g (chord (arcTop R α) (arcBot R α) t) :=
    funext fun t => by ring
  unfold truncContour arcIntegral chordIntegral
  rw [harc, hch,
    intervalIntegral.integral_add (arcIntegrable (hf.mono harcS)) (arcIntegrable (hg.mono harcS)),
    intervalIntegral.integral_add (chordIntegrable (hf.mono hchS)) (chordIntegrable (hg.mono hchS))]
  ring

/-! ### ML estimates

    The standard "length times sup" bounds for the two pieces. These are what Newman's
    three semicircle estimates are ultimately applications of. -/

/-- On the arc, `‖γ'(θ)‖ = |R|`. -/
theorem norm_deriv_circleMap (R θ : ℝ) : ‖deriv (circleMap 0 R) θ‖ = |R| := by
  rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero]

/-- ML bound on the arc: `‖∫_arc f‖ ≤ |R| · M · |2α|`. -/
theorem norm_arcIntegral_le {f : ℂ → ℂ} {R α M : ℝ}
    (hf : ∀ z ∈ arcSet R α, ‖f z‖ ≤ M) :
    ‖arcIntegral f R α‖ ≤ |R| * M * |α - -α| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
  have hmem : circleMap 0 R θ ∈ arcSet R α := arcSet_mem (uIoc_subset_uIcc hθ)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hf _ hmem)
  rw [norm_mul, norm_deriv_circleMap]
  exact mul_le_mul_of_nonneg_left (hf _ hmem) (abs_nonneg R)

/-- ML bound on the chord: `‖∫_chord f‖ ≤ ‖Q − P‖ · M`. -/
theorem norm_chordIntegral_le {f : ℂ → ℂ} {P Q : ℂ} {M : ℝ}
    (hf : ∀ z ∈ chordSet P Q, ‖f z‖ ≤ M) :
    ‖chordIntegral f P Q‖ ≤ ‖Q - P‖ * M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖Q - P‖ * M)
    (f := fun t : ℝ => (Q - P) * f (chord P Q t)) fun t ht => by
      have hmem : chord P Q t ∈ chordSet P Q := chordSet_mem (uIoc_subset_uIcc ht)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _ hmem) (norm_nonneg _)
  simpa [chordIntegral] using h

/-! ### FTC on each piece -/

/-- FTC along the arc: with a primitive `F`, the arc integral telescopes. -/
theorem arcIntegral_eq_sub {f F : ℂ → ℂ} {R α : ℝ}
    (hF : ∀ z ∈ arcSet R α, HasDerivAt F (f z) z)
    (hf : ContinuousOn f (arcSet R α)) :
    arcIntegral f R α = F (arcTop R α) - F (arcBot R α) := by
  have hmem : ∀ θ ∈ uIcc (-α) α, circleMap 0 R θ ∈ arcSet R α := fun θ hθ => ⟨θ, hθ, rfl⟩
  have hderiv : ∀ θ ∈ uIcc (-α) α,
      HasDerivAt (fun θ : ℝ => F (circleMap 0 R θ))
        (deriv (circleMap 0 R) θ * f (circleMap 0 R θ)) θ := by
    intro θ hθ
    have hg : HasDerivAt (circleMapC 0 R) ((R : ℂ) * Complex.exp ((θ : ℂ) * I) * I) (θ : ℂ) :=
      hasDerivAt_circleMapC 0 R (θ : ℂ)
    have hF' : HasDerivAt F (f (circleMapC 0 R (θ : ℂ))) (circleMapC 0 R (θ : ℂ)) := by
      rw [circleMapC_ofReal]; exact hF _ (hmem θ hθ)
    have := hasDerivAt_comp_ofReal_path hF' hg
    rw [circleMapC_ofReal] at this
    have hval : (R : ℂ) * Complex.exp ((θ : ℂ) * I) * I = deriv (circleMap 0 R) θ := by
      rw [deriv_circleMap, circleMap]; ring
    rwa [hval] at this
  have hderivEq : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * I :=
    funext fun θ => deriv_circleMap 0 R θ
  have hcont : ContinuousOn (fun θ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ))
      (uIcc (-α) α) := by
    have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap 0 R) θ) (uIcc (-α) α) := by
      rw [hderivEq]; exact ((continuous_arc R).continuousOn).mul continuousOn_const
    exact h1.mul (hf.comp (continuous_arc R).continuousOn (fun θ hθ => hmem θ hθ))
  simpa [arcIntegral, arcTop, arcBot] using
    integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- FTC along the chord: with a primitive `F`, the chord integral telescopes. -/
theorem chordIntegral_eq_sub {f F : ℂ → ℂ} {P Q : ℂ}
    (hF : ∀ z ∈ chordSet P Q, HasDerivAt F (f z) z)
    (hf : ContinuousOn f (chordSet P Q)) :
    chordIntegral f P Q = F Q - F P := by
  have hmem : ∀ t ∈ uIcc (0:ℝ) 1, chord P Q t ∈ chordSet P Q := fun t ht => ⟨t, ht, rfl⟩
  have hderiv : ∀ t ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => F (chord P Q t)) ((Q - P) * f (chord P Q t)) t := by
    intro t ht
    exact hasDerivAt_comp_ofReal_path (hF _ (hmem t ht)) (hasDerivAt_chordC P Q (t : ℂ))
  have hcont : ContinuousOn (fun t => (Q - P) * f (chord P Q t)) (uIcc (0:ℝ) 1) :=
    continuousOn_const.mul (hf.comp (continuous_chord P Q).continuousOn (fun t ht => hmem t ht))
  simpa [chordIntegral, chord, chordC] using
    integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-! ### The loop vanishes -/

/-- ORACLE: CPathFTC.v : pathint_primitive_loop (specialised to the truncated contour).
    If `f` has a primitive `F` at every point of the contour, the loop integral is zero. -/
theorem truncContour_eq_zero_of_primitive {f F : ℂ → ℂ} {R α : ℝ}
    (hF : ∀ z ∈ contourSet R α, HasDerivAt F (f z) z)
    (hf : ContinuousOn f (contourSet R α)) :
    truncContour f R α = 0 := by
  have harc : arcSet R α ⊆ contourSet R α := subset_union_left
  have hch : chordSet (arcTop R α) (arcBot R α) ⊆ contourSet R α := subset_union_right
  rw [truncContour,
    arcIntegral_eq_sub (fun z hz => hF z (harc hz)) (hf.mono harc),
    chordIntegral_eq_sub (fun z hz => hF z (hch hz)) (hf.mono hch)]
  ring

/-- Non-vacuity: the contour set is nonempty. -/
theorem contourSet_nonempty (R α : ℝ) : (contourSet R α).Nonempty :=
  ⟨circleMap 0 R (-α), Or.inl ⟨-α, left_mem_uIcc, rfl⟩⟩

end TDLean.Newman
