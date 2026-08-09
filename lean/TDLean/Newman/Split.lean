/-
  TDLean.Newman.Split -- Brick C8, part 3: splitting the contour at `Re z = 0`.

  NO COQ ORACLE (brick 8 is open on the Coq side).

  Newman's argument needs different bounds on the two halves of the contour, so the
  contour has to be cut at `θ = ±π/2`, where `Re z = R cos θ` changes sign:

      C(α) = rightSemi ∪ leftPart(α),
      rightSemi   = arc over [−π/2, π/2]   (Re z ≥ 0)
      leftPart(α) = arc over [−α, −π/2] and [π/2, α], plus the chord   (Re z ≤ 0)

  The payoff is the **deformation for free** (`leftPart_eq_leftSemi` below). At `α = π`
  the chord degenerates -- `arcTop R π = arcBot R π = −R` -- so `C(π)` *is* the full
  circle. Applying C6 at `α` and at `π` gives the same value `2πi F(0)`, and the two
  right halves are literally the same integral, so the two left parts are equal.

  That is exactly Zagier's "deform the left part to the left semicircle" step, obtained
  without building a second contour or a second Cauchy theorem.
-/
import TDLean.Newman.Contour
import TDLean.Newman.Winding
import TDLean.Newman.StarPrimitive

namespace TDLean.Newman

open Complex Set intervalIntegral Real
open scoped Interval

/-! ### Arc integrals over a general angle range -/

/-- The arc integral over an arbitrary range of angles. -/
noncomputable def arcIntegralOn (f : ℂ → ℂ) (R a b : ℝ) : ℂ :=
  ∫ θ in a..b, deriv (circleMap 0 R) θ * f (circleMap 0 R θ)

/-- The points traced by that arc. -/
def arcSetOn (R a b : ℝ) : Set ℂ := circleMap 0 R '' uIcc a b

theorem arcIntegral_eq_on (f : ℂ → ℂ) (R α : ℝ) :
    arcIntegral f R α = arcIntegralOn f R (-α) α := rfl

theorem arcSet_eq_on (R α : ℝ) : arcSet R α = arcSetOn R (-α) α := rfl

theorem arcSetOn_mem {R a b θ : ℝ} (hθ : θ ∈ uIcc a b) : circleMap 0 R θ ∈ arcSetOn R a b :=
  ⟨θ, hθ, rfl⟩

theorem arcSetOn_mono {R a b c d : ℝ} (h : uIcc a b ⊆ uIcc c d) :
    arcSetOn R a b ⊆ arcSetOn R c d := Set.image_mono h

theorem arcIntegrandOn_continuousOn {f : ℂ → ℂ} {R a b : ℝ}
    (hf : ContinuousOn f (arcSetOn R a b)) :
    ContinuousOn (fun θ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ)) (uIcc a b) := by
  have hderivEq : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * I :=
    funext fun θ => deriv_circleMap 0 R θ
  have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap 0 R) θ) (uIcc a b) := by
    rw [hderivEq]; exact ((continuous_arc R).continuousOn).mul continuousOn_const
  exact h1.mul (hf.comp (continuous_arc R).continuousOn fun θ hθ => arcSetOn_mem hθ)

theorem arcIntegrableOn {f : ℂ → ℂ} {R a b : ℝ} (hf : ContinuousOn f (arcSetOn R a b)) :
    IntervalIntegrable (fun θ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ))
      MeasureTheory.volume a b :=
  (arcIntegrandOn_continuousOn hf).intervalIntegrable

/-- Adjacent arc ranges add. -/
theorem arcIntegralOn_add {f : ℂ → ℂ} {R a b c : ℝ}
    (hab : ContinuousOn f (arcSetOn R a b)) (hbc : ContinuousOn f (arcSetOn R b c)) :
    arcIntegralOn f R a b + arcIntegralOn f R b c = arcIntegralOn f R a c :=
  intervalIntegral.integral_add_adjacent_intervals (arcIntegrableOn hab) (arcIntegrableOn hbc)

/-! ### An ML bound that tolerates the endpoints

    On the right semicircle the endpoints `θ = ±π/2` have `Re z = 0`, where Newman's
    pointwise bound legitimately fails (it carries a `1/Re z`). Those are two points, so
    they cannot affect the integral -- but `norm_integral_le_of_norm_le_const` wants the
    bound on all of `Ι a b = Ioc _ _`, which contains one of them. Hence this a.e. version,
    which only asks for the bound on the open interval. -/

theorem norm_arcIntegralOn_le_of_ae {f : ℂ → ℂ} {R a b C : ℝ}
    (h : ∀ θ ∈ Ioo (min a b) (max a b), ‖f (circleMap 0 R θ)‖ ≤ C) :
    ‖arcIntegralOn f R a b‖ ≤ |R| * C * |b - a| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
  have hmax : ∀ᵐ θ : ℝ, θ ≠ max a b := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hmax] with θ hθ hmem
  have h1 : θ ∈ Ioc (min a b) (max a b) := hmem
  have hIoo : θ ∈ Ioo (min a b) (max a b) := ⟨h1.1, lt_of_le_of_ne h1.2 hθ⟩
  rw [norm_mul, norm_deriv_circleMap]
  exact mul_le_mul_of_nonneg_left (h θ hIoo) (abs_nonneg R)

/-! ### The split at `Re z = 0` -/

/-- The right semicircle: `θ ∈ [−π/2, π/2]`, where `Re z ≥ 0`. -/
noncomputable def rightSemi (f : ℂ → ℂ) (R : ℝ) : ℂ := arcIntegralOn f R (-(π / 2)) (π / 2)

/-- Everything else in `C(α)`: the two outer arc pieces and the chord, where `Re z ≤ 0`. -/
noncomputable def leftPart (f : ℂ → ℂ) (R α : ℝ) : ℂ :=
  arcIntegralOn f R (-α) (-(π / 2)) + arcIntegralOn f R (π / 2) α
    + chordIntegral f (arcTop R α) (arcBot R α)

/-- Angle ranges of the three arc pieces sit inside the full range. -/
theorem uIcc_pieces_subset {α : ℝ} (hα : π / 2 ≤ α) :
    uIcc (-α) (-(π / 2)) ⊆ uIcc (-α) α ∧ uIcc (-(π / 2)) (π / 2) ⊆ uIcc (-α) α ∧
      uIcc (π / 2) α ⊆ uIcc (-α) α := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 : -α ≤ α := by linarith
  rw [uIcc_of_le h1]
  refine ⟨?_, ?_, ?_⟩
  · rw [uIcc_of_le (by linarith : -α ≤ -(π / 2))]
    exact Icc_subset_Icc le_rfl (by linarith)
  · rw [uIcc_of_le (by linarith : -(π / 2) ≤ π / 2)]
    exact Icc_subset_Icc (by linarith) (by linarith)
  · rw [uIcc_of_le hα]
    exact Icc_subset_Icc (by linarith) le_rfl

/-- **The contour splits at `Re z = 0`.** -/
theorem truncContour_split {f : ℂ → ℂ} {R α : ℝ} (hα : π / 2 ≤ α)
    (hf : ContinuousOn f (contourSet R α)) :
    truncContour f R α = rightSemi f R + leftPart f R α := by
  obtain ⟨s1, s2, s3⟩ := uIcc_pieces_subset hα
  have harcS : arcSet R α ⊆ contourSet R α := subset_union_left
  have hA : ∀ {a b : ℝ}, uIcc a b ⊆ uIcc (-α) α → ContinuousOn f (arcSetOn R a b) :=
    fun h => (hf.mono harcS).mono (arcSetOn_mono h)
  have e1 : arcIntegralOn f R (-α) (-(π / 2)) + arcIntegralOn f R (-(π / 2)) (π / 2)
      = arcIntegralOn f R (-α) (π / 2) := arcIntegralOn_add (hA s1) (hA s2)
  have e2 : arcIntegralOn f R (-α) (π / 2) + arcIntegralOn f R (π / 2) α
      = arcIntegralOn f R (-α) α := by
    refine arcIntegralOn_add (hA ?_) (hA s3)
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -α ≤ π / 2),
      uIcc_of_le (by linarith [Real.pi_pos] : -α ≤ α)]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  unfold truncContour rightSemi leftPart
  rw [arcIntegral_eq_on, ← e2, ← e1]
  ring

/-! ### The chord degenerates at `α = π`, so `C(π)` is the full circle -/

theorem arcTop_pi (R : ℝ) : arcTop R π = -(R : ℂ) := by
  simp [arcTop, circleMap, Complex.exp_pi_mul_I]

theorem arcBot_pi (R : ℝ) : arcBot R π = -(R : ℂ) := by
  simp [arcBot, circleMap, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]

/-- With coincident endpoints the chord contributes nothing. -/
theorem chordIntegral_self (f : ℂ → ℂ) (P : ℂ) : chordIntegral f P P = 0 := by
  simp [chordIntegral]

/-- At `α = π` the left part is exactly the left semicircle: the chord vanishes. -/
theorem leftPart_pi (f : ℂ → ℂ) (R : ℝ) :
    leftPart f R π = arcIntegralOn f R (-π) (-(π / 2)) + arcIntegralOn f R (π / 2) π := by
  rw [leftPart, arcTop_pi, arcBot_pi, chordIntegral_self, add_zero]

/-- **The deformation, for free.** If a function has the same contour integral at `α` and at
    `π` -- which C6 guarantees for `F · K_R` with `F` holomorphic, since both equal
    `2πi F(0)` -- then its left parts agree. The shared right semicircle cancels.

    This is Zagier's "deform the left part to the left semicircle" step, with no second
    contour and no second Cauchy theorem. -/
theorem leftPart_eq_of_truncContour_eq {f : ℂ → ℂ} {R α : ℝ} (hα : π / 2 ≤ α)
    (hfα : ContinuousOn f (contourSet R α)) (hfπ : ContinuousOn f (contourSet R π))
    (h : truncContour f R α = truncContour f R π) :
    leftPart f R α = leftPart f R π := by
  have hππ : π / 2 ≤ π := by linarith [Real.pi_pos]
  rw [truncContour_split hα hfα, truncContour_split hππ hfπ] at h
  exact add_left_cancel h

/-! ### Geometry of the contour -/

/-- A point of the chord is a convex combination of its endpoints, so its norm is bounded
    by theirs. -/
theorem norm_chord_le {P Q : ℂ} {M : ℝ} (hP : ‖P‖ ≤ M) (hQ : ‖Q‖ ≤ M) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖chord P Q t‖ ≤ M := by
  have hrw : chord P Q t = (1 - (t : ℂ)) * P + (t : ℂ) * Q := by unfold chord chordC; ring
  have h1 : ‖(1 - (t : ℂ))‖ = 1 - t := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have h2 : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [hrw]
  calc ‖(1 - (t : ℂ)) * P + (t : ℂ) * Q‖
      ≤ ‖(1 - (t : ℂ)) * P‖ + ‖(t : ℂ) * Q‖ := norm_add_le _ _
    _ = (1 - t) * ‖P‖ + t * ‖Q‖ := by rw [norm_mul, norm_mul, h1, h2]
    _ ≤ (1 - t) * M + t * M := by
        gcongr
        · linarith [ht.2]
        · exact ht.1
    _ = M := by ring

/-- Every point of the contour has norm `≤ R`. -/
theorem norm_le_of_mem_contourSet {R α : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ contourSet R α) :
    ‖z‖ ≤ R := by
  rcases hz with ⟨θ, -, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [norm_circleMap_zero, abs_of_pos hR]
  · refine norm_chord_le ?_ ?_ (by rwa [uIcc_of_le zero_le_one] at ht)
    · rw [arcTop, norm_circleMap_zero, abs_of_pos hR]
    · rw [arcBot, norm_circleMap_zero, abs_of_pos hR]

/-- The contour sits inside any strictly larger ball. -/
theorem contourSet_subset_ball {R R' α : ℝ} (hR : 0 < R) (hRR : R < R') :
    contourSet R α ⊆ Metric.ball 0 R' := fun _ hz =>
  mem_ball_zero_iff.mpr (lt_of_le_of_lt (norm_le_of_mem_contourSet hR hz) hRR)

/-- A ball centred at the origin is star-shaped about `0`. -/
theorem starAboutZero_ball {R' : ℝ} : StarAboutZero (Metric.ball (0 : ℂ) R') := by
  intro z hz t ht
  rw [mem_ball_zero_iff] at hz ⊢
  calc ‖(t : ℂ) * z‖ = t * ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ 1 * ‖z‖ := by
        apply mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
    _ = ‖z‖ := one_mul _
    _ < R' := hz

/-- The contour avoids the origin: the arc has norm `R > 0`, and the chord sits on the
    line `Re z = R cos α < 0`. -/
theorem zero_not_mem_contourSet {R α : ℝ} (hR : 0 < R) (hα : π / 2 < α) (hα2 : α ≤ π) :
    (0 : ℂ) ∉ contourSet R α := by
  have hcos : Real.cos α < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hα (by linarith [Real.pi_pos])
  rintro (⟨θ, -, hθ⟩ | ⟨t, -, ht⟩)
  · have : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [hθ] at this; simp at this; linarith
  · have hre := chord_re_eq (R := R) (α := α) t
    rw [ht] at hre
    simp only [Complex.zero_re] at hre
    nlinarith

end TDLean.Newman
