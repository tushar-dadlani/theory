/-
  TDLean.PNT.Region -- C10, part 8: Newman's `hregion` for `g`.

  For each `R > 0` we must exhibit `α ∈ (π/2, π]` and an open star-shaped `U ∋ 0` containing
  the truncated contour, on which `g` is holomorphic. The contour reaches leftmost at
  `Re = R·cos α`, so `α` has to be chosen as a function of `R` and of how far past the
  imaginary axis `g` actually continues -- which is exactly what compactness supplies.

  The δ comes from `IsCompact.exists_cthickening_subset_open` applied to
  `K = {Re z ≥ 0} ∩ closedBall 0 (R+1)`, compact and inside the open `gRegion`.
-/
import TDLean.PNT.GNewman
import TDLean.Newman.Contour
import TDLean.Newman.StarPrimitive

namespace TDLean.PNT

open TDLean.Zeta TDLean.Newman Set Metric

/-! ### Where `g` is holomorphic -/

/-- `g` is holomorphic exactly where `Φ⁻` is, shifted by one. -/
def gRegion : Set ℂ := {z : ℂ | z + 1 ∈ phiRegion}

theorem isOpen_gRegion : IsOpen gRegion :=
  isOpen_phiRegion.preimage (by fun_prop)

theorem mem_gRegion_ne_zero {z : ℂ} (hz : z ∈ gRegion) : z + 1 ≠ 0 := by
  intro h
  have := hz.1
  rw [h] at this
  simp at this

theorem differentiableOn_gNewman : DifferentiableOn ℂ gNewman gRegion := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hinner : DifferentiableAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
  have hcomp : DifferentiableAt ℂ (fun w : ℂ => PhiMinus (w + 1)) z := by
    have hc := (differentiableAt_PhiMinus hz).comp z hinner
    simpa [Function.comp_def] using hc
  exact (hcomp.sub_const 1).div hinner (mem_gRegion_ne_zero hz)

theorem rightHalfplane_subset_gRegion : {z : ℂ | 0 ≤ z.re} ⊆ gRegion := by
  intro z hz
  refine halfplane_subset_phiRegion ?_
  simp only [Set.mem_setOf_eq, Complex.add_re, Complex.one_re]
  linarith [Set.mem_setOf_eq ▸ hz]

/-! ### The compact core and its thickening -/

theorem isCompact_core (R : ℝ) :
    IsCompact ({z : ℂ | 0 ≤ z.re} ∩ closedBall 0 (R + 1)) :=
  (isCompact_closedBall 0 (R + 1)).inter_left
    (isClosed_le continuous_const Complex.continuous_re)

/-- A point just left of the imaginary axis is within `|Re z|` of the core. -/
theorem mem_cthickening_core {R δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hre : -δ < z.re) (hball : ‖z‖ < R + 1) :
    z ∈ cthickening δ ({z : ℂ | 0 ≤ z.re} ∩ closedBall 0 (R + 1)) := by
  by_cases h : 0 ≤ z.re
  · refine mem_cthickening_of_dist_le z z δ _ ⟨h, ?_⟩ (by simpa using hδ.le)
    exact mem_closedBall_zero_iff.mpr hball.le
  · -- project onto the imaginary axis
    push_neg at h
    set w : ℂ := z - (z.re : ℂ) with hw
    have hwre : w.re = 0 := by simp [hw]
    have hwim : w.im = z.im := by simp [hw]
    have hwnorm : ‖w‖ ≤ ‖z‖ := by
      have : w = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hw, hwim]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact Complex.abs_im_le_norm z
    have hwmem : w ∈ ({z : ℂ | 0 ≤ z.re} ∩ closedBall 0 (R + 1)) :=
      ⟨by simp [hwre], mem_closedBall_zero_iff.mpr (le_trans hwnorm hball.le)⟩
    refine mem_cthickening_of_dist_le z w δ _ hwmem ?_
    rw [dist_eq_norm, hw]
    simp only [sub_sub_cancel]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg h]
    linarith

/-! ### Geometry of the contour -/

theorem norm_arcTop {R α : ℝ} (hR : 0 < R) : ‖arcTop R α‖ = R := by
  simp [arcTop, abs_of_pos hR]

theorem norm_arcBot {R α : ℝ} (hR : 0 < R) : ‖arcBot R α‖ = R := by
  simp [arcBot, abs_of_pos hR]

theorem re_arcTop (R α : ℝ) : (arcTop R α).re = R * Real.cos α := by
  rw [arcTop, circleMap]
  simp only [zero_add, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem re_arcBot (R α : ℝ) : (arcBot R α).re = R * Real.cos α := by
  rw [arcBot, circleMap]
  simp only [zero_add, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem chord_eq_combo (P Q : ℂ) (t : ℝ) :
    chord P Q t = (1 - (t : ℂ)) * P + (t : ℂ) * Q := by
  simp only [chord, chordC]; ring

theorem contourSet_subset {R α : ℝ} (hR : 0 < R) (hα0 : 0 ≤ α) (hα : α ≤ Real.pi) :
    contourSet R α ⊆ {z : ℂ | R * Real.cos α ≤ z.re} ∩ closedBall 0 R := by
  rintro z (⟨θ, hθ, rfl⟩ | ⟨t, ht, rfl⟩)
  · rw [Set.uIcc_of_le (by linarith : -α ≤ α)] at hθ
    have habs : |θ| ≤ α := abs_le.mpr ⟨hθ.1, hθ.2⟩
    have hcos : Real.cos α ≤ Real.cos θ := by
      rw [← Real.cos_abs θ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hα habs
    refine ⟨?_, ?_⟩
    · change R * Real.cos α ≤ (circleMap 0 R θ).re
      rw [circleMap]
      simp only [zero_add, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      exact mul_le_mul_of_nonneg_left hcos hR.le
    · simp [mem_closedBall_zero_iff, abs_of_pos hR]
  · rw [Set.uIcc_of_le zero_le_one] at ht
    rw [chord_eq_combo]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Complex.add_re, Complex.re_ofReal_mul, re_arcBot,
        Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [show ((1 : ℂ) - (t : ℂ)) * arcTop R α
          = ((1 - t : ℝ) : ℂ) * arcTop R α by push_cast; ring]
      rw [Complex.re_ofReal_mul, re_arcTop]
      nlinarith [ht.1, ht.2]
    · rw [mem_closedBall_zero_iff]
      have h1 : ‖((1 : ℂ) - (t : ℂ)) * arcTop R α‖ = (1 - t) * R := by
        rw [show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2]),
          norm_arcTop hR]
      have h2 : ‖(t : ℂ) * arcBot R α‖ = t * R := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1, norm_arcBot hR]
      calc ‖((1 : ℂ) - (t : ℂ)) * arcTop R α + (t : ℂ) * arcBot R α‖
          ≤ ‖((1 : ℂ) - (t : ℂ)) * arcTop R α‖ + ‖(t : ℂ) * arcBot R α‖ := norm_add_le _ _
        _ = (1 - t) * R + t * R := by rw [h1, h2]
        _ = R := by ring

/-! ### `hregion`, Newman's last hypothesis -/

/-- **Newman's region hypothesis for `g`.** For every `R > 0` there is an admissible `α` and an
    open star-shaped `U ∋ 0` containing the truncated contour on which `g` is holomorphic.
    `α` must depend on `R`: the contour reaches leftmost at `Re = R·cos α`, and how far past
    the imaginary axis `g` continues is only known by compactness. -/
theorem hregion_gNewman {R : ℝ} (hR : 0 < R) :
    ∃ α U, Real.pi / 2 < α ∧ α ≤ Real.pi ∧ IsOpen U ∧ StarAboutZero U ∧
      (0 : ℂ) ∈ U ∧ contourSet R α ⊆ U ∧ DifferentiableOn ℂ gNewman U := by
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_core R).exists_cthickening_subset_open isOpen_gRegion
    (fun z hz => rightHalfplane_subset_gRegion hz.1)
  set δ' : ℝ := min δ R with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ hR
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'R : δ' ≤ R := min_le_right _ _
  set c : ℝ := -(δ' / (2 * R)) with hcdef
  have hc0 : c < 0 := by rw [hcdef]; simp only [neg_neg, neg_lt_zero]; positivity
  have hcge : (-1 : ℝ) ≤ c := by
    rw [hcdef]
    have : δ' / (2 * R) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) two_pos]; linarith
    linarith
  have hcle : c ≤ 1 := by linarith
  set α : ℝ := Real.arccos c with hαdef
  have hcos : Real.cos α = c := Real.cos_arccos hcge hcle
  have hαpi : α ≤ Real.pi := Real.arccos_le_pi c
  have hα0 : 0 ≤ α := Real.arccos_nonneg c
  have hαhalf : Real.pi / 2 < α := by
    by_contra hcon
    push_neg at hcon
    have hnn : 0 ≤ Real.cos α :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hcon⟩
    rw [hcos] at hnn; linarith
  refine ⟨α, {z : ℂ | -δ' < z.re} ∩ ball 0 (R + 1), hαhalf, hαpi, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball
  · -- star-shaped about `0`
    rintro z ⟨hzre, hzball⟩ t ht
    rw [mem_ball_zero_iff] at hzball
    refine ⟨?_, ?_⟩
    · have hre : ((t : ℂ) * z).re = t * z.re := Complex.re_ofReal_mul t z
      rw [Set.mem_setOf_eq, hre]
      rcases le_or_gt 0 z.re with h | h
      · nlinarith [ht.1]
      · nlinarith [ht.2, Set.mem_setOf_eq ▸ hzre]
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      nlinarith [ht.2, norm_nonneg z]
  · exact ⟨by simpa using hδ'0, by simp; linarith⟩
  · -- the contour lies in `U`
    intro z hz
    obtain ⟨hzre, hzball⟩ := contourSet_subset hR hα0 hαpi hz
    rw [mem_closedBall_zero_iff] at hzball
    refine ⟨?_, mem_ball_zero_iff.mpr (by linarith)⟩
    rw [Set.mem_setOf_eq]
    have hRc : R * c = -(δ' / 2) := by
      rw [hcdef]; field_simp
    have : R * Real.cos α = -(δ' / 2) := by rw [hcos, hRc]
    rw [Set.mem_setOf_eq, this] at hzre
    linarith
  · -- `U ⊆ gRegion`, by the thickening
    refine differentiableOn_gNewman.mono ?_
    rintro z ⟨hzre, hzball⟩
    rw [mem_ball_zero_iff] at hzball
    refine hthick ?_
    exact cthickening_mono hδ'δ _ (mem_cthickening_core hδ'0 hzre hzball)

end TDLean.PNT

