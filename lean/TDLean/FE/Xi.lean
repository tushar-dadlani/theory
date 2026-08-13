/-
  TDLean.FE.Xi -- cluster A19: Riemann's `ξ`, entire.

      ξ(s) := s(s−1)/2 · Λ(s)

  `Λ` has simple poles at `0` and `1`; multiplying by `s(s−1)` clears both. As in
  `Transfer.lean`, the way to make that *visible* to Lean is to cancel symbolically rather
  than analytically — expanding `Λ = 1/(s−1) − 1/s + M(s/2−1) + M((1−s)/2−1)` and multiplying
  through gives

      ξ(s) = 1/2 + s(s−1)/2 · (M(s/2−1) + M((1−s)/2−1))

  in which no pole appears at all. Since `M` is entire (A14), `ξ` is entire outright — no
  removable-singularity argument, no excluded points.

  This also settles the `{0,1}` exclusions carried since A16. `ξ(0) = ξ(1) = 1/2 ≠ 0`, so
  clearing the poles introduces no new zeros: **the zeros of `ξ` are exactly the zeros of `Λ`**,
  hence exactly the nontrivial zeros of `ζ`, and they all lie in the closed critical strip.

  `ξ` is the object both remaining routes to *existence* of nontrivial zeros need — Hadamard
  factorisation directly, and any contour/counting argument via its entirety. Nothing here
  exhibits a zero.
-/
import TDLean.FE.CriticalValue

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-- **Riemann's `ξ`**, written with the poles symbolically cancelled. -/
noncomputable def xi (s : ℂ) : ℂ :=
  1 / 2 + s * (s - 1) / 2 * (mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1))

/-- **`ξ` is entire.** -/
theorem differentiable_xi : Differentiable ℂ xi := by
  intro s
  refine DifferentiableAt.add (differentiableAt_const _) (DifferentiableAt.mul ?_ ?_)
  · exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2)
  · refine DifferentiableAt.add ?_ ?_
    · have h : DifferentiableAt ℂ (mellinTail ∘ fun z : ℂ => z / 2 - 1) s :=
        DifferentiableAt.comp s (differentiable_mellinTail _)
          ((differentiableAt_id.div_const 2).sub_const 1)
      exact h
    · have h : DifferentiableAt ℂ (mellinTail ∘ fun z : ℂ => (1 - z) / 2 - 1) s :=
        DifferentiableAt.comp s (differentiable_mellinTail _)
          ((((differentiableAt_const 1).sub differentiableAt_id).div_const 2).sub_const 1)
      exact h

/-- Off `{0,1}`, `ξ` really is `s(s−1)/2 · Λ(s)`. -/
theorem xi_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedZeta s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  set M : ℂ := mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1) with hM
  rw [completedZeta_eq_mellinTail, xi, ← hM]
  field_simp
  ring

/-- **`ξ(1−s) = ξ(s)`,** unconditionally — the functional equation in its cleanest form.
    `(1−s)((1−s)−1) = s(s−1)` and the two tail terms simply exchange. -/
theorem xi_symm (s : ℂ) : xi (1 - s) = xi s := by
  rw [xi, xi, show (1 : ℂ) - (1 - s) = s by ring]
  ring

/-! ### Clearing the poles introduces no zeros -/

@[simp] theorem xi_zero : xi 0 = 1 / 2 := by rw [xi]; ring

@[simp] theorem xi_one : xi 1 = 1 / 2 := by rw [xi]; ring

/-- **The zeros of `ξ` are exactly the zeros of `Λ`.** -/
theorem xi_eq_zero_iff {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = 0 ↔ completedZeta s = 0 := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [xi_eq h0 h1]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases div_eq_zero_iff.mp h' with h2 | h2
      · rcases mul_eq_zero.mp h2 with h'' | h''
        · exact absurd h'' h0
        · exact absurd h'' hs1
      · norm_num at h2
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- **Every zero of `ξ` lies in the closed critical strip.** -/
theorem xi_zeros_in_strip {s : ℂ} (h : xi s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  have h0 : s ≠ 0 := by
    intro hc
    rw [hc, xi_zero] at h
    norm_num at h
  have h1 : s ≠ 1 := by
    intro hc
    rw [hc, xi_one] at h
    norm_num at h
  exact completedZeta_zeros_in_strip ((xi_eq_zero_iff h0 h1).mp h)

/-! ### `ξ` on the critical line -/

/-- On the critical line, `conj s = 1 − s`. -/
theorem conj_eq_one_sub_of_re_half {s : ℂ} (hs : s.re = 1 / 2) : (starRingEnd ℂ) s = 1 - s := by
  have h := (TDLean.Zeta.refl_fixed_iff s).mpr hs
  rw [TDLean.Zeta.refl] at h
  linear_combination -h

theorem ne_zero_of_re_half {s : ℂ} (hs : s.re = 1 / 2) : s ≠ 0 := by
  intro hc
  rw [hc] at hs
  norm_num at hs

theorem ne_one_of_re_half {s : ℂ} (hs : s.re = 1 / 2) : s ≠ 1 := by
  intro hc
  rw [hc] at hs
  norm_num at hs

/-- **`ξ` is real on the critical line.** The prefactor `s(s−1)/2` is real there too:
    `conj(s(s−1)) = (1−s)(−s) = s(s−1)`. -/
theorem xi_conj_eq_self {s : ℂ} (hs : s.re = 1 / 2) : (starRingEnd ℂ) (xi s) = xi s := by
  have hconj := conj_eq_one_sub_of_re_half hs
  have hpre : (starRingEnd ℂ) (s * (s - 1) / 2) = s * (s - 1) / 2 := by
    rw [map_div₀, map_mul, map_sub, map_one, hconj]
    simp only [map_ofNat]
    ring
  rw [xi_eq (ne_zero_of_re_half hs) (ne_one_of_re_half hs), map_mul, hpre,
    completedZeta_conj_eq_self hs]

theorem xi_im_eq_zero {s : ℂ} (hs : s.re = 1 / 2) : (xi s).im = 0 := by
  have h := xi_conj_eq_self hs
  rw [Complex.ext_iff] at h
  have h2 := h.2
  simp only [Complex.conj_im] at h2
  linarith

/-- **`ξ(1/2) > 0`.** Since `ξ(1/2) = −Λ(1/2)/8` and `Λ(1/2) < 0`. Together with
    `xi_im_eq_zero` this pins a genuine positive real value at the centre of the line —
    the opposite sign to `Λ(1/2)`, because the prefactor `s(s−1)/2` is negative there. -/
theorem xi_half_re_pos : 0 < (xi (1 / 2 : ℂ)).re := by
  have h0 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have h1 : (1 / 2 : ℂ) ≠ 1 := by norm_num
  have hpre : (1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) / 2 = -(1 / 8) := by norm_num
  rw [xi_eq h0 h1, hpre]
  have : ((-(1 / 8) : ℂ) * completedZeta (1 / 2 : ℂ)).re
      = -(1 / 8) * (completedZeta (1 / 2 : ℂ)).re := by
    simp [Complex.mul_re]
  rw [this]
  linarith [completedZeta_half_re_lt_zero]

end TDLean.FE
