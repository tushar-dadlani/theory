/-
  TDLean.FE.Transfer -- cluster A15 (step 2): pushing the identity into the strip.

      Λ(s) = π^{−s/2}·Γ(s/2)·ζ(s)      for  Re s > 0,  s ≠ 1

  `completedZeta_eq` gives this only on `Re s > 1`. The identity theorem extends it to the
  whole half-plane, which is what makes everything cluster A proved about `Λ` into a statement
  about `ζ`.

  **Clearing the poles first.** Both sides have a simple pole at `s = 1`, so neither is
  holomorphic on `{Re s > 0}` as it stands. Rather than work on a punctured region (and have
  to prove it preconnected), multiply through by `s − 1` and write the products in a form
  where the pole is *visibly* gone:

      L(s) := (1 − (s−1)/s + (s−1)·(M(s/2−1) + M((1−s)/2−1))) · π^{s/2}
      R(s) := Γ(s/2) · (1 + (s−1)·ζ_diff(s))

  `L` is `(s−1)·Λ(s)·π^{s/2}` and `R` is `Γ(s/2)·(s−1)·ζ(s)` wherever `s ≠ 1`, but both are
  manifestly holomorphic on all of `{Re s > 0}` — the `1/(s−1)` terms have been cancelled
  symbolically, not analytically. So the identity theorem applies on a convex region.

  This is the second use of `Zeta/Identity.lean`'s `eqOn_halfplane_of_eqOn_subhalfplane`,
  built for exactly this cluster.
-/
import TDLean.FE.Holo
import TDLean.Zeta.Identity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-- `(s−1)·Λ(s)·π^{s/2}`, written so the pole at `1` is symbolically cancelled. -/
noncomputable def poleFreeL (s : ℂ) : ℂ :=
  (1 - (s - 1) / s + (s - 1) * (mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1)))
    * ((π : ℝ) : ℂ) ^ (s / 2)

/-- `Γ(s/2)·(s−1)·ζ(s)`, likewise. -/
noncomputable def poleFreeR (s : ℂ) : ℂ :=
  Complex.Gamma (s / 2) * (1 + (s - 1) * zetaDiffSum s)

theorem poleFreeL_eq {s : ℂ} (h1 : s ≠ 1) :
    poleFreeL s = (s - 1) * completedZeta s * ((π : ℝ) : ℂ) ^ (s / 2) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hcancel : (s - 1) * (1 / (s - 1) - 1 / s
        + (mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1)))
      = 1 - (s - 1) / s
        + (s - 1) * (mellinTail (s / 2 - 1) + mellinTail ((1 - s) / 2 - 1)) := by
    rw [mul_add, mul_sub, mul_one_div, div_self hs1, mul_one_div]
  rw [poleFreeL, completedZeta_eq_mellinTail, ← hcancel]

theorem poleFreeR_eq {s : ℂ} (h1 : s ≠ 1) :
    poleFreeR s = Complex.Gamma (s / 2) * ((s - 1) * zetaCont s) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hc : (s - 1) * zetaCont s = 1 + (s - 1) * zetaDiffSum s := by
    rw [zetaCont, mul_add, mul_one_div, div_self hs1]
  rw [poleFreeR, hc]

/-! ### Both are holomorphic on `Re s > 0` -/

theorem differentiableOn_poleFreeL : DifferentiableOn ℂ poleFreeL {s : ℂ | 0 < s.re} := by
  intro s hs
  have hspos : 0 < s.re := hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hspos
    simp at hspos
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
  · refine DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_const 1) ?_) ?_
    · exact (differentiableAt_id.sub_const 1).div differentiableAt_id hs0
    · refine (differentiableAt_id.sub_const 1).mul (DifferentiableAt.add ?_ ?_)
      · have h : DifferentiableAt ℂ (mellinTail ∘ fun z : ℂ => z / 2 - 1) s :=
          DifferentiableAt.comp s (differentiable_mellinTail _)
            ((differentiableAt_id.div_const 2).sub_const 1)
        exact h
      · have h : DifferentiableAt ℂ (mellinTail ∘ fun z : ℂ => (1 - z) / 2 - 1) s :=
          DifferentiableAt.comp s (differentiable_mellinTail _)
            ((((differentiableAt_const 1).sub differentiableAt_id).div_const 2).sub_const 1)
        exact h
  · exact (differentiableAt_id.div_const 2).const_cpow (Or.inl hπ)

theorem differentiableOn_poleFreeR : DifferentiableOn ℂ poleFreeR {s : ℂ | 0 < s.re} := by
  intro s hs
  have hspos : 0 < s.re := hs
  refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
  · have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hcon
      have hre : (s / 2).re = (-(m : ℂ)).re := by rw [hcon]
      rw [Complex.div_ofNat_re] at hre
      simp at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h : DifferentiableAt ℂ (Complex.Gamma ∘ fun z : ℂ => z / 2) s :=
      DifferentiableAt.comp s (Complex.differentiableAt_Gamma _ hne)
        (differentiableAt_id.div_const 2)
    exact h
  · exact (differentiableAt_const 1).add
      ((differentiableAt_id.sub_const 1).mul (differentiableAt_zetaDiffSum hspos))

/-! ### They agree past `Re s = 1`, hence everywhere on `Re s > 0` -/

theorem pi_cpow_neg_mul_self (s : ℂ) :
    ((π : ℝ) : ℂ) ^ (-s / 2) * ((π : ℝ) : ℂ) ^ (s / 2) = 1 := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← Complex.cpow_add _ _ hπ, show (-s / 2 + s / 2 : ℂ) = 0 by ring, Complex.cpow_zero]

theorem eqOn_poleFree_gt_one : EqOn poleFreeL poleFreeR {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs1' : 1 < s.re := hs
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hs1'
    simp at hs1'
  rw [poleFreeL_eq hne1, poleFreeR_eq hne1, completedZeta_eq hs1', zetaCont_eq_zetaSeries hs1']
  linear_combination (Complex.Gamma (s / 2) * ((s - 1) * zetaSeries s)) * pi_cpow_neg_mul_self s

theorem eqOn_poleFree : EqOn poleFreeL poleFreeR {s : ℂ | 0 < s.re} :=
  eqOn_halfplane_of_eqOn_subhalfplane (by norm_num) differentiableOn_poleFreeL
    differentiableOn_poleFreeR eqOn_poleFree_gt_one

/-- **The identity, extended into the strip.** `Λ(s) = π^{−s/2}·Γ(s/2)·ζ(s)` for every `s`
    with `Re s > 0` and `s ≠ 1` — not just `Re s > 1`. -/
theorem completedZeta_eq_zetaCont {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    completedZeta s = ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaCont s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpiL : ((π : ℝ) : ℂ) ^ (s / 2) ≠ 0 := pi_cpow_ne_zero _
  have h := eqOn_poleFree hs
  rw [poleFreeL_eq h1, poleFreeR_eq h1] at h
  refine mul_left_cancel₀ hs1 (mul_right_cancel₀ hpiL ?_)
  calc (s - 1) * completedZeta s * ((π : ℝ) : ℂ) ^ (s / 2)
      = Complex.Gamma (s / 2) * ((s - 1) * zetaCont s) := h
    _ = (s - 1) * (((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaCont s)
          * ((π : ℝ) : ℂ) ^ (s / 2) := by
        linear_combination (-(Complex.Gamma (s / 2) * ((s - 1) * zetaCont s)))
          * pi_cpow_neg_mul_self s

/-! ### The payoff: cluster A now speaks about `ζ` -/

/-- **The zeros of `Λ` and of `ζ` coincide on `Re s > 0`, `s ≠ 1`.** -/
theorem completedZeta_eq_zero_iff {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    completedZeta s = 0 ↔ zetaCont s = 0 := by
  rw [completedZeta_eq_zetaCont hs h1]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' (pi_cpow_ne_zero _)
      · exact absurd h'' (gamma_half_ne_zero hs)
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- **Reflection in the critical line, for `ζ` itself.** If `ζ(s) = 0` in the strip then
    `ζ(1 − s̄) = 0`. Before the functional equation only conjugation `s ↦ s̄` was available on
    the `ζ` side; this is the other generator, and it is the one whose fixed-point set is
    `Re s = 1/2`. -/
theorem zetaCont_zero_refl {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (h : zetaCont s = 0) :
    zetaCont (1 - (starRingEnd ℂ) s) = 0 := by
  have hlt : s.re < 1 := zetaCont_zero_re_lt_one h1 h
  have hre : (1 - (starRingEnd ℂ) s).re = 1 - s.re := by simp
  have hpos : 0 < (1 - (starRingEnd ℂ) s).re := by rw [hre]; linarith
  have hne1 : (1 - (starRingEnd ℂ) s) ≠ 1 := by
    intro hc
    have hz : (1 - (starRingEnd ℂ) s).re = (1 : ℂ).re := by rw [hc]
    rw [hre, Complex.one_re] at hz
    linarith
  exact (completedZeta_eq_zero_iff hpos hne1).mp
    ((completedZeta_zero_quadruple ((completedZeta_eq_zero_iff hs h1).mpr h)).2.2)

/-- **The Klein four-group, on `ζ`'s zeros.** -/
theorem zetaCont_zero_quadruple {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (h : zetaCont s = 0) :
    zetaCont ((starRingEnd ℂ) s) = 0 ∧ zetaCont (1 - (starRingEnd ℂ) s) = 0
      ∧ zetaCont (1 - s) = 0 := by
  refine ⟨zetaCont_eq_zero_conj h, zetaCont_zero_refl hs h1 h, ?_⟩
  have hconj : (starRingEnd ℂ) ((starRingEnd ℂ) s) = s := Complex.conj_conj s
  have hpos : 0 < ((starRingEnd ℂ) s).re := by simpa using hs
  have hne1 : (starRingEnd ℂ) s ≠ 1 := by
    intro hc
    exact h1 (by rw [← hconj, hc, map_one])
  have := zetaCont_zero_refl hpos hne1 (zetaCont_eq_zero_conj h)
  rwa [hconj] at this

end TDLean.FE
