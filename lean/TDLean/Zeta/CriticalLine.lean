/-
  TDLean.Zeta.CriticalLine -- the critical line as a fixed-point set, and RH stated precisely.

  `refl z = 1 − z̄` is an antiholomorphic involution of `ℂ` whose fixed-point set is **exactly**
  the line `Re z = 1/2`. So RH is the statement that every nontrivial zero of `ζ` is a fixed
  point of `refl`.

  ORACLE: `spectral-theory/ZetaZeroQuadruple.v:142 line_reflection_fixed`
  (`1 − z̄ = z → Re z = 1/2`). The Lean form is an **iff**, so slightly stronger.

  ## The two halves, and which one is proved

  `refl = (z ↦ 1−z) ∘ (z ↦ z̄)`. The zero set of `ζ` is symmetric under:

    * `z ↦ z̄`   — **proved**, `Zeta.zetaCont_eq_zero_conj`. Needs only real coefficients.
    * `z ↦ 1−z` — **not proved.** This is exactly the functional equation, i.e. cluster A.

  So `refl`-symmetry of the *zero set* is unavailable, and RH is not approached. What is
  achieved is that the target is now a machine-checked proposition rather than prose, and the
  missing half is a named predicate rather than a comment.
-/
import TDLean.Zeta.Conj

namespace TDLean.Zeta

open Complex

/-! ### The involution -/

/-- `refl z = 1 − z̄`, the composite of the functional-equation reflection with conjugation. -/
def refl (z : ℂ) : ℂ := 1 - (starRingEnd ℂ) z

@[simp] theorem refl_involutive (z : ℂ) : refl (refl z) = z := by
  simp only [refl, map_sub, map_one, Complex.conj_conj]
  ring

/-- **The critical line is exactly the fixed-point set of `refl`.**
    ORACLE: `ZetaZeroQuadruple.v:142 line_reflection_fixed` (there, one direction only). -/
theorem refl_fixed_iff (z : ℂ) : refl z = z ↔ z.re = 1 / 2 := by
  rw [refl, Complex.ext_iff]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h1, -⟩; linarith
  · intro h; exact ⟨by linarith, by ring⟩

/-- The critical line. -/
def criticalLine : Set ℂ := {z : ℂ | z.re = 1 / 2}

theorem fixedPoints_refl : {z : ℂ | refl z = z} = criticalLine := by
  ext z
  exact refl_fixed_iff z

/-! ### The Riemann Hypothesis, as a proposition -/

/-- **The Riemann Hypothesis.** Stated, **not proved**. -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → zetaCont s = 0 → s.re = 1 / 2

/-- RH says exactly that every nontrivial zero is a fixed point of `refl`. -/
theorem RH_iff_zeros_refl_fixed :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s ≠ 1 → zetaCont s = 0 → refl s = s := by
  constructor
  · exact fun h s h1 h2 h3 => (refl_fixed_iff s).mpr (h s h1 h2 h3)
  · exact fun h s h1 h2 h3 => (refl_fixed_iff s).mp (h s h1 h2 h3)

/-- Equivalently: RH says the nontrivial zeros lie on the critical line. -/
theorem RH_iff_zeros_mem_criticalLine :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s ≠ 1 → zetaCont s = 0 → s ∈ criticalLine :=
  Iff.rfl

/-! ### What is actually known about the zero set -/

/-- **Half of the symmetry, proved.** The zero set is invariant under `z ↦ z̄`. -/
theorem zeros_conj_invariant {s : ℂ} (h : zetaCont s = 0) :
    zetaCont ((starRingEnd ℂ) s) = 0 := zetaCont_eq_zero_conj h

/-- **The missing half, named.** Invariance under `z ↦ 1−z` is the functional equation; it is
    not proved here. Given it, `refl`-invariance of the zero set follows from
    `zeros_conj_invariant` by composition — which is the content of the Klein four-group
    `{z, 1−z, z̄, 1−z̄}` (`ZetaZeroQuadruple.v:129 XiC_zero_quadruple`, stated there for `XiC`). -/
def FunctionalEquationSymmetry : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → 0 < (1 - s).re → zetaCont s = 0 → zetaCont (1 - s) = 0

/-- Given the functional-equation half, the zero set is `refl`-invariant. -/
theorem zeros_refl_invariant (hFE : FunctionalEquationSymmetry) {s : ℂ}
    (h1 : 0 < ((starRingEnd ℂ) s).re) (h2 : (starRingEnd ℂ) s ≠ 1)
    (h3 : 0 < (refl s).re) (h : zetaCont s = 0) : zetaCont (refl s) = 0 :=
  hFE ((starRingEnd ℂ) s) h1 h2 h3 (zeros_conj_invariant h)

/-! ### Non-vacuity -/

theorem criticalLine_nonvacuous : ((1 : ℂ) / 2) ∈ criticalLine := by
  simp [criticalLine]

end TDLean.Zeta
