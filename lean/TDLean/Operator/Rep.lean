/-
  TDLean.Operator.Rep -- the Bost–Connes representation on `ℓ²(ℕ⁺)`.

      π(μₙ) εₘ = ε₍ₙₘ₎            (the isometries, already built)
      π(e(γ)) εₘ = χ(m·γ) εₘ      (diagonal, χ(q) = e^{2πiq})

  `χ` is the canonical character of `ℚ/ℤ`: well-defined precisely because `e^{2πik} = 1` for
  integer `k`, which is what makes `ℚ/ℤ` — rather than `ℚ` — the right group. Its values are
  roots of unity, so each `π(e(γ))` is **unitary**, in contrast with the isometries `Sₙ`.

  The conjugation `Sₙ π(e(γ)) Sₙ*` is computed below: it is diagonal, supported on multiples
  of `n`, with entry `χ((j/n)·γ)` at `j`. That is the left-hand side of the coupling relation
  `μₙ e(γ) μₙ* = (1/n)∑_{nδ=γ} e(δ)` made concrete as an operator identity.

  ## Honest scope

  This is the representation at `ρ = 1 ∈ Ẑ`. The general `π_ρ(e(γ)) εₘ = χ(ρ(mγ)) εₘ` needs
  `Ẑ` as an actual parameter group, which is not built. Closing the coupling relation also
  needs the root-of-unity sum `∑_{k<n} ζⁿ_{jk} = n·[n ∣ j]`; the fibre side of it is done
  (`nsmul_eq_iff`), that sum is not.
-/
import TDLean.Operator.QModZ
import TDLean.Operator.BCAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace TDLean.Operator

open Complex

/-! ### The canonical character of `ℚ/ℤ` -/

/-- `χ(q) = e^{2πiq}`, well-defined on `ℚ/ℤ`. -/
noncomputable def chi (γ : QModZ) : ℂ :=
  Quotient.liftOn γ (fun q : ℚ => Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)))
    (by
      intro a b hab
      have heq : (qz a) = (qz b) := Quotient.sound hab
      have hmem : a - b ∈ AddSubgroup.zmultiples (1 : ℚ) :=
        QuotientAddGroup.eq_iff_sub_mem.mp heq
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      have hk' : (b : ℚ) = (a : ℚ) + (-k : ℤ) := by
        have hka : a - b = (k : ℚ) := by simpa using hk.symm
        push_cast
        linarith
      rw [hk']
      push_cast
      rw [mul_add, Complex.exp_add]
      have hone : Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ)) = 1 := by
        rw [show (2 : ℂ) * Real.pi * Complex.I * (((-k : ℤ)) : ℂ)
            = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I (-k)
      push_cast at hone
      rw [hone, mul_one])

@[simp] theorem chi_mk (q : ℚ) :
    chi (qz q) = Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) := rfl

/-- `χ` is an additive character. -/
theorem chi_add (a b : QModZ) : chi (a + b) = chi a * chi b := by
  induction a using QuotientAddGroup.induction_on with | H x =>
  induction b using QuotientAddGroup.induction_on with | H y =>
  change chi (qz (x + y)) = chi (qz x) * chi (qz y)
  rw [chi_mk, chi_mk, chi_mk, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem chi_zero : chi 0 = 1 := by
  change chi (qz 0) = 1
  rw [chi_mk]
  simp

/-- Values of `χ` are roots of unity: `π(e(γ))` is **unitary**. -/
theorem norm_chi (γ : QModZ) : ‖chi γ‖ = 1 := by
  induction γ using QuotientAddGroup.induction_on with | H q =>
  change ‖chi (qz q)‖ = 1
  rw [chi_mk, Complex.norm_exp]
  norm_num

theorem chi_ne_zero (γ : QModZ) : chi γ ≠ 0 := by
  intro h
  have := norm_chi γ
  rw [h] at this
  simp at this

theorem chi_neg (γ : QModZ) : chi γ * chi (-γ) = 1 := by
  rw [← chi_add, add_neg_cancel, chi_zero]

/-! ### The diagonal operators `π(e(γ))` -/

/-- `π(e(γ)) εₘ = χ(m·γ) εₘ`. -/
noncomputable def Eop (γ : QModZ) : Module.End ℂ (ℕ+ → ℂ) where
  toFun := fun f m => chi ((m : ℕ) • γ) * f m
  map_add' := by intro f g; funext m; simp [mul_add]
  map_smul' := by intro c f; funext m; simp [smul_eq_mul]; ring

@[simp] theorem Eop_apply (γ : QModZ) (f : ℕ+ → ℂ) (m : ℕ+) :
    Eop γ f m = chi ((m : ℕ) • γ) * f m := rfl

/-- **The representation property.** `π(e(γ₁))π(e(γ₂)) = π(e(γ₁+γ₂))`. -/
theorem Eop_mul (γ₁ γ₂ : QModZ) : Eop γ₁ * Eop γ₂ = Eop (γ₁ + γ₂) := by
  ext f m
  simp only [Module.End.mul_apply, Eop_apply, nsmul_add, chi_add]
  ring

@[simp] theorem Eop_zero : Eop 0 = 1 := by
  ext f m
  simp [Module.End.mul_apply]

/-- Each `π(e(γ))` is invertible, with inverse `π(e(−γ))`. -/
theorem Eop_mul_neg (γ : QModZ) : Eop γ * Eop (-γ) = 1 := by
  rw [Eop_mul, add_neg_cancel, Eop_zero]

/-- Conjugation inverts the label: `conj χ(γ) = χ(−γ)`. -/
theorem chi_conj (γ : QModZ) : (starRingEnd ℂ) (chi γ) = chi (-γ) := by
  induction γ using QuotientAddGroup.induction_on with | H q =>
  change (starRingEnd ℂ) (chi (qz q)) = chi (qz (-q))
  rw [chi_mk, chi_mk, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ratCast, map_ofNat]
  push_cast
  ring

/-- `π(e(γ))` is diagonal with unimodular entries, so its adjoint is `π(e(−γ))`:
    the operator is **unitary**, unlike the isometries `Sₙ`. -/
theorem ip_Eop_adjoint (γ : QModZ) (f g : ℕ+ → ℂ) :
    ip (Eop γ f) g = ip f (Eop (-γ) g) := by
  rw [ip, ip]
  refine tsum_congr fun m => ?_
  simp only [Eop_apply, map_mul]
  rw [chi_conj, smul_neg]
  ring

/-! ### The conjugation `Sₙ π(e(γ)) Sₙ*` -/

/-- **The left-hand side of the coupling relation, computed.** `Sₙ π(e(γ)) Sₙ*` is diagonal,
    supported on the multiples of `n`, with entry `χ(i·γ)` at `j = n·i`. -/
theorem conj_Eop_apply_mul (n : ℕ+) (γ : QModZ) (f : ℕ+ → ℂ) (i : ℕ+) :
    (Sop n * Eop γ * Sadj n) f (n * i) = chi ((i : ℕ) • γ) * f (n * i) := by
  simp only [Module.End.mul_apply, Sop_apply, Sadj_apply, shift_apply_mul, Eop_apply, coshift]

/-- Off the multiples of `n`, the conjugate vanishes — this is the projection `SₙSₙ*` showing
    through, and it is why the right-hand side of the coupling relation must sum to zero there. -/
theorem conj_Eop_apply_of_not_dvd (n : ℕ+) (γ : QModZ) (f : ℕ+ → ℂ) {j : ℕ+}
    (h : ¬ (n : ℕ) ∣ (j : ℕ)) : (Sop n * Eop γ * Sadj n) f j = 0 := by
  simp only [Module.End.mul_apply, Sop_apply]
  exact shift_apply_of_not_dvd _ h

/-- The covariance of the two families: conjugating by `Sₙ` divides the `ℚ/ℤ` label. Combined
    with `nsmul_eq_iff` this is the fibre structure of the BC coupling relation. -/
theorem conj_Eop_nthPart (n : ℕ+) (γ : QModZ) (f : ℕ+ → ℂ) (i : ℕ+) :
    (Sop n * Eop (nthPart n γ) * Sadj n) f (n * i) = chi ((i : ℕ) • nthPart n γ) * f (n * i) :=
  conj_Eop_apply_mul n (nthPart n γ) f i

end TDLean.Operator
