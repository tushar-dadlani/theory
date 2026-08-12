/-
  TDLean.Operator.RootSum -- the root-of-unity sum, and the BC coupling relation closed.

  The last step. Everything else was in place: `conj_Eop_apply_mul` computes the left-hand
  side of `μₙ e(γ) μₙ* = (1/n)∑_{nδ=γ} e(δ)`, and `nsmul_eq_iff` identifies the fibre on the
  right with a torsion coset indexed by `ZMod n`. What joins them is character orthogonality,

      ∑_{k : ZMod n} χ(j·(k/n)) = n·[n ∣ j],

  which is why the `1/n` normalisation is forced and why the right-hand side vanishes off the
  multiples of `n` — matching the projection `SₙSₙ*` that `conj_Eop_apply_of_not_dvd` exposes.
-/
import TDLean.Operator.Rep
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace TDLean.Operator

open Complex Finset

/-- `ζₙ = e^{2πi/n}`. -/
noncomputable def zetaRoot (n : ℕ+) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((1 : ℕ) / (n : ℂ)))

theorem isPrimitiveRoot_zetaRoot (n : ℕ+) : IsPrimitiveRoot (zetaRoot n) (n : ℕ) :=
  Complex.isPrimitiveRoot_exp_of_coprime 1 (n : ℕ) n.pos.ne' (Nat.coprime_one_left _)

theorem zetaRoot_pow_n (n : ℕ+) : zetaRoot n ^ (n : ℕ) = 1 :=
  (isPrimitiveRoot_zetaRoot n).pow_eq_one

theorem zetaRoot_pow_eq_one_iff (n : ℕ+) (l : ℕ) :
    zetaRoot n ^ l = 1 ↔ (n : ℕ) ∣ l :=
  (isPrimitiveRoot_zetaRoot n).pow_eq_one_iff_dvd l

theorem chi_torsionEmb_nsmul (n j : ℕ+) (k : ZMod n) :
    chi ((j : ℕ) • torsionEmb n k) = zetaRoot n ^ ((j : ℕ) * k.val) := by
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
  rw [torsionEmb, qz_nsmul, chi_mk, zetaRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- **Character orthogonality on the `n`-torsion.** -/
theorem sum_chi_torsion (n j : ℕ+) :
    ∑ k : ZMod n, chi ((j : ℕ) • torsionEmb n k)
      = if (n : ℕ) ∣ (j : ℕ) then ((n : ℕ) : ℂ) else 0 := by
  haveI : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  set x : ℂ := zetaRoot n ^ (j : ℕ) with hx
  have hterm : ∀ k : ZMod n, chi ((j : ℕ) • torsionEmb n k) = x ^ k.val := by
    intro k
    rw [chi_torsionEmb_nsmul, hx, ← pow_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  -- reindex `ZMod n` as `range n`
  have he : Function.Bijective (fun k : ZMod n => (⟨k.val, ZMod.val_lt k⟩ : Fin (n : ℕ))) := by
    constructor
    · intro a b hab
      exact ZMod.val_injective _ (by simpa using congrArg Fin.val hab)
    · intro y
      refine ⟨((y : ℕ) : ZMod n), ?_⟩
      ext
      simp [ZMod.val_natCast_of_lt y.isLt]
  have hsum : ∑ k : ZMod n, x ^ k.val = ∑ y : Fin (n : ℕ), x ^ (y : ℕ) :=
    Fintype.sum_bijective _ he _ _ (fun _ => rfl)
  rw [hsum, Fin.sum_univ_eq_sum_range (fun v => x ^ v)]
  by_cases hd : (n : ℕ) ∣ (j : ℕ)
  · rw [if_pos hd]
    have hx1 : x = 1 := (zetaRoot_pow_eq_one_iff n (j : ℕ)).mpr hd
    simp [hx1]
  · rw [if_neg hd]
    have hx1 : x ≠ 1 := fun h => hd ((zetaRoot_pow_eq_one_iff n (j : ℕ)).mp h)
    rw [geom_sum_eq hx1]
    have hxn : x ^ (n : ℕ) = 1 := by
      rw [hx, ← pow_mul, mul_comm, pow_mul, zetaRoot_pow_n, one_pow]
    rw [hxn, sub_self, zero_div]

/-! ### The coupling relation -/

/-- **`μₙ e(γ) μₙ* = (1/n) ∑_{nδ = γ} e(δ)`**, as an operator identity on `ℓ²(ℕ⁺)`.
    The sum runs over the fibre in its `ZMod n` parametrisation (`nsmul_eq_iff`), which is
    faithful and exhaustive by `couple_indexes_fibre`. -/
theorem bc_coupling (n : ℕ+) (γ : QModZ) (f : ℕ+ → ℂ) (j : ℕ+) :
    (Sop n * Eop γ * Sadj n) f j
      = ((n : ℕ) : ℂ)⁻¹ * ∑ k : ZMod n, Eop (nthPart n γ + torsionEmb n k) f j := by
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
  -- factor the right-hand side
  have hrhs : ∑ k : ZMod n, Eop (nthPart n γ + torsionEmb n k) f j
      = chi ((j : ℕ) • nthPart n γ) * f j * ∑ k : ZMod n, chi ((j : ℕ) • torsionEmb n k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Eop_apply, nsmul_add, chi_add]
    ring
  rw [hrhs, sum_chi_torsion]
  by_cases hd : (n : ℕ) ∣ (j : ℕ)
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ+, j = n * i := ⟨pdiv j n hd, (mul_pdiv j n hd).symm⟩
    rw [conj_Eop_apply_mul, if_pos (by rw [PNat.mul_coe]; exact Dvd.intro _ rfl)]
    -- `(n·i)·δ₀ = i·(n·δ₀) = i·γ`
    have hsm : ((n * i : ℕ+) : ℕ) • nthPart n γ = (i : ℕ) • γ := by
      rw [PNat.mul_coe, mul_comm, mul_smul, nsmul_nthPart]
    rw [hsm]
    field_simp
  · rw [conj_Eop_apply_of_not_dvd n γ f hd, if_neg hd]
    ring

end TDLean.Operator
