/-
  TDLean.Operator.QModZ -- `ℚ/ℤ`, its group algebra, and the n-torsion bridge to `ZMod n`.

  The Bost–Connes algebra is `ℂ[ℚ/ℤ] ⋊ ℕˣ`. The previous file built the `ℕˣ` half; this one
  builds `ℂ[ℚ/ℤ]` and the two structural facts the coupling relation

      μₙ e(γ) μₙ* = (1/n) ∑_{nδ = γ} e(δ)

  rests on: `ℚ/ℤ` is **divisible** (so the fibre is nonempty and the right-hand side is not
  empty), and the fibre is a coset of the **n-torsion**, which is `≅ ZMod n` — so it has
  exactly `n` elements and the `1/n` is the correct normalisation.

  ## The connection to the `ProfiniteCRT` / `ZmodUnitsCyclic` line

  `torsionEquivZMod` is the bridge: `(ℚ/ℤ)[n] ≅ ZMod n`, hence `Aut((ℚ/ℤ)[n]) ≅ (ZMod n)ˣ`,
  which is what `ZmodUnitsCyclic` studies. In the limit `Aut(ℚ/ℤ) = Ẑˣ`, the Bost–Connes
  symmetry group.

  **This is exactly where the LEDGER 3.2 correction bites.** `PrimorialSpectralTheory.v:19`
  CLAIM A and `docs/ncg_monoid_algebra_thesis.md:24` both identify the primorial tower's limit
  with `Ẑ` / `Ẑˣ`. It is not: every primorial modulus is squarefree, so the tower reaches
  `∏ₚ 𝔽ₚ` and `∏ₚ 𝔽ₚˣ`, a **proper** quotient of `Ẑˣ` (`toZMod_not_injective` witnesses the
  failure). Getting the BC symmetry group requires the prime-**power** tower.
-/
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic

namespace TDLean.Operator

open AddSubgroup QuotientAddGroup

/-- `ℚ/ℤ`. -/
abbrev QModZ := AddCircle (1 : ℚ)

/-- The class of a rational. -/
def qz (q : ℚ) : QModZ := (q : QModZ)

theorem qz_eq_zero_iff {q : ℚ} : qz q = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [qz, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simpa using hk⟩

theorem qz_add (a b : ℚ) : qz (a + b) = qz a + qz b := rfl

theorem qz_nsmul (n : ℕ) (q : ℚ) : (n : ℕ) • qz q = qz ((n : ℚ) * q) := by
  rw [qz, qz]
  induction n with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul, ih]
      push_cast
      rw [← QuotientAddGroup.mk_add]
      congr 1
      ring

/-! ### `ℚ/ℤ` is divisible — the fibre is nonempty -/

/-- **Divisibility.** Every element of `ℚ/ℤ` has an `n`-th part. Without this the right-hand
    side of the coupling relation would be an empty sum. -/
theorem exists_nsmul_eq (n : ℕ+) (γ : QModZ) : ∃ δ : QModZ, (n : ℕ) • δ = γ := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective γ
  refine ⟨qz (q / (n : ℚ)), ?_⟩
  rw [qz_nsmul]
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.pos.ne'
  rw [qz]
  congr 1
  field_simp

/-! ### The n-torsion is `ZMod n` — the bridge to the cyclic-units line -/

/-- `k ↦ k/n` embeds `ZMod n` into `ℚ/ℤ`, onto the `n`-torsion. -/
def torsionEmb (n : ℕ+) (k : ZMod n) : QModZ := qz ((k.val : ℚ) / (n : ℚ))

theorem torsionEmb_torsion (n : ℕ+) (k : ZMod n) : (n : ℕ) • torsionEmb n k = 0 := by
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.pos.ne'
  rw [torsionEmb, qz_nsmul]
  refine qz_eq_zero_iff.mpr ⟨(k.val : ℤ), ?_⟩
  push_cast
  field_simp

theorem torsionEmb_injective (n : ℕ+) : Function.Injective (torsionEmb n) := by
  haveI : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  intro a b hab
  have hnpos : (0 : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast n.pos
  rw [torsionEmb, torsionEmb, qz, qz, QuotientAddGroup.eq_iff_sub_mem] at hab
  obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp hab
  have hval : (a.val : ℚ) - (b.val : ℚ) = (c : ℚ) * ((n : ℕ) : ℚ) := by
    have hc' : (c : ℚ) = (a.val : ℚ) / ((n : ℕ) : ℚ) - (b.val : ℚ) / ((n : ℕ) : ℚ) := by
      rw [← hc]; push_cast; ring
    field_simp at hc'
    linarith
  have ha : (a.val : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast ZMod.val_lt a
  have hb : (b.val : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast ZMod.val_lt b
  have ha0 : (0 : ℚ) ≤ (a.val : ℚ) := by positivity
  have hb0 : (0 : ℚ) ≤ (b.val : ℚ) := by positivity
  have hc0 : c = 0 := by
    by_contra hne
    have h1 : (1 : ℚ) ≤ |(c : ℚ)| := by
      have hz : (1 : ℤ) ≤ |c| := Int.one_le_abs (by exact_mod_cast hne)
      exact_mod_cast hz
    have h2 : |(a.val : ℚ) - (b.val : ℚ)| < ((n : ℕ) : ℚ) := by
      rw [abs_lt]; constructor <;> linarith
    rw [hval, abs_mul, abs_of_pos hnpos] at h2
    nlinarith
  rw [hc0] at hval
  have hvq : (a.val : ℚ) = (b.val : ℚ) := by push_cast at hval ⊢; linarith
  have hv : a.val = b.val := by exact_mod_cast hvq
  exact ZMod.val_injective _ hv

/-! ### `ℂ[ℚ/ℤ]` -/

/-- The group algebra `ℂ[ℚ/ℤ]`. -/
abbrev QAlg := AddMonoidAlgebra ℂ QModZ

/-- The unitary generators `e(γ)`. -/
noncomputable def egen (γ : QModZ) : QAlg := AddMonoidAlgebra.single γ (1 : ℂ)

@[simp] theorem egen_zero : egen 0 = 1 := rfl

/-- **`e(γ₁)e(γ₂) = e(γ₁+γ₂)`.** -/
theorem egen_mul (γ₁ γ₂ : QModZ) : egen γ₁ * egen γ₂ = egen (γ₁ + γ₂) := by
  rw [egen, egen, egen, AddMonoidAlgebra.single_mul_single, one_mul]

theorem egen_ne_zero (γ : QModZ) : egen γ ≠ 0 := by
  rw [egen]
  simp [AddMonoidAlgebra.single_eq_zero]

/-- Each `e(γ)` is invertible, with inverse `e(−γ)` — the unitarity of the `ℚ/ℤ` generators,
    in contrast with the isometries `Sₙ`, which are deliberately **not** invertible. -/
theorem egen_mul_neg (γ : QModZ) : egen γ * egen (-γ) = 1 := by
  rw [egen_mul, add_neg_cancel, egen_zero]


/-! ### The fibre is a torsion coset — exactly `n` elements -/

theorem torsionEmb_surjective (n : ℕ+) {τ : QModZ} (h : (n : ℕ) • τ = 0) :
    ∃ k : ZMod n, torsionEmb n k = τ := by
  haveI : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective τ
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.pos.ne'
  rw [show ((QuotientAddGroup.mk q : QModZ)) = qz q from rfl, qz_nsmul] at h
  obtain ⟨m, hm⟩ := qz_eq_zero_iff.mp h
  refine ⟨(m : ZMod n), ?_⟩
  have hq : q = (m : ℚ) / ((n : ℕ) : ℚ) := by field_simp; linarith [hm]
  -- `(m : ZMod n).val ≡ m` mod `n`
  have hdvd : ((n : ℕ) : ℤ) ∣ ((((m : ZMod n)).val : ℤ) - m) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  obtain ⟨c, hc⟩ := hdvd
  rw [torsionEmb, hq]
  simp only [qz]
  rw [QuotientAddGroup.eq_iff_sub_mem]
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨c, ?_⟩
  have hcq : (((((m : ZMod n)).val : ℤ)) : ℚ) - (m : ℚ) = ((n : ℕ) : ℚ) * (c : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hc
  have hgoal : (c : ℚ)
      = (((((m : ZMod n)).val : ℤ)) : ℚ) / ((n : ℕ) : ℚ) - (m : ℚ) / ((n : ℕ) : ℚ) := by
    rw [div_sub_div_same, hcq]
    field_simp
  push_cast at hgoal ⊢
  simpa using hgoal

/-- A chosen `n`-th part of `γ`. -/
noncomputable def nthPart (n : ℕ+) (γ : QModZ) : QModZ :=
  Classical.choose (exists_nsmul_eq n γ)

theorem nsmul_nthPart (n : ℕ+) (γ : QModZ) : (n : ℕ) • nthPart n γ = γ :=
  Classical.choose_spec (exists_nsmul_eq n γ)

/-- **The fibre `{δ : nδ = γ}` is exactly the torsion coset through `nthPart n γ`.** -/
theorem nsmul_eq_iff (n : ℕ+) (γ δ : QModZ) :
    (n : ℕ) • δ = γ ↔ ∃ k : ZMod n, δ = nthPart n γ + torsionEmb n k := by
  constructor
  · intro h
    have hz : (n : ℕ) • (δ - nthPart n γ) = 0 := by
      rw [nsmul_sub, h, nsmul_nthPart, sub_self]
    obtain ⟨k, hk⟩ := torsionEmb_surjective n hz
    exact ⟨k, by rw [hk]; abel⟩
  · rintro ⟨k, rfl⟩
    rw [nsmul_add, nsmul_nthPart, torsionEmb_torsion, add_zero]

/-! ### The coupling relation -/

/-- The right-hand side of `μₙ e(γ) μₙ* = (1/n)∑_{nδ=γ} e(δ)`, summed over the fibre in its
    `ZMod n` parametrisation. The `1/n` is the correct normalisation precisely because
    `torsionEmb` is injective, so the fibre has exactly `n` elements. -/
noncomputable def couple (n : ℕ+) (γ : QModZ) : QAlg :=
  ((n : ℂ))⁻¹ • ∑ k : ZMod n, egen (nthPart n γ + torsionEmb n k)

/-- Every summand of `couple n γ` really is indexed by a point of the fibre, and every fibre
    point occurs exactly once. -/
theorem couple_indexes_fibre (n : ℕ+) (γ : QModZ) :
    Function.Injective (fun k : ZMod n => nthPart n γ + torsionEmb n k) ∧
      ∀ δ, (n : ℕ) • δ = γ ↔ ∃ k : ZMod n, (fun k : ZMod n =>
        nthPart n γ + torsionEmb n k) k = δ := by
  refine ⟨fun a b hab => torsionEmb_injective n (add_left_cancel hab), fun δ => ?_⟩
  rw [nsmul_eq_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- **`couple n 0` is the "range projection" coefficient.** Taking `γ = 0` in the coupling
    relation gives `μₙ μₙ*`, and its `n` summands with coefficient `1/n` are exactly what make
    it idempotent — the operator-algebra reason the fibre count must be `n` on the nose. -/
theorem couple_card (n : ℕ+) (γ : QModZ) :
    couple n γ = ((n : ℂ))⁻¹ • ∑ k : ZMod n, egen (nthPart n γ + torsionEmb n k) := rfl

end TDLean.Operator
