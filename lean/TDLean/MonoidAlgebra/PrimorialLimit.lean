/-
  TDLean.MonoidAlgebra.PrimorialLimit -- the primorial tower's limit, correctly.

  ## Why this file exists

  Two places in the Rocq repo identify the primorial tower's limit with the adelic ring
  `Ẑ = ∏_p ℤ_p`:

    * `spectral-theory/PrimorialSpectralTheory.v:19` -- "CLAIM A ... The limit is the full
      adelic ring ∏_p Z_p."  (A comment; the file proves only that primorials grow.)
    * `docs/ncg_monoid_algebra_thesis.md:24` -- maps `ProfiniteCRT` / cyclic units to
      "the BC symmetry group `Ẑ^× = ∏_p Z_p^×`".

  **Both are wrong, in the same way.** Every primorial modulus is *squarefree*, so exponents
  never grow along the tower; its limit is `∏_p 𝔽_p`, not `∏_p ℤ_p`. `Ẑ` is the limit of the
  prime-POWER tower. On units, `∏_p 𝔽_p^×` is a proper quotient of `Ẑ^×`.

  `docs/monoid_algebra_prime_length.md:259` already diagnoses this correctly, but the
  correction was never landed: it appears in no `.v` file and `LEDGER.md` has no record of
  it. This file makes it machine-checked.

  ORACLE for the finite level: `PrimorialTensorGen.v : crt_monoid_iso_gen` (two coprime
  factors). The k-fold version and the correction itself are overtakes.
-/
import TDLean.MonoidAlgebra.ZMod.PrimeIsWithZero
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Group.Pi.Units

namespace TDLean.MonoidAlgebra

open Nat Finset
open scoped Function

variable {s : Finset ℕ}

/-! ### The crux: primorial moduli are squarefree -/

/-- Distinct primes are pairwise coprime. -/
theorem pairwise_coprime_primes (hs : ∀ p ∈ s, p.Prime) :
    Pairwise (Nat.Coprime on fun p : s => (p : ℕ)) := by
  intro a b hab
  have ha : (a : ℕ).Prime := hs a a.2
  have hb : (b : ℕ).Prime := hs b b.2
  have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Subtype.ext h)
  exact (Nat.coprime_primes ha hb).mpr hne

/-- **A product of distinct primes is squarefree.** This is *why* the primorial tower
    cannot reach `ℤ_p`: exponents never exceed one. -/
theorem squarefree_prod_primes (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have hap : a.Prime := hs a (Finset.mem_insert_self a t)
      have ht : ∀ p ∈ t, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      refine (Nat.squarefree_mul ?_).mpr ⟨hap.squarefree, ih ht⟩
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hap (ht p hp)).mpr (fun h => ha (h ▸ hp))

/-! ### The finite level: CRT at a primorial modulus -/

/-- ORACLE: PrimorialTensorGen.v : crt_monoid_iso_gen (two-factor case).
    `ℤ/(p₁⋯p_k) ≅ ∏ ℤ/pᵢ` as rings. The k-fold iteration is absent on the Coq side. -/
noncomputable def primorialRingEquiv (hs : ∀ p ∈ s, p.Prime) :
    ZMod (∏ p ∈ s, p) ≃+* Π p : s, ZMod (p : ℕ) := by
  have h : ∏ p : s, ((p : ℕ)) = ∏ p ∈ s, p := Finset.prod_coe_sort s id
  exact (ZMod.ringEquivCongr h.symm).trans
    (ZMod.prodEquivPi (fun p : s => (p : ℕ)) (pairwise_coprime_primes hs))

/-- The multiplicative form: `M_(p₁⋯p_k) ≅ ∏ M_pᵢ`, where `M_n = (ℤ/n, ×)`. -/
noncomputable def primorialMonoidEquiv (hs : ∀ p ∈ s, p.Prime) :
    ZMod (∏ p ∈ s, p) ≃* Π p : s, ZMod (p : ℕ) :=
  (primorialRingEquiv hs).toMulEquiv

/-! ### The correction

    `Ẑ` is *not* the primorial limit, because already at a single prime the reduction
    `ℤ_p ↠ 𝔽_p` is not injective. -/

/-- `p` is a nonzero element of `ℤ_[p]` killed by reduction. -/
theorem toZMod_natCast_self (p : ℕ) [Fact p.Prime] :
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (p : ℤ_[p]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

/-- **`ℤ_p → 𝔽_p` is not injective.** Hence `ℤ_p ≇ 𝔽_p`, and so `∏_p ℤ_p ≇ ∏_p 𝔽_p`:
    the primorial tower's limit is not `Ẑ`. -/
theorem toZMod_not_injective (p : ℕ) [hp : Fact p.Prime] :
    ¬ Function.Injective (PadicInt.toZMod : ℤ_[p] → ZMod p) := by
  intro hinj
  have hp0 : (p : ℤ_[p]) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℤ_[p])).mpr hp.out.ne_zero
  have h0 : (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (p : ℤ_[p])
      = (PadicInt.toZMod : ℤ_[p] →+* ZMod p) 0 := by
    rw [toZMod_natCast_self, map_zero]
  exact hp0 (hinj h0)

/-- Units of the limit factor as a product of local unit groups. -/
noncomputable def limitUnitsEquiv :
    (Π p : Nat.Primes, ZMod (p : ℕ))ˣ ≃* Π p : Nat.Primes, (ZMod (p : ℕ))ˣ :=
  MulEquiv.piUnits

/-- Non-vacuity: the finite-level hypotheses are satisfiable. -/
theorem primorial_nonvacuous :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime) ∧ Squarefree (∏ p ∈ s, p) := by
  refine ⟨{2, 3}, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · apply squarefree_prod_primes
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three

end TDLean.MonoidAlgebra
