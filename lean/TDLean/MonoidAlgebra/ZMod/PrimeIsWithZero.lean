/-
  TDLean.MonoidAlgebra.ZMod.PrimeIsWithZero -- Brick B6.

  ORACLE: spectral-theory/ZmodMultMonoid.v : zmod_prime_iso
  Claim: the multiplicative monoid (Z/p, x) is isomorphic to the zero-adjunction of its
  unit group. The Coq statement is `Bijective phi /\ (phi is a hom)` on a bespoke sig
  type `Rp := { x : nat | x < p }`, built with `is_unit_b`, `umul`, `rmul`, `phi`, `psi`
  and a `UIP_dec`-based `sig_eq_bool` -- 199 lines. Here it is one application of
  mathlib's `WithZero.withZeroUnitsEquiv`, because `Fact p.Prime` gives `Field (ZMod p)`
  and hence `GroupWithZero (ZMod p)`, and mathlib already knows every group with zero is
  `WithZero` of its units.

  The Coq `Adj G` (an `Inductive Adj := AZero | AElt (g : G)`) IS mathlib's `WithZero G`.

  LEDGER: the Coq statement is narrower than its name -- it is about the sig type `Rp`,
  carries no ring structure, and never links to `p-1` or to cyclicity. `card_units` and
  `isCyclic_units` below are the content that name implies; both are free here.
-/
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace TDLean.MonoidAlgebra

open WithZero

/-- mathlib has no `Fintype (WithZero α)` instance: `WithOne α := Option α` is a plain
    `def`, so the `Option` instances do not fire through it. Supplied here.
    (Recorded in LEDGER.md as a mathlib gap, not a td-theory finding.) -/
instance instFintypeWithZero {α : Type*} [Fintype α] : Fintype (WithZero α) :=
  inferInstanceAs (Fintype (Option α))

@[simp] theorem card_withZero {α : Type*} [Fintype α] :
    Fintype.card (WithZero α) = Fintype.card α + 1 :=
  Fintype.card_option

variable (p : ℕ) [Fact p.Prime]

/-- ORACLE: ZmodMultMonoid.v : zmod_prime_iso.
    `(Z/p, x) ≃* WithZero (Z/p)ˣ` -- the multiplicative monoid of the prime field is the
    zero-adjunction of its unit group. -/
noncomputable def zmodPrimeEquiv : WithZero (ZMod p)ˣ ≃* ZMod p :=
  letI := Classical.decPred (fun a : ZMod p ↦ a = 0)
  withZeroUnitsEquiv

/-- The carrier has cardinality exactly `p`: this is what "prime length" means, and it is
    the whole point of the `M_p` family. -/
theorem card_withZero_units : Fintype.card (WithZero (ZMod p)ˣ) = p := by
  have hp := (Fact.out : p.Prime).pos
  rw [card_withZero, ZMod.card_units p]
  omega

/-- The unit group has order `p - 1`. Coq states this nowhere; the plan doc asserts it in
    prose only. -/
theorem card_units_eq : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p

/-- The unit group is cyclic. In Coq this is the whole of `PrimitiveRoot.units_cyclic`
    (~250 lines); here it is an instance. -/
instance : IsCyclic (ZMod p)ˣ := inferInstance

/-- Non-vacuity witness: the hypotheses are satisfiable. See LEDGER.md section 2 -- Lean
    makes it easy to state a theorem whose hypotheses are unsatisfiable, so every
    headline carries one of these. -/
theorem zmodPrimeEquiv_nonvacuous : ∃ q : ℕ, ∃ _ : Fact q.Prime, Fintype.card (ZMod q) = q :=
  ⟨2, ⟨Nat.prime_two⟩, by simp⟩

end TDLean.MonoidAlgebra
