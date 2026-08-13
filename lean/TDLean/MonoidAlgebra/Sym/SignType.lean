/-
  TDLean.MonoidAlgebra.Sym.SignType -- Brick B7.

  ORACLE: spectral-theory/INFMonoid.v : Sym, op, val, val_hom, val_inj
          spectral-theory/AdjBoolINF.v : Adj_bool_iso_INF

  Claim: the base monoid `{I, N, F}` of the td-theory tower is `({+1,-1,0}, x) = (F_3, x)`,
  and it is the `p = 3` member of the family `M_p := (F_p, x)`.

  mathlib's `SignType` IS that monoid:

      Coq `Sym`  |  Lean `SignType`  |  `val` / `castHom`
      -----------|-------------------|--------------------
      I          |  pos              |  1
      N          |  neg              |  -1
      F          |  zero             |  0

  Coq hand-rolls `op` as a 9-case match and proves associativity/commutativity by
  `destruct`; here `SignType` is a `CommGroupWithZero` instance, and `val` is
  `SignType.castHom`, a bundled `→*₀`, so `val_hom` is `map_mul` and `val_inj` is
  `cast_injective` -- both free.
-/
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Data.Fintype.Units

namespace TDLean.MonoidAlgebra

open WithZero

/-- ORACLE: INFMonoid.v : val. Coq's `val : Sym -> Z` is `SignType.castHom`. -/
noncomputable def symVal : SignType →*₀ ℤ := SignType.castHom

/-- ORACLE: INFMonoid.v : val_hom. Free from the bundled `→*₀`. -/
theorem symVal_mul (a b : SignType) : symVal (a * b) = symVal a * symVal b :=
  map_mul symVal a b

/-- ORACLE: INFMonoid.v : val_inj. -/
theorem symVal_injective : Function.Injective symVal := by decide

/-- `{I, N, F}` has exactly three elements -- the `p = 3` case of "prime length". -/
theorem card_signType : Fintype.card SignType = 3 := by decide

/-- The unit group has order `p - 1 = 2`. -/
theorem card_units_signType : Fintype.card SignTypeˣ = 2 := by decide

/-- ORACLE: AdjBoolINF.v : Adj_bool_iso_INF.
    `{I, N, F}` is the zero-adjunction of its two-element unit group -- i.e. it really is
    an `Adj G`, with `G` the two-element group. This is the `p = 3` instance of brick B6's
    `zmodPrimeEquiv`, obtained from the same mathlib lemma. -/
noncomputable def symEquiv : WithZero SignTypeˣ ≃* SignType :=
  letI := Classical.decPred (fun a : SignType ↦ a = 0)
  withZeroUnitsEquiv

/-- Non-vacuity: the three values are genuinely distinct, so `Sym` is not a degenerate
    one-point monoid. (Coq proves this by `discriminate`.) -/
theorem symVal_values :
    symVal SignType.pos = 1 ∧ symVal SignType.neg = -1 ∧ symVal SignType.zero = 0 := by
  refine ⟨rfl, rfl, rfl⟩

end TDLean.MonoidAlgebra
