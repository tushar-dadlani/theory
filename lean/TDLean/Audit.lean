/-
  TDLean.Audit -- the enforced axiom roll-call.

  Each block below asserts, at build time, that a headline theorem sits at tier L1:
  axioms exactly `[propext, Classical.choice, Quot.sound]`, and in particular NOT
  `sorryAx`. `#guard_msgs` turns `#print axioms` from a printout into an assertion --
  strictly stronger than the Coq side's trailing `Print Assumptions`, which only prints.

  Because TDLean.lean imports this file last, a green `lake build TDLean` IS the audit.

  Add one block per headline as bricks land. See LEDGER.md section 2 for the tier table,
  and in particular for why tier L1 -- not "axiom-free" -- is the honest bar in Lean.
-/
import TDLean.Basic
import TDLean.MonoidAlgebra.ZMod.PrimeIsWithZero
import TDLean.MonoidAlgebra.Sym.SignType
import TDLean.Newman.Region
import TDLean.Newman.Kernel

/-! ### Cluster B -- monoid algebra of prime length -/

/-- info: 'TDLean.MonoidAlgebra.card_withZero_units' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.card_withZero_units

/-- info: 'TDLean.MonoidAlgebra.card_units_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.card_units_eq

/-- info: 'TDLean.MonoidAlgebra.symVal_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.symVal_injective

/-- info: 'TDLean.MonoidAlgebra.symVal_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.symVal_mul

/-- info: 'TDLean.MonoidAlgebra.card_signType' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.card_signType

/-! ### Cluster C -- Newman contour route -/

/-- info: 'TDLean.Newman.convex_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.convex_truncDisk

/-- info: 'TDLean.Newman.isOpen_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.isOpen_truncDisk

/-- info: 'TDLean.Newman.newmanKernel_of_norm_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newmanKernel_of_norm_eq

/-- info: 'TDLean.Newman.norm_newmanKernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_newmanKernel

/-! ### Non-vacuity witnesses

    These must be audited too. A `sorry` here is exactly as fatal as a `sorry` in a
    headline -- an unproved non-vacuity witness means the headline may be quantifying
    over an empty set, which `#print axioms` on the headline alone would not reveal.
    (Found by testing the gate: a `sorry` injected into an unlisted witness passed the
    build. See LEDGER.md section 2, item 2.) -/

/-- info: 'TDLean.MonoidAlgebra.zmodPrimeEquiv_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.zmodPrimeEquiv_nonvacuous

/-- info: 'TDLean.MonoidAlgebra.symVal_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.symVal_values

/-- info: 'TDLean.Newman.truncDisk_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncDisk_nonvacuous

/-- info: 'TDLean.Newman.zero_mem_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.zero_mem_truncDisk

/-- info: 'TDLean.Newman.newmanKernel_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newmanKernel_nonvacuous
