/-
  TDLean.Basic -- shared conventions for the Lean cross-verification of td-theory.

  This file deliberately contains NO mathematics. It records the conventions that every
  other file in this project follows, so they live in one auditable place.

  ## The `-- ORACLE:` convention

  Every headline theorem carries a comment of the form

      -- ORACLE: <coq-file>.v : <coq-name>
      -- <one line of prose stating what equivalence is being claimed>

  naming the Coq theorem it cross-verifies. Lean cannot check that link -- the two
  developments share no definitions -- so a human must. A theorem with no ORACLE comment
  is either scaffolding or an overtake (a result the Coq side does not have); overtakes
  are marked `-- OVERTAKE:` instead and listed in LEDGER.md.

  ## The import rule

  NEVER write `import Mathlib`. Import leaf modules only. Two reasons:

  1. It is what keeps `lake exe cache get <paths>` targeted rather than pulling the whole
     ~7-9 GB olean set (see lean/README.md -- disk is the binding constraint here).
  2. It is how the from-scratch discipline is enforced. A module is banned iff importing
     it would *discharge* a headline rather than support it; the ban list is in
     LEDGER.md §1. Cross-checks against banned modules are allowed, but only inside
     TDLean/Audit/CrossCheck.lean, which nothing imports -- so they can never enter the
     dependency graph of a headline.

  ## The axiom bar

  Rocq's "Closed under the global context" has no counterpart here. mathlib's order,
  topology and measure API is built through `Classical.choice`, `propext` and
  `Quot.sound`, so every result about R or C reports those three, permanently. That is
  the honest clean bar (tier L1), not a defect. See LEDGER.md §2.

  Enforcement is in TDLean/Audit.lean, which TDLean.lean imports last, so a green
  `lake build TDLean` *is* the axiom audit.
-/

namespace TDLean

end TDLean
