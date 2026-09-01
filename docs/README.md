# Documentation & papers

Prose write-ups (`.md`), conjecture drafts (`.docx`), the design notes (`DESIGN.md`), and
hand-worked material such as `ARC_SOLVING_BY_HAND.md`.

## Start here

- **`rh_routes.md`** — what the Riemann-side formalization does and does not prove, the three
  distinct RH proof programs and how they differ, and where the certified zeros actually sit
  (none of the three). Read this before trusting a status claim elsewhere.
- **`certificate_cost.md`** — the cost model for the interval-arithmetic sign certificates.

## How to read the plan documents

`identity_theorem_plan.md`, `route_b_C4_newman_plan.md`, `complex_gamma_plan.md`,
`newman_route_status.md` and the `route_b_milestone_*` notes are **chronological working
logs, not current issue lists.** They record blockers as they were encountered, and later
sections routinely close what earlier sections declare open — `identity_theorem_plan.md`
localises a "precise blocker" partway through and then completes the entire program at the
end of the same file.

**Do not quote a claim of absence from these files without checking `spectral-theory/`
first.** Claims found false on inspection, and since corrected in place:

| claimed missing / blocked | actually present |
|---|---|
| the identity theorem | `CGammaComplete.GammaC_functional_equation`, tower B1→B6, `CWalk.reach` |
| complex Γ functional equation | same |
| `GammaC z ≠ 0` on `Re z > 0` | `GammaCNe0.GammaC_ne0_final` |
| region-restricted contour machinery | `CGoursatConv`, `CPrimConv`, `CGoursatExcept` |
| local factorisation at a zero | `CZeroFactorDisk.zero_factor_disk`, `CZeroListFactor.DivBy_distinct` |
| `∮ f'/f` machinery | `XiLogDerivZeros`, `ExplicitFormulaXiLogDeriv` |
| complex residue of ζ at `s=1` | `ZetaResidue.zeta_residue_one` |
| `(s−1)ζ(s)` **holomorphic** at `s=1` (blocker C0) | `CZetaRegular6.BfnT_holo`, wired up in `ZetaPoleCancel2.v` |
| `∮dz/(z−a) = 2πi` at arbitrary interior `a` | `CWindingOffCenter.winding_interior` (circle); rectangle still open |

That sweep was not exhaustive. Treat every remaining "absent" as unverified.
