# TDLean — a Lean 4 second verification of td-theory

An **independent re-verification**, in Lean 4 + mathlib, of results already machine-checked
in Rocq 9.1.1 elsewhere in this repository. Same worktree, same git history, different
prover.

A result counts as cross-verified only when a **human** judges the Lean statement
equivalent to the named Coq statement — Lean cannot check that link, because the two
developments share no definitions. Every headline therefore carries an `-- ORACLE:` comment
naming `<file>.v : <name>` and one line of prose saying what equivalence is claimed.

Read **[LEDGER.md](LEDGER.md)** first. It is the honest audit: the ban list, the axiom
tiers, and every discrepancy found so far.

## Scope

This directory edits **no Coq files and no Coq docs**. Findings about the Rocq development
are recorded in `LEDGER.md` only.

⚠️ **Never run `make` in this worktree.** It holds all 947 Coq sources (without `.vo`), and
a full Rocq rebuild would add gigabytes to a disk that is already the binding constraint.
Build Coq in the main checkout at `/Users/tushar/workspace/td-theory` instead.

## Build

```sh
cd lean
lake build TDLean      # this IS the axiom audit -- see below
./scripts/check_sorry.sh
```

`TDLean.lean` imports `TDLean.Audit` **last**, and `Audit.lean` wraps every headline in
`#guard_msgs in #print axioms`. So a green build asserts that every audited theorem sits at
tier L1 (`[propext, Classical.choice, Quot.sound]`) and in particular contains no
`sorryAx`. This is strictly stronger than the Coq side's trailing `Print Assumptions`,
which only prints. Verified by injection: a `sorry` in an audited theorem fails the build.

Query one theorem without rebuilding the audit:

```sh
./scripts/axioms.sh TDLean.Newman.norm_newmanKernel
```

## Toolchain — pinned, deliberately

| | |
|---|---|
| toolchain | `leanprover/lean4:v4.29.0-rc6` |
| mathlib | tag `v4.29.0-rc6` (rev `5c8398df`) |

This matches the already-installed toolchain **and** the already-built mathlib in the
sibling project `~/workspace/millenium-problems/GHS/.lake`, so `lake exe cache get` is warm
and no second toolchain is downloaded. On first setup `lake update` reported *"No files to
download"* and decompressed 8112 oleans straight from `~/.cache/mathlib`.

- ⚠️ **Do not uninstall `v4.29.0-rc6`** — the GHS project depends on it.
- ⚠️ **Do not bump to mathlib master** without checking disk: master needs
  `v4.33.0-rc2`, i.e. a second ~1.5 GB toolchain plus a fresh ~7 GB olean set.
- `lake-manifest.json` is **committed** — it is the only record of the exact dependency
  SHAs. Regenerate only via a deliberate `lake update`, in its own commit.

### Disk protocol

Disk is the binding constraint on this machine (it sat at 99% full before setup, and
`.lake` alone is 6.8 GB). Before any `lake` command that downloads:

```sh
df -h /Users/tushar     # abort below 6 GiB free
```

Prefer targeted fetches — `lake exe cache get <leaf modules>` — over a bare
`lake exe cache get`, which unpacks the whole ~7–9 GB olean set. This is also why
**`import Mathlib` is banned**: a single stray one forces the full cache forever.

## Layout

```
TDLean.lean                  root import; imports Audit LAST
TDLean/
  Basic.lean                 conventions only, no mathematics
  FE/                        cluster A -- Riemann functional equation
  MonoidAlgebra/             cluster B -- monoid algebras of prime length
  Newman/                    cluster C -- Newman contour route -> PNT
  Audit.lean                 the enforced axiom roll-call
  Audit/CrossCheck.lean      banned-lemma comparisons; nothing imports this
scripts/check_sorry.sh       comment-aware syntactic gate + import hygiene
scripts/axioms.sh            ad-hoc single-theorem axiom query
```

## Status

Scaffold complete; audit mechanism verified working in both directions (passes clean, fails
on injected `sorry`). Four bricks landed, all tier L1:

| Brick | File | Oracle |
|---|---|---|
| B6 | `MonoidAlgebra/ZMod/PrimeIsWithZero.lean` | `ZmodMultMonoid.v` |
| B7 | `MonoidAlgebra/Sym/SignType.lean` | `INFMonoid.v`, `AdjBoolINF.v` |
| C1 | `Newman/Region.lean` | `CTruncDisk.v` |
| C2 | `Newman/Kernel.lean` | `CNewmanKernel.v` |
| C3 | `Newman/Contour.lean` | `CPathFTC.v` |
| C4 | `Newman/StarPrimitive.lean` | `CGoursatConv.v`, `CPrimConv.v`, `CGoursatExcept.v` |
| C5 | `Newman/Winding.lean` | `CTruncWind.v` |
| C6 | `Newman/TruncCauchy.lean` | `CTruncCauchy.v` |
| C7 | `Newman/Laplace.lean` | `CLaplace.v` |
| C8 (part) | `Newman/Tauberian.lean` | — (overtake) |

C5 (`∮_C dz/z = 2πi`) turned out **not** to need the keystone C4: on the chord
`Re z < 0`, so `log(-z)` is a primitive of `1/z` there and C3 finishes it. See LEDGER §3.1.

**The whole Coq contour wall (C4-7 in the Coq plan) is now cross-verified.**

Two findings stand out:

- **C6 is strictly stronger than its Coq oracle.** Coq's `trunc_cauchy` is conditional on
  φ's global-continuity interface, and `docs/newman_route_status.md` lists discharging that
  interface as one of the *deep remaining blockers* of the Coq route. In Lean the hypothesis
  never arises. That blocker is an artifact of the bespoke `ComplexField`, not mathematics.
- **C4 and C5 both took different proof routes than Coq** — radial primitive instead of
  triangle Goursat, and `log(-z)` instead of `arctan` antiderivatives — so the agreement is
  genuinely independent rather than a re-run of the same argument.

**C8 is complete.** `newman_tauberian` — Newman's analytic Tauberian theorem in Zagier's
form — is proved, tier L1, no `sorry`:

> `f` continuous and bounded by `B` on `[0,∞)`, `g` its Laplace transform on `Re z > 0`,
> `g` holomorphic past the imaginary axis  ⟹  `∫₀ᵀ f(t) dt → g(0)` as `T → ∞`.

This is an **overtake, not a cross-verification**: `CNewman.v` does not exist, and
`docs/newman_route_status.md` lists brick 8 as open. Nothing in cluster C8 may be
described as "verified against Coq".

The proof, and where each earlier brick is used:

| Step | Rests on |
|---|---|
| `newman_contour_identity` — `∮_C F·K_R = 2πi F(0)` | C6 (`1/z` half) + C4 (`z/R²` half) |
| `truncContour_split` — cut at `Re z = 0` | C3 |
| `leftPart_kernel_deform` — Zagier's deformation | C6 at `α` **and at `π`**, where the chord degenerates so `C(π)` is the full circle |
| right-semicircle estimate → `2B/R²` | C7 tail bound + C2 kernel identity |
| left-semicircle estimate → `2B/R²` | `norm_gT_le_of_re_neg` + C2 |
| `tendsto_leftPart_g_zero` — the `T → ∞` step | dominated convergence, three pieces |
| `newman_inequality` — `2π‖g(0)−g_T(0)‖ ≤ 4πB/R + ‖leftPart(g…)‖` | all of the above |
| `newman_tauberian` | the inequality + the limit, `ε`-chase in `R` |

The remaining route to PNT is C9 (the zeta-side input `Φ(s) − 1/(s−1)` holomorphic on
`Re s ≥ 1`) and C10 (the Chebyshev assembly). C9 is the Coq route's own gating blocker and
is a different area of mathematics; mathlib has `riemannZeta` and its non-vanishing, but
both are banned as endpoints under the from-scratch rule.
