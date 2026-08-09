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

C5 (`∮_C dz/z = 2πi`) turned out **not** to need the keystone C4: on the chord
`Re z < 0`, so `log(-z)` is a primitive of `1/z` there and C3 finishes it. See LEDGER §3.1.

**C4, the keystone, is done** — Cauchy on a star-shaped region, via the radial primitive
rather than the planned adaptation of mathlib's `HasPrimitives.lean` (see LEDGER §3.3 for
why that route is blocked). The whole Coq contour wall is now cross-verified except C6.

Next: C6 (`∮_C F/z = 2πi F(0)`, which should now be short: split `F z / z` as
`dslope F 0 z + F 0 / z`, kill the first with C4 and the second with C5), then C7/C8.
Also outstanding: B4 (the `⋉`-is-really-`×` splitting theorem) and A2 (the theta
transformation from Poisson summation — the hardest single brick).
