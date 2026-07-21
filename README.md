# td-theory — The Symbol Construction

> *From nothing but the idea of a symbol, all of mathematics emerges — step by step.*

This repository is a machine-checked development (Coq / Rocq) of a single idea: start with
the most minimal possible mathematical object, **a symbol**, and ask what each additional
symbol *forces* into existence. The answer is a tower, each level forced by the previous:

```
1 symbol  →  a point         existence
2 symbols →  a line          distinction + direction
3 symbols →  a triangle      closure + Fano plane + three number systems
4 symbols →  a square        complex numbers + metric + the critical line
```

The framework is then applied — number systems, geometry, number theory, the Millennium
Problems, ARC-AGI, AI/ML, biology, physics, cryptography.

## How this repo is organized

Files are arranged as a **construction ladder** you can read in order, followed by the
themes the framework is applied to, the shared library packages, and the prose/scripts.

### The construction spine — read these in order

| Dir | Step |
|-----|------|
| [`00-foundations/`](00-foundations) | Before the symbols: axioms, the observer, rays, light, measurement, **witnessing** |
| [`01-symbol-point/`](01-symbol-point) | **1 symbol → the point** (`s ∘ s = s`) |
| [`02-symbol-line/`](02-symbol-line) | **2 symbols → the line** (0/1, OR/AND, the half-step) |
| [`03-symbol-triangle/`](03-symbol-triangle) | **3 symbols → triangle, Fano plane, three number systems** (the triadic core) |
| [`04-symbol-square/`](04-symbol-square) | **4 symbols → square, ℂ, Gaussian integers, the metric** |
| [`05-higher-symbols/`](05-higher-symbols) | **n / 7 / 9 symbols and the towers** |
| [`06-synthesis/`](06-synthesis) | **Synthesis & capstone** — completeness, universal theorem, hard problems as special cases |

### Application areas

| Dir | Theme |
|-----|-------|
| [`number-systems/`](number-systems) | ℕ/ℚ/ℝ interval tower, fields, rings, idempotents, floats, octonions |
| [`geometry-metric/`](geometry-metric) | Euclidean/Riemannian geometry, manifolds, the metric, Pythagoras |
| [`number-theory/`](number-theory) | adelic, p-adic, primes, factorization, Kronecker bridge |
| [`spectral-theory/`](spectral-theory) | spectral algebra, Dirac, eigen-systems, the standing wave |
| [`category-topos/`](category-topos) | categories, functors, monads, limits, topos |
| [`complexity-sat/`](complexity-sat) | 3-SAT, SAT3, P vs NP |
| [`millennium-problems/`](millennium-problems) | Riemann, Hodge, BSD, Navier–Stokes, Yang–Mills, Poincaré, obstruction groups |
| [`arc-agi/`](arc-agi) | ARC / ARC-2 benchmark, grammars, solvers, AIMO |
| [`ai-ml/`](ai-ml) | transformers, learning, agents, LLM inversion, language functors |
| [`biology/`](biology) | genetic code, nucleotide spectra, helix, protein primes, drug discovery |
| [`physics/`](physics) | four forces, SU(3), particles, three-body, orbital resonance |
| [`crypto/`](crypto) | RSA, SHA-256, eigen-Merkle, triadic factorizers |

### Support

| Dir | Contents |
|-----|----------|
| [`packages/`](packages) | Shared substrate libraries: `DIM/`, `GHS/`, `Stratum/` |
| [`docs/`](docs) | Prose write-ups (`.md`), conjecture drafts (`.docx`), design notes |
| [`scripts/`](scripts) | Standalone Python helpers |

Every directory has its own `README.md` describing its files.

## Building

The repository builds under **Rocq 9.1** (Coq). Each directory is mapped to the root
logical namespace in `_CoqProject`, so every file is imported by its basename
(e.g. `Require Import Triple.`).

```sh
coq_makefile -f _CoqProject -o Makefile   # regenerate the Makefile (already committed)
make -j                                    # build everything
make -k -j                                 # build as much as possible, keep going past errors
```

**Build status:** as of this reorganization, **218 / 397** proof files compile clean under
Rocq 9.1. The remainder are works-in-progress with incomplete or erroneous proofs
(pre-existing — unchanged by the reorganization). The move itself introduced **zero** new
build failures and made 20 previously-unbuildable files compile by unifying the import
conventions.

---

## The construction, in one page

### Level 1 — One symbol: the point
A single symbol can only compose with itself: `s ∘ s = s`. Existence without distinction —
a **point**. The natural number **0** lives here.

### Level 2 — Two symbols: the line
A second symbol forces a distinction: `0 = OR` on the 0° horizontal, `1 = AND` on the 90°
vertical. The distance between them is **the line**; its midpoint is the half-step ½.

### Level 3 — Three symbols: the triangle, Fano plane, three number systems
The third symbol is the diagonal at 45°. It forces three axes, the equilateral triangle,
and — with midpoints and center — the **Fano plane** PG(2,2) (7 points). Three number
systems appear: linear (0°), Gaussian (45°), 3-step/modular (90°).

### Level 4 — Four symbols: the square and everything else
The fourth symbol is the axis-swap `(x,y) ↦ (y,x)` — multiplication by *i*. It closes the
triangle into a **square** = GF(2)², the observer plane with four spectral cells
(ZERO, REAL, IMAG, DIAG). Out of it come ℂ, the Gaussian integers ℤ[i], the Euclidean
metric `ds² = dx² + dy²`, and the four-cell spectral screen on which the Millennium
Problems are read — with the critical line living on the DIAG cell.

*Each level is forced by the previous. Nothing is assumed.*
