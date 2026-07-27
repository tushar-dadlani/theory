# Discrete ↔ Continuous Bridges — the graded-isolation ladder

**Context.** The repo has, until now, treated the discrete/continuous divide as a **binary
wall**: a result is either *axiom-free* (Closed under the global context — everything over
ℚ/ℤ/ℕ and the constructive reals `CReal`) or *quarantined* (it uses the classical `Reals`
axioms `sig_forall_dec`, `sig_not_dec`, `functional_extensionality_dep`, pulled in through
stdlib `Reals` or `ComplexField`). That wall is honest, but it is **either/or**: it says
nothing about *which* continuous facts are reachable from discrete data, and it lumps a
genuinely-transcendental object (π²/6, the Gaussian integral) together with objects that a
finite/rational certificate fully determines.

This document reframes the divide as a **ladder of structural isolations**. Each rung is a
*hypothesis that pins a continuous object to certifiable discrete data*, so the continuous
object can live **below** the quarantine wall. The organizing question is not "is it real?"
but "**what finite content, plus what structural constraint, reconstructs the continuum?**" —
content *and* structure, not either/or.

---

## 1. The four existing bridge families

All live in `spectral-theory/`. Each connects a discrete side to a continuous side; the
"quarantine" column is the honest axiom status.

| Bridge | File(s) | Discrete side → Continuous side | Axiom status |
|---|---|---|---|
| **Constructive reals** | `CRealCv.v` (`cvQ`, `cvQ_of_regular`) | rational Cauchy sequence + explicit modulus → a real | **axiom-free** |
| **Adelic valuation** | `ProductFormulaQ.v`, `ProfiniteCRT.v`, `LocalGlobalCompat.v` | finite places / `ℤ/nℤ` tower → archimedean size (on ℚ-points) | **axiom-free** (ceiling: never reaches ℝ=ℚ_∞) |
| **Finite Fourier / sampling** | `WalshSampling.v`, `FinitePoisson.v`, `DFTInversion.v`, `Parseval.v`, `DirichletKernel.v` | DFT / Walsh transform on `ℤ/N`, `F₂ⁿ` → the Poisson / inversion / sampling *mechanism* | axiom-free (`WalshSampling`) / quarantined via `ComplexField` (DFT cluster) |
| **Sum ↔ integral** | `ZetaContinuation.v`, `GammaFunction.v`, `FourierRL.v`, `HagedornTransition.v` | Dirichlet partial sum / factorial / frequency index → integral, ζ continuation, Riemann–Lebesgue | **quarantined** (stdlib `Reals`/`RiemannInt`) |

The load-bearing observation: **`CRealCv.cvQ` is the general content-bridge.** It already
de-quarantined the entire ζ(2) arc — `ZetaConstructive`, `ZetaSquareConstructive`,
`EulerProductConstructive`, `PrimorialTowerConstructive`, bundled axiom-free in
`ZetaArcConstructive.zeta_arc_free`. The classical `ZetaMaster`/`BaselZeta` versions remain as
the parallel above the wall. This is the template: *isolate the one transcendental fact,
rebuild everything structural below the wall.*

---

## 2. The isolation ladder

Each rung adds a structural constraint that lets discrete data determine a continuous object.
Lower rungs are axiom-free; only the top rung is irreducibly quarantined.

- **Rung 0 — pure discrete.** `ℤ/N` and `F₂ⁿ` transforms: `WalshSampling` (finite
  Shannon–Nyquist, `bandlimited_reconstruction`: 4 samples ⟺ 4-band signal), `FinitePoisson`
  (`Σ_{r<m}(DFT_N f)(rd) = m·Σ_{a<d}f(am)`), `DFTInversion`, `Parseval`. Finite → finite.
  **Now axiom-free at the ℤ/N level too**: `QPolyQuot` builds an axiom-free primitive N-th root of
  unity ζ in ℚ[x]/(Φ_N) (primitivity from squarefreeness of Xᴺ−1, *no* Φ_N irreducibility),
  `CycloOrthogonality` proves the orthogonality at ζ, and the DFT cluster's identities are given
  axiom-free ζ-companions **in-place**: `dft_inversion_R`, `conv_theorem_R`, `finite_poisson_R` (all
  "Closed under the global context"). The classical-ℂ versions stay as quarantined companions
  (`C=ℝ×ℝ` inherently carries the axioms); `Parseval`/`GaussSum` *positivity* is Archimedean and
  cannot move.

- **Rung 1 — band-limited continuum from samples.** A continuous object with a *bandwidth*
  constraint is finite content, so it is reconstructed from finitely many samples **below the
  wall**. The archetype is Nyquist–Shannon. Its axiom-free algebraic instance is
  **`BandlimitedInterp.v`** (see §3): *bandwidth = polynomial degree*, `N` samples at `N`
  distinct nodes reconstruct and pin a degree-`<N` signal on all of ℚ. Axiom-free.

- **Rung 2 — convergent series as `CReal` limits.** A continuous object presented as the limit
  of rung-1 objects, transported through `cvQ`. This is where Fourier *series* convergence,
  Riemann–Lebesgue, and the sum↔integral bridges belong once rebuilt on `CReal` instead of
  stdlib `RiemannInt`. Target: axiom-free.

- **Rung 3 — irreducibly transcendental ℝ.** Objects that are genuinely archimedean and *must*
  stay quarantined: the value **π²/6** (`BaselZeta`), `Γ(½)=√π` (the Gaussian integral),
  holomorphy / contour arguments, ζ zeros. No structural isolation removes the classical-ℝ
  axioms here — and the ledger says so plainly.

The point of the ladder: a fact's rung is decided by **content + structure**, not by whether
"ℝ appears." `WalshSampling` and `BandlimitedInterp` are continuous-flavoured yet axiom-free;
`BaselZeta` is transcendental and quarantined; and most of what currently sits at rung 3 (the
Euler–Maclaurin continuation, Riemann–Lebesgue) is really rung-2 work waiting to be moved down.

---

## 3. The first new rung-1 bridge: `spectral-theory/BandlimitedInterp.v`

The **algebraic Nyquist–Shannon theorem**, axiom-free over ℚ (`Print Assumptions
nyquist_sampling` = Closed under the global context). It reuses the axiom-free ℚ[X] tower
(`QPoly`/`QPolyDiv`/`QPolyMul`/`QPolyRoot`/`QPolyPIT` over the decidable field `Qc`) — no
trigonometry, no integral, no L².

- **`sampling_unique` (anti-aliasing).** Two signals band-limited to degree `n`, agreeing at
  more than `n` distinct sample nodes, agree **everywhere on ℚ** — the discrete samples pin the
  whole continuous function. Direct from `QPolyPIT.poly_roots_eval` (a degree-`≤n` polynomial
  with `>n` roots is identically zero).
- **`sampling_reconstruct` (reconstruction).** For any distinct nodes and any prescribed sample
  values there **is** a band-limited signal (degree `< #nodes`) hitting them — an explicit
  Newton incremental interpolant (`newton`), with the sharp degree bound `newton_degle` and the
  correction term tuned through the field inverse at each new node.
- **`sampling_alias`.** Constructive contrapositive: two band-limited signals that differ
  anywhere must already disagree at some sample node (finite search via `Qc`'s decidable
  equality — no classical logic).
- **`nyquist_sampling`.** Bundles existence ∧ uniqueness: *bandwidth = #samples*, undersampling
  aliases, finite discrete data determines the function on the continuum.

This is the algebraic **sibling** of `WalshSampling` (the finite F₂³ trigonometric instance):
same principle — samples = bandwidth, undersampling aliases, discrete data fixes a continuum —
realized where it needs no complex analysis.

**Honest scope.** This is the algebraic (polynomial-degree) Nyquist. The genuine
*trigonometric* Nyquist on `T = ℝ/ℤ` (band-limited = Fourier support in `[−N,N]`) needs a
constructive Fourier analysis over ℝ — constructive trig, improper integrals, L² — that the
repo does **not** build (confirmed: `RootsOfUnity.w`/`EulerFormula.Cexp` use classical
`cos`/`sin`; the only integral in the repo is `FourierRL`'s bounded `RiemannInt`). The continuum
here is ℚ (dense, the axiom-free substrate), not the completed ℝ.

---

## 4. Build queue (ordered, each a self-contained brick)

1. **`BandlimitedInterp.v`** — algebraic Nyquist over ℚ. **Done, axiom-free.**
1b. **Axiom-free ℤ/N DFT cluster** — `QPolyQuot` (algebraic ζ) + `CycloOrthogonality`
   (orthogonality at ζ) + in-place ζ-companions `dft_inversion_R` / `conv_theorem_R` /
   `finite_poisson_R`. **Done, all axiom-free.** (`Parseval`/`GaussSum` positivity is Archimedean
   and stays quarantined.)
2. **Evaluation into `CReal`** — a ℚ-polynomial's value extends to any `CReal` argument via
   `cvQ`, so the `N` rational samples determine the reconstructed function on the *completed*
   real line, not just ℚ. Promotes rung 1 to the genuine continuum, still axiom-free.
3. **`FourierRL` on `CReal`** — rebuild Riemann–Lebesgue (F1) over `CReal`/`cvQ` instead of
   stdlib `RiemannInt`, moving the first sum↔integral brick from rung 3 down to rung 2. This is
   the flagged-hard `RiemannInt` slog the classical `FourierRL` header already calls out.
4. **Continuous Poisson as a `CReal` limit** — the rung-2 limit of `FinitePoisson`, the honest
   successor that the finite file explicitly disclaims.

Rung 3 (π²/6, Gaussian integral, holomorphy, ζ zeros) stays quarantined by design — the ledger
pins exactly where the classical-ℝ axioms re-enter.
