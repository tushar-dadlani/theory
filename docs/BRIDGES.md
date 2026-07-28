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

---

## 5. Why the wall is there at all: Cantor's cardinality

The isolation ladder above is, at bottom, a **stratification of ℝ by cardinality**, and Cantor's
diagonal is the theorem that makes the wall unavoidable:

- An **axiom-free** (= constructive) development can only ever *name* countably many reals — each
  comes with a finite/countable certificate (a rational, an algebraic number like ζ_N, a Cauchy
  sequence-with-modulus `CReal`). The countable side of the ladder (rungs 0–2) lives here.
- **Cantor's diagonal** produces a real outside any countable list. So a genuinely complete ℝ (all
  Cauchy sequences / all cuts) is **uncountable, `2^ℵ₀`**, and cannot be reached constructively.
- That is *precisely why* ℝ must sit behind the three classical axioms (`sig_forall_dec`,
  `sig_not_dec`, `functional_extensionality_dep`). `CRealCv` states the mechanism: classical ℝ is the
  axiom-free `CReal` **quotiented by those axioms**. The recurring honest note — "ℝ=ℚ_∞ is the
  separate archimedean factor needing the quarantined axioms" — is the *constructive shadow of the
  uncountability of ℝ*.

The repo already contains both halves of Cantor's theory:

| side | cardinality | in the repo |
|---|---|---|
| countable ℵ₀ | ℚ, ℚ̄, {ps}-smooth numbers | `PrimeFactorizationExists.code_bijection_smooth` (ℕᵏ ↔ smooth numbers), Farey/Stern-Brocot + `FordCircles` (enumerate ℚ), `InvLimit.InvLim` (= ω+1, *proved* countable) |
| Cantor's diagonal | \|A\| < \|2^A\| | `category-topos/CategoryInterval.cantor` (on `A→Prop`), `SelfReferentialTopos`, Lawvere fixed-point (unifies Cantor/Gödel/Turing) |
| continuum 2^ℵ₀ | ℤ_p, ℝ | `PadicIntegers.Zp` (built as coherent sequences; classically a Cantor set), classical ℝ (quarantined) |

**The formalized bridge** (`spectral-theory/PadicUncountable.v`): the two-adic instance wires
`PadicIntegers.Zp` (p=2) to Cantor's diagonal. A binary stream is a coherent 2-adic residue
sequence, so `{0,1}^ℕ ↪ ℤ₂` (`ofbits`), and running the diagonal on the 2-adic digits gives
**`Zp2_uncountable`: no `ℕ → ℤ₂` is onto** — the repo's first machine-checked continuum-cardinality
statement, **axiom-free** (the digits are `bool`, so the diagonal stays pointwise/constructive).
ℤ₂ and ℝ=ℚ_∞ are the two completions of the countable ℚ, both jumping to `2^ℵ₀`; the 2-adic jump is
proved outright, the archimedean one is what the quarantine pays for.

**Between the endpoints — cardinal invariants** (`spectral-theory/DominatingModulus.v`). The
characteristics of the continuum live in `(ℵ₀, 𝔠]`. The **bounding/dominating** numbers 𝔟, 𝔡 sit on
the eventual-domination order `f ≤* g` of ℕ→ℕ — which is exactly the type of the `CReal` convergence
**modulus** (`CRealCv.cvQ_of_regular`, a `precision ↦ index` function). Axiom-free backbone: the
windowed-max diagonal `g n = 1 + max_{i≤n} fᵢ n` dominates any countable family, so
`countable_family_bounded` ⟹ **ℵ₀ < 𝔟** and `no_countable_dominating` ⟹ **ℵ₀ < 𝔡** — the same "escape
past every listed function" as Cantor's diagonal (which gave the top endpoint `𝔠 = |ℤ₂|`), now on the
modulus order: *no countable set of convergence gauges converges every real*. (Coq gets the ZFC
`> ℵ₀` backbone, not the independent values.) Other handles the repo already carries: the null ideal
`𝓝` (cov/non) via the Cantor/p-adic measure (`TriadicMeasure`, `PadicUncountable`); the tower numbers
𝔭, 𝔱 via the inverse-limit towers (`ChainTower`, `PadicIntegers`); and the **Cichoń diagram itself**
as a finite Alexandrov poset — the repo's `PosetTopology`/`FiniteTopology` order-theory — with ℵ₀ at
the bottom and `𝔠 = |ℤ₂|` at the top.

---

## 6. A companion bridge: order → ring (zeta = linearized Galois closure)

A different (non-continuum) bridge in the same order-theory cluster, formalized in
`spectral-theory/ZetaClosureBridge.v`. It makes precise the slogan *"Möbius/zeta is the
ring-linearized, invertible version of a Galois connection."* On the single-prime divisibility chain,
one operation — **aggregate over the down-set `{d ≤ n}`** — appears in two monoids:

- **order / Boolean (`⋁`, idempotent):** `dclose P n = existsb P (seq 0 (S n))` is a genuine
  *closure operator* (`dclose_extensive`/`_monotone`/`_idempotent` — the very laws
  `PosetTopology.cl` gets from a **Galois connection** `α ⊣ γ`). Not invertible.
- **additive / ring (`+`, a group):** `PosetMobiusFTC.zeta_t` on the indicator, invertible with
  inverse the Möbius/backward-difference `mobius_t` (`ftc_1`/`ftc_2`).

The bridge — *read `+` as `⋁`, i.e. test the sum for nonzero* — is
**`zeta_pos_iff_dclose : 0 < zeta_t (ind P) n ↔ dclose P n = true`** (axiom-free). And
`dclose_lossy` shows the closure is non-injective (distinct predicates, equal closure), so it has no
inverse — whereas `zeta_t` does. That gap **is** why Möbius inversion needs the group `(+)`
(subtraction = inclusion–exclusion) and cannot live over the idempotent join `(⋁)`: strictly,
Möbius/zeta is not a Galois connection but the *ring-linearized, invertible upgrade* of one.
