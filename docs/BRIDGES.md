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
𝔭, 𝔱 via the inverse-limit towers (`ChainTower`, `PadicIntegers`); and the **Cichoń diagram itself,
now formalized** (`spectral-theory/CichonPoset.v`) as an axiom-free finite partial order —
`cichon_poset`: the 12 characteristics with their 15 ZFC-provable `≤` arrows, proved reflexive/
transitive/antisymmetric (antisymmetry via a rank linear extension), genuinely partial
(`cov(𝒩) ⊥ add(ℳ)`, separated by an Alexandrov-open up-set), with `ℵ₁` the bottom (`bottom`),
`𝔠 = |ℤ₂|` the top (`top`), and the interior edge `𝔟 ≤ 𝔡` (`b_le_d`) being exactly the
`DominatingModulus` pair. The cardinality arc is thus one poset: `ℵ₀ < 𝔟 ≤ 𝔡 ≤ … ≤ 𝔠 = |ℤ₂|`.

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

---

## 7. The functional-equation skeleton (a fixed-point involution)

The repo's north star, the ζ functional equation `ξ(s) = ξ(1−s)`, is *in shape* the invariance of a
function under an **involution with one fixed point** — and that shape is now formalized axiom-free
(`spectral-theory/FEInvolution.v`). Over ℚ, `refl s = 1−s` is an involution whose **unique fixed
point is `s = 1/2` — the critical line** (`refl_fixed_unique`); centred there it is negation `u↦−u`
(the self-adjoint `S²=I` reflection), and `F(1−s)=F(s)` is the FE shape (`FE_reflects`), self-dual at
`1/2`. Its modular face — the theta symmetry under `S : τ↦−1/τ`, i.e. `a/b ↦ −b/a` on Ford/Farey
indices — **preserves the tangency determinant `ad−bc`** (`Smod_preserves_det`), so it maps Farey
neighbours to Farey neighbours and tangent Ford circles to tangent Ford circles (the `det=±1`
condition is exactly `FordCircles.ford_tangent`'s hypothesis).

Honest boundary: this is the *shape* — the involution, the fixed point (critical line), the
self-duality, the modular symmetry — **not** the analytic `ξ(s)=ξ(1−s)`, which needs the self-dual
invariant *value* `∫e^{−πx²}=√π=Γ(½)`, the irreducible archimedean residue. Just as `FordCircles` is
the modular skeleton without the analytic θ-transformation, this is the functional-equation skeleton
without the archimedean `√π` — the geometric form of the involution, with the value still behind the
continuum wall.

**The residue, isolated** (`spectral-theory/FEResidue.v`). Since the shape is axiom-free and only the
self-dual *value* is missing, we name it as **one axiom**: the value of the FE-symmetric Gamma
reflection `Γ(s)Γ(1−s)=π/sin(πs)` at the fixed point `s=½`, i.e. `Γ(½)²=π` — `Γ(½)=√π`
(`Gamma_half_is_sqrt_pi`). This is the single place in the arc deliberately *not* `Closed under the
global context`: `Print Assumptions` shows **exactly** this residue and **not** the classical-ℝ trio.
The functional equation's whole archimedean cost is one number, honestly named — the template being
`LandauerBound`'s isolation of `ln 2`, here `√π`.

---

## 8. Prying at knot 1: the continuous-Poisson LHS as a CReal

The first concrete step into the constructive-integration knot (`spectral-theory/PoissonLHS.v`). An
honest caveat first: `finite_poisson_R` is the *discrete shadow* of Poisson, but it lives over the
**algebraic** cyclotomic ring ℚ(ζ_N) — its roots of unity aren't real numbers, so it has **no
literal CReal limit**. The object it shadows is the *continuous* Poisson summation `Σ_{n∈ℤ}f(n) =
Σ_{k∈ℤ}f̂(k)`, whose **left side is a lattice sum** that genuinely is a CReal.

We build that LHS, axiom-free, for the archetype `f(x)=1/(1+x²)` (classical identity `Σ_{n∈ℤ}1/(1+n²)
= π·coth π`): the bilateral partial sums `1 + 2·Σ_{n=1}^{N}1/(1+n²)` are rational, monotone, and
Cauchy with the explicit modulus `N=2p` from the telescoping tail `Σ_{n>i}1/(1+n²) ≤ 1/i`, handed to
`cvQ_of_regular` to yield `poisson_lhs : CReal`. Closed under the global context.

Honest boundary: this is the **sum side only**. The Fourier right side `Σ_k f̂(k)` with
`f̂(k)=π·e^{−2π|k|}` needs the constructive integral `f̂ = ∫f(x)e^{−2πikx}dx` — the core of knot 1,
and the next brick. The lattice-sum LHS is now below the wall; the integral is what remains.

---

## 9. The core of knot 1: the constructive integral of a Lipschitz function

`spectral-theory/CIntegral.v` builds the actual missing tool — a constructive Riemann integral on
[0,1], axiom-free. For `f : ℚ→ℚ` that is `L`-Lipschitz, the dyadic Riemann sums `R_k =
2^{−k}·Σ_{j<2^k} f(j·2^{−k})` are rational and Cauchy. The engine is the **doubling estimate** `|R_k −
R_{k+1}| ≤ B_k − B_{k+1}` (`B_k = 2^{−k}·L/2`): one dyadic refinement is a sum-reindex into pairs,
whose two children differ by one cell width `2^{−(k+1)}`, so each cell moves the sum by at most the
Lipschitz variation over it. That **telescopes** to `|R_i − R_j| ≤ B_i − B_j`, giving the explicit
modulus `N = L·p`, handed to `cvQ_of_regular` to yield `cintegral : CReal` with `cvQ R cintegral` —
the value `∫₀¹ f`. Closed under the global context.

This is the tool §8's Poisson right side (and the Gaussian integral, and the real Γ) was blocked on.
What remains of knot 1 is built ON it: improper integrals `∫_ℝ` (the tails), 2-D integration + polar
change of variables (the Gaussian `∫e^{−πx²}=√π`, which discharges the `FEResidue` axiom), and the
Mellin transform (θ → ξ). The seed is now below the wall; the extensions are the next bricks.

---

## 10. Extending knot 1: the improper integral ∫₀^∞ f as a CReal

`spectral-theory/ImproperIntegral.v` takes the [0,1] integral to the whole half-line, axiom-free.
`∫₀^∞ f = Σ_{m≥0} ∫_m^{m+1} f`: each unit cell `∫_m^{m+1} f` is `cintegral` of the `m`-shifted
integrand `t ↦ f(m+t)`, which is Lipschitz with the **same** constant (translation preserves the
bound), so it is a CReal. The reusable engine (a **summable series of CReals**) shows that if
`|cell m| ≤ Bd m` with `Bd` summable (an explicit tail modulus), the partial sums are Cauchy — the
block bound `|psum(i+d) − psum i| ≤ Σ_{i≤m<i+d} Bd m` follows by a CReal triangle induction — and
`CRealComplete` delivers the limit `improper_integral : CReal`. The cell magnitudes are pinned by a
new `CIntegral.cintegral_abs_le` (the integral is ≤ its sup on the cell).

`∫_ℝ f = ∫₀^∞ f + ∫₀^∞ (x ↦ f(−x))` — two applications. So the tails are now below the wall. The one
remaining piece of knot 1 is the **2-D integral + polar change of variables** that computes the
Gaussian `∫e^{−πx²} = √π` and thereby **discharges the `FEResidue` axiom**.
