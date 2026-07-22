# Spectral-theory ledger — an honest audit

This ledger states plainly **what is proved, at what strength, and where the honest
boundaries are** for the spectral-theory arc. It exists because the repository carries
ambitious names (e.g. `millennium-problems/`) and the value of this machinery depends
entirely on not confusing a *formalized skeleton* with a *solved problem*.

Every file below is machine-checked with **zero `Admitted`** in the stated results. The
distinction that matters is (a) axiom status, (b) genuine theorem vs structural analogy,
and (c) complete structure vs curated bundle.

---

## 1. Axiom status

"Axiom-free" = `Print Assumptions` reports **"Closed under the global context"** (constructive
ℚ/ℤ/ℕ; no classical logic, no functional extensionality). The ℝ files deliberately use the
standard classical `Reals` axioms and are **quarantined** — nothing axiom-free depends on them.

| Axiom-free (ℚ/ℤ/ℕ) | Uses classical `Reals` axioms (quarantined) |
|---|---|
| `PrimonGas`, `LadderOps`, `MobiusReciprocal`, `VonMangoldt`, `PosetMobiusFTC` | `EulerFactorR`, `LadderDerivR`, `VonMangoldtR`, `MobiusReciprocalR` |
| `FreeDivMeet`, `BiView`, `BiViewProduct`, `ProductFormula`, `Padic` | `HeatFlow`, `MassGap` (bundled master), `Involution`, `Landauer`, `LandauerBound`, `WalshHadamardHilbert` |
| `PosetTopology`, `FiniteTopology`, `ChainTower`, `InvLimit` | |
| `PadicIntegers`, `PadicMetric`, `PadicRing` | |
| the ℚ-sweep: `WalshHadamardHilbertQ`, `InvolutionQ`, `LandauerQ`, `HeatFlowQ`, `MassGapQ`, `LandauerBoundL` | |

The `LandauerBound` (real `ln 2`) vs `LandauerBoundL` (parameter `L`, axiom-free) split is the
template: the one genuinely transcendental fact is isolated in an ℝ file, everything structural
is axiom-free.

---

## 2. Genuine theorem vs structural analogy

**Genuine theorems** — the stated result is literally proved about the stated object:

- **Euler product (finite)** `PrimonGas.euler_product`: `Σ_states ∏ x_p^{k_p} = ∏_p Σ_{k<K} x_p^k`.
  A true finite distributive identity. (The *infinite* Euler product / actual `ζ` is **not** here.)
- **Möbius inversion**, three forms — all genuine over the stated (single-prime / chain) domain:
  `MobiusReciprocal` (`(1−x)·psum = 1−x^K`, `∏(1−p⁻ˢ)=1/ζ` finite form), `VonMangoldt`
  (`Λ = μ⋆log`, `Σ_{d|pᵐ}Λ = log pᵐ`), `PosetMobiusFTC` (zeta/Möbius transforms mutually inverse).
- **CRT coincidence** `FreeDivMeet.crt_lattice_coincidence`: genuine, but proved **at the two
  prime-power axis generators**, not the full interior lattice (see §3).
- **p-adic ultrametric** `Padic`, `PadicMetric`: genuine ultrametric (norm / strong triangle).
- **Order → topology** `PosetTopology`: genuine Alexandrov topology + `monotone ⇒ continuous`;
  `FiniteTopology` a genuine finite instance; `ChainTower` a genuine inverse system.
- **Inverse limits** `InvLimit` (ω+1), `PadicIntegers` (`ℤ_p`), `PadicRing` (`ℤ_p` a commutative
  semiring): genuine, with the deferrals in §3.
- **Analytic Euler factor / log-derivative** `EulerFactorR`, `VonMangoldtR`, `LadderDerivR`:
  genuine limits/derivatives over ℝ — but **per single prime factor**, not summed over all primes.

**Structural analogies** — a real theorem is proved, but about a *toy model*; it is **not** a
statement about the classical object it evokes. These must never be cited as progress on the
hard problem:

- `MassGap` — "mass gap" = the spectral gap `⅓` of a toy `𝔽₂³` diffusion; the `E=mc²`/mass
  reading is an interpretation, **not** Yang–Mills. (The nat-level gap is a real theorem; the
  physics identification is analogy.)
- `BitDensity`, `BitCountContrast` — the "critical-line symmetry" is the binomial complement
  `C(n,k)=C(n,n−k)`, and the "growth contrast" is boundedness of a finite bit-count vs the
  (unformalized) `N(T)`. **Explicitly analogies** — the repo has no `ζ`, no zeros, no `N(T)`.
- `SpectralTripleRH` and relatives — spectral-triple *scaffolding*, not a proof of RH.

**No result in this arc proves, or materially advances, RH, the Yang–Mills mass gap, or any
Millennium problem.** The arc formalizes the *elementary skeleton* (Euler product ↔ CRT,
Möbius inversion, order→topology, inverse limits/completions) that those problems sit far above.

---

## 3. Complete structure vs curated bundle

Each file's `*_master`/bundle theorem collects **selected** facts, not necessarily a complete
structure. Known gaps between "what the name suggests" and "what is proved":

- **`FreeDivMeet`**: the CRT coincidence at the axis generators (`FreeDivMeet`), now extended
  to the full **order embedding** `code u ∣ code v ↔ fle u v` (`FreeDivMeetIso.code_order_iso`),
  i.e. `Div(pᵃqᵇ) ≅ [0..a]×[0..b]` as posets. What is still **not** proved is the *lattice-
  operation* form `gcd(pⁱqʲ,pⁱ'qʲ') = p^min·q^min` as an equation (the order iso gives the
  poset structure; the explicit coordinatewise gcd/lcm formula is not separately derived).
- **`PadicRing` / `PadicRingOpp`**: the commutative **semiring** axioms (`PadicRing`) *and* the
  **additive inverse** (`PadicRingOpp.Zadd_opp_l`, with `neg_coh` handling nat truncated
  subtraction) are now proved — so `ℤ_p` is a proved **commutative ring**. Only the Coq
  `Add Ring` *tactic registration* (setoid Proper boilerplate) is still not done; the ring
  axioms themselves are complete.
- **Möbius / von Mangoldt / FTC**: proved for the **single prime** (chain), the **two-prime
  product of chains** for the FTC (`ProductFTC`), and lifted to the **two-prime product** for
  Möbius (`ProductMobius.mu2_reciprocal`: `(1−x)(1−y)`) and von Mangoldt
  (`ProductMobius.vm2_interior_zero`: Λ supported on prime-power axes). All generalise to `k`
  primes by iteration. The general **arbitrary-`ℕ⁺`** divisor-sum forms (needing divisor
  enumeration / factorisation of a general `n`) are still **not** proved.
- **Infinite process**: `ZetaConverge.zeta2_converges` proves the infinite sum `Σ_{n≥1} 1/n² =
  ζ(2)` **converges** (existence, not the value `π²/6`; the same telescoping bound gives
  `Σ 1/nˢ` for all `s ≥ 2`) — the first genuinely-infinite, over-all-numbers object.
- **Primorial-relativized Euler product**: `PrimorialEuler` builds the primorial tower
  `EP n = ∏_{first n primes} (1−p⁻²)⁻¹` and proves each rung is a finite Euler product
  (`EP_is_limit`) and the tower is monotone (`EP_monotone`), mirroring the primorial's growth.
  What is **not** proved: the tower's **convergence** to `ζ` (needs a uniform bound on the smooth
  partial sums), the infinite **Euler product** as an actual product `ζ = ∏_p (1−p⁻ˢ)⁻¹`,
  `−ζ'/ζ`, and the `1<s<2` range.
- **Analytic layer** (`EulerFactorR`, `EulerProductR`, `LadderDerivR`, `NxnZero`, `VonMangoldtR`):
  the single Euler factor, the **finite** Euler product (`EulerProductR`), the number operator as a
  derivative (`LadderDerivR`), and now the number-weighted series `Σ k xᵏ = x/(1−x)²`
  (`NxnZero.number_series`, built on the from-scratch `n·xⁿ→0`) are proved. The **infinite**
  Euler product, full `ζ`, `−ζ'/ζ = Σ Λ(n)n⁻ˢ` over all primes, and general term-by-term
  differentiation are **not** proved (stdlib-only; no analysis library).
- **`ChainTower`/`InvLimit`**: the tower's inverse limit is **ω+1** (profinite completion of the
  chain), *not* `ℤ_p`. `ℤ_p` is the separate `PadicIntegers` tower (`ℤ/pⁿ`, reduction maps).
- **`Padic`**: the ultrametric on ℚ; the **completion** to `ℚ_p` (Cauchy quotient) is **not**
  built — `PadicIntegers`/`PadicMetric` realize `ℤ_p` as an inverse limit instead.

---

## 4. What this arc *is*

A clean, interlocking, almost-entirely-axiom-free formalization of the **conceptual scaffold**
linking elementary number theory, order theory, and finite topology: Euler product ↔ CRT,
Möbius inversion (three forms), order → Alexandrov topology, and inverse-limit completions
(`ω+1`, `ℤ_p`). Its value is that every individual claim is small, true, and machine-checked,
and the honest boundaries above are stated rather than blurred. It is a trustworthy sandbox,
not a proof of anything deep.
