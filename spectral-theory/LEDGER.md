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
  A true finite distributive identity.
- **Euler product formula for ζ(2)** `EulerProductZeta.euler_product_zeta2`: `∏_{p prime, p≤B} (1−p⁻²)⁻¹
  → ζ(2)` as `B→∞` — the genuine *infinite* Euler product identity **at `s=2`**, unconditional,
  built from the finite distributive identity above by reindexing along the factorization
  bijection and squeezing between the ζ-partial-sums and `ζ(2)`. Honest scope: existence of the
  product limit `= ζ(2)` (itself an existence limit, **not** the value `π²/6`); general `s`,
  `−ζ'/ζ`, and zeta *zeros* are still absent.
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
  `PrimeFactorizationN` now **generalizes the order embedding to `n` distinct primes**
  (`code_order_iso_N`) and adds **injectivity** (`code_inj`); `PrimeFactorizationExists` adds
  **surjectivity** onto the `{ps}`-smooth positives (`code_surj`, via a total `p`-adic
  valuation). Together (`code_bijection_smooth`) `code` is a full **bijection** exponent-tuples
  ↔ `{first n primes}`-smooth positives — unique factorization over the first `n` primes, both
  existence and uniqueness. Axiom-free.
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
  `PrimorialEulerBound.EP_converges` now proves the tower **converges** (the rungs are uniformly
  bounded, `EP n ≤ 2`, via a telescoping majorant `M n = 2−2/(n+2)`, under `P i ≥ i+2` which the
  actual primes satisfy) — so the primorial-relativized Euler product **exists as a limit**.
  `PrimorialZeta.tower_is_zeta` then proves — **rigorously, modulo one isolated hypothesis** —
  that the tower's limit **is ζ(2)**: given the two consequences of the Euler factorization
  `EP n = Σ_{{first n primes}-smooth m} 1/m²` (namely `∀n, EP n ≤ ζ(2)` and
  `∀N, ∃n, zpart N ≤ EP n`), the analytic squeeze (`growing_ineq` + `lim_le` + `Rle_antisym`)
  gives `Un_cv (EP P) ζ(2)`. So the two infinite processes (`Σ 1/n²` and the product tower)
  provably share a limit. The factorization crux has two halves; the **uniqueness** half is now
  **done**: `PrimeFactorizationN` proves `code ps : exponent-tuples → {first n primes}-smooth
  numbers` (`∏ pᵢ^{kᵢ}`) is an **order embedding** and **injective** (`code_inj`,
  `code_order_iso_N`) — unique factorization over the first `n` primes, as a bijection onto its
  image, generalizing `FreeDivMeetIso` from 2 to `n` distinct primes (axiom-free, via the
  `p`-adic cancellation `prime_pow_cancel`). The **existence** half is now **also done**:
  `PrimeFactorizationExists` proves `code ps` **surjective** onto the `{ps}`-smooth positives
  (`code_surj`) — every `m>0` whose prime divisors lie in `ps` has an exponent tuple — via the
  total `p`-adic valuation (`padic_val`, well-founded recursion on `0≤·<m`) and
  `has_prime_divisor` (every `m>1` has a prime divisor, via stdlib `not_prime_divide`). So
  `code_bijection_smooth` makes `code` a genuine **bijection** exponent-tuples ↔ `{ps}`-smooth
  positives — both halves of the factorization crux complete, **fully axiom-free**. The
  **reindexing** is now also done: `EulerReindex` proves (over ℚ, axiom-free) `weight_fug`
  (the primon-gas weight with fugacity `1/p²` equals `1/(code ps ks)²`) and hence `euler_reindex`
  — the finite Euler product `∏ᵢ Σ_{k<K} pᵢ⁻²ᵏ = Σ_{occupation states} 1/(code ps ks)²`, a sum
  of `1/m²` over the (pairwise distinct, `codes_distinct`) smooth numbers `m = code ps ks`.
  What remains open toward `∏_p = ζ(2)` is then: (i) tying this ℚ reindexing to the ℝ tower
  `EP`/`zpart` and taking `K→∞` (the analytic bridge), and (ii) "every `m ≤ pₙ` is
  `{first n primes}`-smooth" (a property of the prime *enumeration* `P` — that it lists all
  primes in order — not of `code`). The **ℝ-side domination** for (i) is now proved:
  `RecipSquareBound.recip_sq_nodup_bound` — any finite set of distinct positive integers sums
  (of `1/m²`) to at most `ζ(2)` (via `incl_sum_le` over `List.remove` + `seqsum_zpart` +
  `growing_ineq`). This is the tight bound (`ζ(2) < 2`) that gives `EP n ≤ ζ(2) = Hupper` once
  the ℚ→ℝ transport of `euler_reindex` feeds `EP n`'s reindexed (distinct-smooth-number) form
  into it. **That transport is now done**: `EulerProductZetaBound.euler_factor_le_zeta` proves,
  for any list `ps` of distinct primes, the finite Euler product `∏_{p∈ps}(1−p⁻²)⁻¹ ≤ ζ(2)` —
  i.e. **`Hupper` for the concrete prime enumeration** — via `Q2R` transport of `euler_reindex`
  (`euler_partial_reindex_R`: the ℝ partial product = sum of `1/m²` over the coded numbers),
  `codes_nat_nodup`/`code_pos` (distinct positive integers, using `gstates_nodup`),
  `recip_sq_nodup_bound`, and `K→∞` (`euler_product_R` + `lim_le`). So the full chain
  **primon gas → reindex → factorization bijection → ζ(2) domination → `EP ≤ ζ(2)`** is
  machine-checked (quarantined Reals axioms). **`Hlower` is now also done**, and the arc is
  **closed**: `EulerProductZeta.euler_product_zeta2` proves the unconditional Euler product
  formula `∏_{p prime, p≤B}(1−p⁻²)⁻¹ → ζ(2)` — a squeeze between `zpart_le_euler` (`Hlower`, via
  a prime enumeration `primes_upto`, `small_smooth`, factorization *existence* `code_surj` with
  bounded exponents `entry_pow_le_code`/`gstates_complete`, and `incl_sum_le`) and the constant
  `ζ(2)` (Hupper). This is the genuine classical Euler product identity at `s=2`. What is **not**
  done (deliberately, and cleanly separable): the *value* `π²/6`; general `s` and the `−ζ'/ζ`
  Dirichlet series; and the nat-indexed `PrimorialZeta.tower_is_zeta2` repackaging (which would
  need an *ordered* "nth prime" enumeration — the `primes_upto`/bound-indexed form here sidesteps
  that and is the more natural statement).
  Also still **not** proved: the value `π²/6`, `ζ` as a general infinite-product identity for
  `s≠2`, `−ζ'/ζ`, and the `1<s<2` range.
- **Contour-free prime bridge** (`AbelSummation`): the analytic zeta→primes bridge runs through a
  *contour integral* (Perron + residue theorem, invariant = winding number), which our system
  has no machinery for (no ℂ, no Cauchy, no analytic continuation, no zeros). We instead build
  its **elementary shadow**: `abel_summation` (summation by parts) is the discrete
  integration-by-parts that replaces the contour shift; combined with `Λ = μ⋆log` it is the
  pre-Riemann toolkit for Chebyshev's `ψ(x) ≍ x`. **Status:** the tool (`abel_summation`) **and**
  the arithmetic crux — the general-`n` identity `Σ_{d|n} Λ(d) = log n` — are **done**.
  `VonMangoldtGlobal.vonmangoldt_identity` proves it for a genuine global `Λ:ℕ→ℝ`, entirely in
  `nat` (`Nat.gauss`) + `R` (only `ln` pulls the quarantined classical Reals axioms), via: `spf`
  proved prime; the **coprime divisor split** `c=gcd(c,a)·gcd(c,b)` (`split_divisor`, the Gauss
  keystone); the **divisor-list bijection** `divisors(a·b)≅divisors(a)×divisors(b)`
  (`divisors_prod_perm`, `dsum_prod`); `Λ` with `Lam_mul_zero` (`Λ(d·e)=0` for coprime `d,e≥2`,
  via `is_pow_true_pow`+`prime_dvd_prime_pow`); **multiplicativity** `dsum Λ (a·b)=dsum Λ a+
  dsum Λ b` (`dsum_mult`, pure sum manipulation); the **prime-power base** `dsum Λ (p^k)=ln(p^k)`
  (`dsum_primepow`); and the strong-induction **assembly** (peel `p=spf n`, `n=p^a·m` coprime via
  `pval`, `dsum_mult`+base+IH+`ln_mult`). This closes the "general-`n` divisor sums" gap. The
  **order swap is now also done** (`Chebyshev.order_swap_identity`): `Σ_{n≤N} log n =
  Σ_{d≤N} Λ(d)⌊N/d⌋` — the Dirichlet-hyperbola / elementary-Perron bridge, proved without Fubini
  (both sides satisfy `f(S N)=f N + dsum Λ(S N)`, key nat fact `⌊(N+1)/d⌋=⌊N/d⌋+[d∣N+1]`). What
  remains for `ψ(x)≍x` is now purely the **final analytic squeeze**: `log⌊x⌋!` bounds (elementary
  Stirling) + the `T(x)−2T(⌊x/2⌋)` argument via `abel_summation`. **Hard ceiling:** the *sharp* `ψ(x)∼x` (PNT), the explicit
  formula, and anything about zeta *zeros* genuinely require the contour step / complex analysis
  we deliberately do not build.
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
