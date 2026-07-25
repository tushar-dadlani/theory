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
| the ℚ-sweep: `WalshHadamardHilbertQ`, `InvolutionQ`, `LandauerQ`, `HeatFlowQ`, `MassGapQ`, `LandauerBoundL` | `ComplexField` (custom `C = ℝ[i]`; footprint = R only) |

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
- **Product formula over ℚ** `ProductFormulaQ.product_formula` (`_int` + `_Q`): Ostrowski's
  `∏_v |x|_v = 1` for nonzero rationals — for a positive integer `n`, `n = ∏_p p^{v_p(n)}`
  (via `code_surj`) so `|n|_∞·∏_p |n|_p = 1`; for `a/b` the quotient of the two integer
  instances. **Axiom-free** — genuine, because for a *rational* input `|x|_∞` is itself rational
  (a ratio of coded integers), so no ℝ is constructed. This is the honest **adelic bridge**:
  finite valuations determine archimedean size *on rational points*. It does **not** build
  `ℝ=ℚ_∞` (the completion at `∞`, a separate factor `𝔸_ℚ=ℝ×𝔸_f` orthogonal to the profinite
  tower `∏_p ℤ_p=lim ℤ/nℤ`); Γ-factors, `ξ(s)`, the functional equation, and ζ special values
  (π²/6) are archimedean-local and stay out of reach — the file's closing note pins where the
  quarantined Reals axioms would re-enter (Cauchy/Dedekind completion).
- **Profinite completion, explicit** `ProfiniteCRT.profinite_crt`: the finite/non-archimedean
  factor `𝔸_f` of `𝔸_ℚ = ℝ × 𝔸_f`, machine-checked as (1) the **CRT ring iso**
  `ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ` (coprime `m,n`) — `crt_iso` with explicit Bézout reconstruction
  inverting the reduction pair, `crt_roundtrip` closing the round-trip via `Gauss`, reduction a
  ring hom (`Zplus_mod`/`Zmult_mod`); and (2) the **inverse system** `Ẑ = lim_n ℤ/nℤ` — commuting
  projections (`proj_compat`), the prime-power tower `ℤ/p^{k+1}→ℤ/pᵏ` (`tower_proj`), directedness
  (`system_directed`). **Axiom-free**: built from finite discrete data. Iterating CRT over
  `n=∏_p p^{v_p}` gives `Ẑ ≅ ∏_p ℤ_p`. Honest ceiling (same as ProductFormulaQ): this is the
  finite factor only; `ℝ=ℚ_∞` (the archimedean completion, hence Γ-factors/`ξ(s)`/functional
  equation/ζ special values) is the separate factor it never reaches.
- **Local–global compatibility** `LocalGlobalCompat` (`fabs_is_recip` + `local_global_compat`):
  the valuation description of `𝔸_f` (`ProductFormulaQ.fabs = ∏_p |·|_p`) and the ring
  description (`ProfiniteCRT`: `Ẑ = lim ℤ/nℤ = ∏_p ℤ_p`) read the **same** exponents. Global:
  `fabs ps ks == /inject_Z(code ps ks)` (`∏_p |n|_p = 1/n`). Local: for `n = code (p::ps')(k::ks')`,
  the CRT-split modulus `p^k` (ring component `ℤ/p^{v_p}ℤ`) is the reciprocal of the local abs
  value `|n|_p = p^{−v_p}` that `fabs` peels off — same `k = v_p(n)`. **Axiom-free.** The
  non-archimedean local–global principle; `ℝ=ℚ_∞` stays the separate archimedean factor.
- **Custom complex field** `ComplexField.complex_field_axioms`: `C = ℝ[i] = ℝ×ℝ` with **every
  complex-number axiom proved as a theorem** (field laws — `ring`/`field` registered; `i²=−1`;
  `c = Re+i·Im`; `ℝ↪C` injective ring hom; conjugation involution/hom; `c·c̄ = |c|² ≥ 0`).
  Deliberate replacement for an opaque/external `C`: `Print Assumptions` = **exactly** the two
  quarantined classical-`ℝ` axioms (`sig_forall_dec`, `functional_extensionality_dep`), so **no
  new axiom** enters — the "complex axioms" are Qed lemmas, not assumptions. Genuine field;
  footprint = R. **Weak/strong layering** `ComplexField.ring_core_generalization`: the `Im·Im`
  coupling is parameterised as `i²=δ` (`Cmulg δ`); the **ring core is genuine for every δ**
  (`Cring_theory_g` — `ℝ[e]/(e²=δ)` a commutative ring, no use of `−1`), `i²=−1` (`Ci_sq`) is a
  *downstream* `δ=−1` fact (via `Cig_sq`: `e²=δ`), and the **field cap** adds the *single* honest
  hypothesis `δ<0` (`Cnorm2g_pos`, nonzero norm-form off `0`). Trichotomy `δ<0/=0/>0` =
  complex/dual/split-complex. Same footprint (2 axioms); refactor keeps all public names, so the
  ~15 downstream `C`-files compile unchanged.
- **Bridge into ℤ — Gaussian integers** `GaussianIntegers.gaussian_integers`: the same parametric
  ring core run over `ℤ`, `ZI = ℤ[e]/(e²=δ) = ℤ×ℤ`, and over `ℤ` it is **AXIOM-FREE** ("Closed under
  the global context") — strictly cleaner than the `ℝ` version. Weak ring core for every `δ`
  (`ZIring_theory_g`); `i²=−1` a downstream `δ=−1` fact. **The bridge is the multiplicative norm**
  `N_δ:ZI→ℤ`, `N_δ(a)=Re²−δ·Im²`, a genuine ring→ℤ homomorphism `N_δ(a·b)=N_δ(a)·N_δ(b)`
  (`ZInorm_mul`) with `a·conj a = N_δ(a)` (`ZImulg_conj`). Gaussian case: `ℤ↪ZI` ring hom, and the
  **units = norm-1 elements = {1,−1,i,−i}** (`unit_norm` + `gaussian_units` + `norm1_unit`), all
  genuine theorems. Arithmetic shadow of `ComplexField`; `δ<0/=0/>0` = Gaussian/dual/split integers.
  Entry point for sums-of-two-squares / Gaussian-prime number theory.
- **ℤ[i] is a Euclidean domain** `GaussianDivision.ZI_euclid` (**axiom-free**): the cornerstone of
  unique factorisation in `ℤ[i]`. For `b ≠ 0` there exist `q, r` with `a = q·b + r` and
  `N(r) < N(b)`. Construction: `znear` rounds each rational coordinate of `a·conj(b)/N(b)` to the
  nearest integer (`znear_spec`: `|x − q·d| ≤ d/2`, via `Z.div_mod` + `nia`); then
  `r·conj(b) = (X−qx·d, Y−qy·d)` coordinatewise, so `N(r)·d = N(r·conj b) = (X−qx d)²+(Y−qy d)² ≤
  d²/2 < d²` (using `ZInorm_mul`, `ZInorm_conj`, `ZImulg_conj`), giving `N(r) < N(b)`. Closed under
  the global context. **Next:** gcd/Euclidean algorithm, Bézout, irreducible=prime, unique
  factorisation, and the Gaussian-prime classification — the ℤ[i] engine the general Jacobi
  identity `r₂(n)=4·S(n)` needs.
- **ℤ[i] divisibility, gcd and Bézout** `GaussianGCD.ZI_bezout` (**axiom-free**): divisibility
  `ZIdvd a b := ∃c, b=a·c` (with `refl`/`trans`/`add`/`sub`/`mul_r`/`0` lemmas), and the **Bézout
  property**: every pair `x,y` has a gcd `g = u·x + v·y` that divides both `x` and `y` and is divided
  by every common divisor. Proved by **well-founded induction on `N(y)`** (the Euclidean algorithm
  `gcd(x,y)=gcd(y, x mod y)` via `ZI_euclid`), with no recursive `gcd` function — the norm decrease
  from `GaussianDivision` powers the recursion. Closed under the global context. **Next:** Euclid's
  lemma (irreducible ⇒ prime) from Bézout, then existence + uniqueness of factorisation, then the
  Gaussian-prime classification.
- **ℤ[i] units, associates, Euclid's lemma** `GaussianIrreducible.ZI_euclid_lemma` (**axiom-free**):
  units = norm-1 elements = `{1,−1,i,−i}` (`ZIunit_norm`, `ZIunit_cases`); ℤ[i] is an **integral
  domain** (`ZI_no_zero_div`, `ZImul_cancel_l`) since the norm is multiplicative and `N(z)=0 ⟺ z=0`;
  associates via units, with mutual divisibility of nonzero elements ⟹ associate
  (`dvd_antisym_assoc`). **Euclid's lemma**: for `p` irreducible, `p | a·b ⇒ p | a ∨ p | b` — proved
  **constructively** from Bézout: `g = gcd(p,a) = u·p+v·a` and `g | p`, so `p = g·k` gives (unit `g`)
  or (unit `k`) — the split is on the *factorisation*, not on decidability of `p|a`; unit `k` ⟹ `p ~ g
  | a`, unit `g` ⟹ `1 = U·p + V·a` ⟹ `p | b`. This is the uniqueness half of unique factorisation in
  ℤ[i]. Closed under the global context. **Next:** existence of factorisation (norm induction), then
  the Gaussian-prime classification.
- **ℤ[i] factorisation existence** `GaussianFactorization.factor_exists` (**axiom-free**): every
  nonzero non-unit is a product of irreducibles. Constructive: the nearest-integer quotient is
  **exact** when `a | z` (`ZIdiv_exact`, since `znear(c·d, d)=c`), so **divisibility is decidable**
  (`ZIdvdb`/`ZIdvd_dec`) with no search; a **bounded box search** over `{N(a) ≤ N(z)}`
  (`gbox`/`pdiv_list`) then either returns a proper divisor (`1 < N(d) < N(z)`) or certifies
  irreducibility (`pdiv_nil_irreducible` — the disjunction `unit a ∨ unit b` for `z=a·b` comes from
  deciding `N(a)=1`, not excluded middle). Strong induction on `N` splits `z = d·(z/d)` into two
  smaller non-units and concatenates their factor lists. Together with Euclid's lemma this is
  **unique factorisation in ℤ[i]**. Closed under the global context. **Next:** the Gaussian-prime
  classification (`2` ramifies, `p≡1 (4)` splits, `p≡3 (4)` inert).
- **Gaussian-prime classification** `GaussianPrimes.gaussian_prime_classification` (**axiom-free**):
  the engine `norm_prime_irreducible` (if `N(π)` is a rational prime then `π` is irreducible, since
  `N(π)=N(a)·N(b)` forces a norm-1 factor), and the three cases over a rational prime: **`2`
  ramifies** — `2 = (1+i)(1−i)` with `1+i` a Gaussian prime of norm 2 (`two_ramifies`/`two_eq`);
  **`p≡1 (4)` splits** — `p = a²+b² = (a+bi)(a−bi)` via Fermat (`sum2_prime1`), with `a+bi` a
  Gaussian prime of norm `p` (`prime1_splits`); **`p≡3 (4)` inert** — `p` stays a Gaussian prime of
  norm `p²` (`prime3_inert`), because a factor of norm `p` would make `p` a sum of two squares,
  impossible for `p≡3 (4)` (via `prime_mult` + `two_squares_iff` — `q3even p` fails as `p` divides
  itself to the odd power 1). This completes the ℤ[i] arithmetic engine (Euclidean division → gcd →
  Bézout → Euclid's lemma → unique factorisation → prime classification) that the general Jacobi
  identity `r₂(n)=4·S(n)` builds on. Closed under the global context.
- **ℤ[i] coprime split** `GaussianCoprime.gaussian_split` (**axiom-free**): the surjectivity core of
  r₂-multiplicativity. If `N(z)=m·n` with `gcd(m,n)=1` then `z=x·y` with `N(x)=m`, `N(y)=n`. Take
  `x = gcd_{ℤ[i]}(z, m)` (`ZI_bezout`); then `N(x) | m` two ways — `N(x) | N(z)=mn` and `N(x) |
  N(m)=m²` give `N(x) | gcd(mn,m²)=m` (`Z.gcd_mul_mono_l` + the `Nat.gcd`→`Z.gcd` bridge `nat_gcd_Z`);
  and **conjugating the Bézout identity** `x = u·z + v·m` shows `(m) | x·conj(x) = ZtoZI(N x)` — the
  cross term carries `z·conj z = m·n` — so `m | N(x)` (`ZtoZI_dvd`, off the real coordinate). Hence
  `N(x)=m` and `y=z/x` has norm `n`. Closed under the global context. **Next:** the 4-to-1 count
  `r₂(m)·r₂(n)=4·r₂(mn)` (each norm-`mn` element has exactly 4 splits — its unit orbit), then the
  multiplicative-agreement assembly for the full `r₂(n)=4·S(n)`.
- **r₂ is multiplicative (up to 4)** `R2Multiplicative.r2_mult` (**axiom-free**): `gcd(m,n)=1 ⇒
  r₂(m)·r₂(n) = 4·r₂(mn)`. Via `r₂(n)=#{N(z)=n}` (`Lnorm`), the product map `(x,y)↦x·y` on
  norm-`m`×norm-`n` pairs is **surjective** onto norm-`mn` elements (`gaussian_split`) and exactly
  **4-to-1**: every fibre is the unit orbit `{(x₀·u, y₀·conj u) : u∈units}` of size 4
  (`fiber_length_4`), because a second split `x·y=x₀·y₀` with matching norms forces `x~x₀` — `x`, `y₀`
  are ℤ[i]-coprime (their norms `m`, `n` are coprime, so their gcd has norm 1) so `x | x₀·y₀ ⇒ x | x₀`
  via Bézout (`split_unique`). A generic key-partition count (`count_by_key`: every fibre size `c` ⇒
  `|domain|=c·|image|`) then gives `r₂(m)·r₂(n) = |norm-m × norm-n| = 4·|norm-mn| = 4·r₂(mn)`. Closed
  under the global context. **This completes both multiplicativity facts** (`S_mult`, `r2_mult`) and
  all prime-power values on both sides; the general `r₂(n)=4·S(n)` now needs only the
  multiplicative-agreement assembly over the prime factorisation.
- **JACOBI'S TWO-SQUARE FORMULA** `R2Jacobi.jacobi_two_squares` (**axiom-free**): for `n ≥ 1`,
  `r₂(n) = 4·(d₁(n) − d₃(n))` — the exact count of representations `n = a²+b²` equals four times the
  excess of divisors `≡1` over divisors `≡3 (mod 4)`. The **multiplicative-agreement assembly**:
  `r₂` and `4·S` agree on prime powers (`r2_ppow_eq_4S`, casing `2`/`p≡1`/`p≡3` against `r2_2pow`/
  `r2_1pow`/`r2_3pow` and `S_prime_pow_*`), and both `r₂` and `S` are multiplicative on coprimes
  (`r2_mult`, `S_mult`), so by strong induction peeling one prime power `p^v ∥ n` (`nat_padic`,
  `gcd_pow_coprime`): `4·r₂(n) = r₂(p^v)·r₂(m') = (4·S(p^v))·(4·S(m')) = 16·S(n)`, giving
  `r₂(n) = 4·S(n) = 4·(d₁−d₃)` (`jacobi_full` + `S_as_d1d3`). This is the genuine classical theorem,
  machine-checked with **zero axioms**, resting on the full ℤ[i] unique-factorisation tower
  (`GaussianDivision`…`GaussianCoprime`), the three prime-power counts, and both multiplicativities.
  Closed under the global context. The `vm_compute` check `jacobi_upto` (n ≤ 200) is now a corollary,
  not the evidence.
- **Legendre symbol + Euler's criterion** `LegendreSymbol` (**axiom-free**, QR brick 1): the
  foundation for quadratic reciprocity. Defines `(a/p) : ℤ` (`0` if `p∣a`, else `±1` by whether
  `a^((p-1)/2) ≡ 1`), and proves **Euler's criterion** `a^((p-1)/2) ≡ (a/p) (mod p)`
  (`legendre_euler`) — the half-power `pw p a ((p-1)/2)` squares to `a^(p-1)=1` (Fermat), so is `1`
  or `p-1` (`euler_pm1`, via `sqrt1`). Plus **complete multiplicativity** `(ab/p)=(a/p)(b/p)` on units
  (`legendre_mult_unit`): both sides are `±1` congruent mod `p` to `pw a·pw b` (Euler + `pw_mul_base`),
  and a sign is pinned by its residue mod an odd prime (`sign_mod_inj`). Reuses `fermat`, `sqrt1`,
  `unit_not_div`, `not_div_pow`, `pw_add`. Closed under the global context. **Next (QR bricks 2–5):**
  Gauss's lemma `(a/p)=(-1)^μ`, Eisenstein's `⌊ka/p⌋`-sum refinement, the lattice-point count, and
  the assembly `(p/q)(q/p)=(-1)^(((p-1)/2)((q-1)/2))`.
- **Gauss's lemma** `GaussLemma.legendre_gauss` (**axiom-free**, QR brick 2): `(a/p) = (-1)^μ`, where
  `μ = #{ k ∈ [1,(p-1)/2] : (k·a) mod p > (p-1)/2 }` (`mu`). The combinatorial heart: the
  least-absolute residues `fres k` of `a, 2a, …, ((p-1)/2)a` are a **permutation** of `1..(p-1)/2`
  (`fres_perm` — injective since `fres i = fres j` forces `i≡±j` and `i+j<p` rules out the minus,
  via `cancel_mod`), so taking the product mod `p`, `a^((p-1)/2)·((p-1)/2)! ≡ (-1)^μ·((p-1)/2)!`
  (`prod_res_val`/`prod_res_sign`), and cancelling the unit `((p-1)/2)!` (`fact_coprime`) gives
  `a^((p-1)/2) ≡ (-1)^μ`, hence `(a/p)=(-1)^μ` by Euler's criterion + `sign_mod_inj`. Uses a reusable
  `Zprod` (product-over-list) layer with permutation-invariance, sum-over-product, and sign-count
  lemmas. Closed under the global context. **Next (QR bricks 3–5):** Eisenstein's `μ ≡ Σ⌊ka/p⌋
  (mod 2)`, the lattice-point count, and the assembly.
- **Eisenstein's refinement** `EisensteinLemma.legendre_eisenstein` (**axiom-free**, QR brick 3): for
  an odd prime `p` and an **odd** unit `a`, `(a/p) = (-1)^(Σ_{k=1}^{(p-1)/2} ⌊k·a/p⌋)`. From the
  division identity `k·a = p·⌊k·a/p⌋ + (k·a mod p)` summed over `k` (`eis_div`), the permutation
  `Σ fres = Σ k` (`eis_perm`), and the residue split `Σ res + 2U = Σ fres + p·μ` (`eis_res`), one gets
  `(a-1)·Σk + 2U = p·(Σ⌊⌋ + μ)`; with `a`, `p` odd this forces `2 | (Σ⌊⌋ + μ)`, i.e. `μ ≡ Σ⌊k·a/p⌋
  (mod 2)` (`eis_parity`), so Gauss's `(a/p)=(-1)^μ` becomes `(-1)^(Σ⌊⌋)`. Adds a reusable `Zsum`
  (sum-over-list) layer. Closed under the global context. **Next (QR bricks 4–5):** the lattice-point
  count `Σ⌊kq/p⌋+Σ⌊kp/q⌋ = ((p-1)/2)((q-1)/2)` and the assembly.
- **Lattice-point count** `ReciprocityCount.reciprocity_count` (**axiom-free**, QR brick 4): for
  distinct odd primes `p,q`, `fsum p q + fsum q p = ((p-1)/2)·((q-1)/2)`, where `fsum p q =
  Σ_{k=1}^{(p-1)/2} ⌊k·q/p⌋`. Pure elementary counting over ℕ/lists: the lattice points `(k,j)` in
  `[1,(p-1)/2]×[1,(q-1)/2]` split into **below** (`p·j < q·k`) and **above** (`q·k < p·j`) the line
  `q·x = p·y`, with *no* point on it (`p ∤ q·k` for `k ≤ (p-1)/2`, `p≠q`, via `p_ndvd`). Each row
  count `#{j : p·j < q·k}` is exactly `⌊k·q/p⌋` (`count_row`: `p·j<q·k ↔ j ≤ ⌊q·k/p⌋`, and
  `⌊q·k/p⌋ ≤ (q-1)/2`); summing rows (`count_list_prod`) gives `below = fsum p q`, the transpose
  (`count_transpose`) gives `above = fsum q p`, and `below`+`above` partition the box
  (`filter_length`). Self-contained list layer. Closed under the global context. **Next (QR brick
  5):** apply Eisenstein twice and multiply.
- **THE LAW OF QUADRATIC RECIPROCITY** `QuadraticReciprocity.quadratic_reciprocity` (**axiom-free**,
  QR brick 5 / capstone): for distinct odd primes `p, q`,
  `(q/p)·(p/q) = (-1)^(((p-1)/2)·((q-1)/2))`. Assembled in a few lines: Eisenstein's refinement gives
  `(q/p) = (-1)^(Σ⌊kq/p⌋)` and `(p/q) = (-1)^(Σ⌊kp/q⌋)` (the two floor sums `Tsum`/`fsum` coincide
  definitionally), their product is `(-1)^(Σ⌊kq/p⌋ + Σ⌊kp/q⌋)`, and the lattice-point count
  (`reciprocity_count`) makes the exponent `((p-1)/2)·((q-1)/2)`. To let the numerator exceed the
  modulus, the whole Euler/Gauss/Eisenstein layer was generalized from `1≤a≤p-1` to `~ p∣a`
  (`fermat_gen`). Gauss's-lemma proof of Gauss's reciprocity, machine-checked with **zero axioms** —
  a landmark classical theorem, resting on Fermat/`sqrt1`/order machinery (bricks 1–2), the
  Eisenstein floor identity (brick 3), and a pure lattice-point double-count (brick 4). Closed under
  the global context. The **two supplements** are also proved (`first_supplement`,
  `second_supplement`): `(-1/p) = legendre p (p-1) = (-1)^((p-1)/2)` (Euler's criterion + `-1 ≡ p-1`,
  via `Zpow_mod_cong`); and `(2/p) = (-1)^((p²-1)/8)` (Gauss's lemma at `a=2`: the count `mu p 2 =
  (p-1)/2 − ((p-1)/2)/2` (`mu_two`) has the same parity as `(p²-1)/8 = h(h+1)/2` (`parity_h`, via the
  `2x mod 4` / `mod 4` bridge)). All axiom-free — quadratic reciprocity and both supplements are
  complete.
- **Euclid: infinitely many primes** `EuclidPrimes.euclid_primes` (**axiom-free**, Dirichlet brick 1):
  for every `m` there is a prime `p > m`. Classic argument over `nat`: `m! + 1` has a prime divisor
  `p` (`nat_prime_divisor`, via `has_prime_divisor` + the `Z`↔`nat` bridge `Zdiv_nat`); if `p ≤ m`
  then `p | m!` (`divide_fact`) and `p | m!+1`, so `p | 1` (`Nat.divide_sub_r`), absurd. The
  foundation for the arithmetic-progression results. Closed under the global context.
- **The order lemma → primes ≡ 1 (mod n)** `OrderPrimeMod.order_prime_mod` (**axiom-free**,
  Dirichlet brick 2): if a prime `q` divides `a^n − 1` but divides **no** `a^d − 1` for any proper
  divisor `d | n` (`d < n`), then the multiplicative order of `a` mod `q` is exactly `n`, hence
  `n | q − 1`, i.e. `q ≡ 1 (mod n)`. Proof reduces `a` to `r = a mod q ∈ [1,q−1]` (`~q∣a`), turns
  `q | x−1` into `x ≡ 1 (mod q)` (`dvd_pred_iff`), so `q | a^k−1 ↔ pw q r k = 1` (`pw_a_pow`,
  base-invariance of the residue power); then `ord_divides` forces `ord q r | n`, `ord_period` +
  the "no proper divisor" hypothesis rules out `ord q r < n`, so `ord q r = n`, and `ord_div_pm1`
  gives `n | q−1`. The arithmetic core of "infinitely many primes ≡ 1 (mod n)"; the remaining piece
  is a cyclotomic `Φ_n` supplying, for each `n`, an integer with a primitive prime divisor.
- **Integer polynomials ℤ[X]** `IntPoly` (**axiom-free**, Dirichlet brick 3a — cyclotomic
  foundation): polynomials as `list Z` (low degree first), with the **evaluation homomorphism** —
  `eval` commutes with `padd` (`eval_add`), `pscale` (`eval_scale`), `pmul` (`eval_mul`) and sends
  `pmonom n` to `X^n` (`eval_monom`). Semantic divisibility `pdivides p q := ∃r, ∀x, eval q x =
  eval p x · eval r x` (reflexive, transitive). Delivers the **geometric divisibility**
  `Xn1_dvd : m | n → pdivides (X^m−1) (X^n−1)` with an **explicit integer cofactor** `geo m k =
  1 + X^m + ⋯ + X^{(k−1)m}` (via the telescoping `(X^m−1)·geo m k = X^{mk}−1`, `geo_telescope`),
  and its evaluated form `Xn1_dvd_val : m | n → (a^m−1 | a^n−1)` in ℤ. This is the reusable base the
  cyclotomic `Φ_n` and the product identity `∏_{d|n} Φ_d = X^n−1` will be built on. Closed under the
  global context.
- **Dirichlet, the case n = 4** `DirichletMod4.dirichlet_1_mod_4` (**axiom-free**): a genuine
  arithmetic-progression theorem — **infinitely many primes ≡ 1 (mod 4)**: for every `m` there is a
  prime `q > m` with `q mod 4 = 1`. Fully elementary via `x²+1` and the order lemma: set `a = 2·m!`,
  `N = a²+1`; a prime divisor `q` of `N` (from `EuclidPrimes.nat_prime_divisor`) is `> m` (else
  `q | m! | a` and `q | a²+1` give `q | 1`), odd (`N` is odd as `a` is even), divides `a⁴−1 =
  (a²+1)(a²−1)`, and divides neither `a`, `a²−1`, nor `a−1` (each would force `q | 2`, so `q = 2`).
  Hence `order_prime_mod` makes `ord_q(a) = 4`, so `4 | q−1`, i.e. `q ≡ 1 (mod 4)`. The first
  complete Dirichlet-type theorem here (the general-`n` version awaits the cyclotomic `Φ_n`). Closed
  under the global context.
- **Monic division in ℤ[X]** `PolyDiv.monic_div` (**axiom-free**, Dirichlet brick 3b — cyclotomic
  foundation): Euclidean division by a MONIC polynomial — for any `f` and any monic `g` of degree
  `d ≥ 1` there are integer polynomials `q, r` with `∀x, eval f x = eval q x · eval g x + eval r x`
  and `degle r (d−1)` (degree of `r` below `d`). Coefficients stay in ℤ precisely because `g` is
  monic: each step subtracts `(lead f)·X^k·g`, cancelling the top term with **no coefficient
  division** (`monic_div_aux`, by induction on a degree bound of `f`; the cancellation uses only
  `coeff` of `padd`/`pscale`/`pshiftk`, never the full multiplication convolution). Supporting layer:
  `coeff` (i-th coefficient), the operations `pneg`/`psub`/`pshiftk` with their `eval` and `coeff`
  laws, the degree-bound predicate `degle`, and `monic g d := coeff g d = 1 ∧ degle g d`. This is the
  primitive that will define `Φ_n` as the exact quotient of `X^n−1` by `∏_{d|n,d<n} Φ_d` and feed the
  squarefreeness/gcd arguments for `∏_{d|n} Φ_d = X^n−1`. Closed under the global context.
- **r₂ as a ℤ[i] norm-count** `GaussianNormCount.r2_as_gnorm` (**axiom-free**): the bridge
  `r₂(n) = #{ z ∈ ℤ[i] : N(z) = n }` — R2Count's lattice-point count re-read in ℤ[i] under
  `(a,b) ↔ a+bi` (via `length_filter_map` + the definitional match of the two boxes). This is the
  foundation for counting norm-`n` elements through unique factorisation, the last conceptual step to
  the general Jacobi identity `r₂(n)=4·S(n)`. Closed under the global context. **Next (the payoff):**
  count norm-`n` elements via the Gaussian factorisation — `r₂` multiplicative on coprimes and the
  prime-power counts (`r₂(2^k)=4`, `r₂(p^k)=4(k+1)` for `p≡1`, `4·[k even]` for `p≡3`) — then combine
  with `JacobiRHS` (`S` multiplicative + prime powers) for `r₂(n)=4·S(n)`.
- **ℤ[i] prime-power count machinery** `GaussianPrimePowerCount` (part 1, **axiom-free**): the shared
  base for the three prime-power values `r₂(2^k)=4`, `r₂(p^k)=4(k+1)` (`p≡1`), `4·[k even]` (`p≡3`).
  Gaussian powers `ZIpow` with `N(a^m)=(N a)^m` (`ZIpow_norm`) and nonzero (`ZIpow_nonzero`);
  extraction of an irreducible factor `irr_factor_exists` (head of the nonempty `factor_exists`
  list); and **prime-power divisibility** `prime_pow_dvd` (`π` irreducible, `π | a^m ⇒ π | a`, by
  induction via Euclid's lemma, `π ∤ unit`). These pin down the Gaussian-prime structure of a
  norm-`p^k` element, the reusable core of all three counts. Closed under the global context.
  **Next:** the case decompositions + `NoDup_Permutation` counts (`p=2`/`p≡3` first, then split
  `p≡1`).
- **ℤ[i] norm-`p^k` decompositions** `R2PrimePower.decomp_p3` / `decomp_p2` (Milestone A structural
  half, **axiom-free**): for the single-prime-family cases, every norm-`p^k` Gaussian integer is a
  unit times a power of the prime over `p`. **`p≡3 (4)` (inert)**: `N(z)=p^k ⇒ z = u·(ZtoZI p)^j`
  with `k=2j` (so `k` must be even). **`p=2` (ramified)**: `N(z)=2^k ⇒ z = u·(1+i)^k`. Both by strong
  induction on `N(z)`: `z·conj z = (base)^k` (`z_conj_pow`), so any irreducible factor divides
  `(ZtoZI p)^k` — for `p≡3`, `prime_pow_dvd` + inertness makes it an associate of `ZtoZI p`; for
  `p=2`, `2 = (−i)(1+i)²` (`two_eq_sq`) routes it through `(1+i)²` to `(1+i)` — so the prime divides
  `z`, peel it off and recurse. Uses the associate helpers `irr_dvd_irr_assoc` (irreducible ∣
  irreducible ⇒ associate) and `assoc_dvd_r`. From these, the **prime-power counts**
  `R2PrimePower.r2_prime_power_2_3`: `r₂(2^k)=4` (`r2_2pow`) and `r₂(p^k)=4·[k even]` for `p≡3 (4)`
  (`r2_3pow`). Via the bridge `r₂(n)=#{N(z)=n}` (`r2_as_gnorm`), the norm-`p^k` elements are exactly
  the 4 associates `assoc4` of the base power (unit × base^j, `in_assoc4`); a `NoDup_Permutation`
  between the norm-filtered box (`gbox_NoDup`) and that 4-element list (or `[]` when `p≡3` and `k`
  odd, since the decomposition forces `k` even) gives the count. Closed under the global context.
  **Next (Milestone B):** the split case `p≡1 (4)` — `r₂(p^k)=4(k+1)` (two conjugate Gaussian-prime
  families `π₀,π̄₀`, `k+1` exponent splits × 4 units, distinctness via cancellation +
  `prime_pow_dvd`).
- **ℤ[i] split-prime non-associate + decomposition** `R2PrimePowerSplit` (Milestone B structural
  half, **axiom-free**): for `p≡1 (4)`, `p = a²+b² = q₀·q₁` with `q₀=a+bi`, `q₁=a−bi` its conjugate.
  **`q0_not_assoc_q1`**: `q₀` and `q₁` are *not* associates — checking the 4 unit multiples forces
  `b=0`/`a=0` (⇒ `p` a square, impossible by `prime_not_sq`) or `a=±b` (⇒ `p=2·square` even,
  impossible for odd `p`). **`decomp_p1`**: `N(z)=p^k ⇒ z = u·q₀^i·q₁^(k−i)` with `i≤k`, by strong
  induction on `N(z)` — `z·conj z = (q₀q₁)^k = q₀^k·q₁^k`, so an irreducible factor divides `q₀^k` or
  `q₁^k` (Euclid on the product), hence (via `prime_pow_dvd` + associate) equals `q₀` or `q₁`; peel
  it off and recurse. From these, the **split count** `r2_1pow`: `r₂(p^k)=4(k+1)` for `p≡1 (4)`. The
  `4(k+1)` norm-`p^k` elements `u·q₀^i·q₁^(k−i)` (`0≤i≤k`, `u` a unit) are all distinct
  (`base_distinct`): distinct exponents can't coincide even up to a unit, since `q₀^i·q₁^(k−i)` twist
  would force `q₀ | q₁^d` (`prime_pow_dvd`) hence `q₀ ~ q₁`, contradicting `q0_not_assoc_q1`. A
  `NoDup_Permutation` (`count_eq_list`) between the norm-filtered box and the explicit
  `list_prod`-of-`(exponent, unit)` list (`splitlist`, length `4(k+1)` via `length_list_prod`) gives
  the count. Closed under the global context. **All three prime-power counts are now proved**
  (`r2_2pow`, `r2_3pow`, `r2_1pow`); assembling the general `r₂(n)=4·S(n)` additionally needs
  `S_mult` + `r₂`-multiplicativity.
- **Sums of two squares — two pillars** `SumTwoSquares.sum_two_squares_pillars` (**axiom-free**):
  (1) **Brahmagupta–Fibonacci** `sum2_mul` — sums of two squares closed under multiplication,
  `(a²+b²)(c²+d²)=(ac−bd)²+(ad+bc)²`, proved as *exactly* Gaussian-norm multiplicativity
  (`ZInorm_mul`); (2) **`−1` a QR mod `p` for `p ≡ 1 (mod 4)`** `neg1_QR` — `∃x, x²+1 ≡ 0 (mod p)`,
  from the from-scratch cyclicity `units_cyclic` (`x=g^{(p−1)/4}`, its square a non-trivial root of
  `1`) + the sqrt-of-1 fact `sqrt1` (Euclid via `prime_mult_nat`). Both genuine theorems.
  These are the two *ingredients* of Fermat's `p ≡ 1 (mod 4) ⟹ p = a²+b²`, now assembled below.
  The global valuation-parity iff (deferred there) is now **completed** in `TwoSquaresFull` (below).
- **Fermat's two-square theorem** `FermatTwoSquares.fermat_two_squares` (**axiom-free**): every prime
  `p ≡ 1 (mod 4)` is a sum of two squares, `p = a²+b²` — a genuine classical theorem of number
  theory, reached entirely within the repo. Proof = **Euler's descent**: `neg1_QR` seeds `p ∣ x²+1`,
  `nearest_rep` reduces to `m·p = u²+1` with `0<m<p`, and `descent_step` uses Brahmagupta–Fibonacci
  (`sum2_mul`, `ring`) + cancellation (`Z.mul_reg_l`) to produce `r·p = A²+B²` with `0<r<m`
  (`r≠0` since else `m∣p`, barred by `prime_divisors` for `1<m<p`); `descent_fuel` iterates the
  decreasing `m` (induction on `Z.to_nat m`) to `m=1`. Built on the from-scratch cyclicity tower +
  the Gaussian-integer bridge; no external axioms. `Print Assumptions` = Closed under the global
  context.
- **Two-square converse + characterisation engine** `SumTwoSquaresConverse.two_squares_characterisation`
  (**axiom-free**): `neg1_not_QR` — `−1` is *not* a QR mod a prime `q ≡ 3 (mod 4)` (mirror of
  `neg1_QR`, from the order theory: an `x²≡−1` has order 4 ⟹ `4∣q−1`); the **obstruction**
  `prime3_obstruction` — `q ≡ 3 (mod 4)` prime, `q ∣ a²+b²` ⟹ `q∣a ∧ q∣b` (Bezout + `neg1_not_QR_Z`);
  the **necessity engine** `prime3_descent` — such a `q` divides a sum of two squares to an even power
  (`q²∣n`, `n/q²` still sum2); and the **sufficiency blocks** (`2`, squares, products via `sum2_mul`,
  primes `≡1 mod4` via Fermat). All genuine theorems, both directions of the classical
  characterisation. **Boundary (now lifted):** the global valuation-parity *iff* is completed in
  `TwoSquaresFull` (next).
- **FULL two-square characterisation** `TwoSquaresFull.two_squares_iff` (**axiom-free**): for `n>0`,
  `sum2 n ↔ (∀ prime q ≡ 3 (mod 4), even q-valuation of n)` — the complete classical Fermat–Euler
  theorem. Both directions by strong induction (`Z.lt_wf`): necessity via `prime3_descent` +
  `pow_split2` + `even_shift2`; sufficiency via `has_prime_divisor` + `padic_val` + `q3even_transfer`
  (Euler hypothesis carried to the cofactor by Euclid `prime_mult`/`prime_ndvd_pow`) + `prime_mod4`
  case split (`sum2_2` / Fermat `sum2_prime1` / even-power `sum2_sq`) + `sum2_mul`. Uses only
  **per-prime** coprimality/cancellation — *not* a general valuation-additivity theorem (which was
  declined). `Print Assumptions` = Closed under the global context. A genuine classical number-theory
  theorem, machine-checked with zero axioms. **Not done:** a reusable valuation function, or `n=0`.
  (Counting representations is now started in `R2Count`, below.)
- **Counting two-square representations `r₂(n)`** `R2Count.two_squares_count` (**axiom-free**): defines
  `r₂(n) = #{(a,b)∈ℤ² : a²+b²=n}` as a decidable bounded count (`filter` over the box
  `[−⌊√n⌋,⌊√n⌋]²`, since a representation forces `|a|,|b| ≤ √n`), and proves two structural facts.
  **(1) Positivity ↔ representability:** `r₂(n) > 0 ↔ sum2 n`, hence by `two_squares_iff`, for `n>0`,
  `r₂(n) > 0 ↔ q3even n` — the full arithmetic test for when the count is nonzero.
  **(2) The factor of 4 in Jacobi:** `4 | r₂(n)` for `n>0`, proved directly — the Gaussian-unit
  rotation `(a,b) ↦ (−b,a)` (mult by `i`) is a **fixed-point-free order-4** action on the solution set
  (general lemma `div4_of_free_order4`: a `NoDup` list closed under such an `f` has length divisible by
  4, by orbit removal via strong induction). Everything is over ℤ/ℕ/lists — no Reals — so `Print
  Assumptions` = Closed under the global context. **Not done:** the full Jacobi count
  `r₂(n) = 4(d₁(n)−d₃(n))` (a deeper theta/Gaussian-integer result) — its RHS is built in
  `JacobiRHS` (below).
- **Jacobi's formula — the RHS** `JacobiRHS.jacobi_rhs` (**axiom-free**): builds the right-hand side of
  `r₂(n) = 4·Σ_{d|n} χ₄(d)` and checks the identity reflectively. Defines `χ₄` (the nontrivial
  character mod 4, `+1/−1/0`) and proves it **completely multiplicative** (`chi4_mul`, 16-case mod-4
  analysis); the divisor sum `S(n) = Σ_{d|n} χ₄(d)` (over `Totient.divisors`) equals `d₁(n)−d₃(n)`
  (`S_as_d1d3`); and the **prime-power values** `S(2^k)=1`, `S(p^k)=k+1` for `p≡1 (4)`, `S(p^k)=[k even]`
  for `p≡3 (4)` (`S_prime_pow_*`, via `divisors_prime_pow`: divisors of `p^k` are exactly `p^0…p^k`,
  proved with a nat/ℤ divisibility bridge + `Nat.gauss`). The full identity `r₂(n) = 4·S(n)` is
  **verified by `vm_compute` for n ≤ 200** (`jacobi_upto`). `Print Assumptions` = Closed under the
  global context. `S` is also proved **multiplicative on coprimes** (`S_mult`): `gcd(m,n)=1 ⇒
  S(mn)=S(m)·S(n)`, via the divisor-product permutation `divisors(mn) ~ {a·b : a|m, b|n}`
  (`divisors_mul_perm`, a `NoDup_Permutation` — existence of the split from `Nat.divide_mul_split`,
  uniqueness from the coprime gcd identity `gcd(a·b,m)=a`, `gcd_prod_l`) plus the sum-over-product
  distributivity `fold_prod_mul` and `chi4_mul`. **Not done (deferred):** `S(n)>0 ↔ q3even n`, and the
  general `r₂(n)=4·S(n)` — the ℤ[i] unique-factorisation engine and all three prime-power counts now
  exist (`GaussianDivision`…`R2PrimePowerSplit`), so what remains is `r₂`-multiplicativity + a
  multiplicative-agreement assembly.
- **A number as a field — the triad `1/x, x, x^x` in `𝔽_p`** `FpField.Fp_field_triad`
  (**axiom-free**): the prime `p` makes `ℤ/pℤ` a field; the inverse is a power `1/x = x^{p−2} mod p`
  with `x·(1/x) ≡ 1` proved as `fermat` (`inv_correct`), self-power `x^x = pw p x x`, so the triad is
  `pw p x` at exponents `{p−2, 1, x}` (`triad_powers_of_x`). In discrete-log space (base a primitive
  root, `DirichletModP.dlog`) it is `{L·(p−2), L, x·L} mod p−1` — reciprocal = negation, self-power =
  scaling by `x` (`dlog_triad`), collapsing to `1` at `x=1` (`triad_collapse`). Genuine theorems,
  reusing the from-scratch cyclicity tower; the reused `dlog` lemmas are axiom-free so `Print
  Assumptions` = Closed under the global context.
- **Self-power dynamics `x ↦ x^x mod p`** `SelfPowerDynamics.self_power_dynamics` (**axiom-free**):
  the self-power map as a dynamical system on `𝔽_p*`. `selfpow_exp_reduce` — the careful
  base/exponent asymmetry `x^x mod p = pw p x (x mod (p−1))` (exponent reduces mod `p−1`, base stays
  `x`), giving `selfpow p (p−1) = 1`; `selfpow_unit` (stays on units); fixed points
  `selfpow_fixed_ord` (`x^x ≡ x ⟺ ord(x) ∣ (x−1)`, cancel a unit via `cancel_mod`); and the capstone
  **eventual periodicity** `orbit_eventually_periodic` via a newly-built constructive pigeonhole
  `orbit_collision` (`existsb` double-search + `NoDup_incl_length`: `p` iterates can't be distinct in
  `p−1` units) + `orbit_shift`. One step linearises in discrete-log space to scaling by `x`
  (`orbit_dlog_step`, from `FpField.dlog_triad`). **Honest scope:** no cycle-length count, no
  fixed-point uniqueness, no pre-period-tail analysis. `Print Assumptions` = Closed under the global
  context.
- **Counting self-power fixed points** `SelfPowerFixedCount.self_power_fixed_count` (**axiom-free**):
  `nfix p = #{x∈[1,p−1] : x^x ≡ x}` as a rigorous computable count (`length (filter …)`), with the
  set-characterisation `fixed_pts_ord` (`ord(x) ∣ (x−1)`), the universal **sandwich
  `1 ≤ nfix p ≤ p−2`** (odd p: `x=1` always fixed ⇒ `≥1`; `x=p−1` never fixed ⇒ `≤p−2`; pins
  `nfix 3 = 1`), and computed values `nfix ∈ {1,1,1,2}` for `p∈{2,3,5,7}` (`vm_compute`, capped at
  `p=7` by unary-`nat` `x^x`). **Analogy boundary:** `nfix p` is an *irregular* function — no
  closed-form or asymptotic is proved or claimed; the count beyond the bounds and small table is
  left open. `Print Assumptions` = Closed under the global context.
- **The "inessential ℝ", made precise** `AlgebraicOrthogonality.algebraic_orthogonality`
  (**axiom-free**): DFT/character orthogonality proved over an *abstract field* with an *abstract
  root of unity* (`apow w N = 1`) — `w^m=1 ⟹ Σ w^{km} = N·1`, `w^m≠1 ⟹ Σ = 0`, pure geometric
  series (`ageom`) + field cancellation. Zero axioms, no ℝ/ℂ/trig. A measured **axiom-footprint
  contrast** then pins where ℝ enters: the same vanishing law over our `ℂ` for an *abstract* root
  (`c_orth_vanish`) carries **2** axioms (field-of-ℝ, *not* the order axiom `sig_not_dec`); the
  *analytic* root `exp(2πi/N)` (`c_orth_w`, via `w_pow_N`) carries **3**. Conclusion: the quarantined
  ℝ-axioms of the entire character/DFT/Dirichlet layer are cosmetic — the orthogonality is axiom-free
  field algebra; ℝ enters solely through the analytic realisation of a concrete root of unity.
- **Euler's formula / circle group** `EulerFormula.euler_circle_group` (quarantined ℝ): `Cexp t =
  cos t + i·sin t` proved to be a group homomorphism `(ℝ,+) → (ℂ*,×)` onto the unit circle —
  `Cexp 0 = 1`, `Cexp(a+b)=Cexp a·Cexp b` (one identity = `cos_plus` **and** `sin_plus`),
  `|Cexp t|²=1`, `Cinv(Cexp t)=Cconj(Cexp t)=Cexp(−t)`, de Moivre `(Cexp t)ⁿ=Cexp(n·t)`, `Cexp 2π=1`,
  and `w N = Cexp(2π/N)` (with `w_pow_N` re-derived from Euler). This is the analytic backbone that
  *manufactures* the root of unity the axiom-free orthogonality (`AlgebraicOrthogonality`) consumes —
  the precise locus of the quarantined ℝ. Genuine theorem; classical Reals axioms (via cos/sin).
- **Gauss sum `|g(χ)|² = p`** `GaussSum.gauss_sum_abs` (quarantined ℝ): for a nonprincipal Dirichlet
  character `χ` mod a prime `p` and additive root `ζ = w p`, the Gauss sum `g(χ) = Σ χ(n)ζⁿ` has
  `g(χ)·conj g(χ) = p` — a genuine classical theorem (a complex character sum whose modulus² is the
  integer `p`), the marquee union of the analytic + number-theory threads. Proof (the arc's largest)
  uses the multiplicative reindex `a=(b·c) mod p` (`units_perm`), `dchar_mul` + `|χ|=1`, the geometric
  series of the `p`-th roots (`β(c)`, `sum_pow_eq_0`), and `Σχ=0` (`dirichlet_orthogonality`). Only the
  3 classical-ℝ axioms — and by `AlgebraicOrthogonality` even that is confined to the analytic root.
  **Analogy boundary:** the *value/sign* of `g(χ)` (the deep Gauss-sign theorem) and non-prime moduli
  are not done.
- **Quadratic Gauss sum `g² = χ(−1)·p`** `QuadraticGaussSum.quadratic_gauss_sum_sq` (quarantined ℝ):
  for an *odd* prime `p` and the order-2 (Legendre) character `χ = dchar p g ((p−1)/2)`, the Gauss sum
  squares to `χ(−1)·p`, and since `χ(−1) = ±1`, `g² = +p` or `−p`. Builds directly on `GaussSum`: the
  already-proved `|g|² = g·conj g = p` (`gauss_abs`) plus the *reflection* `conj g = χ(−1)·g`
  (`gauss_conj_chi`), which holds because the quadratic character is **real-valued** (`chi_real`, via
  `w(p−1)^{2·a₀·k} = 1` for `2a₀ = p−1`). Then `p = g·conj g = χ(−1)·g²`. The reflection uses the
  reindex `b ↦ (p−1)·b mod p` (`Sf_reindex_mul`) and `wc_p^{(p−1)x mod p} = w_p^x` (inverse-of-root,
  `wc_reindex`). Uses the same quarantined classical-ℝ axioms as the character layer. **Not done:** the
  *sign* `χ(−1) = (−1)^((p−1)/2)` (needs `g^((p−1)/2) ≡ −1`), i.e. `+p` for `p≡1 (4)` vs `−p` for
  `p≡3 (4)`.
- **Dirichlet kernel** `DirichletKernel.dirichlet_kernel_thm` (quarantined ℝ): the Fourier-convergence
  kernel `D_n(t) = Σ_{k=−n}^n e^{ikt}`, two faces. Real closed form `dirichlet_kernel`:
  `(1+2Σ_{k=1}^n cos kt)·sin(t/2) = sin((n+½)t)` (telescoping `2cosA sinB = sin(A+B)−sin(A−B)`),
  division-free, and the divided corollary. Complex skeleton `dk_geom`:
  `(Cexp t−1)·DK n t = Cexp(−nt)·(Cexp(t)^{2n+1}−1)` = `geom_sum` via `EulerFormula.Cexp`. Genuine
  theorem; classical Reals axioms (via cos/sin). (The real↔complex identification `DK = RtoC(Dsum)`
  — a symmetric-pair Csum reindex — is not spelled out; both faces are proved independently.)
- **Chebyshev polynomials** `ChebyshevPoly.chebyshev_poly` (quarantined ℝ): `Tₙ` of the first kind
  (recurrence `T_{n+2}=2x·T_{n+1}−Tₙ`, `T₂=2x²−1`, `T₃=4x³−3x`) with the defining identity
  `Tcheb_cos : Tₙ(cos t)=cos(nt)` (two-step induction, cosine recurrence via product-to-sum), the de
  Moivre link `Tcheb_Re : Tₙ(cos t)=Re((Cexp t)ⁿ)`, `Tₙ(1)=1`, and the `n` roots at `cos((2k+1)π/2n)`
  (`cos_odd_pihalf`). Genuine theorem; classical Reals axioms (via cos/sin). Distinct from the
  number-theoretic `Chebyshev.v` (ψ function).
- **N-th roots of unity + DFT orthogonality** `RootsOfUnity` (`w_pow_N`, `w_primitive`,
  `dft_orthogonality_delta`): in the custom `C`, `w N = exp(2πi/N)` with `(w N)ᴺ = 1` (De Moivre),
  and the character sum `Σ_{k<N} (w N)^{jk} = N` (if `(w N)ʲ=1`) or `0` — the complex-DFT
  orthogonality, general-`N` cousin of `WalshHadamard.H²=8I`. The vanishing branch is pure
  `C`-field algebra (geometric series + `aᴺ=1`); trig enters only for `(w N)ᴺ=1`.
  **Primitivity is proved** (`w_primitive`: `(w N)ʲ ≠ 1` for `0<j<N`, from `cos(2πj/N) < 1`
  strictly — `cos_lt_1` via `cos x = 1−2sin²(x/2)`), so orthogonality holds in the
  **unconditional Kronecker-delta form** `dft_orthogonality_delta`: for `j < N`, `Σ = N·[j=0]`
  — the exact input for ℂ-DFT inversion `F⁻¹F = id`. Quarantined Reals axioms (via `C`/trig).
- **Complex DFT inversion** `DFTInversion.dft_inversion`: on the custom `C`, `IDFT (DFT f) k = f k`
  (`k < N`) with `(DFT f) m = Σ_{k<N} f k·(wc N)^{mk}`, `(IDFT g) k = (1/N)Σ_{m<N} g m·(w N)^{mk}`,
  `wc N = conj(w N)` — the finite Fourier transform on `ℂ` is invertible (`F⁻¹F = id`), the ℂ
  analogue of `WalshHadamard.H²=8I`. Engine: two-index orthogonality `orthogonality_2` (off-diagonal
  vanishing from injectivity `w_pow_inj`, i.e. primitivity) + finite Fubini (`Csum_swap`) + delta
  extraction (`Csum_delta`) — all pure `C`-field algebra. Quarantined Reals axioms (via `C`/trig).
- **DFT convolution theorem** `DFTConvolution.conv_theorem`: the DFT diagonalises cyclic
  convolution — `DFT (f⋆g) m = DFT f m · DFT g m` for `(f⋆g)(n)=Σ_{k<N} f k·g((n−k) mod N)`.
  New ingredient: a cyclic shift permutes `{0..N−1}` (`rotation_perm` via `NoDup_Permutation_bis`
  + shift injectivity) ⟹ reindexing `Csum_reindex`; with root periodicity `Cpow_wc_mod` it gives
  the shift theorem `dft_shift`, then finite Fubini (`Csum_swap`) finishes. With `DFTInversion`
  this is the full finite-Fourier toolkit on `C`. Quarantined Reals axioms (via `C`/trig).
- **Parseval / Plancherel** `Parseval` (`plancherel`, `parseval_norm`): the DFT is (up to `N`) an
  **isometry** — `Σ_k f k·conj(g k) = (1/N)Σ_m F̂_m·conj(Ĝ_m)`, and `Σ_k |f k|² = (1/N)Σ_m |F̂_m|²`.
  Same `orthogonality_2` + Fubini + delta engine as inversion, plus conjugation commuting with the
  transform (`conj_wc_pow`). Completes finite Fourier analysis on `C` (inversion + convolution +
  isometry). Quarantined Reals axioms (via `C`/trig).
- **Characters of ℤ/Nℤ** `CharactersModN` (`characters_of_Z_mod_N`): `χ_a(n)=(w N)^{an}` are the
  characters of the cyclic group `(ℤ/Nℤ,+)`, forming the dual group `ℤ/Nℤ` (`chi_add`, `chi_mul`,
  `chi_pow_N`), with **both orthogonality relations** of the character table (`char_orthogonality_row/col`:
  `Σ χ_a conj(χ_b) = N·[a=b]`) — the DFT orthogonality in character language. **Honest ceiling:**
  these are characters of the *cyclic* group `ℤ/Nℤ`, the abelian orthogonality underlying Dirichlet
  characters; a Dirichlet char mod `N` is a character of the *multiplicative* `(ℤ/Nℤ)*` — cyclic
  ⟹ these via a primitive root, but `(ℤ/Nℤ)*`, primitivity, and L-series are NOT built.
  Quarantined Reals axioms (via `C`/trig).
- **Units mod p + Fermat** `ZmodPStar` (Phase 1 of the actual-Dirichlet-mod-p build):
  `fermat : 1≤a≤p−1 ⟹ a^{p−1} mod p = 1` — **axiom-free**. Units group `(ℤ/pℤ)*` closure
  (`mulmod_in_units`), cancellation (`cancel_mod` via `Gauss`), and Fermat via the
  units-permutation product argument (`units_perm`, `Pi_coprime`). `nat`↔`ℤ` primality bridged
  through `mod` (`prime_mult_nat`, `Zof_nat_divide_inv`). Foundation for the from-scratch
  primitive-root / Dirichlet build (now COMPLETE, Phases 1–5).
- **Euler totient + divisor sum** `Totient` (Phase 2): `totient_divisor_sum : Σ_{d∣n} φ(d) = n`
  — **axiom-free**. Partition of `[1,n]` by `n/gcd(k,n)` into `φ`-sized fibers
  (`count_key_eq_phi` via a membership-`Permutation`, `disjoint_filter_sum`). Counting input for
  the order-counting primitive-root proof (Phase 4).
- **Roots bound over 𝔽_p** `PolyRootsFp` (Phase 3): `dth_roots_bound : #{a∈[1,p−1] : a^d mod p = 1}
  ≤ d` — **axiom-free**. Minimal polynomial theory over `ℤ` + synthetic division (`sdiv`) + factor
  theorem (`factor_mod`) + Lagrange bound `roots_le` (strong induction on degree, `𝔽_p` an
  integral domain via `prime_mult`, `NoDup_incl_length`), instantiated at `X^d−1`. The
  field-theoretic input for the order-counting primitive-root proof (Phase 4).
- **Multiplicative order mod p** `ZmodOrder` (Phase 4a): `ord p a` (least positive period),
  with `ord_least`, `ord_divides`, `ord_div_pm1` (via Fermat), `pow_inj_below` (powers below the
  order are distinct). **Axiom-free.** Foundation for the order-counting primitive-root proof;
  the counting/squeeze (`ψ(d)≤φ(d)`, `Σψ=Σφ=p−1 ⟹ ∃` primitive root) is Phase 4b.
- **(ℤ/pℤ)\* is cyclic** `PrimitiveRoot.units_cyclic` (Phase 4b): for prime `p`, `∃ g, ord p g = p−1`
  (a primitive root) — proven from scratch, unconditionally, **axiom-free**. Order-counting:
  `psi_le_phi` (`ψ(d)≤φ(d)` via surjectivity-onto-roots `root_is_power` + `gcd_of_order`),
  `sum_psi` (`Σψ=p−1`), squeeze against `Totient.totient_divisor_sum` (`Σφ=p−1`) ⟹ `ψ=φ` ⟹
  `ψ(p−1)=φ(p−1)≥1`. This is the genuine cyclicity theorem the whole Dirichlet arc rests on;
  every ingredient axiom-free. Feeds the Dirichlet-character construction (Phase 5).
- **Dirichlet characters mod p + orthogonality** `DirichletModP.dirichlet_characters_mod_p` (Phase 5):
  genuine Dirichlet characters `χ_a` mod a prime `p` (via discrete log base a primitive root:
  `χ_a(n) = (w(p−1))^{a·dlog n}` on units, 0 on multiples of `p`) with `χ_a(1)=1`, period `p`,
  vanishing on multiples, and the orthogonality `Σ_{n<p} χ_a(n)conj(χ_b(n)) = (p−1)[a=b]` —
  reindexing units→exponents (`powers_units_perm`) onto `CharactersModN.char_orthogonality_row`
  (`N=p−1`). Quarantined Reals axioms (via `C`/trig). **Completes the 5-phase from-scratch
  Dirichlet-mod-p build**: the number-theory core (Phases 1–4b, `(ℤ/pℤ)*` cyclic) is axiom-free;
  only Phase 5's `ℂ`/trig is quarantined.
- **Finite Dirichlet L-function / Euler product** `DirichletLEuler.dirichlet_L_function`: the genuine
  theorem-content is **complete multiplicativity** of the character — `dchar_mul` (`χ(mn)=χ(m)χ(n)`)
  and `dchar_pow` (`χ(qᵏ)=χ(q)ᵏ`), proved from scratch via the discrete-log homomorphism
  `dlog_mul` (`dlog(uv)≡dlog u+dlog v mod (p−1)`, from `pw_mod` + `pow_inj_below`); this closes the
  "complete multiplicativity" bullet `DirichletModP` had only advertised. Plus the local Euler factor
  `local_euler_factor` (`(1−χ(q)x)·Σ_{k<K}χ(qᵏ)xᵏ = 1−(χ(q)x)^K`, genuine geometric closed form) and
  the finite Euler product `dirichlet_L_euler_product` (`PrimonGas` state-sum machinery ported to `C`
  as `euler_product_C`, at character-twisted fugacities: `Σ_states ∏_q(χ(q)x_q)^{k_q} = ∏_q Llocal_q`).
  **Analogy boundary, stated honestly:** the *finite* Euler product = product of local factors is
  proved; `L(s,χ)=∏(1−χ(q)q⁻ˢ)⁻¹=Σχ(n)n⁻ˢ` as an *infinite* product/series (needing the
  state↔integer unique-factorisation bijection and convergence) stays prose. Quarantined Reals axioms
  (via `C`/trig).
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
- **The 3-symbol algebra `{I,N,F}`** `INFMonoid`: a genuine theorem identifying it as the
  commutative monoid `({+1,−1,0},×) = (𝔽₃,×)` (via an injective hom `val`) whose unit group is
  the Walsh sign group `Z/2 = {I,N}`, and — via `sym_of_mu` — **exactly the value-monoid of the
  Möbius function on prime powers** (`MobiusReciprocal.mu_pp`), `F` = the squarefree collapse.
  Axiom-free. (Honest: this is a proved structural *identification*/bridge between the two arcs,
  not a claim beyond it.) `INFProduct` inducts it to `n` observers: the `n`-fold monoid
  `({I,N,F})ⁿ` (`op_n` commutative monoid) with product-sign `val_n`, proving the homomorphism
  `val_n_op`, the free-split `val_n_app` (`val_n (a++b) = val_n a·val_n b` — arbitrary
  observer/observed partition), the one-`F` veto `val_n_zero_iff` (`val_n l = 0 ⟺ In F l`), and
  `val_n_mu` (= `μ` of a product of `n` prime-powers). "Observer" stays an *interpretation* of a
  coordinate/prime; the theorems are about the product monoid. Axiom-free.
- **Hermitian operator on the observer/observed/observation triad** `ObserverTriad`: a genuine
  self-adjoint (Hermitian-over-ℝ = symmetric) operator `M` with real spectrum `{0,+√2,−√2}` and
  an orthogonal eigenbasis (`M_self_adjoint`, `eig_*`, `ortho_*`), the eigenvalue-0 mode being
  the observer−observed kernel. Axiom-quarantined (ℝ). Honest: the role names are
  interpretation; the theorems are about the symmetric operator. `ObserverSwap` adds the
  involution cousin — the observer↔observed swap `S` (self-adjoint + `S²=I`, spectrum `{+1,−1}`)
  realising the unit group `{I,N}` of `INFMonoid` (`IZR(val N)=−1`, `IZR(val I)=+1`), with `v0`
  simultaneously `M`'s kernel and `S`'s `−1` mode, plus the reflection residue decomposition.
  `ObserverSpectral` shows `M` and `S` are **commuting observables** (`[M,S]=0`) simultaneously
  diagonalized by `{v0,vp,vm}` — the finite spectral picture of simultaneously-measurable
  observables (`v0` = `(0,−1)`, `vp/vm` = `(±√2,+1)`). Axiom-quarantined; role names interpretation.
- **Finite Fourier + sampling** `WalshHadamard` (DFT on `F₂ⁿ`: shift, convolution, `H²=8I`
  inversion, Parseval), `WalshSampling` (the finite Shannon–Nyquist sampling theorem: comb
  transform `Ĥ 1_H = |H| 1_{H⊥}`, Poisson summation, band-limited reconstruction), and
  `WalshUncertainty` (the **Donoho–Stark discrete uncertainty principle**: `f≠0 ⟹
  |supp f|·|supp Ĥf| ≥ 8 = |F₂³|` — the l¹/l∞ argument done entirely over `ℤ`, the complement
  to sampling: it bounds *why* you cannot localize in space and frequency at once): all **genuine
  theorems** about the actual transform (axiom-free). The *bridge* framing — Poisson summation as
  the shadow of `ζ`'s functional equation, and Fourier/sampling inversion as the finite instance
  of Perron's contour inversion (cousin: `PosetMobiusFTC` = Möbius inversion) — is honest
  **lineage/shared-structure**, **not** a formalized `Ĥ → ζ` theorem (which needs the contour).

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
  remains for `ψ(x)≍x` is the **final squeeze**. Its **combinatorial building blocks are now
  built** (`Chebyshev`): `Lam_nonneg` (`Λ≥0`), the floor lemma `floor_half_step`
  (`⌊N/d⌋−2⌊N/(2d)⌋=(⌊N/d⌋)mod 2∈{0,1}`), and `ψ`. These give (via `order_swap_identity`) the
  sandwich `ψ(N)−ψ(⌊N/2⌋) ≤ D(N) ≤ ψ(N)` with `D(N)=T(N)−2T(⌊N/2⌋)=Σ_d Λ(d)·((⌊N/d⌋)mod 2)`,
  reducing `ψ≍x` to the single **numerical input** `D(N)≈N·log 2`. The **factorial–log bridge
  is now built** (`Chebyshev.Tlog_eq_ln_fact`: `T(N)=Σ_{n≤N}log n = log(N!)`), so
  `D(N)=log(N!/(⌊N/2⌋!)²)=log C(2M,M)`. The remaining `ψ≍x` pieces (a dedicated ~pass): the
  **binomial↔factorial** identity `C(n,k)·k!·(n−k)! = n!`, the **row sum** `Σ_k C(n,k)=2^n`
  (generalizing `BitDensity.cube3_total`), **unimodality** `C(2M,M) = max_k C(2M,k)` ⟹
  `4^M/(2M+1) ≤ C(2M,M) ≤ 4^M`, the reformulation `D=Σ_d Λ(d)·((⌊N/d⌋)mod 2)` (order-swap +
  range extend), and the `T(N)−2T(⌊N/2⌋)` telescoping. **Hard ceiling:** the *sharp* `ψ(x)∼x` (PNT), the explicit
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
