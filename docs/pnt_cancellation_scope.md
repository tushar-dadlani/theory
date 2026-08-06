# Scoping the PNT cancellation (the one remaining gap)

Everything *structural* on the road to elementary PNT is machine-checked and
axiom-clean. What remains is a single analytic fact — the **cancellation** —
in four equivalent forms. This note scopes exactly what it is, what is already
proven, which sub-lemmas a completion needs, and which of those are buildable
now versus genuinely research-hard.

## 0. The statement (four equivalent forms)

Let `R(x) = ψ(x) − x`, `M(x) = Σ_{n≤x} μ(n)` (Mertens), `L(x) = Σ_{n≤x} λ(n)`
(Liouville). The cancellation is any one of:

| form | statement | repo name |
|------|-----------|-----------|
| PNT | `ψ(x) ~ x` (⟺ `θ~x` ⟺ `π ~ x/ln x`) | goal |
| Selberg | `α := limsup |R(x)|/x = 0` (⟺ `Un_cv Vrem 0`) | `Vrem`, `SelbergPin` |
| Mertens | `M(x) = o(x)` | — (μ exists) |
| Liouville | `L(x) = o(x)` (⟺ `liouville_pnt_lam`) | `LiouvilleConcrete` |

All four are equivalent, and each equivalence is itself elementary (no new
"hard" content) — see §4. So there is exactly **one** hard theorem, appearing
in four costumes. The parity heuristic explains why: sieve/multiplicative
structure cannot see it (that structure is exactly what we *did* finish).

## 1. What is already machine-checked (the reduction)

The chain from `α = 0` up to PNT is DONE and axiom-clean:

- `PsiAsymp.psi_asymp_cv : Un_cv Vrem 0 -> Un_cv (fun N => ψ N / N) 1`.
  So **`α = 0` ⟹ PNT** is closed. Also `Vrem_cv0`, `Vrem_bound_all`
  (Chebyshev gives `Vrem ≤ Kup−1`, i.e. `α < ∞`, in fact `α < 1`).
- The Selberg engine (all axiom-clean):
  - `SelbergMainTerm.lam2_sum_bound : Σ_{n≤N} Λ₂(n) = 2N ln N + O(N)`
    (the symmetry formula — the elementary prime-mass budget).
  - `SelbergAverageSigned.selberg_average_signed`: the **signed** degree-1
    identity `R(x) ln x + Σ_{n≤x} Λ(n) R(x/n) = O(x)`.
  - `StarInequality.star_inequality`: the degree-2 `|R|`-inequality;
    `SmoothingLemma.lam2_over_n_bound : Σ Λ₂(n)/n = ln²x + O(ln x)`.
- The signed extremes (axiom-clean):
  - `SelbergPin.signed_pin : is_limsup Vsig V -> is_liminf Vsig v ->
    is_limsup Vrem α -> 0 < α -> V = α /\ v = −α`.
    So if `α > 0`, `R/x` reaches **both** `+α` and `−α` infinitely often
    (`sign_oscillation`): full-amplitude oscillation is forced.
  - `LimSup`/`LimInf`/`sum_upper` interfaces.

**Net:** the problem is reduced to proving `α = 0`, with the symmetry budget,
the signed identity, and the forced full-amplitude oscillation all in hand.
The remaining gap is the **self-improvement** `α > 0 ⟹ contradiction`.

## 2. Route A — the elementary Selberg–Erdős completion

This is the route the repo is built for. `α = 0` factors into three
sub-lemmas.

### S1 — signed degree-2 identity  (ATTEMPTED — UNSOUND as scoped)

The hoped-for clean form
```
Vsig(N) ln²N + Σ_{n≤N} (Λ₂(n)/n) Vsig(N/n) = O(ln N)
```
does NOT hold. Reason (verified by redoing the `StarInequality` derivation
with `Vsig` in place of `Vrem`): the `|·|` degree-2 `star_inequality` works
because iterating `selberg_average` gives
`Σ_d (Λd/d) Vrem(N/d) ln(N/d) ≤ +doublesum + C`, and the `−Σ (Λ ln n/n) Vrem`
from the log-gap expansion (`HLGT`) cancels the `−Σ (Λ ln n/n) Vrem` from
`star_reindex`. But the SIGNED iterate flips the sign of `doublesum`:
`selberg_average_signed` gives `Vsig(N/d) ln(N/d) = e(N/d) − Σ_e (Λe/e) Vsig(N/(de))`,
so `Σ_d (Λd/d) Vsig(N/d) ln(N/d) = Etot − doublesum`. Feeding this through the
same (sign-agnostic) `HLGT` and `star_reindex` yields
```
ln N · G(N) + Σ (Λ₂/n) Vsig(N/n) = Etot + 2·Σ (Λ ln n/n) Vsig(N/n) − E1
```
and the `Σ (Λ ln n/n) Vsig(N/n)` term does NOT cancel (it cancelled in the `≤`
version only because `doublesum` had the opposite sign there). That term is
`O(ln²N)` — degree-2 sized — so the identity above is `O(ln²N)`, not `O(ln N)`.

A valid signed degree-2 identity DOES exist, but with the useless weight
`Λ log − Λ∗Λ` instead of `Λ₂ = Λ log + Λ∗Λ`:
`Vsig(N) ln²N − Σ (Λ₂/n) Vsig + 2 Σ (Λ ln n/n) Vsig = O(ln N)`. It does not use
the `Σ Λ₂ = 2x ln x` budget and gives no degree-2 pin.

**Conclusion:** the cancellation that makes the degree-2 estimate work is
inherently ONE-SIDED (absolute values). Passing to signed quantities loses it.
This is the same phenomenon as the `avg_below` dead-end (§5): the sign
information at degree 2 is exactly what is hard. So S1 is NOT a buildable step;
it joins the recorded dead-ends. The degree-2 route does not linearize the
self-improvement.

### S2 — the oscillation-structure lemma  (THE WALL, research-hard)

This is the only genuinely hard step. It must show that full-amplitude
oscillation of `σ` is incompatible with the pinned symmetry budget. The
correct form is **global** (a prime-budget / sign-pattern argument), NOT a
local average — the local versions are provably false (§5). Concretely, the
Erdős–Selberg argument (Nathanson, *Elementary Methods*, Ch. 8, Thm 8.4–8.5;
Montgomery–Vaughan §8.2) factors as:

- **(a) Spacing.** A point `y` with `σ(y) ≈ +α` has `ψ(y) ≈ (1+α)y`; a later
  `y'` with `σ(y') ≈ −α` has `ψ(y') ≈ (1−α)y'`. Since `ψ` is nondecreasing,
  `(1−α)y' ≥ (1+α)y`, so `y'/y ≥ (1+α)/(1−α) > 1`: consecutive extremes are
  separated by a **fixed multiplicative gap**. Hence `≤ ln x / ln((1+α)/(1−α))`
  oscillations in `[1,x]`. (Uses `ψ` monotone + Chebyshev — repo has these.)
- **(b) Prime-budget accounting.** Maintaining amplitude `α` forces `ψ` to run
  alternately ahead of and behind `x` over each gap; the prime mass that pattern
  demands is constrained by the pinned `Σ Λ₂ = 2x ln x + O(x)`. Balancing local
  demand against the global budget yields a strict deficit. **(This is the
  crux and the novel formalization content.)**
- **(c) Contraction.** (a)+(b) give `α ≤ (1−c)·α` for an explicit `c>0`.

Status: needs faithful reconstruction from a reference *before* formalizing —
it is a multi-page case analysis with explicit constants, not a reduction to
existing tools. This is where "elementary PNT is hard" actually lives.

### S3 — iterate to zero  (easy, given S2)

`α ≤ (1−c)α` with `c>0` and `α ≥ 0` ⟹ `α = 0`. One-liner over the `LimSup`
interface. Then compose with `psi_asymp_cv` for PNT.

## 3. Route B — the analytic completion (alternative)

`PNT ⟺ ζ(1+it) ≠ 0`. This trades S2 for:

- **(i)** ζ continued to `Re = 1` (the repo has substantial ζ machinery:
  `ZetaFunctionalEq`, `CEulerProductZeta`, `DirichletMaster`, …).
- **(ii)** Non-vanishing on `Re = 1` via the 3–4–1 inequality
  `|ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ 1` (elementary once (i) holds).
- **(iii)** A Tauberian theorem (Wiener–Ikehara, or Newman's contour method —
  the shortest) turning `ζ ≠ 0` on `Re=1` into `ψ ~ x`.

Assessment: (ii) is short; (i) may be partly present; (iii) (the Tauberian
step, contour integration + the analytic `ψ↔ζ` dictionary) is a substantial
*separate* development. Route B is viable given the repo's complex analysis,
but it duplicates the Selberg reduction rather than completing it. Recommend
Route A unless (iii) turns out to be closer than expected.

## 4. The equivalences are cheap (no shortcut, but buildable glue)

- **Liouville ⟺ Mertens.** `λ = 1_□ ∗ μ`, i.e. `λ(n) = Σ_{d²|n} μ(n/d²)`,
  gives the **exact** identity
  ```
  L(x) = Σ_{d ≤ √x} M(x/d²).
  ```
  So `M(x)=o(x) ⟹ L(x)=o(x)` immediately (bound each `M(x/d²)=o(x/d²)`, sum
  `Σ 1/d²`). Buildable now (repo has `divisors`, `μ`, `mu_mult`, and now
  `lam_mult`): prove `λ = 1_□ ∗ μ` on prime powers via the multiplicative
  framework, then rearrange. This does NOT need the cancellation — it is a
  clean, axiom-clean piece connecting `LiouvilleConcrete` to Mertens.
- **Mertens ⟺ ψ.** `Λ = μ ∗ log` and `MobiusMertens.conv_swap` /
  `mob_mertens_one` are exactly the tools to convert an `M`-statement into a
  `ψ`-statement by partial summation. Both directions elementary (~a few
  hundred lines each); `conv_swap` is the load-bearing identity, already proven.

These let the four forms be used interchangeably in Coq. None removes the S2
wall — they relocate it.

## 5. Dead-ends (do NOT re-attempt — proven false/unsound here)

- `avg_below` / `dip_scales` (local `Λ`-weighted average dips below `α`):
  **FALSE**. The signed pin forces `Σ(Λ/n)|σ(x/n)| ≥ |σ(x)| ln x − O(1) ~ α ln x`
  at spikes — the `|·|`-average is pinned at `~α ln x`, no room to dip. The
  degree-2 (`Λ₂`) version is pinned the same way (S1 makes this rigorous).
  `PsiAsymp.pnt_of_avg_below` is a valid implication with an **unsatisfiable**
  premise.
- Range-average dip over `[y, y^K]` via zero-crossings: **UNSOUND**. Crossings
  are log-negligible (`|R|≲ln t` over log-length `o(1)`), and widening them
  needs fine slow-variation `ψ(m)−ψ(n) ≤ C(m−n)` = PNT-strength (repo only has
  the doubling bound `ψ(2n)−ψ(n) ≤ 2n ln 2 = O(n)`).

- **S1 — signed degree-2 identity with `Λ₂` weight (§2): UNSOUND.** The
  `Σ (Λ ln n/n) Vsig` term is degree-2 and does not cancel in the signed
  setting (it cancels only under the one-sided `|·|` inequality). Verified by
  redoing the `StarInequality` derivation with `Vsig`.

The lesson: any "bound `σ(x)` by a dipping *local* average" reduction silently
assumes PNT-strength, and the degree-2 cancellation is one-sided (lost when
passing to signed quantities). S2 must be the global budget argument.

## 6. Recommendation & buildable-now sub-targets

The single wall is **S2**. Everything else is done or mechanically buildable.
Concrete next steps, in increasing hardness:

1. **`L = Σ_{d≤x} [d²]·M(x/d)`** (§4, Liouville⟺Mertens forward). DONE, see
   `LiouvilleMobius.v` (`L_mertens`, built on the axiom-free `lam_eq_sq_conv_mu`
   `= 1_square ∗ mu`). Gives `M=o(x) ⟹ liouville_pnt_lam` for free.
2. ~~S1 (signed degree-2 identity)~~ — ATTEMPTED, UNSOUND (see §2, §5). The
   degree-2 cancellation is one-sided; the signed version keeps a degree-2
   `Λ log` term. Not a step.
3. **S2** only after reconstructing the exact spacing + budget + iteration from
   a named reference as a lemma-by-lemma spec with explicit constants. Do not
   formalize from intuition — the prior intuitive attempts (avg_below, range
   average, S1) were all unsound. This is the single genuine wall.

Honest status line: **elementary PNT is machine-checked modulo `α = 0`**, with
the symmetry budget, the signed identity, the signed pin `V = −v = α`, and the
forced full-amplitude oscillation all established; the Selberg self-improvement
(S2) is the single remaining, genuinely hard, step — identical to the Liouville
mean-zero / Mertens `o(x)` / `ζ ≠ 0 on Re=1` wall.
