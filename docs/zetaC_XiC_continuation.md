# Closing the complex `zetaC ↔ XiC` continuation gap

## The result

The completed-zeta identity, previously only real and only for `s > 1`, is now proven
**complex on the whole right half-plane**, and it **connects the zeros**:

> **`XiC_completed_strip`** (`CZetaStripId.v`): for every `z` with `Re z > 0`,
> `XiC z = ½·z · π^{−z/2} · GammaC(z/2) · BfnT z`,
> where `BfnT z = (z−1)·zetaC z` is the **regular** completed factor (holomorphic across `z=1`).

> **`zetaC_zero_implies_XiC_zero`** (unconditional): `zetaC z = 0 ⇒ XiC z = 0`.
> Every zeta zero in the strip is a zero of the completed function `XiC`.

> **`XiC_zero_iff_zetaC_zero`**: for `0 < Re z < 1`, **given `GammaC(z/2) ≠ 0`**,
> `XiC z = 0 ⟺ zetaC z = 0`.

All files are **axiom-clean** (only the 4 standard classical-Reals axioms). No `Admitted`/`Axiom`/`admit`.

## Why it was hard (and how it was done)

`XiC` is entire; `zetaC` has a simple pole at `s=1`. The real identity `XiC_is_completed_zeta`
lives only on the ray `s>1`. Two obstructions blocked the strip:

1. **The real-ray identity theorem is useless here.** `CWalk.reach` continues from the *entire*
   positive real axis — but the identity on the segment `(0,1)` is exactly the unknown (circular).
   The continuation had to proceed from the **2-D region `{Re>1}`**.
2. **`zetaC` is singular *per term* at `z=1`.** `zetaC = 1/(z−1) + Σ gtermC`, and each `gtermC`
   carries a `1/(1−s)`. To get a difference that is holomorphic on *all* `{Re>0}` (needed for the
   march), the pole had to be cancelled into a genuinely regular object.

The construction (phases, each a committed axiom-clean file):

| phase | file(s) | content |
|---|---|---|
| **A** | `CZetaXiComplex.v` | complex identity on `Re z > 1` via `reach` shifted to `{Re>1}` |
| **B1** | `CZetaRegular.v` | `bterm = (s−1)gtermC` (entire; the `1/(1−s)` cancels), summable |
| **B2.1** | `CZetaRegular2.v` | `ℓ_n = 1/(n+1) − ln((n+2)/(n+1))`, `Σℓ_n = ellsum` convergent |
| **B2.2** | `CZetaRegular3.v` | per-term limit `gtermC z n → ℓ_n` (difference-quotient of `x^{1−z}`) |
| **B2.3** | `CZetaRegular4.v` | `cseries_remainder_bound` (complex tail ≤ majorant tail) |
| **B2.4** | `CZetaRegular5.v` | `G(z) = Σ gtermC z → ellsum` as `z→1` (ε/3, uniform majorant `3(n+1)^{−3/2}`) |
| **B2.5** | `CZetaRegular6.v` | `BfnT = (z−1)zetaC`, total, **holomorphic on all `{Re>0}`** (incl. `z=1`) |
| **C1** | `CZetaMarchH.v` | `region_reach`: holo on `{Re>0}` + `≡0` on `{Re>1}` ⇒ `≡0` on `{Re>0}` (horizontal march) |
| **C2** | `CZetaStripId.v` | the strip identity + the zero equivalence |

The load-bearing new analytic fact is **B2**: `(z−1)·zetaC z` extends holomorphically across the
pole with value `1`, because `is_Cderiv BfnT 1 d ⟺ G(z) → d`, and `G` (the regularized part) has a
limit at `1` — proven by a uniform-majorant ε/3 argument, `ellsum` being ζ's Laurent constant there.

## Honest scope

- **Forward direction and the identity are unconditional** and closed.
- The **reverse** direction carries one explicit hypothesis: `GammaC(z/2) ≠ 0` on the strip. `Γ` never
  vanishes, but the repo has only real-axis nonvanishing (`GammaC_ne0_real`); the complex
  reflection / reciprocal-product needed to discharge it on the strip is **not present** and is named
  as the single remaining sub-fact — not asserted. The other prefactor factors (`½z`, `π^{−z/2}`,
  `z−1`) *are* proven nonzero.

## Discharging `GammaC ≠ 0` on the strip — scoped, in progress

The complex-side input is **built** (`CSine.v`): the entire complex sine `Csin`, `Csin(RtoC t)=RtoC(sin t)`,
and `Csin(π w) ≠ 0` for `0<Re w<1`. With the identity-theorem machinery already in hand, `GammaC ≠ 0` on
the strip reduces to the single **real** reflection lemma `Gam(s)·Gam(1−s) = π/sin(πs)` on `(0,1)`
(then lift `g(z)=GammaC(z)·GammaC(1−z)·Csin(πz)` from the real axis to the strip; `g(1/2)=Gam(1/2)²≠0`).

That real reflection is the load-bearing keystone, and a survey confirms **its entire supply chain is absent**:
no reflection (real or complex), no Beta function, no sine/Gamma infinite product, no Fubini for improper
integrals, no Hankel-contour representation. Each classical route is a dedicated foundational build:
(a) `Beta = Γ·Γ/Γ` via Fubini + `∫₀^∞ v^{s−1}/(1+v) = π/sin(πs)`; (b) Weierstrass product (γ is available, but
needs product convergence + the Gauss-limit = Euler-integral identity via dominated convergence); (c) the
Hankel representation `1/Γ` entire. All are large; none admits a committable partial short of the whole
lemma. **Status:** `Csin` done; the reflection keystone remains an open milestone.
