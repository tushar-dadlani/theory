# The identity theorem: a scoping plan

## Goal

Prove the **identity theorem** in the form the complex-Γ functional equation needs:
```
f holomorphic on Re z > 0,  f = 0 on ℝ⁺  ⟹  f ≡ 0 on Re z > 0.
```
This directly discharges `GammaCFE.GammaC_FE_from_identity` (giving the full `GammaC(z+1)=z·GammaC(z)`), and is broadly reusable (uniqueness of analytic continuation anywhere in the corpus). The general statement (vanishing on any set with an accumulation point in a connected domain) is strictly harder; the ℝ⁺-on-a-convex-half-plane form above is the minimal sufficient target and the one to build.

## What already exists (reuse — richer than expected)

| Capability | Where | Notes |
|---|---|---|
| Contour / path integrals, split, **ML estimate** | `CPathIntegral.v` | `pathint`, `seg`, `arc`, `pathint_split`, `pathint_ML` |
| **Cauchy's theorem** (Goursat, triangles) + convex machinery | `CGoursat.v`, `CGoursatConv.v`, `CGoursatExcept.v` | triangle-integral vanishing, corner splits, convex combinations |
| **Primitive on a convex domain** | `CPrimConv.v` | `Convex U`, `seg_int`/`tri_int` vanishing (`tri_int_deg*`, `tri_split_vertex`) — F holomorphic on convex U ⟹ has a primitive |
| **Cauchy integral formula, center form** | `CCauchyFormula.v` | `cauchy_integral_formula`, `meanval0 : M 0 = 2π·F(0)`, `M_const` — the mean-value / center value `(1/2πi)∮ F/z = F(0)` |
| Holomorphic calculus, `is_Cderiv_cont` | `Holomorphic.v`, `CDeriv.v`, `CHoloCalculus.v` | product/chain/quotient, complex-diff ⟹ continuous |
| Diff-under-the-integral in a complex parameter | `CLaplace.v`, `LaplaceFull.v`, `GammaNearCHolo.v` | template for Cauchy's derivative formula (B2) |

**Missing:** general Cauchy formula at interior points, Cauchy's derivative formula, Taylor / local power series, term-by-term integration of a uniformly convergent series over a contour, and any connectedness/clopen argument.

## Building blocks (dependency order)

### B1 — General Cauchy integral formula at interior points  *(gateway; substantial)*
Generalize the center-only formula to `f(w) = (1/2πi) ∮_{|z−a|=R} f(z)/(z−w) dz` for `|w−a| < R`. Route: apply Cauchy's theorem (Goursat) to `f(z)/(z−w)` on the disk with a small circle excised around `w` (keyhole/annulus), so `∮_{C_R} = ∮_{small circle}` → `2πi f(w)` by the mean value around `w`. Reuses `CGoursat*` + `pathint_ML` + `cauchy_integral_formula`. The punctured disk is not convex, so this needs a keyhole/annulus argument on top of the convex primitive machinery. **First recommended milestone — independently valuable.**

### B2 — Cauchy's derivative formula / holomorphic ⟹ C^∞  *(medium)*
`f^{(n)}(w) = (n!/2πi) ∮_{C_R} f(z)/(z−w)^{n+1} dz`, by differentiating B1 under the integral sign (the `CLaplace`/`GammaNearCHolo` diff-under-integral template applies). Yields all higher complex derivatives and the standard bounds `|f^{(n)}(a)| ≤ n! M / R^n`.

### B3 — Taylor's theorem (local power series)  *(THE CRUX)*
For `|w−a| < R`: expand `1/(z−w) = Σ_n (w−a)^n/(z−a)^{n+1}` (geometric, ratio `|w−a|/R < 1`), which converges **uniformly** in `z` on `C_R`; integrate B1 term by term to get `f(w) = Σ_n a_n (w−a)^n` with `a_n = (1/2πi)∮ f/(z−a)^{n+1} = f^{(n)}(a)/n!`. The gating sub-lemma is **term-by-term integration of a uniformly convergent series over a contour** (a `CVU`/`pathint`-swap lemma), which the repo does not have and must be built (stdlib `CVU` + `pathint_ML` are the seeds).

### B4 — All coefficients zero ⟹ locally zero  *(small, given B3)*
If `f^{(n)}(a) = 0` for all `n` then every Taylor coefficient is 0, so `f ≡ 0` on the disk `D(a,R)`.

### B5 — Vanishing on ℝ⁺ ⟹ all derivatives zero at a real point  *(small–medium)*
At real `a > 0`, `f = 0` on a real interval around `a`, so the restriction `t ↦ f(a+t)` is `≡ 0`, hence all its real derivatives vanish; holomorphy (Cauchy–Riemann) identifies `f^{(n)}(a)` with the `n`-th real-direction derivative, so `f^{(n)}(a) = 0` for all `n`. Feeds B4.

### B6 — Propagation over the convex half-plane  *(medium; needs a clopen/connectedness argument)*
The set `Z = { z : Re z > 0, f ≡ 0 on a neighborhood of z }` is open by definition, contains ℝ⁺ (B4∘B5 at every real point), and is **closed** in the half-plane (at a limit point, all `f^{(n)}` vanish by continuity of the derivatives from B2, so B4 gives a zero neighborhood). The half-plane is convex, hence connected, so `Z` = the whole half-plane. Requires a small connectedness/clopen development (or a direct convex chain-of-disks argument along the segment from a real point to the target `w`, which convexity makes clean and may avoid general topology).

## Assembly for the FE
Take `f := GammaCFE.FE_diff`, `a := 1`. `FE_diff` is holomorphic on `Re>0` (`FE_diff_holo`) and `0` on ℝ⁺ (`FE_diff_vanishes_real`). B5→B4→B6 give `FE_diff ≡ 0`, i.e. the hypothesis of `GammaC_FE_from_identity`, closing `GammaC_FE`.

## Honest assessment

- **Cost centers:** B1 (general Cauchy formula — keyhole/annulus on top of Goursat) and B3 (Taylor — needs term-by-term contour integration of a uniformly convergent series). B6 needs a modest connectedness argument. This is a **multi-file, mini-complex-analysis-library** effort — realistically the largest single undertaking proposed so far.
- **Reusability:** very high. B1–B4 (Cauchy formula → derivative formula → Taylor → isolated zeros) unlock analyticity, the maximum principle, Liouville, and uniqueness throughout the corpus — not just the Γ FE.

## Recommendation & the cheaper alternative

- **If the goal is only the Γ functional equation:** the **complex IBP route is likely cheaper** — a single focused file (u-derivative of the Γ kernel `gnkC`, built from a base-power line-derivative + product rule; the componentwise FTC pattern of `CFTC.gC_FTC`; and the improper two-sided limits with boundary vanishing via `RpowerZero.Rpower_pos_cv0` and `exp` decay). It sidesteps general uniqueness entirely. See `docs/complex_gamma_plan.md`.
- **If the goal is general complex-analysis capability:** build the identity theorem, starting with **B1 (general Cauchy integral formula at interior points)** as the first, independently-useful milestone, then B2 → B3.

**Suggested first concrete step either way:** B1. It is the shared gateway (Cauchy formula at interior points), reuses the existing Goursat + center-formula + ML machinery, and is the prerequisite for B2/B3 and for much else besides.
