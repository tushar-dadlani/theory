# The identity theorem: a scoping plan

## Goal

Prove the **identity theorem** in the form the complex-Γ functional equation needs:
```
f holomorphic on Re z > 0,  f = 0 on ℝ⁺  ⟹  f ≡ 0 on Re z > 0.
```
This directly discharges `GammaCFE.GammaC_FE_from_identity` (giving the full `GammaC(z+1)=z·GammaC(z)`), and is broadly reusable (uniqueness of analytic continuation anywhere in the corpus). The general statement (vanishing on any set with an accumulation point in a connected domain) is strictly harder; the ℝ⁺-on-a-convex-half-plane form above is the minimal sufficient target and the one to build.

## What already exists (reuse — a whole "Milestone C" complex-analysis layer)

A second survey found the substrate is **far richer** than first thought: an entire center-based
Cauchy-integral-formula development is already proven, axiom-clean.

| Capability | Where | Notes |
|---|---|---|
| Contour / path integrals, split, **ML estimate** | `CPathIntegral.v` | `pathint`, `seg`, `arc`, `pathint_split`, `pathint_ML` |
| **Path FTC** + loop-of-a-primitive is 0 | `CPathFTC.v` | `pathint_FTC`, `pathint_primitive_loop` (the engine) |
| **Cauchy's theorem** (Goursat, triangles/convex) | `CGoursat.v`, `CGoursatConv.v` | triangle-integral vanishing, corner splits |
| **Primitive on a convex domain ⟹ loop = 0** | `CPrimitive.v`, `CPrimConv.v` | `Prim_deriv`, `PrimC_deriv`, `pathint_loop_holo`, **`pathint_loop_conv`** (Cauchy's theorem, closed loop of a holomorphic F on convex U is 0) |
| **Removable-singularity loop = 0** | `CGoursatExcept.v` | `tri_int_except`, `PrimE_deriv`, **`pathint_loop_except`** — loop of F holomorphic on convex U *except continuous at one point* is 0 (the exact tool for the Cauchy formula) |
| **Cauchy integral formula, center form** | `CCauchyFormula.v`, `CMeanValue.v` | `cauchy_integral_formula`, `meanval0`, `M_const`, `circint_Fp_zero` — `(1/2πi)∮_{\|z\|=R} F/z = F(0)` |
| **Center Cauchy formula via removable quotient + winding** | `CTruncCauchy.v` | **`trunc_cauchy`** (`∮_C F/z = 2πi·F(0)` on a truncated contour) assembled from the removable quotient `φ=(F−F(0))/z` (`pathint_loop_except`/`PrimE`) + **`trunc_winding`** (`∮_C dz/z = 2πi`) |
| Holomorphic calculus, `is_Cderiv_cont` | `Holomorphic.v`, `CDeriv.v`, `CHoloCalculus.v` | product/chain/quotient, complex-diff ⟹ continuous |
| Diff-under-the-integral in a complex parameter | `CLaplace.v`, `LaplaceFull.v`, `GammaNearCHolo.v` | template for Cauchy's derivative formula (B2) |

**So already done:** Cauchy's theorem, the removable-singularity loop, the **center** Cauchy formula,
and the **center** winding `∮ dz/z = 2πi`. `CTruncCauchy.trunc_cauchy` is a complete (if intricate,
Section-parametrised, ~200-line) template for the formula **at the origin**.

**Still missing (the true remaining path):** the formula at **interior points** `w ≠ center` (the only
thing Taylor needs), which reduces to the **non-center winding** `∮_{\|z−a\|=R} dz/(z−w) = 2πi`
(`\|w−a\|<R`); then Cauchy's derivative formula, Taylor / local power series (term-by-term integration
of a uniformly convergent series), and the connectedness/clopen propagation.

## Building blocks (dependency order)

### B1 — Cauchy integral formula at interior points  *(the non-center winding — the crux — is now DONE)*
Generalize `trunc_cauchy` from the center `0` to an interior point `w`: `f(w) = (1/2πi) ∮_{|z−a|=R} f(z)/(z−w) dz` for `|w−a| < R`. Split `f(z)/(z−w) = (f(z)−f(w))/(z−w) + f(w)/(z−w)`:
- **removable quotient `φ = (f−f(w))/(z−w)`** → `∮ φ = 0`: this is *exactly* the `trunc_cauchy` construction with the pole moved from `0` to `w` — reuse `pathint_loop_except` / `PrimE_deriv` (φ holomorphic off `w`, continuous through `w`). Mechanical port of the existing ~200-line apparatus. *(remaining)*
- **non-center winding `∮_{|z|=R} dz/(z−w) = 2πi`** (`|w|<R`): ✅ **DONE** — `CWindingOffCenter.winding_interior`, axiom-clean. Built (route 2, not the annulus but **parameter differentiation**): slide the pole `w_s = clamp(s)·w` from `0` to `w`; the winding's `s`-derivative is a loop of an exact form, hence `0` (`Jg_zero` via `pathint_FTC`); Leibniz (`leibniz_deriv`, with a clamped globally-continuous integrand) + MVT give `W(1)=W(0)`, and `winding_dz_z` gives `W(0)=2πi`. The heavy pieces: the remainder identity `w²(s−s0)²/(A B²)` (`rem_identity`, reduced to the ring identity `(B−A)²=(wδ)²`), the uniform first-order estimate (`wphi_hunif`), a `Cinv`-continuity lemma, and a small C-algebra/`Cmod` toolkit — all now in the repo and reusable.

With the non-center winding done, **B1 reduces to the mechanical `trunc_cauchy` port** (pole `0→w`, reusing `pathint_loop_except`).

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

## Honest assessment (revised after finding Milestone C)

- **Already done:** Cauchy's theorem, removable-singularity loop, center Cauchy formula, center winding. The hard *foundations* exist.
- **Cost centers now:** the **non-center winding** (B1's annulus deformation) and **Taylor** (B3's term-by-term contour integration of a uniformly convergent series). B6 needs a modest connectedness/clopen argument (eased by convexity). B1's removable half is a mechanical port of `trunc_cauchy`.
- **Scale:** still a multi-file effort, but materially smaller than the original estimate — the center-based apparatus is a working template, so this is "generalise + extend," not "build from scratch."
- **Reusability:** very high. B1–B4 (interior Cauchy formula → derivative formula → Taylor → isolated zeros) unlock analyticity, the maximum principle, Liouville, and uniqueness across the corpus — not just the Γ FE.

## Recommendation & the cheaper alternative

- **If the goal is only the Γ functional equation:** the **complex IBP route is likely cheaper** — a single focused file (u-derivative of the Γ kernel `gnkC` from a base-power line-derivative + product rule; the componentwise FTC pattern of `CFTC.gC_FTC`; improper two-sided limits with boundary vanishing via `RpowerZero.Rpower_pos_cv0` + `exp` decay). It sidesteps general uniqueness. See `docs/complex_gamma_plan.md`.
- **If the goal is general complex-analysis capability (the reusable investment):** build the identity theorem. The center apparatus is done; proceed **B1 → B2 → B3 → B4/B5 → B6**.

**First concrete brick: the non-center winding integral** `∮_{|z−a|=R} dz/(z−w) = 2πi` (`|w−a|<R`), via annulus deformation (`pathint_split` + `pathint_loop_conv` on convex pieces) + small-circle parametrisation. It is the one genuinely new analytic ingredient of B1; with it, B1 assembles by porting `trunc_cauchy` (pole `0 → w`). This is the shared gateway to B2/B3 and the maximum principle, Liouville, etc.
