# Route B (analytic PNT) — Milestone A: `Φ(s) = −ζ′(s)/ζ(s)` on `Re s > 1`  ✅ DONE

**End state theorem** (`spectral-theory/CVonMangoldtZeta.v`):

```coq
phi_zeta_eq_neg_zeta' :
  forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
    Cmul (Phi s H) (zetaC s H0 H1) = Copp (proj1_sig (dcterm_cv s H)).

phi_eq_neg_zeta_ratio :
  forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
    Phi s H = Copp (Cmul (proj1_sig (dcterm_cv s H)) (Cinv (zetaC s H0 H1))).
```

All eight files compile axiom-clean (only `classic`, `sig_forall_dec`,
`sig_not_dec`, `functional_extensionality_dep`), no `Admitted`/`Axiom`,
registered in `_CoqProject`, pushed to `origin/riemann-functional-equation`.

## The route (Dirichlet convolution, not Euler log-derivative)

`Φ(s)·ζ(s) = (ΣΛ(n)n⁻ˢ)(Σn⁻ˢ) = Σ(Σ_{d|n}Λ(d))n⁻ˢ = Σ ln(n) n⁻ˢ = −ζ′(s)`,
then divide by `ζ ≠ 0`. The arithmetic core `Σ_{d|n}Λ(d)=ln n` is the
existing `VonMangoldtGlobal.vonmangoldt_identity`.

## Files (build order)

| File | Content | Key result |
|------|---------|-----------|
| `CVonMangoldtSeries.v` (B1) | `Φ(s)=ΣΛ(n)n⁻ˢ` converges for `Re s>1` | `Phi`, `Phi_spec` |
| `CZetaDerivDirichlet.v` (B2) | `ζ′(s)=Σ(−ln n)n⁻ˢ` | `dcterm_cv`, `dcterm_series_eq` |
| `CListSum.v` (B3a) | C-valued list sum `Cls` + `Re/Im` bridge to `Rls` | `Re_Cls`, `Cls_prodsep`, `Cpsum_shift_eq_Cls` |
| `CHyperbolaSwap.v` (B3b) | C-valued hyperbola swap (from R via bridge) | `Chyperbola_swap` |
| `CDirichletExhaustion.v` (B3c) | square vs hyperbola; corner = seq-tail split | `Csq_hyp_bound` |
| `CDirichletTail.v` (B3d) | corner sum → 0 via the `K=√N` split | `corner_cv0` |
| `CDirichletProduct.v` (B3e) | the complex Dirichlet-series product | `cdirichlet_product` |
| `CVonMangoldtZeta.v` (B4) | assemble `Φ = −ζ′/ζ` | `phi_eq_neg_zeta_ratio` |

## The one genuinely new analytic tool

`cdirichlet_product` (B3): for two absolutely-convergent complex Dirichlet
series with sums `SA`, `SB`, the convolution series `Σ_n (Σ_{d|n} A_d B_{n/d})`
converges to `SA·SB`. Proof: the hyperbolic partial sum `H_N` (= convolution
partial sum, by `Chyperbola_swap`) differs from the square `P_N=(ΣA)(ΣB)` by
the corner `Σ_{d≤N} Σ_{N/d<m≤N} A_d B_m`; splitting the outer index at `K=√N`
bounds the corner by `SA·(SB−PB K)+(SA−PA K)·SB → 0`, and `P_N → SA·SB` by the
componentwise complex product of limits. No contour integration.

## Remaining Route B roadmap (not built)

- **B**: `Φ(s) − 1/(s−1)` extends holomorphically across `Re s=1` — consumes
  the already-proven `ZetaLineNonzero.zetaC_line_nonzero` (ζ(1+it)≠0) + the
  pole structure + `zetaC_holo`; plus the integral rep `Φ(s)=s∫₁^∞ ψ(x)x⁻ˢ⁻¹dx`
  via `AbelSummation`. Bounded.
- **C** (the wall): Newman's analytic theorem — greenfield C-valued contour
  integration + Cauchy's theorem on the custom `ComplexField`.
- **D**: Newman ⇒ `∫(ψ(x)−x)/x²dx` converges; `ψ` monotone ⇒ `ψ(x)~x` ⇒
  `pi_asymp_of_psi` ⇒ PNT.
