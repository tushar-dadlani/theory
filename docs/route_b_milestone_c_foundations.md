# Route B, Milestone C — foundations status (path integration + exp kernel)

Milestone C = Newman's analytic theorem (Zagier form). Chosen strategy: **foundations
first, stage the Goursat/Cauchy wall**. Contour: Zagier truncated disk. This doc records
the foundations built and the honest state of the remainder.

## Built this session (axiom-clean, committed, pushed)

| Brick | File | Content |
|------|------|---------|
| C1a | `CIntegral2.v` | general finite C-valued integral `Cintf f Hf a b` (any continuous `f:R→C`); `Ccont` algebra; Chasles additivity; reversal; proof-irrelevance; the ML inequality `Cmod(Cintf f a b) ≤ 2M(b−a)` |
| C1b | `CPathIntegral.v` | contour integral `pathint γ γ' f`; `pathint_split`/`_swap`/`_ML`; the concrete `seg` (segment) and `arc` (circle, `Cmod_arc = r`) paths with continuity |
| C3 | `CExpKernel.v` | `e^{zt}` kernel: `cexpzt`, `Re/Im_cexpzt`, `Cmod_cexpzt = exp(Re z·t)`, the t-derivative `d/dt e^{zt} = z·e^{zt}` (`Re/Im_cexpzt_deriv`), `Ccont_cexpzt` |

These are reusable and independently verified — the substrate the contour argument stands on.

## Two remaining foundation items — LARGER than the plan's initial estimate

- **C1c — path FTC / chain rule** (`d/du F(γ(u)) = F'(γ(u))·γ'(u)` for holomorphic `F`,
  C¹ `γ`; then `pathint = H(γ b) − H(γ a)` for a primitive `H`). The repo's
  `is_Cderiv_line_Re/Im` (`CDerivLine.v`) only covers the STRAIGHT line `z+t·h` (where
  `γ(t+δ)−γ(t)=δ·h` exactly). The general path needs the full chain-rule `o()` bookkeeping
  (~standard but fiddly, ~80–120 lines). It is the bridge from holomorphy to contour
  integrals, so it is naturally the FIRST brick of the C2 (Goursat/Cauchy) stage, where it
  is consumed (primitive ⇒ loop integral 0).

- **C0 — holomorphy at s=1** (`PhiMinus` holomorphic at `s=1`, needed because Newman's `g`
  must be holomorphic at `z=0 ⟺ s=1`). FINDING: harder than "bounded". The EM analytic part
  `A(s)=Σ gtermC(s)` is defined via `GC = x^{1−s}·Cinv(1−s)` (`CZetaTerm.v:77`), which is
  **singular at s=1** (`Cinv C0`). Extending to `s=1` needs a reformulated integral-based EM
  term `gtermC*(s,n) = (n+1)^{−s} − ∫_{n+1}^{n+2} x^{−s}dx` (well-defined at `s=1`, and now
  buildable via `CFTC.gC_FTC`), proved equal to `gtermC` off `s=1`, with convergence +
  holomorphy at `s=1`. A genuine multi-lemma reconstruction, coupled to the Newman
  application. Best tackled alongside C4/Milestone-D where its exact needs crystallize.

## Remaining Milestone C/D (staged, separately-approved)
C1c (path FTC) → C2 (`CGoursat.v` + `CCauchyConvex.v` — the wall) → C4 (`Newman.v`) →
Milestone D (D1 single-∫ Φ rep, D2 Laplace/CoV, D3 Newman⇒convergence, D4 Tauberian squeeze
⇒ `Un_cv (psi N/INR N) 1` ⇒ `pi_asymp_of_psi` ⇒ PNT). C0 folds into the D2 holomorphy input.
