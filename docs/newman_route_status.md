# Newman (analytic) route to PNT — status note

_Snapshot as of the contour-wall completion. Companion to
`route_b_C4_newman_plan.md` (which has the full brick decomposition)._

## What is DONE (axiom-clean: only the four classical-Reals axioms; no `Admitted`/`Axiom`)

The **entire contour wall** for Zagier's truncated-disk contour
`C = ∂({|z|≤R} ∩ {Re z ≥ −δ})` (arc + vertical chord):

| Brick | File | Headline |
|---|---|---|
| 1 | `CGoursatConv.v` | region Goursat (non-degenerate triangle, signed-area) |
| 2 | `CPrimConv.v` | convex-region primitive + loop-zero |
| 3 | `CGoursatExcept.v` | exceptional-point Goursat + primitive (`PrimE`) |
| 4 | `CTruncWind.v` | `∮_C dz/z = 2πi` (`trunc_winding`) |
| 5 | `CTruncCauchy.v` | `∮_C F/z = 2πi·F(0)` (`trunc_cauchy`, conditional on φ's interface) |
| — | `CTruncDisk.v` | the region `U = {|z|<R} ∩ {Re z>−δ}` is Convex + Open |
| 6 | `CNewmanKernel.v` | `K_R = 1/z + z/R²`, `|K_R| = 2|Re z|/R²` on `|z|=R` |
| 7 | `CLaplace.v` | `g_T(z)=∫₀ᵀ f e^{−zt}dt` is entire (`gT_holo`) |

`trunc_cauchy` is stated as a `Section` theorem that TAKES φ's exceptional-point
interface (global `CcontC` continuity, holo off 0, boundedness/continuity near 0,
agreement `φ = (F−F0)/z` on the contour) as hypotheses — isolating the one true
analytic gap.

## The DEEP remaining blockers (each needs new infrastructure, not just assembly)

1. **C0 — holomorphy of `PhiMinus` at `s=1`** (the gating blocker). `ZetaPoleCancel`
   gives holomorphy on `Re z>0, z≠1, ζ≠0`. The removable pole at `s=1` is ABSENT.
   The complex continuation `zetaC` (defined on `Re z>0`, `z≠1`) has NO Laurent/pole
   structure at 1 — only the **real** continuation `ζ(s)=1/(s−1)+Σgterm(s)` exists
   (`ZetaContinuation.v`, all `s:R`). Needed: the complex fact `(s−1)ζ(s)→1`, i.e.
   `Bfn(s)=(s−1)zetaC(s)` extends holomorphically to 1 with `Bfn 1 = 1` (currently
   `Bfn 1 = 0`, since `zF 1 = C0`). A complex Euler–Maclaurin, or a real→complex
   bridge. Substantial file on its own.

2. **The g-extension / discharge φ.** The integral infrastructure needs GLOBAL
   `CcontC` continuity; `g` is holomorphic only near the truncated disk. Need a
   continuous extension off the domain (or a reformulation). Tied to C0.

3. **Brick 8 `CNewman.v`** — the analytic theorem: identity
   `2πi(g(0)−g_T(0)) = ∮_C (g−g_T)e^{zT}K_R`, the three ML estimates, `R,T→∞`
   limits ⇒ `∫₀^∞ f` converges. Needs C0 + extension + the `g_T` tail bound
   (the improper `∫₀^∞`, `CImproperIntegral`).

4. **Milestone D — Tauberian bridge** `∫₁^∞(ψ(x)−x)/x² dx converges ⟹ ψ(x)/x→1`
   (ABSENT), then `PNTConditional.pi_asymp_of_psi` ⇒ PNT.

## Note

The **elementary (Selberg) route** already reaches `Un_cv (ψ N/INR N) 1` modulo a
single lemma (`PsiAsymp.psi_asymp_of_avg_below`, further reduced via `SelbergDip`).
The analytic route above is the independent, larger path to the same target;
C0 is its highest-value next unlock.
