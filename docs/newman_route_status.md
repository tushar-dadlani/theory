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

## The DEEP remaining blockers — ✅ ALL CLOSED

**This section is superseded.** Every item below has since been discharged, and the route
now reaches `NewmanE7.PNT` outright, axiom-clean. See `docs/pnt_endgame_plan.md` for the
brick-by-brick record. Kept for the history of what each blocker turned out to be.

1. **C0 — holomorphy of `PhiMinus` at `s=1`.** ✅ Closed by `ZetaPoleCancel2.v`. It was a
   *rewiring*, not analysis: `CZetaRegular6.BfnT_holo` already had the holomorphic
   extension, and `ZetaPoleCancel.Bfn` is a different function that is wrong exactly at
   `s = 1` (`ZetaFn.zF` is *defined* to be `C0` there).

2. **The g-extension / discharge φ.** ✅ Closed by `NewmanCutoff.gtrunc` — a two-factor
   (radial × half-plane) cutoff. `CGcutCont.gcut` cannot do it: being radial it needs
   holomorphy on a whole disc, which fails once the disc swallows a zeta zero (the first at
   `|z| ≈ 14.14`). This same demand for *global* continuity recurred twice more, for `1/z`
   (`NewmanKernelCut.Kcut`) and for the step function itself (`CIntegralD.CintfD`), and is
   the single largest source of work on the route.

3. **Brick 8 `CNewman.v`.** ✅ Closed, though not as one file: `CTruncKernel` (the kernel on
   the truncated contour), `NewmanContour` (the identity), `NewmanDeform` (chord → far-left
   arc, without which the `g_T` chord bound is `O(BR/δ²)` and useless), `NewmanML` and
   `NewmanE6` (the estimates), `NewmanE7` (the `δ→0, R→∞, T→∞` limit).

4. **Milestone D — Tauberian bridge.** ✅ Closed by `TauberianBlock` / `TauberianSqueeze`,
   with `TintCoV` supplying the `u = e^t` change of variables.

## Note

The **elementary (Selberg) route** reaches `Un_cv (ψ N/INR N) 1` modulo a single lemma
(`PsiAsymp.psi_asymp_of_avg_below`, further reduced via `SelbergDip`). It is now the
*second* route to a target the analytic route has already reached, so finishing it buys
independence of the argument rather than the theorem.
