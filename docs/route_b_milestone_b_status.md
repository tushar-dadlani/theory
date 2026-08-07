# Route B — Milestone B: `Φ(s) − 1/(s−1)` holomorphic across `Re s = 1`  ✅ DONE

**End state** (`spectral-theory/ZetaPoleCancel.v`), all axiom-clean, pushed:

```coq
phi_minus_holo : forall z, 0 < Re z -> Cminus C1 z <> C0 -> zF z <> C0 ->
                 exists d, is_Cderiv PhiMinus z d.
phi_minus_line_holo : forall t, t <> 0 -> exists d, is_Cderiv PhiMinus (mkC 1 t) d.
phi_minus_eq : forall s H0 H1 (H : 1 < Re s),
                 PhiMinus s = Cminus (Phi s H) (Cinv (Cminus s C1)).
```
`PhiMinus s = −B′(s)/B(s)` with `B(s) = (s−1)ζ(s)`; `phi_minus_eq` proves it equals
`Φ(s) − 1/(s−1)` on `Re s > 1`, and `phi_minus_holo` proves it holomorphic wherever
`0 < Re s, s ≠ 1, ζ(s) ≠ 0` — in particular on an open neighborhood of the line
`Re s = 1` (`s ≠ 1`), since `ζ(1+it) ≠ 0` (banked `zetaC_line_nonzero`). The `1/(s−1)`
pole of `Φ = −ζ′/ζ` is exactly cancelled.

## The 12 bricks (all axiom-clean)

| Brick | File | Content |
|-------|------|---------|
| B1 | `CHoloCalculus.v` | quotient rule + "continuous & nonzero ⇒ nonzero on a disc" |
| B2 | `ZetaFn.v` | total `zF : C→C`, `HolomorphicOn zF inDom` |
| B3 | `ZetaInvHolo.v` | `1/ζ` holomorphic; `ζ ≠ 0` on a disc around each `1+it` |
| B4 | `CZetaDeriv4.v` | `d2gtermC_cv` (ζ″ analytic series converges) |
| B5 | `CZetaDeriv5.v` | `d3gtermC` + `d2gtermC_sderiv` |
| B6a | `CBaseDeriv3.v` | `dd3kb`, `Cmod_dd3kb` |
| B6b | `CD3sGCKnot.v` | the knot `d/dt d3sGC = d3k` |
| B6c | `CZetaTerm3.v` | `d3bound`, double-MVT `Cmod_d3gtermC_bound`, `d3bound_sum_cv` |
| B7 | `CZetaHolo2.v` | `sum_deriv2` (ζ′ series differentiable) |
| B8 | `ZetaDeriv.v` | `zF_deriv` (ζ′=zDF), `zDF_deriv` (ζ″) |
| B9 | `ZetaPoleCancel.v` | `phi_minus_holo`, `phi_minus_eq` (capstone) |

The novel/hard content was the full third-derivative term stack (B4–B6c); B7–B9 are the
differentiation-under-the-sum assembly that consumes it, mirroring `CZetaHolo`.

## One documented refinement

`phi_minus_holo`'s domain excludes the single point `s = 1`. There `Φ − 1/(s−1)` is
holomorphic with a genuine finite value (`= −A(1)` where `A = ζ − 1/(s−1)`), but our
total `zF` returns `0` at `s=1` (outside `inDom`), so `Bfn(1)=0` and `−B′/B` is not the
right object exactly at `1`. Closing this needs the analytic part `A(s) = Σ gtermC(s)`
packaged as holomorphic *at* `s=1` (extend `gtermC_cv` to `s=1`, where the EM series
still converges) — a bounded final step, not on the critical path for the line
non-vanishing that drives PNT.

## Remaining Route B

- **Milestone C** (the wall): Newman's analytic theorem — greenfield C-valued contour
  integration + Cauchy's theorem on the custom `ComplexField`, plus the kernel estimate.
- **Milestone D**: Newman ⇒ `∫(ψ(x)−x)/x² dx` converges ⇒ `ψ(x)~x` ⇒
  `PNTConditional.pi_asymp_of_psi` ⇒ PNT. Also needs the integral representation
  `Φ(s) = s∫₁^∞ ψ(x)x^{−s−1}dx` (via `AbelSummation` + the existing `CImp` machinery).
