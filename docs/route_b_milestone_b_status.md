# Route B — Milestone B: `Φ(s) − 1/(s−1)` holomorphic across `Re s = 1` (IN PROGRESS)

Goal: make the continuation of `Φ = −ζ′/ζ` holomorphic on an open neighborhood of
the closed half-plane `Re s ≥ 1`. Algebraically `Φ − 1/(s−1) = −B′/B` with
`B(s) = (s−1)ζ(s)` holomorphic, `B(1)=1`, nonzero near the line — so the pole is
removable. Making `−B′/B` holomorphic needs `B″`, hence `ζ″`, i.e. `ζ′` packaged
as a differentiable function.

## Done this milestone (all axiom-clean, pushed)

| Brick | File | Content |
|-------|------|---------|
| B1 | `CHoloCalculus.v` | quotient rule `Cderiv_div`, `is_Cderiv_cont`, `Cderiv_nonzero_nbhd` (continuous+nonzero ⇒ nonzero on a disc) |
| B2 | `ZetaFn.v` | total function `zF : C→C`, proof-irrelevance, `HolomorphicOn zF inDom` (lifts `zetaC_holo`) |
| B3 | `ZetaInvHolo.v` | `1/ζ` holomorphic where `ζ≠0`; `zeta_line_open_nonzero` (ζ≠0 on a disc around each `1+it`) |
| B4 | `CZetaDeriv4.v` | `d2gtermC_cv` — the ζ″ analytic series converges |
| B5 | `CZetaDeriv5.v` | `d3gtermC` + `d2gtermC_sderiv` (per-term 3rd s-derivative, via the self-reproducing calculus) |
| B6a | `CBaseDeriv3.v` | `d3kb`, `dd3kb`, `Cmod_dd3kb` (base t-derivatives of the 3rd-deriv kernel) |
| B6b | `CD3sGCKnot.v` | the third-order **knot** `dd_eq3 : d/dt d3sGC = d3k`, `base_deriv_d3sGC_Re/Im` |
| B6c | `CZetaTerm3.v` | `d3bound`, double-MVT `Cmod_d3gtermC_bound`, `d3bound_sum_cv` |

**The complete third-derivative term stack (B4–B6c) is the hard, novel prerequisite
for ζ″ and is finished.** Each ζ-derivative costs only one extra log-power (the knot
keeps the bound tower from exploding), so no fourth-order machinery is needed.

## Remaining bricks (mechanical; mirror CZetaHolo / CZetaDeriv3 one order up)

- **B7 `sum_deriv2`** (mirror `CZetaHolo.v` Part 1 `remainder_Re/Im` + Part 2
  `weighted_pseries_cv` + Part 4 `sum_deriv`): differentiate the ζ′ series
  term-by-term. Reuses the generic `order2_bound`, `is_Cderiv_line_Re/Im`,
  `Cderiv_mul_const_r`, plus `dgtermC_sderiv`, `d2gtermC_sderiv` (B5),
  `Cmod_d3gtermC_bound` (B6c), `d2gtermC_cv` (B4). Result:
  `is_Cderiv (fun w => Σ dgtermC w) z (Σ d2gtermC z)`.
- **B8 ζ′ as a holomorphic function**: package `zDF : C→C` = `−1/(z−1)² + Σ dgtermC`
  (the derivative from `zetaC_holo`), and prove `is_Cderiv zDF z (ζ″(z))` combining
  the pole-derivative part (`+2/(z−1)³`, pure calculus) with B7. Mirror `ZetaFn.v`.
- **B9 pole cancellation**: define `B(s) = (s−1)·zF(s)` (holomorphic, `B(1)=1`),
  show `B ≠ 0` on a neighborhood of `Re s ≥ 1` (B3 + `B(1)=1`), and
  `Φ(s) − 1/(s−1) = −B′(s)/B(s)` holomorphic there (quotient rule B1 with `B′` from
  B8). This is the Milestone-B end state.

Then Milestone C (Newman analytic theorem — greenfield contour integration on the
custom `ComplexField`) and Milestone D (Tauberian ⇒ `ψ(N)/N→1` ⇒ `pi_asymp_of_psi`).
