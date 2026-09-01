# Complex-Γ machinery → the Riemann–Siegel phase θ(T): a build plan

## Goal

Reach the **Riemann–Siegel theta function**
```
theta(T) = Im (log Γ(1/4 + iT/2)) − (T/2) ln π
```
and its **Stirling leading asymptotic**
```
theta(T) ≈ (T/2) ln(T/2π) − T/2 − π/8 + o(1),
```
so that the smooth zero count `Nsmooth T = θ(T)/π + 1 + O(1)` is *derived from Γ* rather than posited. This closes the analytic input that `WeylTerm.v` currently states directly (`Nsmooth`, `dens`) and that the N(T) / Riemann–von Mangoldt asymptotic needs.

## What already exists (reuse — do NOT rebuild)

The substrate is ~60% built. Confirmed axiom-clean and directly reusable:

| Capability | Where | Key names |
|---|---|---|
| **Complex Γ**, entire on `Re z > 0`, agrees with real Γ | `GammaC.v`, `GammaNearCHolo.v`, `GammaTailC.v` | `GammaC z`, `GammaC_entire`, `GammaC_agree : GammaC (RtoC s) = RtoC (Gam s Hs)` |
| First-order **holomorphic calculus** (const, id, add, opp, minus, **product**, **chain**, inv, quotient, cont) | `Holomorphic.v`, `CDeriv.v`, `CHoloCalculus.v` | `is_Cderiv`, `Cderiv_mul`, `Cderiv_comp`, `Cderiv_comp_affine`, `Cderiv_inv`, `Cderiv_div`, `is_Cderiv_cont` |
| **Complex exp** and algebra | `EulerFormula.v`, `CexpFull.v`, `CExpKernel.v` | `Cexp`, `Cexpf`, `Cexpf_add`, `Cmod_Cexpf = exp(Re w)`, `Cexpf_ne0` |
| **Complex power** (real base) — the `π^{−s/2}` block | `CexpFull.v`, `CPowBase/CPowMul/CPower.v` | `Cpw c w`, `Re_Cpw`, `Im_Cpw`, `Cpw_mod`, `Cpw_deriv`, `Cpw_ne0` |
| **Diff-under-the-integral** in a complex parameter (already applied to Γ) | `CLaplace.v`, `LaplaceFull.v`, `GammaNearCHolo.v` | `gT_holo` template; `gnearC_entire`, `gtailC_entire` |
| **Real Γ toolkit** | `GammaReal.v`, `GammaRecur.v`, `GammaHalf.v`, `GammaOne.v` | `Gam`, `Gam_recur : Gam(s+1)=s·Gam s`, `Gam_half = √π`, `Gam_1`, `Gam_nonneg` |
| **Weyl main term** (target consumer) | `WeylTerm.v` | `Nsmooth`, `dens`, `Nsmooth_deriv` |
| Discrete/real Stirling seeds | `StirlingSharp.v`, `WallisAsymptotics.v`, `EulerMaclaurin.v` | `Blog x = x ln x − x`, `Tlog_sharp`, `Wallis_sq_asymp → π/2` |

## The gaps, as build blocks (dependency order)

### Block A — Complex logarithm / continuous argument  *(CRITICAL primitive; build from scratch)*
Nothing named `Clog`/`Carg`/`arg` exists. Two options:
- **A1 (full principal branch)** `Clog z := mkC (ln (Cmod z)) (Carg z)` on a cut plane, with `Cexpf (Clog z) = z` (inverse via the mature `Cexpf`/`Cmod`/`Cexpf_ne0`), `Im (Clog z) = Carg z`, `Re (Clog z) = ln (Cmod z)`, and `is_Cderiv Clog z (Cinv z)` off the cut.
- **A2 (cheaper, sufficient)** a *continuous argument along the vertical line* `t ↦ ArgGamma t := Im (Clog (GammaC (mkC (1/4) (t/2))))`, defined by integrating `Im (Γ'/Γ)` (the log-derivative, which needs only `GammaC_entire` + `Cderiv_div`, no branch cut) from a base point. This sidesteps a global branch and is all θ(T) actually requires.

**Recommendation: A2.** The Riemann–Siegel θ is a *continuous* argument accumulated along one line; building the global principal branch (A1) is strictly more than needed. Seed: `is_Cderiv_cont`, `Cderiv_div`, `Cexpf_ne0`.

### Block B — Γ nonvanishing on `Re z > 0`  *(real axis DONE; off-axis is the standing gap)*
`log Γ` / `Γ'/Γ` need `GammaC z ≠ 0`.

- **Strict real positivity — already proven**: `XiReflection.Gam_pos : 0 < Gam a Ha` (via the `[1,2]` integral lower bound `int12_pos`). No need to rebuild from `Gam_nonneg`.
- **Real-axis anchor — DONE** (`GammaCRealAxis.v`, axiom-clean): `GammaC` is real and strictly positive on `ℝ⁺` (`GammaC_real_Re/_Im`, `GammaC_real_pos`), hence nonvanishing there (`GammaC_ne0_real`), and `GammaC_real_axis_anchor : Im = 0 ∧ Re > 0` — the **arg-0 base point** the continuous-argument route (A2) starts from.
- **Complex functional equation `GammaC(z+1) = z·GammaC(z)` — ✅ PROVEN** (`CGammaComplete.GammaC_functional_equation`, axiom-clean, on `{Re z > 0}`). The route was: `GammaCFE.v` reduces the FE to the identity theorem (`GammaC_FE_real` on ℝ⁺, `FE_diff_holo`, `FE_diff_vanishes_real`, `GammaC_FE_from_identity`), and the identity theorem was then built in full — see `docs/identity_theorem_plan.md` (domain-restricted tower B1→B6, the general-`n` Cauchy analyticity key, and the walk `CWalk.reach`). The IBP alternative was not needed.
- **`GammaC z ≠ 0` for all `Re z > 0` — ✅ PROVEN** (`GammaCNe0.GammaC_ne0_final`, axiom-clean). Consequently `ZetaStripConfinement` no longer assumes it: that file's section A is headed "the two former hypotheses, now theorems", and `GammaC_half_ne0` is derived from `GammaC_ne0_final`.

### Block C — `θ(T)` as a real function  *(thin glue; build after A,B)*
```
theta (T:R) : R := Im (Clog (GammaC (mkC (1/4) (T/2)))) − (T/2) * ln PI
```
(or the A2 line-integral form). Continuity/derivative via `Cderiv_comp` ∘ `GammaC_entire` ∘ the affine `T ↦ 1/4 + iT/2` (`Cderiv_comp_affine`, `is_Cderiv_line_Im`). `π^{−s/2}` phase piece already is `Cpw PI`. Low risk once A+B land.

### Block D — Continuous Stirling leading term for `Im log Γ`  *(HARDEST; dominates effort)*
Target: `Im log Γ(1/4 + iT/2) = (T/2) ln(T/2) − T/2 − π/8 + O(1/T)` (leading term + controlled remainder). Seeds: `StirlingSharp.Blog`/`Tlog_sharp` (the `x ln x − x` bracket) and `WallisAsymptotics` (`√π`/`2π`), plus `EulerMaclaurin.v`. But these are discrete/real; the complex vertical-line expansion with a remainder bound is essentially new work. **This block should be scoped and estimated on its own before committing** — it is the true cost center. A reasonable first sub-milestone: the *leading* term only (no sharp remainder), i.e. `θ(T)/((T/2)ln(T/2π)) → 1`.

### Block E — Reconcile with the Weyl term  *(thin; build last)*
Connect `θ(T)` to `WeylTerm.Nsmooth`: prove `Nsmooth T = θ(T)/π + 1 + O(1)` (leading order), turning the currently-posited `Nsmooth`/`dens` into consequences of the Γ asymptotic. Small once D gives the θ asymptotic.

## Recommended sequencing & first milestone

1. **B (real-axis anchor)** — ✅ **DONE** (`GammaCRealAxis.v`): strict real positivity (`Gam_pos`, already present) + `GammaC` real/positive/nonvanishing on `ℝ⁺` + the arg-0 anchor. Off-axis nonvanishing along the path remains a sub-target of A2.
2. **A2 (log-derivative `Γ'/Γ` + continuous argument along the line)** — the critical primitive, but bounded scope via A2. Needs `Γ'/Γ = GammaC'/GammaC` well-defined along the path — i.e. path nonvanishing, the narrowed remnant of Block B.
3. **C (`θ(T)` definition + its derivative `θ'(T) = ½ Im(Γ'/Γ)(¼+iT/2) − ½ ln π`)** — thin glue; **this is the recommended first shippable milestone**: an axiom-clean `θ(T)` with a proven derivative formula, even before the Stirling asymptotic.
4. **D (Stirling leading term)** — scope separately; start with the leading term, defer the sharp remainder.
5. **E (Weyl reconciliation)** — closes the loop to `WeylTerm.v`.

## Honest risk assessment

- **Reusable substrate is strong**: complex Γ, holomorphy, exp/power, diff-under-integral, real Γ all exist and are axiom-clean. This is the good news — the project is *not* greenfield.
- **Block A2 + B + C** are each moderate and give a genuine, axiom-clean deliverable (`θ(T)` with its derivative) *without* the hardest analysis.
- **Block D (continuous Stirling)** is the dominant effort and the main risk; it may itself need a dedicated Euler–Maclaurin-on-vertical-lines development. Recommend a separate scoping pass before committing to the sharp form.
- Net: ship **B → A2 → C** as the first honest increment (a Γ-derived `θ(T)`), then decide on D based on a focused estimate.
