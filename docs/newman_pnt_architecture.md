# Newman's route to the Prime Number Theorem — formalization architecture

A machine-checked (Coq/Rocq) development of the **Perron → Newman–Tauberian**
route toward `ψ(x) ~ x` (hence `π(x) ~ x/ln x`), under `spectral-theory/`.
Every file below compiles with **only the four classical-Reals axioms**
(`Classical_Prop.classic`, the two `ClassicalDedekindReals` decidability axioms,
`functional_extensionality_dep`) — no `Admitted`, `Axiom`, or `admit`.

The central lever is `y^s/s = (y^s−1)/s + 1/s` (entire part + winding part), and,
for Newman, the transform identity `g(z) = Φ(z+1)/(z+1) − 1/z` with
`Φ(s) = Σ Λ(n) n^{−s} = −ζ'/ζ(s)`.

---

## Part A1/A2 — Perron's formula and Perron-for-ψ

| File | Result |
|---|---|
| `PerronGt1.v` / `PerronLt1.v` | `perron_gt1` / `perron_lt1`: the truncated Perron kernel bounds (both `y>1` and `0<y<1`). |
| `PerronSeriesInt.v` | `Cintf_series`: termwise integration of a Weierstrass-M convergent C-series. |
| `PerronIdentity.v` | `perron_identity`: `Σ Λ(n)·Vperron(x/n) = (1/2π)∫ Φ(c+it) x^{c+it}/(c+it) dt` (incl. `unif_limit_cont`, discharging continuity of `Φ(c+it)`). |
| `PerronPsi.v` | `perron_psi`: the truncated Perron formula for `ψ(N)` at the half-integer `x=N+½` (the classical remainder via the `\|ln(x/m)\| ≥ 1/(2(N+1))` diagonal bound). |

---

## Part A3 — the Newman–Tauberian route

### The transform and the identity

| File | Result |
|---|---|
| `LaplaceFull.v` | `gfull` (full Laplace transform `∫₀^∞ f e^{−zt}dt` as a Cauchy limit of truncations `g_T`), `gfull_tail`: `\|g − g_T\| ≤ 2B e^{−(Re z)T}/(Re z)`. |
| `LaplacePhi.v` | `laplace_one`: `∫₀^∞ e^{−zt}dt = 1/z` (the `1/z` term). |
| `ChebyshevPsiR.v` | `psiR` — the real-argument Chebyshev ψ (step function), monotone, `psiR x ≤ x·Kup`. |
| `PiecewiseTransform.v` | `Cintf_ext_ab` (interval-local integral congruence), `cell_contrib` — the cell foundation for the step transform. |
| `CellAdditivity.v` | `Cintf_partition` and its ln-/integer-partition instances (finite additivity over cells). |
| `PhiCellRep.v` | `phi_incr_rep` / `phi_cellint_rep`: Φ as a ψ-weighted cell-integral sum (via `correction_cells` + `phi_integral_rep` + `gC_FTC`). |
| `ExpBridge.v` | `Cintf_exp_cov`: the `u=eᵗ` complex change of variables (componentwise `cov_local`). |
| `FusionKernel.v` | `Fpow_exp`: `u^{−s−1}·eᵗ = e^{−st}` (the pointwise CoV kernel identity). |
| `FusionIntegral.v` | `CgderivInt_Laplace`: `∫_a^b gderivC s = −s ∫_{ln a}^{ln b} e^{−st}dt` (crosses the global-continuity wall at the RiemannInt component level). |
| `NewmanPhiTerm.v` / `NewmanG.v` | `newman_phi_term` / `step_transform_cv`: the t-space Laplace step transform `→ Φ(s)/s`. |
| `NewmanIdentity.v` | **`newman_identity`**: `g(z) = Φ(z+1)/(z+1) − 1/z` (analytic continuation across `Re z = 0`). |

### The contour estimate (all pointwise/arc modulus bounds)

| File | Bound |
|---|---|
| `NewmanArc.v` | `right_arc_bound`: `\|(g−g_T)e^{zT}K_R\| ≤ 4B/R²` (right semicircle). |
| `NewmanArcML.v` | `arc_ML` / `newman_arc_ML`: integrate the pointwise bound → **O(B/R)**. |
| `NewmanLeft.v` | `left_arc_bound`: `\|g_T e^{zT}K_R\| ≤ 4B/R²` (left semicircle, `g_T` entire). |
| `NewmanGLeft.v` | `gleft_decay`: `\|g e^{zT}K_R\| ≤ (2M/R)e^{−δT}` (left, away from axis). |
| `NewmanNearAxis.v` | `gleft_nearaxis`: `\|g e^{zT}K_R\| ≤ 2Mδ/R²` (left, near axis: `\|K_R\|` small). |
| `NewmanLimits.v` | `exp_decay_T_cv0` (`e^{−δT}→0`), `bound_over_R_cv0` (`C/R→0`) — the limit atoms. |

### The Tauberian engine

| File | Result |
|---|---|
| `NewmanTauber.v` | `ln_lt_lin` (`ln λ < λ−1`, `λ≠1`), `gap_pos` (`0 < λ−1−ln λ`). |
| `NewmanBlock.v` | `block_int`: `∫_a^{λa}(λa−t)/t²dt = λ−1−ln λ` — the fixed positive monotonicity gain. |

---

## The spectral face — `Ell2MellinVM.v`

The ℓ² side ties in through the **von Mangoldt diagonal operator** `D_Λ`
(`Ell2VonMangoldt.v`), whose spectral trace over the first `N` basis vectors is
Chebyshev's `ψ(N)` (`vm_trace_eq_psi`). `D_Λ` is unbounded (`Λ(pᵏ)=log p`).

`Ell2MellinVM.v` regularizes it by the Mellin weight `n^{−σ}`:

> **`M_σ := D_Λ · N^{−σ} = Dmul(n ↦ Λ(n) n^{−σ})`**

- **eigenvalues** `Λ(n) n^{−σ} ≥ 0` (`mvm_eigen_nonneg`) — self-adjoint, positive;
- **spectral trace** `Σ_{n≤N} Λ(n) n^{−σ}` (`mvm_trace_eq`) — the truncated
  Dirichlet series, `→ Φ(σ) = −ζ'/ζ(σ)` for `σ>1`;
- at `σ=0`, `M_0 = D_Λ` and the trace is `ψ(N)` (`mvm_trace_0`).

So the **spectral** trace of `M_σ` is exactly the **analytic** `Φ` that drives the
entire Perron/Newman apparatus — the operator-theoretic face of PNT.

### The complex operator — `CDiagOperator.v`

Its genuine **complex** (`s ∈ ℂ`) analogue. The repo has no complex Hilbert space, so the
complex diagonal operator lives on `nat → C` with coordinate matrix elements:

> **`M_s := CDmul(pterm s)`**,  `(M_s f)(n) = (Λ(n+1)(n+1)^{−s})·f(n)`

- `Ce i` are eigenvectors with **complex eigenvalue** `pterm s i = Λ(i+1)(i+1)^{−s}`
  (`CDmul_eigen`); spectrum `{Λ(n) n^{−s}} ⊂ ℂ`.
- diagonal matrix element `Cdiag_elt (pterm s) n = pterm s n` (`Cdiag_elt_eq`);
- **`trace_cv_Phi`** — the trace `Ctrace s N = Cpsum(pterm s) N` converges to `Φ(s)`
  (this is `Phi_spec` dressed as an operator trace);
- **`trace_cv_neg_zeta_ratio`** — that limit **is** `−ζ'/ζ(s)` (`phi_eq_neg_zeta_ratio`):
  the operator's spectral trace is the analytic logarithmic derivative of ζ;
- `Cdiag_elt_Cmod_real` — at `s = σ` real, the eigenvalue moduli are the real `WLam σ`
  weights, bridging back to `Ell2MellinVM`.

The bridge from **primes** (through `Λ`/`pterm`) to the **complex field** (`s ∈ ℂ`, ζ).

---

## What remains (the irreducible orchestration)

Every self-contained analytic *atom* of Newman's method — the identity, all
pointwise/arc modulus estimates, and both limit atoms — is formalized and
axiom-clean. Status of the stitching:

1. ~~**`g` holomorphic in the disk**~~ — **half closed.** `NewmanGExt.v` supplies
   `gext z = (PhiMinusT (z+1) − 1)/(z+1)`, with `gext_eq` (it agrees with
   `newman_identity`'s limit on `Re z > 0`), `gext_at0`, and
   `gext_holo_re_ge0 : 0 <= Re z -> exists d, is_Cderiv gext z d`. The `1/z` that
   looked like the obstruction cancels identically once `Φ` is written via
   `PhiMinus`, and `z = 0` is `s = 1`, which `ZetaPoleCancel2.PhiMinusT` now
   covers (blocker **C0**, closed). Non-vanishing on the closed half-plane is
   `NewmanGExt.BfnT_ne0_re_ge1`.

   **Still open in this item**, and neither is recorded elsewhere:
   - a **uniform `δ`** — Newman's contour enters `Re z < 0`, so `g` must be
     holomorphic on an open neighbourhood of the *compact* segment
     `{Re z = 0, |z| ≤ R}`. Pointwise open non-vanishing exists
     (`ZetaInvHolo.zeta_line_open_nonzero`); the compactness argument that turns
     it into one `δ` does not. This needs a 2-D uniform-continuity input the repo
     lacks.
   - **global `CcontC`** for the integral infrastructure — `gext` is not globally
     continuous. The `CCutoff.psi` / `CGcutCont.gcut` pattern used in
     `ZetaPoleCancel2` for exactly this purpose should apply.
2. **The orchestration**: Cauchy's formula on the Newman contour + the
   `δ→0, T→∞, R→∞` triple limit (near-axis `\|K_R\| ≤ 2δ/R²` control, arc split
   at `\|Re z\|=δ`) ⟹ `∫₁^∞(ψ(u)−u)/u²du` converges; then `block_int`/`gap_pos`
   against that Cauchy tail + `psiR` monotonicity ⟹ `Un_cv (psi N/INR N) 1` ⟹
   `PNTConditional.pi_asymp_of_psi` ⟹ PNT.

   ✅ **The Tauberian half is DONE** (`TauberianBlock.v`, `TauberianSqueeze.v`):
   `pnt_of_tint_cauchy : TintCauchy -> Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1`.
   PNT is now conditional on **one** analytic input, `TintCauchy` — the Cauchy tail of
   `int_1^oo (psi(u)-u)/u^2 du` — which is exactly what the contour argument delivers.
   `gen_block_int` generalises `NewmanBlock.block_int` to a numerator constant at either
   endpoint (the undershoot case needs it at the LEFT endpoint), giving `block_lower` and
   `block_upper`; the squeeze is then the contradiction against the non-shrinking block.

   Note the far end is shorter than it looks: `PsiAsymp.psi_asymp_cv` already gives
   `Un_cv Vrem 0 -> Un_cv (fun N => psi N / INR N) 1`, and `Vrem_cv0` reduces that
   to `is_limsup Vrem 0`. The Tauberian atoms `NewmanBlock.block_int`,
   `NewmanTauber.gap_pos` and `ChebyshevPsiR.psiR_mono` are all built.

   **Unrecorded prerequisite for the Tauberian step**: nothing in the repo
   integrates `psiR`. `grep Riemann_integrable` over `ChebyshevPsiR.v`/`PsiAsymp.v`
   returns nothing, and Stdlib offers only `RiemannInt_P6` (*continuous* `f`).
   `psiR` is a step function, so `Riemann_integrable` is easy *given* a `StepFun`
   witness — but that means constructing an `adapted_couple` over the integer
   breakpoints in `[a,b]`. Budget this as a separate brick before the squeeze.
