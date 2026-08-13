# Lean cross-verification ledger — an honest audit

This ledger states plainly **what has been re-verified in Lean 4 + mathlib, at what
strength, and where the honest boundaries are**. It is the Lean-side counterpart of
`spectral-theory/LEDGER.md`, and it exists for the same reason that one does: the value of
this machinery depends entirely on not confusing a *formalized skeleton* with a *solved
problem*.

**Scope discipline.** This worktree edits **no Coq files and no Coq docs**. Findings about
the Rocq development are recorded here and nowhere else.

**What a Lean proof adds.** A Coq proof guarantees the *proof* is valid; it guarantees
nothing about whether the *statement* says what its name claims. Restating a theorem over
mathlib's ℝ/ℂ forces every quantifier into the open, and an independent proof route cannot
inherit a modelling mistake from the first one. That — not a lower axiom footprint — is
what this project buys. See §2.

---

## 1. The from-scratch rule and the ban list

Targets are proved **without discharging them from mathlib's zeta / theta / PNT results**.
The boundary is graded, not binary, mirroring the repo's own `docs/BRIDGES.md` ladder.

| Tier | Rule |
|---|---|
| **Foundations — free** | `Mathlib/Analysis/**`, `MeasureTheory/**`, `Topology/**`, `Algebra/**`. Cauchy/Goursat, `dslope`, Mellin machinery, Poisson summation, `Complex.Gamma`, `MonoidAlgebra`, `ZMod`, `WithZero`. |
| **Targets — banned** | Anything whose import would *discharge* a headline: `NumberTheory.LSeries.{RiemannZeta, HurwitzZeta*, Nonvanishing}`, `ModularForms.JacobiTheta.*`, `Gaussian.PoissonSummation`, `Gamma.Deligne`, `NumberTheory.{Chebyshev, PrimeCounting}`. |
| **Grey — excluded** | `LSeries.AbstractFuncEq` (`WeakFEPair`). Mentions no zeta, but it is precisely the engine mathlib uses to derive `completedRiemannZeta_one_sub`; importing it would collapse three planned bricks to ~40 lines. |
| **Never** | `require leanprover-community/PrimeNumberTheoremAnd` — it contains a finished Newman/Wiener–Ikehara PNT and would trivialise cluster C outright. |

`Gaussian.PoissonSummation` is banned specifically because
`Complex.tsum_exp_neg_mul_int_sq` **is the theta transformation verbatim** — the single
piece of hard analytic content in cluster A.

Enforcement: **never write `import Mathlib`**; import leaf modules only. Cross-checks
against banned lemmas live in `TDLean/Audit/CrossCheck.lean`, which nothing imports, so
they can never enter a headline's dependency graph. `scripts/check_sorry.sh` fails on any
banned import outside `TDLean/Audit/`.

---

## 2. Axiom status — and why "axiom-free" does not transfer

**The repo's central honesty metric has no Lean counterpart, and pretending otherwise
would be a category error.** Rocq's `Print Assumptions` → *"Closed under the global
context"* is attainable in `spectral-theory/` because Rocq's ℚ/ℤ/ℕ are constructive and the
classical `Reals` axioms are quarantined — that is the `LandauerBound`/`LandauerBoundL` and
`ZetaConstructive` discipline. In Lean, mathlib's ℝ is a construction (Cauchy completion of
ℚ, no ℝ axioms), but its entire order/topology/measure API routes through
`Classical.choice`, `propext` and `Quot.sound`. Every result about ℝ or ℂ reports those
three, permanently. That is not a defect and must not be spun as one.

**Record the asymmetry honestly: the Coq side's constructive `CReal` results
(`ZetaConstructive`, `ZetaSquareConstructive`, `ZetaArcConstructive.zeta_arc_free`) are
strictly stronger on axioms than anything this project will produce.**

| Tier | `#print axioms` output | Meaning | Coq analogue |
|---|---|---|---|
| **L0** | no axioms | fully constructive; realistically only ℕ/ℤ/ℚ/decidable statements | "Closed under the global context" |
| **L1** | exactly `[propext, Classical.choice, Quot.sound]` | **the honest Lean clean bar** | the repo's quarantined-ℝ tier |
| **L2** | any additional named `axiom` | a declared gap; listed below with its content | Coq `Axiom` / `Parameter` |
| **F** | contains `sorryAx` | **not proved.** Never ship | Coq `Admitted` |
| **F** | `Lean.ofReduceBool` / `ofReduceNat` | `native_decide` used — kernel-untrusted. Banned | (no analogue here) |

**Enforcement is build-failing, which is strictly stronger than the Coq side's
discipline.** Coq's trailing `Print Assumptions` only *prints* — a regression is invisible
unless a human reads the output. Here `TDLean/Audit.lean` wraps each check in
`#guard_msgs`, and `TDLean.lean` imports `Audit` last, so **`lake build TDLean` *is* the
audit**. Verified by injection: a `sorry` placed in `norm_newmanKernel` produced
`[propext, sorryAx, Classical.choice, Quot.sound]` and failed the build.

Three things `#print axioms` cannot check, asserted by hand instead:

1. **Statement fidelity.** Every headline carries `-- ORACLE: <file>.v : <name>` plus one
   line of prose. Lean cannot check this link — the developments share no definitions — so
   a human must.
2. **Non-vacuity.** Lean makes it easy to state a theorem whose hypotheses are
   unsatisfiable; the repo already has a cautionary case in `SpectralTripleRH_closed.v`,
   whose "RH with zero axioms" is vacuously true. Every headline carries a `_nonvacuous`
   witness — **and those witnesses are themselves audited.** *(Found by testing the gate: a
   `sorry` injected into an unlisted witness passed the build. Fixed; all witnesses are now
   in `Audit.lean`.)*
3. **Import hygiene** — `scripts/check_sorry.sh`, comment-aware.

### Current axiom status

All theorems landed so far are **tier L1**. No `sorry`, no `axiom`, no `native_decide`.

---

## 2b. Trusted base — what "pure Lean" actually means here

Regenerate with `python3 scripts/trusted_base.py` (exits non-zero if a banned module ever
enters the closure).

| | |
|---|---|
| Own source | 5,653 lines across 32 files |
| Direct mathlib imports | **39** |
| Transitive mathlib closure | **2,569** modules (of 7,754; mathlib is ~2.13M lines) |
| Banned modules in closure | **0** |
| Audited headlines | **150**, every one at tier L1 |
| Axioms used, total | `propext`, `Classical.choice`, `Quot.sound` |

**mathlib contributes no axioms.** Those three are declared in Lean 4 **core**
(`Init/Prelude.lean`, `Init/Core.lean`). A repo-wide `grep '^axiom '` over `Mathlib/` returns
four hits, of which two are the word "axiom" in prose and two are throwaway `qc`/`hqc` inside a
docstring example in `Tactic/LinearCombination'.lean`, reachable from nothing. So the trusted
base of this project *is* Lean's kernel plus its three core axioms — mathlib supplies
definitions and proofs, all of them kernel-checked, and delegates no trust.

That is the precise sense in which this development is already "pure Lean". Dropping mathlib
would not shrink the trusted base (it is already minimal); it would mean rebuilding ℝ, ℂ,
filters, normed spaces, `tsum`, Fréchet derivatives, Bochner integration, the FTC and Cauchy's
integral theorem before the first line about ζ — and the result would be *less* trustworthy,
because a freshly written analysis foundation is the least exercised component imaginable,
whereas mathlib's is the most exercised one in existence.

The 39 direct imports are the honest dependency surface, and they are worth reading as a
statement of what the proofs actually need: complex analysis (`Analytic.Order`,
`Complex.CauchyIntegral`, `Complex.LocallyUniformLimit`, `Calculus.LogDeriv`), integration
(`IntervalIntegral.FundThmCalculus`, `JacobianOneDim`, `DominatedConvergence`,
`ParametricIntervalIntegral`), and *elementary* number theory only
(`ArithmeticFunction.{Moebius,VonMangoldt}`, `Primorial`, `AbelSummation`,
`TsumDivisorsAntidiagonal`). No zeta, no L-series, no Chebyshev, no prime counting — those are
the ban list, and the closure is verified clear of them.

## 3. Cross-verification outcomes

Verdicts: `confirmed` · `confirmed-but-trivial` · `strengthened` · `narrower-than-named` ·
`corrected` · `absent-in-Coq` (an overtake — Lean proves something the Coq side does not
have).

### 3.1 Verified so far

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| `MonoidAlgebra.zmodPrimeEquiv` | `ZmodMultMonoid.v : zmod_prime_iso` | **confirmed, radically shorter** | 199 Coq lines → one application of `WithZero.withZeroUnitsEquiv`. `Fact p.Prime → Field (ZMod p) → GroupWithZero`, and mathlib already knows every group with zero is `WithZero` of its units. |
| `MonoidAlgebra.card_units_eq`, `instIsCyclic` | — | **absent-in-Coq** | The Coq `zmod_prime_iso` is about a bespoke sig type `Rp`, carries no ring structure, and never links to `p-1` or cyclicity. Both are free here (`ZMod.card_units`; `IsCyclic` is an instance, replacing ~250 lines of `PrimitiveRoot.v`). |
| `MonoidAlgebra.symVal`, `symVal_mul`, `symVal_injective` | `INFMonoid.v : val, val_hom, val_inj` | **confirmed** | mathlib's `SignType` *is* `{I,N,F}`: `pos/neg/zero` ↔ `I/N/F`, and `val` is `SignType.castHom`, a bundled `→*₀`. Coq's 9-case `op` and its `destruct` proofs are the `CommGroupWithZero` instance. |
| `MonoidAlgebra.symEquiv` | `AdjBoolINF.v : Adj_bool_iso_INF` | **confirmed** | Same lemma as `zmodPrimeEquiv`, at `p = 3`. |
| `Newman.convex_truncDisk`, `isOpen_truncDisk` | `CTruncDisk.v` | **confirmed** | 79 Coq lines → two lines. |
| `Newman.newmanKernel_of_norm_eq`, `norm_newmanKernel` | `CNewmanKernel.v : newman_kernel_on_circle, Cmod_newman_kernel` | **confirmed** | The one Coq brick that was already short (45 lines); comparable here. |
| `Newman.truncContour_eq_zero_of_primitive` | `CPathFTC.v : pathint_primitive_loop` | **confirmed** | Specialised to the truncated contour. Coq needs a whole path-integral calculus first (`CPathIntegral.v`, `CPathFTC.v`, `CSegInt.v`) because Rocq has no complex analysis; mathlib has interval integrals + FTC-2 but no path abstraction, so this supplies the minimum. |
| `Newman.hasDerivAt_radialPrimitive`, `truncContour_eq_zero_of_starAboutZero` | `CGoursatConv.v` + `CPrimConv.v` + `CGoursatExcept.v` (**1116 lines**) | **confirmed, different proof** | The keystone. A holomorphic function on an open star-shaped-about-`0` region has a primitive, so closed-loop integrals over the truncated contour vanish. Radial argument (`F z = ∫₀¹ z f(tz) dt`), resting on `∂/∂z[z f(tz)] = f(tz) + t z f'(tz) = d/dt[t f(tz)]`; differentiate under the integral, then FTC-2 in `t` telescopes to `f z`. Coq subdivides triangles (Goursat); mathlib has no triangle Goursat, only rectangles. **Genuinely independent proof route.** |
| `Newman.trunc_cauchy` | `CTruncCauchy.v : trunc_cauchy` (215 lines) | **STRENGTHENED** | `∮_C F/z = 2πi·F(0)`. **The Coq version is conditional and this one is not.** Coq's is a `Section` theorem taking φ's whole exceptional-point interface as hypotheses — global `CcontC` continuity, holomorphy off `0`, boundedness near `0`, agreement with `(F−F0)/z` on the contour. `docs/newman_route_status.md` lists discharging that interface ("the g-extension / discharge φ") as one of the **deep remaining blockers** of the Coq route, because its integral infrastructure demands *global* continuity while `g` is holomorphic only near the truncated disk. In Lean the hypothesis simply does not arise: `dslope F 0` is differentiable on any neighbourhood of `0` where `F` is (`differentiableOn_dslope`), and Bochner integrals carry no global-continuity side condition. **So that blocker is an artifact of the bespoke `ComplexField` development, not mathematics.** This is the single most consequential finding so far. |
| `Newman.hasDerivAt_gT`, `differentiable_gT` | `CLaplace.v : gT_holo` (178 lines) | **confirmed, different proof** | `g_T(z) = ∫₀ᵀ f e^{−zt}` is entire, `g_T'(z) = ∫₀ᵀ f(t)(−t)e^{−zt}`. Coq differentiates by hand: expand the increment as `f(t)e^{−zt}(e^u−1−u)`, bound `|e^u−1−u| ≤ 3|u|²e^{|u|}` (`CexpRemainder`), conclude `O(|h|²) = o(|h|)` by ML. Lean reuses the same differentiation-under-the-integral machinery as C4 with a constant dominating bound. |
| **`Newman.newman_tauberian`** | — | **absent-in-Coq (overtake)** | **Newman's analytic Tauberian theorem, complete.** `f` interval-integrable on every `[0,T]` and bounded by `B`, `g` its Laplace transform on `Re z > 0`, `g` holomorphic past the imaginary axis ⟹ `∫₀ᵀ f → g(0)`. **Correction to the original statement:** this was first proved with `Continuous f`, which is too strong to apply — the PNT input is `ψ(eᵗ)e^{−t} − 1`, a *step* function. `Laplace.lean` has been regeneralised to `IntervalIntegrable` throughout (the domination argument never needed more), so the theorem is now applicable. Verified by exhibiting `⌊t⌋₊` as a discontinuous witness of the hypothesis, via `MonotoneOn.intervalIntegrable`. `CNewman.v` does not exist and `docs/newman_route_status.md` lists this as brick 8, open — so this is Lean proving what the Rocq development does not have. Non-vacuity witness included, since the hypothesis set (esp. `hregion`) is elaborate. |
| `Newman.newman_inequality` | — | **absent-in-Coq** | The quantitative core: `2π‖g(0) − g_T(0)‖ ≤ 4πB/R + ‖leftPart(g·e^{zT}·K_R)‖` for every admissible `R` and every `T ≥ 0`. |
| `Newman.tendsto_leftPart_g_zero` | — | **absent-in-Coq** | The `T → ∞` step, by dominated convergence over the two arc pieces and the chord. |
| `Newman.leftPart_kernel_deform` | — | **absent-in-Coq (overtake)** | Zagier's deformation of the left contour part to the left semicircle. Obtained with no second contour and no off-origin Cauchy theorem: at `α = π` the chord degenerates (`arcTop R π = arcBot R π = −R`), so `C(π)` is the full circle; C6 at `α` and at `π` give the same value, the right semicircles coincide, and the left parts follow by cancellation. |
| `Newman.norm_newman_integrand_left`, `norm_gT_le_of_re_neg` | — | **absent-in-Coq** | The left-semicircle estimate and the `g_T` bound driving it; also `integral_exp_mul_zero` (`∫₀ᵀ e^{at}dt`), which mathlib lacks. |
| `Newman.truncContour_split`, `norm_arcIntegralOn_le_of_ae` | — | **absent-in-Coq** | The cut at `Re z = 0`, and an ML bound requiring the pointwise estimate only on the open interval (the endpoints have `Re z = 0`, where Newman's `1/Re z` bound fails, but they are null). |
| `Newman.newman_contour_identity` | — | **absent-in-Coq (overtake)** | `∮_C F(z)(1/z + z/R²) dz = 2πi·F(0)`. The identity Newman's argument starts from, with `F z = (g z − g_T z)e^{zT}`. The `1/z` half is C6, the `z/R²` half is C4 (that summand is holomorphic, so its loop vanishes). `CNewman.v` does not exist, so nothing here is a cross-verification. |
| `Newman.norm_newman_integrand_right` | — | **absent-in-Coq (overtake)** | The right-semicircle estimate, pointwise: on `‖z‖ = R`, `Re z > 0`, the three inputs `‖g−g_T‖ ≤ B e^{−(Re z)T}/Re z` (C7), `‖e^{zT}‖ = e^{(Re z)T}`, `‖K_R‖ = 2(Re z)/R²` (C2) multiply to the constant `2B/R²` — every `z`-dependence cancels. This cancellation is the reason Newman's argument closes. |
| `Newman.norm_arcIntegral_le`, `norm_chordIntegral_le` | — | **absent-in-Coq** | ML bounds for the two contour pieces. |
| `Newman.norm_laplaceTail_le` | — | **absent-in-Coq** | `‖∫_{t>T} f e^{−zt}‖ ≤ B e^{−(Re z)T}/Re z` for `Re z > 0`. In `route_b_C4_newman_plan.md` this is part of the still-open brick 8. |
| `Newman.trunc_winding` | `CTruncWind.v : trunc_winding` (254 lines) | **confirmed, different proof** | `∮_C dz/z = 2πi`. **Does not need the keystone C4.** On the chord `Re z = R cos α < 0`, so `log(-z)` is a primitive of `1/z` there — `-z` has positive real part, lands in `slitPlane`, and the chord never meets the branch cut. Arc gives `2αi` (integrand collapses to the constant `I`), chord gives `2(π-α)i`, total `2πi`. Coq uses `arctan` antiderivatives precisely because it has no complex `log`. |

### 3.1b Cluster C9 — zeta from scratch (overtake; C9 is the Coq route's own blocker)

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| `Zeta.zetaCont_eq_zetaSeries`, `differentiableAt_zetaCont` | — | **absent-in-Coq (overtake)** | The analytic continuation of ζ to `Re s > 0` with the pole isolated in an explicit `1/(s−1)`, built from the difference series `∑ (m^{−s} − ∫ₘ^{m+1} x^{−s})`. No functional equation, no mathlib zeta. `docs/newman_route_status.md` records the Coq side's `zetaC` as having **no Laurent/pole structure at 1** — that is exactly the gap this closes. |
| `Ell2Zeta.v:133 vonmangoldt_zeta_trace` | **narrower-than-named** | Its name and section header (`:127`) claim `Tr(D_Λ Z_s) = ∑ Λ(n)n^{−s} = −ζ′/ζ`. The theorem is `diag_trace (fun n => Lam n * z s n) N = dvmzeta s N` — a **finite** trace equals a **finite** sum — proved by `apply diag_trace_eq` ("the trace of a diagonal operator is the sum of its diagonal entries"). The `= −ζ′/ζ` is in the comment only. The file's own header (`:22`) is honest: *"Convergence of the partial traces to the analytic ζ(s) (Re s>1) is a separate analytic step."* **Correction to my own earlier claim:** I said C9 item 2 was cross-verification on the strength of this; only the arithmetic half is (`Ell2Zeta.v:149 energy_eq_divisor_sum`, `log n = ∑_{d∣n} Λ(d)`, which is substantive). The analytic half is an overtake. |
| **`Zeta.LS_vonMangoldt_eq`** | `Ell2Zeta.v:149 energy_eq_divisor_sum` (arithmetic half only) | **mixed: cross-verified + overtake** | **C9 item 2, complete:** `∑ Λ(n)n^{−s} = −ζ′(s)/ζ(s)` on `Re s > 1`. The arithmetic input `Λ ∗ 1 = log` has a genuine Coq oracle; the analytic identity does not (see `LogDeriv.lean` header — `vonmangoldt_zeta_trace` is a finite-trace restatement). |
| `Zeta.zetaSeries_ne_zero` | — | **absent-in-Coq** | `ζ(s) ≠ 0` for `Re s > 1`, from `μ ∗ 1 = δ` via `LS_mul`. **No Euler product** — so item 2 does not depend on item 3's hard work. |
| `Zeta.summable_log_rpow` | — | **absent-in-Coq** | `∑ log(n)·n^{−σ}` converges for `σ > 1`, by the elementary bound `log x ≤ x^ε/ε` (from `log y ≤ y − 1` at `y = x^ε`) — no asymptotics machinery. |
| `Zeta.eqOn_halfplane_of_eqOn_subhalfplane`, `eqOn_of_eventuallyEq` | — | **absent-in-Coq (overtake)** | **The complex-analytic identity theorem, region form.** This is the tool whose absence is finding #1 below: the Rocq repo has only *polynomial* identity theorems (`QPolyPIT.v`, `IntPolyDerivResp.v`), which is precisely why `LambdaC_FE`'s symmetry on ℂ cannot be joined to the ζ-identification on the real ray `s > 1`. Built from `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` plus convexity ⇒ preconnectedness of a half-plane. |
| **`Zeta.eqOn_of_eqOn_realRay`**, `eqOn_of_eqOn_seq` | — | **absent-in-Coq (overtake)** | **The identity theorem in real-RAY form — the tool finding #1 actually needs.** *Correction to my own earlier claim:* I said `eqOn_halfplane_of_eqOn_subhalfplane` was that tool. It is not. The Rocq gap is agreement on the **real ray** `s > 1` (`ZetaXiLink.v:18`), a set with **empty interior** in ℂ, so no open-to-open lemma can bridge it; what is required is the accumulation-point principle. Built on mathlib's one-dimensional `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` via the approach sequence `x₀ + 1/(n+1)`. Closes the *tool* gap only — applying it to `Λ(s) = Λ(1−s)` still needs a Lean-side `Ξ`, i.e. cluster A. |
| `Zeta.zetaDiffSum_unique` | — | **absent-in-Coq** | Uniqueness of the continuation: any function holomorphic on `Re s > 0` agreeing with `zetaDiffSum` on `Re s > 1` *is* it. |
| `Zeta.deriv_zetaCont_eq` | — | **absent-in-Coq** | Derivative transfer on `Re s > 1`. Worth noting this does **not** use the identity theorem — the functions agree on an open set, so locality (`EventuallyEq.deriv_eq`) suffices. |
| **`Zeta.mertens_nonneg`** | — | **absent-in-Coq (overtake)** | **C9 item 3, phase 1:** `3·Re F(σ) + 4·Re F(σ+it) + Re F(σ+2it) ≥ 0` for `σ > 1`, where `F = L(Λ) = −ζ′/ζ`. **Correction to my own earlier claim:** I said repeatedly that item 3 "needs the Euler product first". Given item 2 it does not. mathlib needs the Euler product only because it routes through `log ζ` (`LSeries/Nonvanishing.lean:220 re_log_comb_nonneg'`, banned *and* `private`). Taking `−ζ′/ζ` instead, the coefficients `Λ(n) ≥ 0` are non-negative on the nose and the inequality is `tsum_nonneg` applied to `3 + 4cos θ + cos 2θ = 2(1+cos θ)²`. |
| `Zeta.cpow_neg_re`, `three_add_four_cos_nonneg`, `re_LS_LamC` | — | **absent-in-Coq** | Supporting: `((n:ℂ)^{−s}).re = n^{−σ}cos(t log n)`; the trig identity; and the termwise real part of the Dirichlet series (via `Complex.hasSum_re`). |
| **`Zeta.tendsto_sub_mul_logDeriv`** | — | **absent-in-Coq *and* absent-in-mathlib** | **C9 item 3, phase 2:** if `f` is analytic at `z₀` with finite order `n`, then `(z − z₀)·(f′/f)(z) → n` as `z → z₀` off `z₀`. `Mathlib/Analysis/Calculus/LogDeriv.lean` has the full algebra of `logDeriv` (`mul`/`div`/`pow`/`comp`/`prod`) but **nothing about its behaviour at a zero or a pole** — `logDeriv` does not occur anywhere under `Analysis/Meromorphic/`. Built here from `AnalyticAt.analyticOrderAt_ne_top`'s factorisation `f =ᶠ (z − z₀)^n • g`. Nothing zeta-specific: a general fact about analytic functions, and the natural mathlib contribution out of this cluster. |
| `Zeta.logDeriv_eq_order_div_add`, `logDeriv_sub_pow`, `logDeriv_eventuallyEq` | — | **absent-in-mathlib** | Supporting: the splitting `logDeriv f = n/(z−z₀) + logDeriv g` near a finite-order zero; the model pole `logDeriv ((·−z₀)^n) = n/(z−z₀)`; and locality of `logDeriv`. |
| **`Zeta.zetaCont_ne_zero_of_one_le_re`** | `ZetaLineNonzero.v:103 zetaC_line_nonzero` | **cross-verified** | **C9 item 3, COMPLETE:** `ζ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1` — the Hadamard–de la Vallée Poussin theorem. Run on `−ζ′/ζ` rather than `log ζ`, so **no Euler product is used anywhere in this project**. The pole at `s = 1` and the hypothetical zeros at `1 + it₀`, `1 + 2it₀` are handled uniformly by one lemma with an *integer* exponent (`tendsto_sub_mul_logDeriv_of_factor`, exponent `−1` at the pole). The Coq route has no analogue: its `zetaC` has no pole structure at all, which is the gap `docs/newman_route_status.md` records. |
| `Zeta.zetaPoleFactor`, `zetaCont_eq_poleFactor`, `analyticOrderAt_zetaCont_ne_top` | — | **absent-in-Coq** | Supporting. The pole is *free from the construction*: `zetaCont := 1/(s−1) + zetaDiffSum`, so `zetaCont s = (s−1)^(−1)·(1 + (s−1)·zetaDiffSum s)` with the second factor analytic and equal to `1` at `s = 1`. mathlib's version of this fact lives in `Harmonic/ZetaAsymp.lean`, which is banned by dependency — and is not needed. Order-finiteness on the line is likewise local, not global: any ball around a point of `Re s = 1` contains points with `Re s > 1`, where `ζ ≠ 0`, so no connectedness argument is required. |
| **`Zeta.differentiableOn_PhiMinus`** | — | **absent-in-Coq (overtake); closes the Rocq route's own blocker** | **C9 item 4, COMPLETE:** `Φ⁻ = −ζ′/ζ − 1/(s−1)` is holomorphic on an open set containing `Re s ≥ 1`. `docs/newman_route_status.md` records *"holomorphy of PhiMinus at s = 1"* as **ABSENT** — it is the Rocq route's gating blocker, because that development's `zetaC` has no Laurent/pole structure at `1` at all. Here it is nearly free: the pole was isolated *by construction*, so splitting `logDeriv` across `zetaCont = (s−1)^(−1)·zetaPoleFactor` makes the subtraction an **identity**, `Φ⁻ = −logDeriv zetaPoleFactor` (`PhiMinus_eq`), not an estimate. Holomorphy then reduces to `zetaPoleFactor ≠ 0`, which on `Re s ≥ 1` is exactly item 3. |
| `Zeta.zetaPoleFactor_ne_zero`, `logDeriv_zetaCont_eq`, `isOpen_phiRegion` | — | **absent-in-Coq** | Supporting: `(s−1)·ζ(s) ≠ 0` on `Re s ≥ 1` (at `s = 1` by the normalisation `zetaPoleFactor 1 = 1`, elsewhere by item 3); the `logDeriv` splitting across the pole; openness of the region, from analyticity plus `ContinuousAt.eventually_ne`. |

### 3.1c Cluster C10 — Chebyshev and the assembly to PNT

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| **`PNT.psi_le_const_mul`** | `ChebyshevPrime.v:268 chebyshev_theorem` | **cross-verified** | **Chebyshev's bound:** `ψ(x) ≤ (log 4 + 40/log 2)·x` for `x ≥ 1` — Newman's boundedness hypothesis. **Built from scratch on purpose.** mathlib's `NumberTheory/Chebyshev.lean` has `psi_le_const_mul_self` ready-made and its import closure is free of the `LSeries` tree — but `scripts/check_sorry.sh` has banned `Mathlib.NumberTheory.(Chebyshev\|PrimeCounting)` since the first scaffold commit, precisely because `ChebyshevPrime.v` is an oracle and importing would destroy the cross-check. **Correction to my own earlier claim:** I proposed importing it on the grounds that it is "outside the ban"; that was wrong — it is outside the *dependency* ban but inside the *declared* one. Only `Mathlib.NumberTheory.Primorial` (elementary) is used. |
| `PNT.theta_le_mul_log4` | `ChebyshevPrime.v` (`theta`) | **cross-verified** | `θ(x) ≤ x·log 4`, via `θ(x) = log(⌊x⌋#)` and `primorial_le_4_pow`. |
| `PNT.card_ppSet_le` | — | **absent-in-Coq** | The prime-power correction `ψ − θ` has at most `(√x+1)(log₂x+1)` terms: non-prime prime powers `p^k ≤ x` have `k ≥ 2`, hence `p ≤ √x` and `k ≤ log₂x`. Injectivity of `n ↦ (minFac n, exponent)` uses `IsPrimePow.minFac_pow_factorization_eq`. |
| `PNT.log_le_four_mul_sqrt_sqrt` | — | **absent-in-Coq** | `log x ≤ 4·x^(1/4)`, written with nested `Real.sqrt` so no `rpow` is needed — this is what makes `√x·log²x = O(x)` elementary. |
| **`PNT.tendsto_piCount`** | `PNTConditional.v:52 pi_asymp_of_psi` | **cross-verified (strengthened)** | **`π(x)·log x / x → 1` — the Prime Number Theorem.** *Statement-fidelity note:* the Coq theorem is a `Un_cv` over a **ℕ-sequence**; this is a **real** `atTop` limit. They agree at integers and the real form is strictly stronger, so this is a strengthening, not a plain confirmation. **Correction to my own earlier claim:** I named `PiUpperAssembly.v:83` and `ThetaPiBound.v:35` as the oracles; those are the two half-bounds that *feed* `PNTConditional.v:52`, which is the assembled statement and the correct oracle. |
| `PNT.piCount`, `theta_le_piCount_mul_log`, `piCount_le` | `PrimePowerReindex.v:377` (the `ψ` analogue) | **cross-verified** | `π` is defined from scratch — `Mathlib.NumberTheory.PrimeCounting` is gate-banned. The two bounds `θ(x) ≤ π(x)log x` and `π(x) ≤ x^α + 1 + θ(x)/(α log x)` sandwich `π(x)log x/x`; letting `α → 1` pins the limit. |
| **`PNT.tendsto_theta`** | `ThetaLimit.v:99 theta_asymp_of_psi` | **cross-verified** | `θ(x)/x → 1`. Needed exposing `psiErr_mul_log2_le'`, the sharp `(√x+1)(log x+1)log x` bound — the `O(x)` form used for Chebyshev's theorem throws away the `√x` and the limit fails with it. The Coq side's `PsiThetaTail.v:131 psi_minus_theta_bound` is **sharper** (`√N·log N`, charging `log N` to each prime `p ≤ √N`, versus this file's `√x·log²x` from counting `(p,k)` pairs). |
| **`PNT.tendsto_psi`** | `PsiAsymp` / `SelbergPin` (the Coq route's target) | **absent-in-Coq (overtake)** | **`ψ(x)/x → 1` — the Prime Number Theorem in Chebyshev form.** The endpoint of the whole analytic line: C1–C8 (contour wall + Newman), C9 items 1–4 (ζ from scratch, non-vanishing on `Re s = 1`, `Φ⁻` holomorphic), C10 (Chebyshev, Abel, Mellin, change of variable, Newman applied, squeeze). Zagier's final argument: convergence of `∫₀^∞ f` forces small tails, but **monotonicity of `ψ`** makes any overshoot `ψ(eᵗ) ≥ λeᵗ` contribute at least the *fixed* constant `λ − 1 − log λ > 0` over `[t, t+log λ]`. |
| `PNT.no_overshoot`, `no_undershoot`, `integral_ge_overshoot`, `integral_le_undershoot` | — | **absent-in-Coq** | The two-sided squeeze. Both directions give the **same** constant `λ − 1 − log λ`, since `log λ < λ − 1` holds for every `λ ≠ 1` — the overshoot and undershoot gaps are mirror images. |
| `PNT.cauchy_tail`, `integral_model` | — | **absent-in-Coq** | Convergence ⟹ small tails; and `∫_t^{t+c}(λe^{t−s} − 1)ds = λ(1 − e^{−c}) − c` in closed form. Working in `t`-coordinates rather than substituting back to `x = eᵗ` is what keeps the estimate elementary. |
| **`PNT.abel_finite`** | — | **absent-in-Coq (overtake)** | **C10 part 2:** `∑_{n ≤ b} Λ(n)n^{−s} = b^{−s}ψ(b) + s∫₁^b ψ(t)t^{−s−1}dt`, the Abel/Stieltjes identity that converts the Dirichlet series into a Laplace transform. Built on `Mathlib.NumberTheory.AbelSummation` (`sum_mul_eq_sub_integral_mul₀`), which is clean — no `LSeries` anywhere in its import closure. The banned `LSeries/SumCoeff.lean:137 LSeries_eq_mul_integral` is this same statement and rests on the same clean file, so it served as a reproduction template rather than an import. |
| `Zeta.LS_mul` | — | **absent-in-Coq (overtake)** | The Dirichlet-series product formula `L(f,s)·L(g,s) = L(f∗g,s)` for absolutely convergent series. mathlib's `LSeries_convolution` is in the banned `LSeries` tree, so this is rebuilt from `tsum_mul_tsum_of_summable_norm`, the reindex `sigmaAntidiagonalEquivProd` (general combinatorics, not the banned tree) and `Complex.natCast_mul_natCast_cpow`. Indexing over `ℕ+` sidesteps the `n = 0` term. |
| `Zeta.hasSum_deriv_zetaSeries` | — | **absent-in-Coq (overtake)** | `ζ′(s) = −∑ log(n) n^{−s}` on `Re s > 1`, by termwise differentiation (`hasSum_deriv_of_summable_norm` on a ball where `Re w ≥ σ₀ > 1`). The `n = 0` term is locally constant `0` there and `Real.log 0 = 0`, so the formula is uniform in `n`. |
| `Zeta.norm_cpow_sub_le`, `norm_zetaDiff_le`, `summable_zetaDiff` | — | **absent-in-Coq** | The increment estimate and convergence of the difference series on `Re s > 0`. |
| `Zeta.differentiableOn_zetaDiffSum` | — | **absent-in-Coq** | Holomorphy, via differentiation under the integral plus `differentiableOn_tsum_of_summable_norm` applied on balls (the term bound carries `‖s‖`, so it is uniform only on bounded sets). |

### 3.1d Cluster A — the functional equation

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| **`FE.tsum_gaussian_transform`** | `GaussThetaTransform.v:98 theta_transform` | **cross-verified** | **Jacobi's theta transformation:** `∑_{n∈ℤ} e^{−πan²} = a^{−1/2}∑_{n∈ℤ} e^{−πn²/a}`. The two proofs take *different routes*: Coq goes by pointwise Fourier-series convergence for a periodised Gaussian (`GaussPeriod*.v`, `FourierConvergeLoc.v`, ~2900 lines); Lean by general Poisson summation plus the Gaussian's Fourier self-duality. Independent routes to the same theorem is the strongest form of cross-verification this project produces. |
| `FE.gaussian_isLittleO_atTop`, `gaussian_isLittleO_cocompact` | — | **absent-in-Coq** | The decay estimates. **Ban boundary, stated precisely:** `Gaussian.PoissonSummation` is gate-banned and contains the target theorem itself (`Real.tsum_exp_neg_mul_int_sq`); `Analysis.Fourier.PoissonSummation` (general) and `Gaussian.FourierTransform` (`fourier_gaussian_pi`) are **not** banned. Only the decay lemmas live exclusively in the banned file, so only they were rebuilt. **Correction to my own earlier claim:** I said cluster A's "easy route is closed by the gate", implying Poisson summation from scratch. Only the last mile is closed. |
| **`FE.mellin_gaussian_term`** | `MellinTail.v:143 T_exists`, `MellinTailSeries.v:214 tail_series` | **absent-in-Coq (different object)** | `∫₀^∞ t^{s/2−1}e^{−πn²t}dt = π^{−s/2}·n^{−s}·Γ(s/2)` — the single term whose sum over `n ≥ 1` is the completed zeta. The Coq side works with the **tail** `T(s) = ∫₁^∞ t^{s/2−1}ψ(t)dt`; this is the full `∫₀^∞` of one term, which is where the `Γ` comes from. `Gamma.Basic` is not gate-banned (only `Gamma.Deligne` is), so `integral_cpow_mul_exp_neg_mul_Ioi` is available. |
| `FE.cpow_pos_eq_exp`, `scale_factor` | — | **absent-in-Coq** | `x^w = exp(log x·w)` for positive real `x`, and `(1/(πn²))^{s/2} = π^{−s/2}n^{−s}`. Reducing every `cpow` to `exp` of a real logarithm is what makes the scale factor a `ring` identity rather than a `cpow`-arithmetic fight. |
| **`FE.integral_pole_terms`** | — | **absent-in-Coq (overtake)** | `∫₁^∞ (√u−1)/2 · u^{−s/2−1} du = 1/(s−1) − 1/s` for `Re s > 1`. The pole structure of the completed zeta, falling out of the `(√u−1)/2` half of `psiTheta_transform`: a simple pole at `s = 1` and one at `s = 0`. **The `s ↦ 1−s` symmetry is already visible in the answer** — substituting `1−s` gives `1/(−s) − 1/(1−s)`, the same pair with the roles swapped — so the antisymmetry the functional equation asserts is present in this term *before* any of the integral machinery is assembled. Coq's `MellinTail.v` works only with the tail `T(s) = ∫₁^∞`, never with the `(0,1)` half, so it has no counterpart. |
| **`FE.integral_Ioo_eq_integral_Ioi_inv`** | — | **absent-in-Coq (overtake)** | **The fold.** `∫₀¹ ψ(t)t^{s/2−1}dt = ∫₁^∞ ψ(1/u)u^{−s/2−1}du`. This is the step that carries the half of the Mellin integral near `0` — where `ψ` blows up and nothing converges — onto `(1,∞)`, where `ψ` decays like `e^{−πt}`. Note the exponent reflects `s/2−1 ↦ −s/2−1` for free: the Jacobian `u^{−2}` supplies exactly the `−2` that turns `1−s/2` into `−s/2−1`. Composed with `psiTheta_transform` this is the entire content of the functional equation. |
| `FE.inv_cpow_ofReal`, `ofReal_sq_inv_eq_cpow`, `inv_image_Ioi_one` | — | **absent-in-Coq** | `(1/u)^w = u^{−w}` with **no branch-cut side conditions**, because `cpow_pos_eq_exp` reduces both sides to `exp` of a *real* logarithm; the Jacobian `1/u²` as `u^{−2}`; and inversion carrying `(1,∞)` onto `(0,1)`. |
| Method note: `integral_image_eq_integral_abs_deriv_smul` | — | — | The Jacobian form was needed again, for the same reason as `PNT/Substitution.lean`: `integral_comp_smul_deriv_Ioi` demands `ContinuousOn g` on the image, and `g` here involves `psiTheta`, whose continuity is not in hand. Two independent clusters have now hit this; the Jacobian lemma asks nothing of `g`, which is why it is the right default. |
| Method note: `Complex.real_smul` will not `rw` | — | — | The `SMul ℝ ℂ` instance the Jacobian lemma produces is defeq to, but not syntactically, the one `Complex.real_smul` is stated with — so `rw` reports "did not find an occurrence" against a goal that visibly contains `r • z`. `change` bridges it. Same family as the recorded "prints identically but does not unify" hazard. Separately, `field_simp` declined to clear `(1−s)⁻¹` and `s⁻¹` in `integral_pole_terms` even with both nonvanishing facts in context; an explicit `linear_combination` against the two cancellation identities closes it. |
| **`FE.completedZeta_symm`, `completedZeta_eq`** | `RiemannThetaFE.v:28 J_symmetric` + `MellinHead.v:67 Hu_spec` | **cross-verified (real `s`) / overtake (complex `s`)** | **The functional equation.** `Λ(1−s) = Λ(s)` unconditionally, and `Λ(s) = π^{−s/2}Γ(s/2)ζ(s)` for `Re s > 1`. **Both developments organise it the same way, and the honest reading matters:** Coq *defines* `J s := T s + T(1−s) − 1/s + 1/(s−1)` and gets `J_symmetric` by `ring`; the content is in `Hu_spec`, which proves the head integral `∫₀¹` converges to `T(1−s) − 1/s + 1/(s−1)`. The Lean `Λ` is defined the same manifestly-symmetric way, and the content is likewise in `mellin_eq_completedZeta`. **Two real differences:** Coq's `J` takes a *real* `s` and uses Riemann integrals; this is complex `s` with Bochner integrals. And Coq never performs the `(0,1) → (1,∞)` change of variable at all — its head kernel `hker s u := Ψ(1/u)·u^{−s/2−1}` is *defined* already folded on `[1,∞)`, so `integral_Ioo_eq_integral_Ioi_inv` has no Coq counterpart. |
| **`FE.norm_psiNat_le`, `norm_psiTheta_le`, `psiBound`** | — | **absent-in-Coq (overtake)** | **Exponential decay: `‖ψ(a)‖ ≤ (1−e^{−π})⁻¹·e^{−πa}` for `a ≥ 1`.** Elementary — `(n+1)² ≥ n+1` dominates the theta series termwise by a geometric series — but it is *load-bearing*: it is what makes `∫₁^∞ ψ(t)t^{σ−1}dt` converge for **every** real `σ`, and after the fold the surviving exponent `(1−s)/2−1` has *negative* real part precisely when `Re s > 1`. None of the `Re s > 1` Gamma machinery in `Mellin/Term.lean` reaches that case. Coq's `MellinTail.v` gets convergence of `T` from `Psi_bound` in the same spirit but never isolates a decay constant. |
| `FE.integrableOn_cpow_mul_psiTheta`, `integrableOn_rpow_mul_exp_neg_pi` | — | **absent-in-Coq** | `u^w·ψ(u)` integrable on `(1,∞)` for **every** complex `w`, and `u^σe^{−πu}` for every real `σ`. The `σ ≤ 0` case is handled by dominating `u^σ ≤ u^{max σ 0}` — valid precisely because `u ≥ 1`. |
| `FE.aestronglyMeasurable_psiTheta` | — | **absent-in-Coq (different foundation)** | `ψ` is measurable as a pointwise limit of its continuous partial sums, via `aestronglyMeasurable_of_tendsto_ae`. Proving `ψ` *continuous* would need locally uniform convergence and is not required. Coq's `RiemannPsiCont.v` does prove continuity, because Riemann integration gives no measurability route — a foundational difference, not a mathematical one. |
| **Coq `XiC_symmetric` / `J_symmetric` are symmetric *by construction*** | `RiemannXiEntire.v:40`, `RiemannThetaFE.v:28` | **scope clarification (not a defect)** | Both Coq "functional equations" are `ring` identities on objects *defined* to be symmetric: `XiC z := ½ + ½z(z−1)(TC z + TC(1−z))` and `J s := T s + T(1−s) − 1/s + 1/(s−1)`. This is honest and standard — it is how Riemann's argument goes — but it means neither is a proof that ζ satisfies a functional equation. That content lives in the links (`Hu_spec`, `ZetaCompleted.v:58 zeta_completed_eq_J`, `ZetaXiLink.v`), which hold at **real `s`** only. The same caveat applies to the Lean `completedZeta_symm`, and is stated in its docstring. |
| **Coq PNT is still conditional** | `PNTUnconditional.v:27 pnt_of_self_improve` | **correction to scope, Lean overtake stands** | The Coq side has advanced a great deal (77 commits, 58 new `.v` files), and `PNTUnconditional.v` now isolates PNT to a *single* research lemma: `pnt_of_self_improve` takes `(∀ L, is_limsup Vrem L → 0 < L → False)` as an explicit hypothesis, discharged only via `SelbergSelfImprove.v`'s `self_improve_of_dip`, itself conditional on `lambda2_dip`. So Lean's `PNT.tendsto_piCount` remains **unconditional** and the overtake stands — but the gap is now one named lemma on an elementary Erdős–Selberg route, not a missing chain. |
| **Still zero Coq results linking `Cconj` to `zetaC`** | — | **re-verified after 77 new commits** | Re-checked against the new `CoherenceSingularity.v` (`XiC_line_conj : XiC(1−z̄) = conj(XiC z)`) and `SpectralReflectionBridge.v`. Every conjugation result remains about **`XiC`**, never `zetaC`. `Zeta.zetaCont_conj` stays an overtake. |
| `Zeta.refl_involutive`, `refl_fixed_iff` | `SpectralReflectionBridge.v:73 Sbar_involutive`, `:86 Sbar_fixed_iff` | **newly cross-verified** | Coq now has the same antiholomorphic involution `Sbar z := 1 − z̄` with both facts, in a file that postdates the earlier snapshot. Previously `refl_fixed_iff` was cross-verified against `ZetaZeroQuadruple.v:142` alone; `refl_involutive` had no oracle and now does. Coq additionally proves `RH_iff_no_left` / `RH_iff_no_right` (one-sided RH reductions), which Lean does not have. |
| Method note: unreduced beta-redexes defeat `rw` | — | — | The `EqOn` goal from `IntegrableOn.congr_fun` arrives as `(fun u ↦ …) u = (fun x ↦ …) u`, and `rw` cannot see through the redexes — it reports "did not find an occurrence" against a goal that visibly contains the pattern. `dsimp only` first. Third distinct member of the "prints identically but does not match" family this cluster, after the `Complex.real_smul` instance mismatch and the `field_simp` inverse-clearing failure. |
| `spectral-theory/LEDGER.md:239`, `JacobiTheta.v` footer | — | **stale** | Both still describe the theta transformation as "the open next milestone". It landed in Coq on 2026-07-31 (28 files, 5864 lines). Not a defect in the mathematics — a stale status note on a result that exists. |

| **`FE.differentiable_mellinTail`** | — | **absent-in-Coq (overtake)** | **The tail transform `M(w) = ∫₁^∞ u^w·ψ(u)du` is ENTIRE.** Differentiation under the integral sign via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The `w`-derivative of `u^w` is `log u·u^w`, so the dominating function gains a `log u` — absorbed by `log u ≤ u` on `[1,∞)`, which merely shifts the exponent by one and lands back in `integrableOn_rpow_mul_exp_neg_pi`. **No half-plane restriction survives**, because the decay bound already covered every exponent. Coq has no complex differentiation-under-the-integral, so no counterpart. |
| **`FE.differentiableAt_completedZeta`** | — | **absent-in-Coq (overtake)** | **`Λ` is holomorphic on `ℂ \ {0,1}`.** Via `completedZeta_eq_mellinTail`, which rewrites `Λ(s) = 1/(s−1) − 1/s + M(s/2−1) + M((1−s)/2−1)` — two affine precompositions of an entire function plus two explicit poles. This is the hypothesis the identity theorem needs to push `Λ(s) = π^{−s/2}Γ(s/2)ζ(s)` from `Re s > 1` into the strip. |
| Method note: the elaborator unfolds `mellinTail` in `DifferentiableAt.comp` | — | — | `exact DifferentiableAt.comp s (differentiable_mellinTail _) h` fails: with `g` unconstrained the elaborator unfolds `mellinTail` to its `integral` and tries to split the composition there, ending in `NormedAddCommGroup (ℝ → ℂ)`. Pinning both functions through a `have` with the explicit `mellinTail ∘ fun z => …` type fixes it. |

| **`FE.completedZeta_eq_zetaCont`** | — | **absent-in-Coq (overtake)** | **`Λ(s) = π^{−s/2}Γ(s/2)ζ(s)` for `Re s > 0`, `s ≠ 1`** — not just `Re s > 1`. This is what turns everything cluster A proved about `Λ` into a statement about `ζ`. **The trick that makes it easy:** both sides have a simple pole at `s = 1`, so rather than work on a punctured region (and prove it preconnected), multiply through by `s − 1` and write the products with the pole *symbolically* cancelled — `poleFreeL`/`poleFreeR` are manifestly holomorphic on the convex `{Re s > 0}`. The Coq side has no complex analytic continuation of `zetaC` past `Re s = 1` at all, so `ZetaXiLink.v` remains a real-ray statement. |
| **`FE.zetaCont_zero_quadruple`, `zetaCont_zero_refl`** | `ZetaZeroQuadruple.v` (about `XiC`) | **absent-in-Coq for `zetaC` (overtake)** | **The Klein four-group on `ζ`'s own zeros.** `ζ(s) = 0` in the strip implies `ζ(s̄) = ζ(1−s̄) = ζ(1−s) = 0`. Before this, only conjugation was available on the `ζ` side (`zetaCont_eq_zero_conj`); `s ↦ 1−s` existed only for `Λ`. Coq's quadruple results are all about `XiC`, which is tied to `zetaC` only on the real ray. |
| `FE.completedZeta_eq_zero_iff` | — | **absent-in-Coq** | The zeros of `Λ` and of `ζ` coincide on `Re s > 0`, `s ≠ 1`, since `π^{−s/2}` and `Γ(s/2)` are both nonvanishing there. |
| **Correction to my own claim last turn** | — | **correction** | I said `zetaCont_zeros_in_strip` "assumes the left edge rather than proving it", implying a defect. That was overstated: `0 < Re s` is the *domain of definition* of `zetaCont`, not a gap in an argument — there is nothing there to prove. The genuine gain from this cluster is not the left edge but the **transfer**: cluster A's results now apply to `ζ` rather than to the auxiliary `Λ`, and the `s ↦ 1−s` generator reaches `ζ`'s zeros for the first time. |
| Method note: `rw` picked the wrong side | — | — | In `poleFreeR_eq`, `rw [poleFreeR, zetaCont, mul_add, …]` rewrote the `Γ·(1 + …)` on the **left** instead of the intended `(s−1)·(1/(s−1) + …)` on the right — `mul_add` matched the first occurrence. Isolating the intended rewrite in a `have` whose statement has only one match fixes it. |

| **`FE.differentiableAt_zetaFE`** | — | **absent-in-Coq (overtake)** | **`ζ` is holomorphic on `ℂ \ {0,1}`** — the first statement in this development that `ζ` continues past `Re s > 0` at all. Coq has no complex continuation of `zetaC` beyond `Re s = 1`. |
| **`FE.zetaFE_eq_zetaCont`** | — | **absent-in-Coq** | The continued function agrees with `zetaCont` on `Re s > 0`, `s ≠ 1`, so `zetaFE` is *the* continuation and not a rival object. Without this the previous row would be about an unrelated function. |
| **`FE.zetaFE_trivial_zero_genuine`, `differentiable_inv_Gamma_half`** | — | **overtake, and a correction to my own earlier proof** | **The trivial zeros, upgraded from conventional to genuine.** Earlier `zetaFE_trivial_zero` held by Lean's `x/0 = 0` convention — true, but the proof was not the mathematics, and I flagged it as such at the time. The fix is `Complex.differentiable_one_div_Gamma`: mathlib's junk value `Γ(−n) = 0` is not arbitrary, it is the unique assignment making `s ↦ (Γ s)⁻¹` **entire**. Writing `zetaFE` as a product with `(Γ(s/2))⁻¹` rather than a quotient makes `ζ(−2n) = 0` the vanishing of a **holomorphic function at a point**. The old statement is kept and superseded rather than deleted. |
| **`FE.zetaFE_eq_zero_iff_of_re_lt_zero`** | — | **absent-in-Coq (overtake)** | **Off the strip, the trivial zeros are the ONLY zeros:** for `Re s < 0`, `ζ(s) = 0 ↔ ∃n, s = −2n`. Both `Λ(s)` and `π^{s/2}` are nonvanishing there, so every zero comes from `Γ`'s poles, which are exactly the non-positive integers (`Complex.Gamma_eq_zero_iff`). Together with `completedZeta_zeros_in_strip` this accounts for **every** zero of `ζ` outside the closed strip. |
| Scope note: `s = 0` is excluded, not claimed | — | — | `Λ`'s pole at `0` is cancelled by `1/Γ`'s zero there — which is why `ζ(0) = −1/2` is finite — but that cancellation is a separate brick and is **not** proved. `0` is excluded from `differentiableAt_zetaFE` rather than silently absorbed. |

| **`FE.zetaFE_functional_equation`** | — | **absent-in-Coq (overtake)** | **`ζ(1−s) = 2·(2π)^{−s}·cos(πs/2)·Γ(s)·ζ(s)` for `Re s > 1`** — the classical shape, from `Λ(s) = Λ(1−s)` by Euler reflection plus Legendre duplication. **The delicate point is the odd integers:** at `s = 2m+1` the factor `Γ((1−s)/2) = Γ(−m)` has a pole, so the reflection step cannot be run by dividing — but `cos(πs/2)` vanishes at exactly those points, so the identity survives with both sides `0`. `inv_Gamma_half_sub` is therefore proved by an explicit case split, and the result is valid on **all** of `Re s > 1`, odd integers included. Coq has neither Γ-reflection nor duplication for complex argument. |
| **`FE.zetaFE_trivial_zero_via_cos`** | — | **absent-in-Coq** | **The trivial zeros, a third and independent way:** `ζ(−2m) = ζ(1−(2m+1)) = 0` because `cos(π(2m+1)/2) = 0`. The development now has three routes to the same fact, each locating the cause differently — `completedZeta_ne_zero_at_trivial` (the zero is the Γ-pole, not `Λ`), `zetaFE_trivial_zero_genuine` (a holomorphic function vanishing at a point), and this one (read straight off the classical FE). Three independent derivations of one fact is the strongest internal consistency check this project produces. |
| `FE.inv_Gamma_half_sub`, `gamma_ratio` | — | **absent-in-Coq** | Euler reflection in reciprocal form, valid **including** at the poles of `Γ(1/2−z)`; and the combined factor `Γ(s/2)/Γ((1−s)/2) = cos(πs/2)Γ(s)2^{1−s}√π/π`. |
| Method note: `field_simp` rewrites inside `Γ`'s argument | — | — | In `inv_Gamma_half_sub`, `field_simp` normalised `Γ(1/2 − z)` to `Γ((1−2z)/2)` and commuted `cos(↑π * z)` to `cos(z * ↑π)` — so `linear_combination` could not match its own hypothesis. `field_simp` treats the Γ-argument as an ordinary subterm; it has no reason not to. Building the product identity directly and closing with `inv_eq_of_mul_eq_one_right` avoids the normalisation entirely. Fifth member of the "prints identically but does not match" family. |

| **`FE.completedZeta_im_eq_zero`, `completedZeta_conj_eq_self`, `completedZeta_refl`** | **`CoherenceSingularity.v:45 coherence_line`** | **cross-verified** | **`Λ` is real-valued on the critical line.** The two symmetries compose to a *function* identity — `Λ(refl s) = Λ(1−s̄) = Λ(s̄) = conj(Λ(s))` — and `refl s = s` exactly on `Re s = 1/2`. This is the first statement in the development about `ζ`'s **values** on the critical line rather than about symmetries of its zero set. Coq's `coherence_line` is literally `Re z = /2 -> Im (XiC z) = 0`, so this is a genuine two-development check, subject to the standing caveat that Coq's `XiC` is symmetric by construction and tied to `zetaC` only on the real ray. |
| **`FE.completedZeta_half_re_lt_zero`** | — | **absent-in-Coq (overtake)** | **`Λ(1/2) < 0`.** The pole terms give exactly `−4`; the tail is bounded by `2·psiBound·e^{−1} ≤ 2` using the A10 decay bound and `e^{−πu} ≤ e^{−u}`. Note the self-duality showing through: at `s = 1/2` the two exponents `s/2−1` and `(1−s)/2−1` **coincide** at `−3/4`, which is what makes the integrand simply `2u^{−3/4}ψ(u)`. |
| **Scope, stated plainly: no nontrivial zero is exhibited** | — | — | The two rows above are **half** of an intermediate-value argument, not an existence proof. `Λ` is real on the line and negative at the centre; producing a zero needs `Λ(1/2 + it) > 0` for some `t`, and the first zero sits at `t ≈ 14.13` — rigorous numerics at that height, not a corollary of anything built. **Every zero-set theorem in clusters A13–A17 remains conditional on `ζ(s) = 0` and is vacuous until existence lands.** The only other route is Hadamard factorisation (ξ entire of order 1), a large independent development. |
| `FE.psiBound_le_two`, `exp_neg_pi_le_quarter` | — | — | Numeric slack for the above, from `Real.add_one_le_exp`: `e^{−π} ≤ 1/(π+1) ≤ 1/4`, hence `psiBound = (1−e^{−π})⁻¹ ≤ 2`. All bounds are deliberately loose — the true tail is ≈ 0.03 against a budget of 4. |

| **`FE.differentiable_xi`** | `RiemannXiEntire.v:26 XiC_entire` | **cross-verified (different construction)** | **Riemann's `ξ(s) = s(s−1)/2·Λ(s)` is entire.** Same symbolic-cancellation trick as `Transfer.lean`: expanding `Λ` and multiplying through gives `ξ(s) = 1/2 + s(s−1)/2·(M(s/2−1) + M((1−s)/2−1))`, in which **no pole appears at all**, so entirety needs no removable-singularity argument. Coq's `XiC_entire` proves the same for its `XiC`, but that object is *defined* as a symmetrised combination of the tail `TC`; this one is defined from the Mellin transform and shown entire. |
| **`FE.xi_symm`** | `RiemannXiEntire.v:40 XiC_symmetric` | **cross-verified** | `ξ(1−s) = ξ(s)`, unconditionally — the functional equation in its cleanest form. Both developments get it by `ring` after the substitution, which is honest in both cases: the content sits upstream in `completedZeta_eq` / `Hu_spec`. |
| **`FE.xi_zeros_in_strip`, `xi_eq_zero_iff`, `xi_zero`, `xi_one`** | — | **absent-in-Coq (overtake)** | **Clearing the poles introduces no zeros:** `ξ(0) = ξ(1) = 1/2 ≠ 0`, so the zeros of `ξ` are *exactly* those of `Λ`, hence exactly the nontrivial zeros of `ζ`, and all lie in the closed strip. This also retires the `{0,1}` exclusions carried since A16 — `ξ` needs no excluded points at all. |
| **`FE.xi_im_eq_zero`, `xi_half_re_pos`** | — | **absent-in-Coq** | `ξ` is real on the critical line (the prefactor is real there too: `conj(s(s−1)) = (1−s)(−s) = s(s−1)`), and `ξ(1/2) = −Λ(1/2)/8 > 0`. Note the **sign flip** against `completedZeta_half_re_lt_zero`: the prefactor `s(s−1)/2 = −1/8` is negative at the centre, so `Λ(1/2) < 0` while `ξ(1/2) > 0`. Both are recorded because the two objects genuinely disagree in sign and it would be easy to misquote one for the other. |
| **Existence is still open — restated after A19** | — | — | `ξ` entire is what *both* remaining routes to existence require (Hadamard factorisation directly; contour/zero-counting via entirety). Neither is built. `xi_half_re_pos` plus `xi_im_eq_zero` give a real positive value at the centre of the line, which is one endpoint of an IVT — the other endpoint still needs rigorous numerics near `t ≈ 14.13`. **No nontrivial zero is exhibited anywhere in this development.** |

| **mathlib gap: Hadamard *factorisation* is absent** | — | **blocking finding, not a td-theory defect** | `Mathlib/Analysis/Complex/Hadamard.lean` is the **three-lines** theorem, not the factorisation theorem. A repo-wide search of `Mathlib/Analysis/` finds **no** Weierstrass products, **no** genus, **no** order-of-growth theory for entire functions. mathlib *does* have `JensenFormula.lean`, `BorelCaratheodory.lean` and Nevanlinna `ValueDistribution/LogCounting`, which are the raw materials — but the factorisation theorem itself would have to be built. **Consequence: the Hadamard route to existence of nontrivial zeros is a large independent project, not a brick.** Recorded here so the estimate is not re-derived later. |
| **`FE.norm_mellinTail_le_gamma`** | — | **absent-in-Coq (overtake)** | **The Γ-form growth bound:** `‖M(w)‖ ≤ psiBound·π^{−(σ+1)}·Γ(σ+1)` for `σ = Re w ≥ 0`, since `∫₁^∞ u^σe^{−πu}du ≤ ∫₀^∞ u^σe^{−πu}du = Γ(σ+1)/π^{σ+1}`. This is the analytic input any finite-order argument consumes. |
| `FE.norm_mellinTail_le_of_nonpos`, `integral_rpow_mul_exp_neg_pi` | — | **absent-in-Coq** | For `Re w ≤ 0` the tail is merely bounded (`u^σ ≤ 1` on `[1,∞)`), and the Γ integral is evaluated by reusing `Mellin/Term.lean`'s `integral_norm_term` at a real parameter. |
| **`FE.norm_xi_le`** | — | **absent-in-Coq (overtake)** | A growth bound for `ξ` on `Re s ≥ 2`: the `M(s/2−1)` term carries the Γ-factor, the reflected term is merely bounded. **Scope, explicit:** converting `Γ(Re s/2)` into the literal order-1 statement `‖ξ(s)‖ ≤ exp(C‖s‖log‖s‖)` requires Stirling and is **not** proved. The bound itself is what is delivered, and it is the reusable object. |

### 3.1f The critical strip — what the functional equation unlocked

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| **`FE.completedZeta_zeros_in_strip`** | `XiTwoSided.v` (under `Hypothesis`) | **overtake (unconditional)** | **Every zero of `Λ` has `0 ≤ Re s ≤ 1`.** The `Re s > 1` half is the three factors `π^{−s/2}`, `Γ(s/2)`, `ζ(s)` each being nonzero; the `Re s < 0` half follows **by symmetry alone** and was simply unreachable before `completedZeta_symm`. Recorded earlier: Coq's `XiC_zeros_in_strip` sits under two `Hypothesis` declarations (`H_compl`, `H_gamma`). These are unconditional. |
| **`FE.completedZeta_ne_zero_at_trivial`** | — | **absent-in-Coq (overtake)** | **The content of the trivial zeros:** `Λ(−2n) ≠ 0` for `n ≥ 1`, so the zero of `ζ` at `−2n` comes **entirely from the pole of the `Γ`-factor and not from `Λ`**. |
| `FE.zetaFE`, `zetaFE_eq_zetaSeries`, `zetaFE_trivial_zero` | — | **absent-in-Coq, and partly conventional** | `ζ` continued past `Re s ≤ 0` by `ζ(s) := Λ(s)π^{s/2}/Γ(s/2)`, agreeing with the Dirichlet series on `Re s > 1`. **`zetaFE_trivial_zero` is flagged as weak on purpose:** mathlib assigns `Γ` the junk value `0` at its poles, so `Λ/Γ = Λ/0 = 0` holds by Lean's division convention rather than by a limit. The statement is true but the proof is not the mathematics; the mathematics is the row above. Both the module docstring and the theorem docstring say so. |
| **`FE.completedZeta_conj`**, `conj_psiTheta` | `CoherenceSingularity.v:38 XiC_line_conj` | **cross-verified (different object)** | `Λ(s̄) = conj(Λ(s))`, because `ψ` is real on `ℝ`. Coq's `XiC_line_conj` is the composite form `XiC(1−z̄) = conj(XiC z)` for its symmetrised `XiC`; this is the plain conjugation law for the Mellin-defined `Λ`. |
| **`FE.completedZeta_zero_quadruple`, `completedZeta_zeros_refl_invariant`** | `ZetaZeroQuadruple.v`, `SpectralReflectionBridge.v:62 zeros_S_symmetric` | **cross-verified** | **The Klein four-group `{s, 1−s, s̄, 1−s̄}` acting on the zero set of `Λ`** — now with *both* generators proved rather than assumed. The composite is exactly `Zeta.refl`, whose fixed-point set is the critical line (`refl_fixed_iff`). **This is where the symmetry package stops and RH begins:** the zeros are invariant under an involution fixing `Re s = 1/2`; RH says they *are* its fixed points. Nothing here bears on that. |
| Method note: `RCLike ℂ` instance mismatch | — | — | `rw [← integral_conj]` fails against a goal that visibly contains `conj (∫ …)` — the `RCLike ℂ` instance in the goal is defeq to but not syntactically the lemma's. Stating the rewrite via `show … from integral_conj.symm` lets elaboration bridge it. Fourth member of the "prints identically but does not match" family, after `Complex.real_smul`, `field_simp` inverse-clearing, and beta-redexes in `EqOn` goals. |

### 3.1e The critical line — the symmetry package

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| **`Zeta.zetaCont_conj`** | — | **absent-in-Coq (overtake)** | **`ζ(s̄) = conj(ζ(s))`**, hence `zetaCont_eq_zero_conj`: the zero set is symmetric about the **real axis**. Needs **no functional equation** — only that the Dirichlet coefficients are real. **A repo-wide search finds zero Coq results connecting `Cconj` to `zetaC`**: every conjugation result in `spectral-theory/` is about `XiC` (`ZetaZeroQuadruple.v:71,111,125`), which `ZetaXiLink.v:18` ties to ζ only on the real ray `s > 1`, so none of them constrains a zero of ζ off that ray. mathlib has no zeta-conjugation lemma either. |
| `Zeta.conj_intervalIntegral` | — | **absent-in-mathlib** | Conjugation through an interval integral, **unconditionally**. mathlib has root-level `integral_conj` (`Bochner/ContinuousLinearMap.lean:175`, no integrability hypothesis) but no interval version; `intervalIntegral` unfolds to a difference of set integrals, so it follows in two lines. This dodged the `IsScalarTower ℝ ℂ ℂ` diamond entirely — the `conjCLE` route I had planned would have cost an integrability side goal. |
| **`Zeta.refl_fixed_iff`** | `ZetaZeroQuadruple.v:142 line_reflection_fixed` | **cross-verified (strengthened)** | `refl z = 1 − z̄` is an involution, and **its fixed-point set is exactly the critical line**: `refl z = z ↔ Re z = 1/2`. The Coq statement is the forward direction only; the Lean form is an iff. |
| `Zeta.RiemannHypothesis`, `RH_iff_zeros_refl_fixed` | `spectral-theory/RiemannHypothesis.v:33` (about `XiC`) | **statement only, not proved** | RH as a machine-checked proposition about **`zetaCont` itself**, plus the equivalence with `refl`-fixedness. The Coq statement is about `XiC`, so — per finding #1 — it is not yet provably equivalent to RH for ζ. |
| `Zeta.FunctionalEquationSymmetry`, `zeros_refl_invariant` | — | **the gap, named** | `refl = (z ↦ 1−z) ∘ (z ↦ z̄)`. The conjugation half is **proved**; the `z ↦ 1−z` half **is** the functional equation and is not. Naming it as a predicate, with `zeros_refl_invariant` showing it suffices, makes the missing piece machine-visible instead of prose. **This does not approach RH.** |

### 3.2 Findings recorded during planning, pending Lean proof

| Coq oracle | Verdict | Note |
|---|---|---|
| `ZetaFunctionalEq.v:25 LambdaC_FE` | **narrower-than-named** | Reads as the functional equation for ζ. `LambdaC` is *defined* (`:21`) from the entire theta-tail `XiC`; the tie to zeta (`LambdaC_agree :35`, `ZetaXiLink.XiC_is_completed_zeta`) holds **only for real `s > 1`**. Symmetry is on all of ℂ; the identification with `π^{−s/2}Γ(s/2)ζ(s)` is on a ray. Bridging needs an identity theorem, and the repo has only *polynomial* ones (`QPolyPIT.v`, `IntPolyDerivResp.v`). Planned Lean A11 states it on the half-plane `1 < re s`; A13 closes the gap with `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. |
| `RiemannThetaFE.v:28 J_symmetric` | **confirmed-but-trivial** | Proof is `ring`. `J s := T s + T(1−s) − /s + /(s−1)` is symmetric by construction, as is `xi_eq_J` (also `ring`). The genuine content is in `MellinTail.T_spec` and `MellinHead.Hu_spec` — which *are* real theorems. Not a defect, but the name oversells the line. |
| `FEResidue.v Gamma_half_is_sqrt_pi` | **narrower-than-named** | Not about Γ. `GammaHalf := constructive_sqrt_pi`, `piR := constructive_pi` (Wallis), so it proves `(√π_Wallis)² = π_Wallis`. The file's own header admits the identification with Γ(1/2) and the circle π is unformalized. Honest Lean counterpart is `Real.Gamma_one_half_eq`, a one-liner — **do not port**. |
| `docs/monoid_algebra_prime_length.md` — the `⋉` | **corrected** | The doc advertises `ℤ[M_p] ≅ ℤ[ℤ/(p−1)] ⋉ ℤδ₀`. From `gconv_adj_zero_full`, `(x,s)(y,t) = (xy, ε(x)t + ε(y)s + st)`; substituting `s ↦ ε(x)+s` splits it. **It is a direct product `×`, not semidirect.** Planned Lean B4 states the sharpened form. |
| `PrimorialSpectralTheory.v:19` CLAIM A | **corrected** | "The limit is the full adelic ring `∏_p ℤ_p`." False: every primorial modulus is squarefree, so exponents never grow and the limit is `∏_p 𝔽_p`. `Ẑ` is the limit of the prime-**power** tower. `docs/monoid_algebra_prime_length.md:259` diagnosed this but the correction was never landed in any `.v` file or in the Coq LEDGER. Now machine-checked in `TDLean/MonoidAlgebra/PrimorialLimit.lean` (`squarefree_prod_primes`, `toZMod_not_injective`). Note CLAIM A is a *comment*, not a theorem — the file proves only that primorials grow. |
| `docs/ncg_monoid_algebra_thesis.md:24` | **corrected** | Same conflation, second site: maps `ProfiniteCRT` / cyclic units to "the BC symmetry group `Ẑ^× = ∏_p ℤ_p^×`". What the primorial tower reaches is `∏_p 𝔽_p^×`, a **proper** quotient (kernel `∏_p (1+pℤ_p)`); `toZMod_not_injective` witnesses the failure at a single prime. |
| `docs/ncg_monoid_algebra_thesis.md:41-45` | **narrower-than-named** | Milestones 1–2 (`Tr(e^{−βN}) = ζ(β)`, primes as spectrum) build the **primon gas**, the commutative bosonic Fock picture that `Ell2Zeta.v` essentially already has — not Bost–Connes, whose content is entirely the crossed product `ℂ[ℚ/ℤ] ⋊ ℕ^×` and its KMS states. Likewise `HagedornTransition`'s β = 1 transition is classical free energy, the right shadow but not a KMS transition. |
| `no_antipode` | **absent-in-Coq** | Listed in the plan doc as Brick 2 item 4 ("~5 lines") and described in `MonoidAlgebraZero.v:108`'s comment, but repo-wide grep finds **no such theorem**. `AdjRatioBreak.azero_no_inverse` refutes only `b ⋆ δ₀ = gunit`; the antipode axiom `m∘(S⊗id)∘Δ = η∘ε` is never contradicted. Planned Lean B5 proves it — an overtake. |
| `HopfGroupTensor.tconv` | **narrower-than-named** | The Coq repo has **no tensor product**; `tconv` is a hand-rolled 4-fold sum on `A → B → Z` and `gconv_prod_tensor` is a *currying* identity. So "ℤ[M₆] ≅ ℤ[M₂] ⊗ ℤ[M₃]" is really "ℤ[M₂×M₃] ≅ (M₂ → M₃ → ℤ)". Planned Lean B10 states the genuine `⊗`. |

### 3.2b Corrections to my own earlier entries

Two errors of mine, found by a later audit of the Rocq repo. Recording them here because the
whole point of this ledger is an honest account, and a wrong "overtake" verdict inflates the
Lean side's contribution.

- **`zetaCont_ne_zero_of_one_le_re` was NOT an overtake.** I classified C9 item 3
  (`ζ(1+it) ≠ 0`) as absent-in-Coq. It is **not**: `spectral-theory/ZetaLineNonzero.v:103
  zetaC_line_nonzero` proves exactly this, unconditionally, `Qed.`, with a 93-file dependency
  closure containing **zero** `Axiom`/`Parameter`/`Admitted`. It is the genuine Mertens 3-4-1
  argument (`ThreeFourOne.v` + the pole bound `zeta_cont_pole` + `CZetaHolo.zetaC_holo`), and
  `zetaC` there is a real Euler–Maclaurin continuation, not a stand-in. The row above is
  corrected to **cross-verified**. What *is* genuinely absent in Rocq remains C9 item 4
  (`Φ⁻` holomorphic at `s = 1`) — the repo's own `docs/newman_route_status.md` says so.
- **`XiC_zeros_in_strip` is conditional, and I stated it as unconditional.**
  `spectral-theory/ZetaStripConfinement.v:76` sits inside `Section Confinement` with two
  `Hypothesis` declarations, both annotated "(to be discharged later)": `H_compl` (the complex
  completion identity `Λ(w) = π^{−w/2}Γ(w/2)ζ(w)` for `Re w > 1`) and `H_gamma` (Γ non-vanishing).
  After `End Confinement` the exported statement carries both as premises. **`H_compl` is
  precisely the off-ray link that finding #1 is about**, so the strip confinement does not
  currently confine any zero of `ξ`.

Also worth reporting upstream: `spectral-theory/ZetaStripConfinement.v` and
`spectral-theory/RiemannHypothesis.v` are absent from `_CoqProject` (919 of 922 `.v` files are
listed). Stale `.vo` files exist, so they compiled once, but they are not part of `make` — and
they are the two most carefully-hedged RH files in the repo. Likely a namespace collision with
`packages/GHS/RiemannHypothesis.v`, since `_CoqProject` maps every directory to the root
namespace.

### 3.2c Cluster O — the operator side, over ℂ

| Lean | Coq oracle | Verdict | Note |
|---|---|---|---|
| **`Operator.ip_diag_adjoint`** | `Ell2Operator.v:66 Dmul_selfadjoint` | **overtake** | `⟪D_a f, g⟫ = ⟪f, D_ā g⟫` — the **adjoint**, which does not exist anywhere in the Rocq repo (no `adjoint : Op → Op` is defined; self-adjointness is only ever an ad-hoc equation between inner products). The conjugate on the multiplier is precisely what a real bilinear form cannot see. |
| `Operator.ip`, `Ell2`, `summable_ip` | `Ell2.v:49, :179` | **overtake** | A genuinely **sesquilinear** inner product on `ℓ²(ℕ⁺, ℂ)`. The Rocq `Ell2` is `nat → R` with `ip = Σ f(n)g(n)`, symmetric bilinear, and a repo-wide search finds **zero** `Cconj` in any `Ell2*` file. Convergence via AM–GM on `‖f‖‖g‖ ≤ (‖f‖²+‖g‖²)/2`. |
| **`Operator.eigenvalue_real_of_selfadjoint`** | — | **absent-in-Coq** | Hermitian self-adjointness ⟹ **real eigenvalues**. This is the entire logic of Hilbert–Pólya, and it is unavailable over ℝ: the real symmetric form of `Ell2Operator.v` is a strictly weaker notion that carries no such consequence. |
| `Operator.trace_zetaKernel` | `Ell2Zeta.v:122 zeta_partition` | **cross-verified + extended** | `∑ₙ ⟪δₙ, Z_s δₙ⟫ = ζ(s)` for `Re s > 1`, where `Z_s` is diagonal with entries `n^{−s}`. The Rocq version is a *finite* partial trace with `s : R`; this is the convergent trace at complex `s`, tied to `zetaSeries`. |
| `Operator.isHermitian_zetaKernel_of_real` | — | **absent-in-Coq** | `Z_s` is Hermitian exactly when `s` is real — the operator-side shadow of the fact that `Ell2Zeta.v` could only ever take `s : R`. |

| **`Operator.partitionFunction_eq_zeta`** | — | **absent-in-Coq (overtake)** | **`Tr(e^{−βN}) = ζ(β)` for `Re β > 1`** — milestone 2 of `docs/ncg_monoid_algebra_thesis.md:41`, machine-checked. `N δₙ = (log n)δₙ`, so `e^{−βN}` is the zeta kernel (`gibbs_eq_zetaKernel`). |
| `Operator.numberOp_mul`, `numberOp_pow` | — | **absent-in-Coq** | What makes `N` a *number* operator rather than an arbitrary diagonal: `N(mn) = N(m) + N(n)` and `N(pᵏ) = k·N(p)`. Additivity is exactly the statement that `ℓ²(ℕ⁺)` is a Fock space with one bosonic mode per prime. |
| `Operator.numberOp_eq_sum_vonMangoldt` | `Ell2Zeta.v:149 energy_eq_divisor_sum` | **cross-verified** | `log n = ∑_{d ∣ n} Λ(d)` — the energy of `δₙ` decomposes into prime-power quanta. |
| **`Operator.partitionFunction_diverges`** | — | **absent-in-Coq** | `‖Tr(e^{−σN})‖ → ∞` as `σ → 1⁺`. The free-energy blow-up at the critical temperature, straight from the pole that `zetaCont = 1/(s−1) + zetaDiffSum` isolates by construction. **Honest label:** this is the classical divergence and the right *shadow* of the Bost–Connes transition — it is **not** a KMS statement, and LEDGER 3.2 already records that `HagedornTransition` has the same limitation. |

| **`Operator.coshift_shift`** / **`shift_coshift_ne_id`** | — | **absent-in-Coq (overtake)** | **`Sₙ* Sₙ = 1` but `Sₙ Sₙ* ≠ 1`** — each prime shift `Sₙ δₘ = δₙₘ` is an **isometry, not a unitary**; `Sₙ Sₙ*` is the projection onto multiples of `n` (`shift_coshift_apply`), witnessed failing at `n = 2` on `δ₁`. This single asymmetry is the whole reason Bost–Connes is a crossed product by a *semigroup of isometries* rather than by a group — and it recasts `MonoidAlgebraZero.v:30 adj_no_inverse` from an obstruction into the feature the construction is built on. |
| **`Operator.numberOp_covariance`**, `numberOp_commutator` | — | **absent-in-Coq** | `N Sₙ = Sₙ(N + log n)`: the shift raises energy by `log n`. This is the crossed-product covariance relation and the generator of the BC time evolution `σ_t(Sₙ) = n^{it}Sₙ`. |
| `Operator.ip_shift_adjoint`, `ell2_shift`, `coshift_coshift` | — | **absent-in-Coq** | The adjoint identity `⟪Sₙf, g⟫ = ⟪f, Sₙ*g⟫`, ℓ²-preservation, and the semigroup law. |

| **`Operator.bc_isometry`, `bc_semigroup`, `bc_coprime`, `bc_not_unitary`** | — | **absent-in-Coq (overtake)** | **The Bost–Connes relations as an algebra presentation**, in `Module.End ℂ (ℕ⁺ → ℂ)`: `Sₙ*Sₙ = 1`, `SₘSₙ = S₍ₘₙ₎`, `SₘSₙ* = Sₙ*Sₘ` for `gcd(m,n) = 1`, and `SₙSₙ* ≠ 1`. **BC3 is the substantive one** — it is what makes the `ℕˣ`-action work, its proof is Gauss's lemma (`m ∣ nk` with `gcd(m,n) = 1` ⟹ `m ∣ k`), and `not_comm_of_not_coprime` shows it is **sharp**: the relation fails at `m = n = 2`, so coprimality is doing real work rather than bookkeeping. |
| `Operator.bcAlgebra`, `ip_coshift_adjoint` | — | **absent-in-Coq** | The generated subalgebra `Algebra.adjoin ℂ (range Sop ∪ range Sadj)`. The `*` is realised by the inner product: `ip_shift_adjoint` and `ip_coshift_adjoint` together say the generating set is closed under adjunction w.r.t. `⟪·,·⟫`. **Not** a C\*-algebra: no norm, no completion. |

| **`Operator.nsmul_eq_iff`** | — | **absent-in-Coq (overtake)** | **The BC coupling fibre.** `nδ = γ ↔ δ = nthPart n γ + torsionEmb n k` for a unique `k : ZMod n` — the fibre in `μₙ e(γ) μₙ* = (1/n)∑_{nδ=γ} e(δ)` is exactly a coset of the `n`-torsion, hence has exactly `n` elements, which is what makes `1/n` the right normalisation. Needs both directions: `exists_nsmul_eq` (ℚ/ℤ is **divisible**, so the fibre is nonempty) and `torsionEmb_surjective`. |
| **`Operator.torsionEmb_injective`**, `torsionEmb_surjective` | — | **the bridge to `ProfiniteCRT` / `ZmodUnitsCyclic`** | `(ℚ/ℤ)[n] ≅ ZMod n` via `k ↦ k/n`, so `Aut((ℚ/ℤ)[n]) ≅ (ZMod n)ˣ` — the object `ZmodUnitsCyclic` studies — and in the limit `Aut(ℚ/ℤ) = Ẑˣ`, the BC symmetry group. **This is where the 3.2 correction bites.** `PrimorialSpectralTheory.v:19` CLAIM A and `docs/ncg_monoid_algebra_thesis.md:24` identify the primorial tower's limit with `Ẑ`/`Ẑˣ`; it is not, because every primorial modulus is squarefree, so the tower reaches `∏ₚ 𝔽ₚˣ`, a **proper** quotient (`toZMod_not_injective` witnesses the failure). Getting the BC symmetry group needs the prime-**power** tower. |
| `Operator.egen_mul`, `egen_mul_neg`, `QAlg` | — | **absent-in-Coq** | `ℂ[ℚ/ℤ]` with `e(γ₁)e(γ₂) = e(γ₁+γ₂)`, `e(0) = 1`, and `e(γ)e(−γ) = 1`. Note the contrast the whole construction turns on: the `e(γ)` **are** invertible; the `Sₙ` deliberately are not. |

| **`Operator.Eop_mul`, `norm_chi`, `ip_Eop_adjoint`** | — | **absent-in-Coq (overtake)** | **The Bost–Connes representation on `ℓ²(ℕ⁺)`:** `π(e(γ))εₘ = χ(m·γ)εₘ` with `χ(q) = e^{2πiq}`. `χ` is well-defined on `ℚ/ℤ` exactly because `e^{2πik} = 1` for integer `k` — which is *why* the group must be `ℚ/ℤ` and not `ℚ`. `‖χ‖ = 1`, so each `π(e(γ))` is **unitary**, and `ip_Eop_adjoint` gives its adjoint as `π(e(−γ))` — the sharp contrast with the `Sₙ`, which are isometries only. |
| **`Operator.conj_Eop_apply_mul`**, `conj_Eop_apply_of_not_dvd` | — | **absent-in-Coq** | **The left-hand side of the coupling relation, computed as an operator identity:** `Sₙ π(e(γ)) Sₙ*` is diagonal, supported on multiples of `n`, with entry `χ(i·γ)` at `j = n·i`, and **zero** off the multiples — the projection `SₙSₙ*` showing through. |

| **`Operator.bc_coupling`** | — | **absent-in-Coq (overtake)** | **The Bost–Connes coupling relation, closed as an operator identity:** `μₙ e(γ) μₙ* = (1/n)∑_{nδ=γ} e(δ)` on `ℓ²(ℕ⁺)`. Joins `conj_Eop_apply_mul` (left side) to `nsmul_eq_iff` (the fibre) via character orthogonality. With `bc_isometry`/`bc_semigroup`/`bc_coprime`, the **full BC presentation** is now machine-checked in this representation. |
| **`Operator.sum_chi_torsion`** | — | **absent-in-Coq** | `∑_{k : ZMod n} χ(j·(k/n)) = n·[n ∣ j]` — character orthogonality on the `n`-torsion. This is what *forces* the `1/n` normalisation and makes the right-hand side vanish off multiples of `n`, matching the projection `SₙSₙ*`. Built on `Complex.isPrimitiveRoot_exp_of_coprime` plus `geom_sum_eq`. The finite-field analogue is the repo's own `CharactersModN.v` / `GaussSum.v`. |

**Scope, stated plainly.** None of this approaches RH. Constructing an operator whose
eigenvalues are the zeta zeros *is* the Hilbert–Pólya problem and is open. What is built is the
**framework in which such a statement can be made at all** — inner product, adjoint, Hermitian
self-adjointness, real spectrum, the diagonal zeta operator, and the number operator with its
partition function — none of which existed on either side before. The spectrum of `N` is
`{log n}`, not the zeros; building an operator with the zeros as spectrum *is* Hilbert–Pólya.
The relations `BC0`–`BC3` are the `ℕˣ` half of the presentation. The BC **presentation** is now complete in this representation (`bc_isometry`, `bc_semigroup`,
`bc_coprime`, `bc_not_unitary`, `bc_coupling`). Still missing for BC proper: the representation
is at `ρ = 1 ∈ Ẑ`, the general `π_ρ(e(γ))εₘ = χ(ρ(mγ))εₘ` needing `Ẑ` as an actual parameter
group; a C\*-completion (this is a
plain subalgebra of endomorphisms, no norm); and KMS states, so no phase transition in the KMS
sense. `partitionFunction_diverges`
is the classical free-energy blow-up, not a KMS transition. `millennium-problems/Riemann.v:75` declares `Parameter H_operator` and
`SpectralTripleRH.v` has `st_self_adjoint : True`; those are placeholders, not operators.

### 3.3 Not a td-theory finding — a mathlib gap

- **`Fintype (WithZero α)` is missing.** `WithOne α := Option α` is a plain `def`, so the
  `Option` instances do not fire through it. Supplied locally in
  `TDLean/MonoidAlgebra/ZMod/PrimeIsWithZero.lean` via `inferInstanceAs`.
- **`MonoidAlgebra.tensorEquiv : R[M] ⊗[R] R[N] ≃ₗ[R] R[M × N]`** exists only on mathlib
  master, not in the pinned `v4.29.0-rc6`; and even there it is only a `≃ₗ`, carrying a
  literal `TODO: ... strengthen to an AlgEquiv`. Brick B10 must rebuild it from
  `finsuppTensorFinsupp'`.
- **`Analysis/Complex/HasPrimitives.lean` does not generalise off the ball, two ways.**
  Its Morera route needs the *rectangle* spanned by pairs of region points to stay inside
  the region, and **balls are not rectangle-closed**: for `z = 0.9`, `w = 0.9i` in
  `ball 0 1`, the corner `0.9 + 0.9i` has modulus `1.27 > 1`. mathlib's proof only ever
  moves a coordinate *toward the centre*, which is why it works for a ball and gives
  nothing for free on a general convex set. Separately, every supporting lemma
  (`re_add_im_mul_mem_ball`, `mem_ball_of_map_re_aux`, `hasDerivAt_wedgeIntegral_re_aux`,
  …) is `private`. The file's own `TODO` — "Extend to holomorphic functions on simply
  connected domains" — is still open. Brick C4 therefore uses the radial argument instead.
- **An `ℝ`-on-`ℂ` typeclass diamond, hit twice.** For a *concrete* `ℂ → ℂ` function,
  `NormedSpace ℝ ℂ` resolves through `instInnerProductSpaceRealComplex`, and the resulting
  `SMul ℝ ℂ` does not match the algebra tower. Consequences:
  1. `(hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt` — the natural chain rule for a
     real path through a holomorphic function — fails to synthesise `IsScalarTower ℝ ℂ ℂ`,
     even though that instance *is* provable standalone with the same imports, and even
     with a `haveI` in context. mathlib's own uses of the idiom sit in contexts where the
     codomain is an abstract `E`. **Workaround** (`Contour.lean`): factor each path as a
     genuinely `ℂ → ℂ` map precomposed with `Complex.ofReal`, keeping the chain rule inside
     `ℂ` and finishing with `HasDerivAt.comp_ofReal`.
  2. `intervalIntegral.integral_const` produces `(b - a) • c` with the action routed through
     `SMulZeroClass.toSMul`; neither `rw` nor `simp` will unify that against
     `Complex.real_smul`. The two actions *are* definitionally equal, so `change` cuts
     through (`Winding.lean`).
  Both are mathlib ergonomics issues, not td-theory findings, but they cost real time and
  are recorded so the next brick does not rediscover them.

---

## 4. Complete structure vs curated bundle

Kept from the Coq LEDGER's third axis, in spirit: a theorem of the form
`foo : A ∧ B ∧ C` that bundles standalone results is an **index, not new mathematics**, and
must say so at the bundle. No such bundles exist here yet.

---

## 5. Model deltas worth knowing

These are the places where the two developments genuinely differ, and therefore where a
second verification earns its keep rather than merely repeating the first.

| | Coq (`HopfGroupAlgebraGen.v`) | mathlib |
|---|---|---|
| Algebra carrier | total functions `A → Z` | `MonoidAlgebra R M = M →₀ R` |
| Finiteness | on the **index type**: `elts`, `NoDup`, `elts_all` | on the **element** (`Finsupp`); `M` may be infinite |
| Coefficients | fixed `Z` | any `[Semiring R]` |
| Monoid axioms | section `Variable`s, re-passed at each call site | typeclasses |
| `Adj G` | `Inductive Adj := AZero | AElt g` | `WithZero G` |

Consequence: Coq's `gconv` is not even *definable* for infinite `G`, and its `gconv_assoc`
/ `gconv_unit_l` are proved *from* `elts_all`. In mathlib they are the `Semiring` instance,
unconditional. If Coq's `sumf_sift`/`sumf_single` toolkit had a subtle error, it would show
up as the two developments disagreeing on `mul_apply` — which is exactly the kind of check
this project is for.

For cluster C the delta is starker: the Coq contour wall is ~1887 lines **only because
Rocq's stdlib has no complex analysis**. Line-count comparison is meaningless there; the
target is the Newman argument itself, not the scaffolding.
