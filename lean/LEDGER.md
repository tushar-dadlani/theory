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
| **`Newman.newman_tauberian`** | — | **absent-in-Coq (overtake)** | **Newman's analytic Tauberian theorem, complete.** `f` continuous and bounded by `B`, `g` its Laplace transform on `Re z > 0`, `g` holomorphic past the imaginary axis ⟹ `∫₀ᵀ f → g(0)`. `CNewman.v` does not exist and `docs/newman_route_status.md` lists this as brick 8, open — so this is Lean proving what the Rocq development does not have. Non-vacuity witness included, since the hypothesis set (esp. `hregion`) is elaborate. |
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
| `Zeta.norm_cpow_sub_le`, `norm_zetaDiff_le`, `summable_zetaDiff` | — | **absent-in-Coq** | The increment estimate and convergence of the difference series on `Re s > 0`. |
| `Zeta.differentiableOn_zetaDiffSum` | — | **absent-in-Coq** | Holomorphy, via differentiation under the integral plus `differentiableOn_tsum_of_summable_norm` applied on balls (the term bound carries `‖s‖`, so it is uniform only on bounded sets). |

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
