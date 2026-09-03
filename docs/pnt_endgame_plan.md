# Unconditional PNT — the endgame, decomposed

## Where this stands

✅ **DONE.** The prime number theorem is machine-checked, axiom-clean:

```coq
NewmanE7.PNT : Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1
```

`Print Assumptions PNT` reports exactly the four standard classical-Reals axioms
(`ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`, `Classical_Prop.classic`).
There is no `Admitted`, `Abort`, `Axiom` or `admit` anywhere in the chain.

The route was Newman's analytic proof in Zagier's form, via seven bricks E1–E7 built in
dependency order. The final link is `TintCoV.pnt_of_nf_cauchy : NfCauchy -> PNT`, whose
hypothesis `NfCauchy` — the Cauchy criterion for the tail of `∫₀^∞ f(t) dt` with
`f(t) = ψ(e^t)e^{−t} − 1` — is discharged by `NewmanE7.newman_nf_cauchy`.

*(The rest of this document is the scoping written before E1, kept because the two
structural findings below were what actually shaped the work, and because the per-brick
sections record where the scoping was wrong.)*

## Two findings from auditing the contour side

These change the shape of the remaining work and are **not** recorded anywhere else.

**(1) `Cintf` is defined only for continuous integrands.**
`CIntegral2.v:61` builds it from `cont_RI`, so `Ccont f` is a *parameter of the
definition*, not a convenience hypothesis. Consequently `LaplaceFull.LT`,
`LaplaceFull.gfull`, `NewmanArc.right_arc_bound` and `NewmanLeft.left_arc_bound` — all
stated for `f` with `Hfc : Ccont f` — **cannot be instantiated at Newman's `f`**, which is
a step function. This is the central structural obstacle, and it is why the repo
reached the identity by the cell route (`StepSum`/`OneSum`) instead.

**(2) `PiecewiseTransform.cell_transform_inner` is vacuous.**
It assumes `Hc : Ccont (fun t => Cmul (RtoC (psiR (exp t))) (K t))`, which is *false* for
any `K` not vanishing at the jumps: `psiR ∘ exp` jumps at every `t = ln N` with `N` a
prime power. The lemma can never be applied, and indeed it is used nowhere outside its own
file. Do not build on it.

What *is* sound: `NewmanIdentity.StepSum`/`OneSum` factor `psi (S k)` **outside** the
integral and integrate only `cexpzt`, which is continuous. The identity itself is fine.

## Brick decomposition

Sizes are calibrated against this session's comparable files (`PsiRIntegrable` 255,
`TintCoV` 351, `NewmanCutoff` 255).

### E1 — `CIntegralD.v`: a complex integral for merely-integrable integrands — ✅ **DONE**

139 lines, axiom-clean. Delivered: `CintfD`, `Re_CintfD`/`Im_CintfD`, `CintfD_irrel`
(proof-irrelevance via `RiemannInt_P5`), **`CintfD_Cintf`** (agrees with `Cintf` wherever
both are defined — the bridge to `StepSum`/`OneSum`, which E4 needs), `CintfD_ext_open`
(the transfer, via `RiemannInt_P18` componentwise), `CintfD_split` (Chasles, via
`RiemannInt_P26`), and **`CintfD_ML`** with constant `2`, matching `CIntegral2.Cintf_ML`'s
convention exactly.

Came in at 139 lines against the 250–350 estimate: the transfer needed no new analysis
(`RiemannInt_P18` is componentwise) and the ML bound reduced to a real one-component bound
`RiemannInt_abs_bound`, proved by comparison against `fct_cte` with `RiemannInt_P19`/`P15`.

✅ **The deferred linearity is now built** (`CIntegralDLin.v`, 143 lines, axiom-clean):
`RI_scal_int`, `RI_scal_val`, **`RI_lincomb_val`**, and `CintfD_add`/`CintfD_sub`/
`CintfD_cmul_l`. E5 fixed its shape: proving `g_T` holomorphic **in z** needs the increment
identity `lint(z+h) − lint z − h·ldint z` under the integral, i.e. additivity plus complex
scalars. Everything reduces to the single real lemma `RI_lincomb_val`, because the real and
imaginary parts of `c·f` are each 2-term real combinations of `Re f` and `Im f`.

The obstacle in finding (1) is dissolved rather than worked around.

```coq
Definition CintfD (f : R -> C) a b
  (prRe : Riemann_integrable (fun t => Re (f t)) a b)
  (prIm : Riemann_integrable (fun t => Im (f t)) a b) : C
```

Needed: proof-irrelevance (`RiemannInt_P5` componentwise); agreement with `Cintf` when `f`
is continuous; linearity and `Cmul`-by-constant; Chasles (`RiemannInt_P26`); the ML bound;
and the complex analogue of `PsiRIntegrable.Riemann_integrable_ext_open`. That last one
already exists in the reals and transfers componentwise.

*Alternative considered and rejected*: stay with cell sums throughout. It avoids E1 but
pushes the same case analysis into every later brick, and the ML estimates become much
harder to state.

### E2 — `NewmanTransform.v`: Newman's transform as an honest integral — ✅ **DONE**

182 lines, axiom-clean. Delivered: `cellwise_integrable` (the cell gluing **abstracted**
over the integrand — `TintCoV.nf_int_k` had it inlined for one function), `nfC`, `lintN`,
`Re_lintN`/`Im_lintN`/`Cmod_lintN`, integrability of both components, `LTN` with
`LTN_irrel` and `LTN_split`, plus `nf_closed_form` (`nf t = psiR(e^t)/e^t − 1`),
`nf_bound` (`|nf| <= Kup + 1`) and `LTN_ML`.

`gN` (the `T → ∞` limit) is **deferred to E3**, where the tail bound that proves the
Cauchy property lives — defining it here would have been circular.

*(original scoping below)*


`nf` is already defined in `TintCoV`. Define `nfC t := RtoC (nf t)`, prove
`fun t => nfC t * cexpzt (−z) t` integrable on `[0,T]` by the **same cell argument** as
`TintCoV.nf_int_cell` (continuous on each open cell), then

```coq
LTN (z : C) (T : R) : C          (* the truncated transform, via CintfD *)
gN  (z : C) (Hz : 0 < Re z) : C  (* the T -> oo limit *)
```

Reuse: `TintCoV.nf_cell_eq`, `nf_int_k`, `floor_exp_ge1`, `cell_lo`, `cell_hi`.

### E3 — the tail bound and `gN` — ✅ **DONE**

`NewmanTail.v`, 209 lines, axiom-clean. Delivered: `LTN_tail`
(`<= 2(Kup+1)(e^{-Re z·a} − e^{-Re z·b})/Re z`), `LTN_tail_le` (the one-sided form),
`tailN` with `tailN_nonneg`/`tailN_dec`/`tailN_cv0`, `LTNn_close`/`LTNn_close_sym`,
`LTNn_Re_cauchy`/`LTNn_Im_cauchy`, and **`gN`** with `gN_Re_cv`/`gN_Im_cv`.

`LaplaceFull.LT_tail_bound` proves the same estimate for continuous `f`, but via
`Cintf_mod_le2` (`|∫f| <= ∫|f|`), which needs `Cmod (lint z u)` **integrable** — there had
for free from continuity. `Cmod (lintN z u)` is discontinuous, so that route would have
cost another cell argument. Bounding the two **components** separately against the
continuous majorant `B·exp(−Re z·t)` avoids it entirely, at the cost of the same factor 2
already in `CintfD_ML`.

*(original scoping below)*


`Cmod (gN z − LTN z T) <= B * exp (− Re z * T) / Re z`, mirroring
`LaplaceFull.LT_tail_bound` / `gfull_tail` but for `CintfD`. `B` comes from
`ChebyshevPsiR.psiR_upper` (`psiR x <= x * Kup`), giving `|nf t| <= Kup + 1`.

### E4 — `gN = gext` on `Re z > 0` — **core DONE, limit plumbing remains**

✅ `NewmanCellSum.v`, 137 lines, axiom-clean. The reconciliation that was flagged as the
riskiest step in the endgame **works**:

```coq
LTN_stepsum : LTN z 0 (ln (INR (S (S M)))) H0 HT = Cminus (StepSum z M) (OneSum z M)
```

Route: `cexpzt_shift` (`e^{-(z+1)t} = e^{-t}·e^{-zt}`), then `lintN_cell_id` — on each open
cell `nf t · e^{-zt} = psi(k+1)·e^{-(z+1)t} − e^{-zt}`, since `psiR(e^t)` is constant there
(`PiecewiseTransform.psiRexp_const_cell`) and `nf t = psiR(e^t)/e^t − 1`
(`NewmanTransform.nf_closed_form`). Both right-hand terms are continuous, so `CintfD_ext_open`
then `CintfD_Cintf` (built in E1 for exactly this) collapse the honest integral to `Cintf`,
which `Cintf_sub`/`Cintf_cmul_l` split into StepSum's and OneSum's k-th summands. `LTN_cell`
is then summed by induction with `LTN_split`, using `LTN_endpoint` to move the base point
from `0` to `ln (INR 1)` without proof transport.

✅ **E4 is now COMPLETE.** `NewmanGN.v` (125 lines, axiom-clean) closes it:

```coq
gN_eq_gext : gN z Hz = gext z          (for 0 < Re z)
```

Route: `LTN_gN_bound` (distance from a fixed truncation to `gN`, via `LTN_tail_le` and a
limit-of-bounded-sequence argument `Un_cv_le_const`), then `LTN_seq_cv` (convergence along
**any** divergent nonnegative sequence), instantiated at `T_M = ln (INR (S (S M)))` with
`cv_infty_ln_INR`; then `CUn_cv_ext` with `LTN_stepsum` turns that into convergence of
`StepSum − OneSum`, and `CUn_cv_unique` against `newman_identity` identifies the limit.
As predicted, `gext_eq` takes its `1 < Re (z+1)` proof as a parameter, so it unified with
the exact proof term inside `newman_identity` — **no `Phi` proof-irrelevance lemma was
needed**.

*(original scoping below)*


Chain: `LTN z (ln (INR (S (S M)))) = StepSum M − OneSum M` by cell additivity
(`CellAdditivity.logpart_additive`) plus `ChebyshevPsiR.psiR_step` on each cell; then
`NewmanIdentity.newman_identity` gives the limit `Φ(z+1)/(z+1) − 1/z`; then
`NewmanGExt.gext_eq` identifies that with `gext z`.

Risk: this is where the cell bookkeeping and the honest integral must be reconciled, and
where a mismatch would surface late.

### E5 — the contour identity (scoped ~250–350) — ✅ **DONE** (1010 lines, four files)

✅ `CTruncCauchyDom.trunc_cauchy_dom` (108 lines, axiom-clean) makes the truncated Cauchy
formula **unconditional**: it discharges `trunc_cauchy`'s whole exceptional-point interface
by taking `phi := rphi F C0 dF`, exactly as `cauchy_interior_dom` does for the circle. Its
input shape — `F` pointwise-continuous everywhere, holomorphic on `U` off `0`,
differentiable at `0` — matches `NewmanCutoff.gtrunc_CcontC` exactly. Also proves
`rphi_holo_off_gen`, the `U`-shaped version of `rphi_holo_off_dom` (the disk in the latter
is incidental; its proof uses the hypothesis at a single point).

**E5 progress**: `NewmanHolo.v` (140 lines, axiom-clean) builds the layer `LTN_holo` needs.
`CLaplace.lint_increment` and `lint_increment_mod` turned out to be **generalised over `f`**
(they use no continuity), so they are reusable verbatim at `f := nfC` — only the integral
layer changes. The new layer is the **`NK` algebra**: `NK K HK a b Ha Hab` is
`∫ nfC·K` for a continuous kernel `K`, with `nfK_Re_int`/`nfK_Im_int` (integrability for
*any* continuous kernel, generalising `lintN_Re_int`), `NK_irrel`, `NK_sub`, `NK_cmul`,
`NK_ML`. Every integrand in the increment argument has the shape `nfC × (continuous)`, so
linearity is proved once at the **kernel** level instead of per-integrand — which is what
makes the `Hrw` step of `gT_holo` transcribable.

✅ **`LTN_holo` is DONE** — `NewmanHolo.v` is now 271 lines, axiom-clean:

```coq
LTN_holo : is_Cderiv (fun w => LTN w 0 T ..) z (LTN' z 0 T ..)
```

`gT_holo`'s proof transcribed onto `CintfD`: `Kz`/`Kd` name the two kernels, `brk` the
increment kernel (written in the exact shape of `lint_increment`'s right-hand side so it
matches syntactically), `brk_id` is the kernel-level increment identity from `cexpzt_add`,
and the whole increment collapses to one `NK` by two `NK_sub`s and one `NK_cmul`. The ML
estimate and the final arithmetic are `gT_holo`'s verbatim, with `NK_ML` for `Cintf_ML` and
`nf_bound` for the bound on `|f|` — the constant `K = 2·K0·T + 1` is unchanged, since
`CintfD_ML` and `Cintf_ML` share the factor 2.

✅ **The kernel and the instantiation are DONE** — two more files, both axiom-clean:

`CTruncKernel.v` (205 lines) upgrades `trunc_cauchy_dom` from `1/z` to Zagier's full kernel
`K_R = 1/z + z/R²`, for an arbitrary `F` pointwise-continuous everywhere and holomorphic on
the convex open `U` carrying the contour:

```coq
trunc_kernel_dom : ∫_arc F·K_R + ∫_chord F·K_R = F(0)·2πi
```

The `z/R²` half does **not** go through `pathint_loop_conv` as scoped — that lemma wants a
single closed `gam` with `gam a = gam b`, and the truncated contour is two parametrised
pieces. Instead `CPrimConv.PrimC` is a primitive for `F·z/R²` on `U` and `pathint_FTC`
telescopes: the arc runs `Qc → Pc`, the chord runs `Pc → Qc`, and the two differences
cancel. This is exactly how `trunc_cauchy` disposes of its `phi` loop, so the pattern was
already in the file it builds on.

`NewmanContour.v` (426 lines) instantiates at `F := (gtrunc − g_T)·e^{zT}`:

```coq
newman_contour : ∫_arc F·K_R + ∫_chord F·K_R = 2πi·(gext 0 − LTN 0 0 T)
```

with `U := TruncDisk (R+1) (2δ)`, contour radius `R`, and the chord at `Re z = −δ` (i.e.
`R·cos α = −δ`). Supporting pieces:

- `PtcontC_mul` / `PtcontC_sub` — pointwise continuity is closed under products and
  differences. `cutprod_ptcont` covered only multiplication by a **real** cutoff; the
  general complex product was missing and is ~35 lines.
- `NewmanCutoff.gtrunc_ptcont` — `gtrunc_CcontC` threw away the `PtcontC` its own proof
  established, and `CcontC` (continuity along paths) does not give it back. Restated with
  `PtcontC` in the conclusion; the old `CcontC` form is now a two-line corollary.
- `newman_contour_params` — the hypotheses are satisfiable: `δ := min(del/4, d₁/4, R/2)`
  from `gtrunc_ptcont (R+1)` and `gext_holo_strip (R+1)`.
- `alpha_of_delta` — `α := acos(−δ/R)` realises any `0 < δ < R`, so E7 can drive `δ → 0`.
- `HfaK_wit` / `HfcK_wit` — the two `Ccont` witnesses the `pathint`s take as arguments, so
  the identity is provably non-vacuous; and `Gdt_arc` / `Gdt_chord`, which say the cutoff is
  invisible on the contour, so every E6 estimate may be stated for the honest `Gd`.

Note this half depends on E2 (it needs `g_T`, the truncated transform of Newman's
discontinuous `f`), so it is **not** independent of E1–E2 after all — only
`trunc_cauchy_dom` was.

### E6 — the contour estimate (scoped ~200–300) — ✅ **DONE** (1328 lines, five files)

The scoping said "mostly assembly". It was not. Three prerequisites had to be built first,
each forced by a real obstruction:

- `CStripBound.strip_bounded` (182) — a pointwise-continuous `F` is bounded on a thin strip
  around `{Re z = 0, |Im z| ≤ Rb}`, by `CUnifCont`/`BfnUniform`'s compactness template.
  The chord estimate is `|g| ≤ M`, and `M` must be fixed **before** the truncation depth `δ`
  is chosen — otherwise the `δ → 0` limit is circular. Reading `M` off the chord's own
  parametrisation makes it depend on `δ`; a strip does not.
- `NewmanKernelCut.Kcut` (168) — `K_R = 1/z + z/R²` with the `1/z` summand damped by a
  radial cutoff. `PrimC` demands **global** `CcontC` and `K_R` has a pole;
  `cutprod_ptcont`'s dichotomy fits exactly (at `0` the cutoff vanishes identically nearby).
- `NewmanDeform.chord_to_arc` (281) — for any entire `W`, the chord `{Re z = −δ}` and the
  far-left arc `{|z| = R, Re z ≤ −δ}` give the same integral of `W·K_R`. **Not optional**:
  the direct chord bound for the `g_T` factor is `O(BR/δ²)`, with no cancellation available,
  whereas on the circle `|K_R| = 2|Re z|/R²` cancels the `1/|Re z|` of the tail bound and
  yields the uniform `4B/R²`. Again `PrimC` + `pathint_FTC`, not `pathint_loop_conv`.

`NewmanML` (194) restates the pointwise bounds for the honest transform.
`right_arc_bound`/`left_arc_bound` are stated for `LaplaceFull`'s `gfull`/`LT`, built on
`Cintf`, so they cannot be instantiated at Newman's step function. `kern_bound` states the
cancellation once, for **any** `w` obeying the tail bound, and covers both signs of `Re z`
via `Rabs` — including `Re z = 0`, where the kernel vanishes on the circle. That last case
is what lets the arc be split at `Re z = 0` with a *closed* parameter interval on each side.
Also `LTN_tail_ne`/`LTN_tail_left`: `LTN_tail` assumed `0 < Re z` only through
`exp_int_AB_scaled`, and `NewmanLeft.exp_int_AB_ne` removes that.

`NewmanE6.newman_bound` (503) assembles five pieces:

```coq
|g(0) − g_T(0)|·2π  ≤  (24πB + 4πMδ)/R  +  4MR(1/δ + 1/R)·e^{−δT}
```

- arc `Re z ≥ 0`: `4B/R²` for the **combined** `g − g_T`. The halves cannot be separated
  here — `|g_T| ~ 2B/Re z` blows up at the axis and only `|K_R| = 2Re z/R²` rescues it.
- arc `Re z ≤ 0` (two pieces): `4B/R²` for `g_T` (its tail bound flips sign) plus `2Mδ/R²`
  for `g`, the kernel being small there.
- chord, `g_T` half: deformed to the far-left arc.
- chord, `g` half: `|g| ≤ M`, `|e^{zT}| = e^{−δT}` — the only piece needing `T → ∞`.

Two scoping corrections. The arc is split at `Re z = 0`, **not** at `|Re z| = δ`: on the
truncated contour the left arc already has `|Re z| ≤ δ`, so `NewmanGLeft.gleft_decay`'s
away-from-axis case never arises and that lemma goes unused. And `NewmanNearAxis.
gleft_nearaxis` was indeed f-agnostic and reused verbatim, as predicted.

### E7 — the triple limit ⇒ `NfCauchy` (scoped ~250–350) — ✅ **DONE** (239 lines)

`NewmanE7.gext_LTN_cv` chooses the three parameters in the one order that works:

- `R` first, killing `24πB/R` — `B = Kup + 1` is absolute;
- then `δ`, killing `4πMδ/R` — `M` depends on `R` but **not** on `δ`, which is exactly what
  `strip_bounded` buys and why it is stated on a strip;
- then `T`, killing the last term, whose constant depends on both.

`exp_decay_below` (`e^{−cT}` eventually undercuts any positive bound) replaces
`NewmanLimits.exp_decay_T_cv0`, which is sequential (`INR n`) while the truncation time here
is a real. `Re_LTN0` identifies `Re (LTN C0 a b)` with `∫_a^b nf` via `RiemannInt_P18`, and
`LTN_split` turns convergence into `NfCauchy`. Then:

```coq
PNT : Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1
```

axiom-clean, on the four standard classical-Reals axioms.

## Total and ordering

**All seven bricks are done: 3512 lines**, against a 1500–2100 scoping — an overrun of about
70%, concentrated in E5 (3x) and E6 (5x).

| brick | status | files | lines |
|---|---|---|---|
| E1 | ✅ | `CIntegralD.v`, `CIntegralDLin.v` | 282 |
| E2 | ✅ | `NewmanTransform.v` | 182 |
| E3 | ✅ | `NewmanTail.v` | 209 |
| E4 | ✅ | `NewmanCellSum.v`, `NewmanGN.v` | 262 |
| E5 | ✅ | `CTruncCauchyDom.v`, `NewmanHolo.v`, `CTruncKernel.v`, `NewmanContour.v` | 1010 |
| E6 | ✅ | `CStripBound.v`, `NewmanKernelCut.v`, `NewmanDeform.v`, `NewmanML.v`, `NewmanE6.v` | 1328 |
| E7 | ✅ | `NewmanE7.v` | 239 |

Where the scoping went wrong, consistently: it counted the *mathematical* content of each
brick and not the *interface* work. Three separate times a lemma was unusable not because
its statement was too weak but because `Cintf`/`PrimC` demand **global** continuity of the
integrand — `NewmanCutoff.gtrunc` for `gext`, `NewmanKernelCut.Kcut` for `1/z`, and
`CIntegralD.CintfD` for the step function itself. That single structural fact, recorded as
finding (1) below before E1 began, accounts for most of the overrun.

## Verification, per brick

`make -j4 -k` green with `MAKE EXIT: $?` reported explicitly; no `Admitted`/`Abort`/
`Axiom`/`admit`; `Print Assumptions` limited to the four standard classical-Reals axioms.

## Honesty

This yields **PNT**, not RH. The two share the ζ machinery but nothing else: PNT needs
non-vanishing only on `Re s = 1` (`PNTZetaLine.zero_free_line_holds`, already proved),
whereas RH is a statement about the interior of the strip. See `docs/rh_routes.md`.
