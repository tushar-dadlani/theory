# Unconditional PNT — the endgame, decomposed

## Where this stands

PNT is reduced to **one unproved proposition**:

```coq
TintCoV.pnt_of_nf_cauchy : NfCauchy ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1
```

`NfCauchy` is the Cauchy criterion for the tail of `∫₀^∞ f(t) dt` with
`f(t) = ψ(e^t)e^{−t} − 1` — literally what Newman's contour argument outputs.
Everything downstream is machine-checked and axiom-clean: C0 (`ZetaPoleCancel2`), the
g-extension (`NewmanGExt`), the uniform δ (`BfnUniform`), global `CcontC`
(`NewmanCutoff`), integrability (`PsiRIntegrable`), the Tauberian squeeze
(`TauberianBlock`, `TauberianSqueeze`), and the `u = e^t` bridge (`TintCoV`).

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

### E5 — the contour identity (~250–350) — **first half DONE**

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

Still to do in E5: `LTN_holo` itself (assemble the increment via `NK_sub`/`NK_cmul`, then
the `NK_ML` estimate), then instantiate at `F := (gtrunc − g_T)·e^{zT}` with `U := TruncDisk`
(`TruncDisk_convex`/`_open`), and split the kernel with
`CNewmanKernel.newman_kernel_split` — `trunc_cauchy_dom` handles the `1/z` part,
`CPrimConv.pathint_loop_conv` kills the holomorphic `z/R²` part. Conclusion
`2πi·F(0) = ∮_C F·K_R`.

Note this half depends on E2 (it needs `g_T`, the truncated transform of Newman's
discontinuous `f`), so it is **not** independent of E1–E2 after all — only
`trunc_cauchy_dom` was.

### E6 — the three ML estimates (~200–300, mostly assembly)

- right arc — restate `NewmanArc.right_arc_bound` for `gN`/`LTN` (needs E3), then
  integrate with `NewmanArcML.arc_ML` ⇒ `O(B/R)`;
- left arc, `g_T` part — `NewmanLeft.left_arc_bound`, likewise restated;
- left arc, `g` part — `NewmanGLeft.gleft_decay` and `NewmanNearAxis.gleft_nearaxis` are
  **already f-agnostic** (they take `gz z : C` as a plain value), so these two need no
  restatement.

### E7 — the triple limit ⇒ `NfCauchy` (~250–350)

`δ → 0`, `R → ∞`, `T → ∞`, splitting the arc at `|Re z| = δ` with the near-axis control
`|K_R| ≤ 2δ/R²`. Atoms exist: `NewmanLimits.exp_decay_T_cv0`, `bound_over_R_cv0`. Output is
`NfCauchy`, which closes PNT via `TintCoV.pnt_of_nf_cauchy`.

## Total and ordering

Roughly **1500–2100 lines** across seven files, of which `trunc_cauchy_dom` (108) is done.
Dependency order is E1 → E2 → E3 → E4, then E5's instantiation, then E6 → E7.

The `trunc_cauchy_dom` half of E5 was correctly identified as buildable first — it needed
only what already existed, and it confirmed the interface. The *rest* of E5 needs `g_T`
from E2, so **E1 is now the next step**.

## Verification, per brick

`make -j4 -k` green with `MAKE EXIT: $?` reported explicitly; no `Admitted`/`Abort`/
`Axiom`/`admit`; `Print Assumptions` limited to the four standard classical-Reals axioms.

## Honesty

This yields **PNT**, not RH. The two share the ζ machinery but nothing else: PNT needs
non-vanishing only on `Re s = 1` (`PNTZetaLine.zero_free_line_holds`, already proved),
whereas RH is a statement about the interior of the strip. See `docs/rh_routes.md`.
