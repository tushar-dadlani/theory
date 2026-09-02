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

### E1 — `CIntegralD.v`: a complex integral for merely-integrable integrands (~250–350)

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

### E2 — `NewmanTransform.v`: Newman's transform as an honest integral (~200–300)

`nf` is already defined in `TintCoV`. Define `nfC t := RtoC (nf t)`, prove
`fun t => nfC t * cexpzt (−z) t` integrable on `[0,T]` by the **same cell argument** as
`TintCoV.nf_int_cell` (continuous on each open cell), then

```coq
LTN (z : C) (T : R) : C          (* the truncated transform, via CintfD *)
gN  (z : C) (Hz : 0 < Re z) : C  (* the T -> oo limit *)
```

Reuse: `TintCoV.nf_cell_eq`, `nf_int_k`, `floor_exp_ge1`, `cell_lo`, `cell_hi`.

### E3 — the tail bound (~120–180)

`Cmod (gN z − LTN z T) <= B * exp (− Re z * T) / Re z`, mirroring
`LaplaceFull.LT_tail_bound` / `gfull_tail` but for `CintfD`. `B` comes from
`ChebyshevPsiR.psiR_upper` (`psiR x <= x * Kup`), giving `|nf t| <= Kup + 1`.

### E4 — `gN = gext` on `Re z > 0` (~200–300) — *the subtlest brick*

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

Remaining in E5: instantiate at `F := (gtrunc − g_T)·e^{zT}`, and kill the `z/R²` half of
the kernel with `pathint_loop_conv`.


`F := (gtrunc − g_T) · e^{zT}`, `U := TruncDisk`. Split the kernel with
`CNewmanKernel.newman_kernel_split`: `trunc_cauchy` for the `1/z` part,
`CPrimConv.pathint_loop_conv` for the holomorphic `z/R²` part. Conclusion
`2πi·F(0) = ∮_C F·K_R`.

**Already audited as dischargeable**: `trunc_cauchy` wants `CcontC phi` for the removable
quotient, `CRemovableExtDom.rphi_cc_dom` supplies it from pointwise continuity, and
`NewmanCutoff.gtrunc_CcontC` provides that. `CTruncDisk.TruncDisk_convex`/`_open` give `U`.

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

Roughly **1500–2100 lines** across seven files. Strict dependency order is
E1 → E2 → E3 → E4, with E5 independent of E1–E4 (it needs only what is already built), and
E6 → E7 last. **E5 can be built first** and is the best next step: it is self-contained,
its inputs are audited, and finishing it would confirm the `trunc_cauchy` interface before
the larger E1–E4 investment.

## Verification, per brick

`make -j4 -k` green with `MAKE EXIT: $?` reported explicitly; no `Admitted`/`Abort`/
`Axiom`/`admit`; `Print Assumptions` limited to the four standard classical-Reals axioms.

## Honesty

This yields **PNT**, not RH. The two share the ζ machinery but nothing else: PNT needs
non-vanishing only on `Re s = 1` (`PNTZetaLine.zero_free_line_holds`, already proved),
whereas RH is a statement about the interior of the strip. See `docs/rh_routes.md`.
