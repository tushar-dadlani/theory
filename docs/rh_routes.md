# Three routes to RH, and where this development sits on each

This note exists because the work in this repository is easy to over-read. Nine zeros of
`Xi` have been certified on the critical line. That is an **existential** result, and RH is
**universal**. The two are almost unrelated, and saying so precisely is more useful than
any further zero.

## 1. The statement

`spectral-theory/RiemannHypothesisXi.v`:

```coq
Definition RiemannHypothesis : Prop := forall z : C, XiC z = C0 -> Re z = / 2.
```

A note on a distinction that is often drawn and is **not** a real one: "all zeros lie on the
critical line" and "no zero lies off the critical line" are the *same proposition*. In
classical logic `∀x (P x → Q x) ≡ ¬∃x (P x ∧ ¬Q x)`, and the definition above is literally
the ∀-form. What genuinely differ are the **proof programs**, and those differ so much that
they share almost no machinery. There are three.

## 1b. Theorems in this repo whose NAME claims RH, and which do not

Grepping this repository for RH progress is actively misleading. These are the results a
reader would hit first, and none of them says anything about ζ:

| result | what it actually is |
|---|---|
| `SpectralTripleRH_closed.RIEMANN_HYPOTHESIS` | About an abstract `FormalSystem` record. **Zero contact with `ζ` or `Ξ`** — imports only `QArith`/`Arith`/`Lia`/`Triple`. Proves a `kernel` is empty at a "tower limit", so "all spectral zeros are on the critical line" is **vacuously true**. The file's own neighbouring theorems are named `RH_at_fixed_point_vacuous` and `spectral_zeros_satisfy_anything`. |
| `SpectralTripleRH.RH_from_spectral_triple` | Rests on `Axiom berry_keating_correspondence`, whose conclusion `on_critical_line_q (1#2)` unfolds to `1#2 == 1#2`. **The axiom is a tautology**, and the theorem mentions no complex number. |
| `millennium-problems/EulerZeta.RIEMANN_HYPOTHESIS_EULER` | Same empty-kernel construction. |
| `packages/GHS/RiemannHypothesis.RIEMANN_HYPOTHESIS_SYMBOLIC` | About a seven-element finite symbol type `Sym7`. |
| `KroneckerSelfAdjoint.zeta_zeros_are_N_phase` | `Proof. intros phases H. exact H. Qed.` — `is_zeta_zero` is *defined* as the conclusion. It is `id`. |

None contaminates anything else (their importers do not use them), and most are self-aware in
their comments. They are dead ends with dangerous names. Renaming or deleting them is a
judgement call for the repo owner; this table exists so that no later status claim — including
an automated one — mistakes them for progress.

Separately, the honest RH results in the repo are **restatements, not reductions**:
`RH_iff_depth_zero`, `RH_iff_no_left`/`no_right`, `RH_is_coherence`, `RH_zeros_are_Bxi_spectrum`,
`RH_iff_WeilPositive`. Changing coordinates is not progress. `RiemannHypothesisXi.
RiemannHypothesis` is not proved, and no theorem anywhere has it as a conclusion.

## 2. Route A — exhaustion / counting

*Shape*: produce zeros on the line, then show there are no others by counting.

Write `N(T)` for the zeros of `Xi` in the strip below height `T`, and `N₀(T)` for those on
the line. Always `N₀(T) ≤ N(T)`. If you also prove `N(T) ≤ N₀(T)`, the two coincide, and
every zero below `T` is forced onto the line — and forced to be simple.

*What it yields*: "RH verified up to height `T`". **It cannot yield RH.** RH would require
every `T`, and that is a limit you cannot complete. This is the route all numerical
verification takes.

*What the repo has*:

- **Lower half — done.** `NineZeros.nine_zeros` gives nine zeros below height 49 by IVT on
  sign changes of `xir t = Re Xi(1/2+it)`, via `ZeroCounting.alternation_zeros`. The nine
  gaps contain exactly the nine true ordinates, one each:

  | gap | ordinate | | gap | ordinate |
  |---|---|---|---|---|
  | (10, 16) | 14.134725 | | (35, 39) | 37.586178 |
  | (16, 22) | 21.022040 | | (39, 42) | 40.918719 |
  | (22, 26) | 25.010858 | | (42, 45) | 43.327073 |
  | (26, 31.5) | 30.424876 | | (45, 49) | 48.005151 |
  | (31.5, 35) | 32.935062 | | | |

- **Upper half — absent.** The best available is `XiZeroDensity.xi_count_below`:

  ```coq
  Theorem xi_count_below : forall (r : R) (s : list C),
    0 < r -> NoDup s ->
    (forall rho, In rho s -> XiC rho = C0) ->
    (forall rho, In rho s -> Cmod rho < r) ->
    INR (length s) <= Bxi r.
  ```

  with `Bxi r = ln (4 * XiM (8*(r+1))) / ln 3`. Numerically `Bxi 49 = 712.9` and
  `Bxi 50 = 730.6`, against true counts of **18** and **20** (zeros come in conjugate
  pairs). So the repo proves, at height 49, roughly

  > 9 ≤ (zeros on the line) ≤ (zeros in the disk) ≤ 712.

  A factor of about 40 from what `N(49) ≤ 9` would need.

*Why that gap is structural, not constant-chasing*: Jensen's formula on a circle centred at
0 is charged for `Xi`'s growth in the direction where it is largest — along the real axis,
where `Xi(σ)` genuinely behaves like `π^{-σ/2}Γ(σ/2)ζ(σ) = exp(Θ(R log R))`. But the zeros
are confined to a thin vertical strip. The circle pays for growth from a direction that
contributes no zeros. `XiGrowthBound.Tgb` is a fair majorant, not a lossy one. An idealised
Jensen bound still lands near 190. Retuning `CPeelBound.peel_count_explicit`'s hard-wired
`Rr/4` and `ln 3` recovers roughly the 8× radius inflation and reaches the tens — never 18,
let alone 9.

*What would close it*: the argument principle, `(1/2πi)∮ Xi'/Xi`, which measures phase
change along the strip boundary rather than max modulus on a large circle — the right shape
for the problem.

**The argument principle is now built** (`CArgPrincipleRect.arg_principle_rect`, axiom-clean,
880 lines across four files):

```coq
F = prodfac l · G,  G holomorphic and non-vanishing on a convex open U,
every w in l strictly inside [x0,x1] × [y0,y1]
  ==>  ∮_{∂rect} F'/F = length l · 2πi
```

Three notes on what that does and does not settle.

- **Multiplicity was dodged, not solved.** The order-of-vanishing brick `f = (z−a)^m·g` is
  still unbuilt. Stating the theorem with a *factorisation hypothesis* whose list may repeat
  moves multiplicity to the caller, exactly as `CZeroListFactor.DivBy_cons` and
  `XiZeroDensity.xi_count_peel` already do. It is off the critical path, not done.
- **No complex logarithm was needed.** The count comes out of residues — one `2πi` per
  linear factor by `RectWindingGen.rect_winding_interior`, zero from the cofactor by
  `CLoopCofactor.rect_loop_region`.
- **It does not produce `N(49) ≤ 9`.** It converts "count the zeros" into "evaluate a contour
  integral". The evaluator side is now built — `ZetaEncloseS.IzetaS` certifies `ζ` on **any**
  vertical line `Re s = σ` for rational `σ > 0`, and `ZetaCertOff2` gives the repo's first
  certified value off the critical line, `ζ(3/2+2i)`. At `σ = 1/2` it agrees with the
  committed `Izeta2` **bit-identically**, which is what rules out the sign trap (the head term
  carries `(σ−1)/D`, the `G` term `(1−σ)/D` — equal and opposite exactly at `σ = 1/2`).

  Two constraints found in the process, both load-bearing for any contour design:

  1. **`σ > 0` is not optional.** `CZeta.zetaC` *takes* `0 < Re s` as an argument, so the
     classical rectangle `[−1,2]×[−T,T]` is unreachable. The fix belongs in the contour: make
     it symmetric under `s ↦ 1−s`, and `XiC_symmetric` with `XiC_conj` make the left and
     bottom edges reflections of the right and top, so only `σ ∈ [1/2, c]` is ever evaluated.
  2. **Certified `|Γ|` is still not required** — a winding count needs only Γ's direction,
     already general via `GammaDir.Pang`. What *is* still missing is `ThetaEnclose` at general
     `σ/2` rather than `1/4`, so there is as yet no certified off-line `ξ` **argument**.

  **The measured cost is now the binding constraint, not the proof effort:** ~87 s per
  evaluation at `t = 2, M = 12`; ~275 s at `t = 26, M = 40`. Cost grows steeply in both the
  ordinate and the term count, and the term count needed for a useful enclosure itself grows
  with `t` (`M ≥ 8` at `t = 2`, `M ≥ 25` at `t = 26`). A contour count sampling hundreds of
  points at `t ≈ 49` is many hours of `vm_compute` on this hardware. Whether the
  pointwise-sampling design is viable at all, or whether it must be replaced by a
  Backlund/Jensen argument needing far fewer points, is now the open question.

**Do not take the planning docs' blocker lists at face value here.** Several are stale:
`docs/identity_theorem_plan.md` localises a blocker at `pathint_loop_except` around line 130
and then, in its own later sections, closes the entire program (`✅ COMPLETE`,
`CGammaComplete.GammaC_functional_equation`). Checked against the source, the following are
**already present and axiom-clean**:

- convex-region loop-zero — `CPrimConv.pathint_loop_conv`, with `PrimC_deriv`;
- loop-zero with an **exceptional point anywhere** — `CGoursatExcept.pathint_loop_except`;
- `∮ dz/z = 2πi` and `∮ F/z = 2πi·F(0)` on the truncated disk — `CTruncWind.trunc_winding`,
  `CTruncCauchy.trunc_cauchy`; the rectangle version is `RectWinding.rect_winding`;
- **local factorisation at a zero** — `CZeroFactorDisk.zero_factor_disk`
  (`F z = (z−w)·H z`, `H` disk-holomorphic), and the distinct-zero list version
  `CZeroListFactor.DivBy_distinct`;
- **log-derivative machinery** — `XiLogDerivZeros.xi_logderiv_zeros` (Hadamard-product form,
  conditional on a zero enumeration), `ExplicitFormulaXiLogDeriv`;
- finiteness/completeness of the zero set in a compact region — `JensenCountComplete` /
  `XiZeroCount.xi_zero_count` (`forall z, Cmod z < Rj -> XiC z = C0 -> In z l`).

That is most of the argument principle's skeleton. Sketching the assembly: factor out the
zeros with `DivBy_distinct`; the residual factor is holomorphic and non-vanishing on the
region, so its log-derivative is holomorphic there and `pathint_loop_conv` kills its loop
integral **with no logarithm required**; each linear factor contributes `2πi`.

What is genuinely confirmed absent:

1. ~~`∮ dz/(z−a) = 2πi` at an arbitrary interior `a`~~ — **closed.** The circle case was
   already there (`CWindingOffCenter.winding_interior`, `CCauchyFull.cauchy_interior`,
   `CRemovableExtDom.cauchy_interior_dom`); the rectangle case is now
   `RectWindingGen.rect_winding_interior`, built off the already-general
   `RectWinding.vseg_winding`/`hseg_winding` as predicted — `atan` bookkeeping, not analysis.
   Multiplicity (`f = (z−a)^m g`) remains unbuilt but is no longer on the critical path; see
   above.
2. a complex log/argument — still absent, and **partly, not wholly, dispensed with.**
   `CPolarPath.pathint_logderiv_phase` does show the contour integral of `F'/F` *is* the phase
   change along the path. `CPathLift.path_polar_lift` then shows that *any* pair of real
   functions whose derivatives are the two components of the log-derivative, and which match
   `F` at the **start point**, satisfies `F(γu) = e^{Lg u}(cos ph u, sin ph u)` on the whole
   interval — one branch choice at `u = a`, everything after forced.

   **Correction to an earlier version of this file, which claimed `path_polar_lift`
   "constructs that phase". It does not.** `Lg` and `ph` are *given*, with their derivatives
   already assumed equal to the log-derivative components; their **existence** (the
   FTC/primitive step) is nowhere proved. It is a uniqueness/consistency theorem, not an
   existence theorem. Its hypotheses are also `forall u : R`, unrestricted — so
   `Hne : forall u, F (gam u) <> C0` demands non-vanishing on the whole infinite line, not
   just the segment, which is a real obstacle to instantiating it on `Xi`.

   So the analytic half of the counting route is *nearly* closed: counting → contour integral
   (`CArgPrincipleRect`) → phase change (`CPolarPath`) → phase *characterised* but not yet
   constructed (`CPathLift`). Note also that `CArgPrincipleRect` and `CPathLift` currently
   have **no downstream consumers at all**.
3. the bridge from a contour count to the height count, i.e. `N(T) = θ(T)/π + 1 + S(T)`.
   Encouragingly `θ` is already certified at these heights (`ThetaEnclose.Itheta`, used at
   `t = 49` in `MoreZeros.chk49`), and `θ(49)/π + 1 = 9.0944` against the nine zeros — so
   pinning the integer `N(49) = 9` needs `S(49)` only to within about ±0.9.

Finiteness of the zero set in a compact region, often the fiddly prerequisite, is **already
available** from the completeness clause of `JensenCountComplete` / `XiZeroCount.xi_zero_count`:
`forall z, Cmod z < Rj -> XiC z = C0 -> In z l`.

## 3. Route B — zero-free region

*Shape*: lower-bound `|Xi|` off the line. No enumeration; no counting.

*What it yields*: RH in one stroke, if the region can be made to be everything off the line.

*What the repo has*: this route is **already working**, at a coarse scale —

```coq
ZetaOpenStrip.XiC_zeros_in_open_strip : forall z, XiC z = C0 -> 0 < Re z < 1
```

That is a genuine zero-free region: no zeros outside the open strip. RH is the same shape
with the region shrunk from the strip to the line.

Two sharper results now exist, and neither approaches RH:

- `DepthBound.zero_free_region_on_disk` — on each disc `|z| < r` there is `s0 ∈ [1/2,1)` with
  no zeros in `s0 < Re z`. **Soft**: `s0` is a max over the finite zero list in that disc, so
  there is no control as `r → ∞`.
- `ZetaZeroFree.XiC_zero_free` — the first region here with **explicit height dependence**:
  `Re z ≤ 1 − 27/(256·Kg(Im z))` for `|Im z| ≥ 2`, with `Kg` growing like `ln⁹|t|`. This is
  the de la Vallée Poussin *shape*, obtained by finally composing
  `ZeroFreeRegion.region_of_zero'` with `ZetaDerivBoundExt` — two halves that had sat
  unjoined, with nothing in the repo even importing `ZeroFreeRegion.v`.

  **Its constant is ~10²⁰ worse than the classical one**: width `4.9e-16` at `|t| = 2` and
  `1.7e-19` at `|t| = 10⁶`, against de la Vallée Poussin's `~0.07`. The value is the shape and
  the unconditionality, not the numbers. And it removes no *fixed* strip: for every `σ₀ < 1`
  it fails for large `t`. The proof uses the Euler product
(`Re > 1`) and the functional equation to reflect it — and neither can be pushed inward.
Every known zero-free region in the literature hugs `Re = 1`; none approaches `Re > 1/2 + δ`.

`CriticalDepth.RH_iff_depth_zero` recoordinatises the strip by the logit so that the
functional equation becomes negation and RH becomes "depth = 0" — a change of variables on
this route, not progress along it.

*Adjacent, and not RH*: `docs/route_b_C4_newman_plan.md` targets **PNT** via Newman's
analytic theorem. Its first listed blocker, C0, is the complex residue of `ζ` at `s = 1` —
justified there by the claim that "`zetaC` has no Laurent/pole structure at 1". That claim
is false: the pole *is* the first summand of `CZeta.zetaC`, and the regular part is
uniformly bounded near `s = 1` by the Euler–Maclaurin tail estimate `ZetaEM.htermC_tail` at
`M = 0`. `ZetaResidue.zeta_residue_one` proves `(s−1)·ζ(s) → 1` outright, axiom-clean,
with no new analytic infrastructure — the machinery built for the *sign certificates* paid
for it. The other half of C0 (`Bfn` **holomorphic** at 1) was already present as
`CZetaRegular6.BfnT_holo` and is wired up in `ZetaPoleCancel2.v`.

**That whole route is now complete**: `NewmanE7.PNT` proves
`π(N)/(N/ln N) → 1`, axiom-clean, via Newman's argument in Zagier's form
(bricks E1–E7, `docs/pnt_endgame_plan.md`). PNT is of course not evidence for RH — it is
equivalent to `ζ(1+it) ≠ 0`, the very edge of the strip, and Route B above explains why that
edge cannot be pushed inward.

## 4. Route C — Hilbert–Pólya / spectral

*Shape*: make off-line zeros **impossible** rather than excluded. Realise the ordinates as
the spectrum of a self-adjoint operator; reality of eigenvalues then forces `Re = 1/2`.

*What the repo has*: `HilbertPolyaCapstone.berry_keating_summary`, proved unconditionally —
the boundary functional is `Xi` and is even, it has no zero off the reflection axis, the
Weyl function selects zeros at the Dirichlet phase, the scattering matrix is trivial, and a
sign change of `xir` is a half-winding of the Weyl phase. Notably **reality of the ordinates
is a theorem** (`SelfAdjointExtension.icayley_real`), not an assumption.

The remaining gap is isolated as one proposition:

```coq
Definition hilbert_polya_open : Prop := hp_target_via_extension.
```

— that the geometric boundary phase realising `XiC`'s zeros is the specific unit-phase
sequence.

**And it would not imply RH even if proved.** Unfolding `hp_target_via_extension`, its
surjectivity clause reads `forall z, XiC z = C0 -> Re z = / 2 -> exists n, ...` — guarded by
`Re z = / 2`. It asserts only that the **on-line** zeros are enumerated by the phase sequence,
and says nothing whatever about a hypothetical zero at `0.6 + 100i`. Genuine Hilbert–Pólya
needs the spectrum to exhaust *all* zeros; this `Prop` has that quantifier restricted away.

*A caution*: "one open `Prop`" reads as nearly finished, and it is not. A single
`Definition` can encode arbitrarily much, and this one encodes essentially the whole
Hilbert–Pólya conjecture. The scaffolding around it being axiom-clean does not make the gap
small. `HilbertPolyaCapstone.rh_conditional_realization` runs the other way — it *assumes*
`RH_XiC` to place zeros in the spectrum.

## 5. Where the nine zeros sit

**None of the three.** They are `∃` statements: nine points shown to be zeros and shown to
lie on the line. Route A wants `∀` by exhaustion, B by exclusion, C by structure. Existence
of zeros *on* the line places no constraint on zeros *off* it — every result in this
repository is consistent with a zero at `0.6 + 100i`.

The one genuine connection is to Route A's lower half:
`WeylWinding.weyl_winding_count` recasts the same sign changes as half-windings of the Weyl
phase through the antipode. That feeds the counting program, which needs its upper half
before it says anything at all about RH at any height — and which cannot reach RH regardless.

## 6. Scope honesty

Completing Route A at height 49 would give a machine-checked "RH up to height 49". That is
about eleven orders of magnitude below what has been verified numerically since the 1980s
(all zeros to height ~3×10¹², isolated zeros near 10²⁴). Its value would be that it is
machine-checked, not the height reached.

And no finite-height verification, at any height, is evidence for RH in the mathematical
sense. RH is not the limit of these statements.
