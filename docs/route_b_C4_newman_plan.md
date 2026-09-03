# C4 — Newman's analytic theorem (Zagier form) + Milestone D → PNT

> **STATUS: ✅ CLOSED.** This route now reaches PNT outright:
> `NewmanE7.PNT : Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1`, axiom-clean, with no
> `Admitted`/`Axiom`. Every blocker list below is **historical**; see
> `docs/pnt_endgame_plan.md` for the brick-by-brick record (E1–E7) and for where this file's
> scoping was wrong. Two claims here were already checked against source and corrected in
> place: the **C0** bullet (its premise about `zetaC` lacking pole structure at 1 was false)
> and the "machinery the repo does not yet have" paragraph (that machinery was in this
> file's own DONE list). Verify against `spectral-theory/` before relying on any remaining
> claim of absence.


## Progress snapshot (contour wall complete; Newman assembly + C0 remain)

**DONE, axiom-clean:** bricks 1–3 (region Goursat / convex primitive / exceptional point),
brick 4 `CTruncWind.trunc_winding` (∮_C dz/z = 2πi), brick 5 `CTruncCauchy.trunc_cauchy`
(∮_C F/z = 2πi·F(0), conditional on φ's exceptional-point interface), `CTruncDisk` (the Convex+Open
region U = {|z|<R}∩{Re z>−δ}), brick 6 `CNewmanKernel`, brick 7 `CLaplace.gT_holo`
(g_T(z)=∫₀ᵀ f e^{−zt}dt entire, via CexpRemainder + ML). The contour wall is finished.

**The deep remaining blockers** (each needs new infrastructure, not just assembly):
- **C0 — holomorphy of `PhiMinus` at `s=1`. PARTIALLY DISCHARGED.**
  ⚠ The original premise here was **false**: `zetaC` *does* have explicit pole structure at 1 —
  `CZeta.zetaC s = 1/(s−1) + Σ gtermC s` **by definition**, so the pole is the first summand and
  the regular part is the series.
  ✅ **The value half is proven**: `ZetaResidue.zeta_residue_one` gives `(s−1)·ζ(s) → 1`,
  axiom-clean, from `ZetaEM.htermC_tail` at `M=0` plus `ZetaTrap.Cmod_htermC_bound` at `n=0`
  (`|Hsum| ≤ 2·Kh`, and `Kh ≤ 5/8` for `|s−1| ≤ 1/2`). The predicted "complex Euler–Maclaurin"
  already existed — it was built for the sign certificates.
  ✅ **The holomorphy half is also closed.** `CZetaRegular6.BfnT_holo` already proved that the
  *total* function `BfnT` (`= (s−1)·zF` off 1, `= 1` at 1) is holomorphic on all of `{Re s > 0}`;
  it was simply never wired to `PhiMinus`. `ZetaPoleCancel2.v` does that wiring:
  `phi_minusT_holo`, `phi_minusT_at1`, `phi_minusT_holo_near1`, and `phi_minusT_eq` (agreement
  with the old `PhiMinus` off 1), all axiom-clean. **C0 is CLOSED.**
  Why a new function was needed rather than a patch: `ZetaFn.zF` is *defined* to be `C0` at
  `s=1`, so `ZetaPoleCancel.Bfn C1 = C0` — recorded as the theorem
  `ZetaPoleCancel2.old_Bfn_broken_at1`.
  The next blocker is therefore the **g-extension**, not C0.
- **The g-extension / discharge φ.** The integral infra needs GLOBAL `CcontC` continuity; `g` is
  only holomorphic near the truncated disk. Need a continuous extension off the domain (or a
  reformulation). Tied to C0.
- **Brick 8 `CNewman.v`** — the analytic theorem: contour identity `2πi(g(0)−g_T(0)) =
  ∮_C(g−g_T)e^{zT}K_R` (brick 5 + loop-zero of z/R²), three ML estimates, R,T→∞ limits ⇒ ∫₀^∞ f
  converges. Needs C0 + extension + the g_T tail bound (improper ∫₀^∞).
- **Milestone D — Tauberian bridge** `∫₁^∞(ψ(x)−x)/x²dx converges ⟹ ψ(x)/x→1` (ABSENT), then
  `pi_asymp_of_psi` ⇒ PNT. (The elementary Selberg route already reaches `ψ/x→1` modulo one lemma.)

## Where C2 landed, and the key architectural finding

C2 delivered Cauchy's integral formula **on a full circle** (`CUnifCont.cauchy_formula_full`),
for `F` holomorphic **everywhere** (`forall z, is_Cderiv F z (Fp z)`). **This does not apply to
Newman.** Newman's `g = PhiMinus = Φ − 1/(s−1)` is holomorphic only on `{0 < Re z, z≠1, ζ≠0}`
(incl. the line `Re s=1` except `s=1`; see `ZetaPoleCancel.phi_minus_holo`/`phi_minus_line_holo`).
A full circle of radius `R→∞` centered at 0 leaves that domain — which is exactly why Zagier uses
the **truncated disk** `C = ∂({|z|≤R} ∩ {Re z ≥ −δ})` (arc + vertical chord). So C4 needs
**region-restricted** contour machinery, `goursat` / `Prim_deriv` / `cauchy_integral_formula`
all being stated for **global/entire** holomorphy. ✅ **Superseded — that machinery was since
built**: see the DONE list at the top of this file (`CGoursatConv.tri_int_conv`,
`CPrimConv.pathint_loop_conv` + `PrimC_deriv`, `CGoursatExcept.pathint_loop_except`).

The one lever already region-friendly: `CPathFTC.pathint_FTC` / `pathint_primitive_loop` take the
primitive `H` **pointwise along the path only** — so once a primitive exists on the region, loop
integrals over paths in the region vanish for free.

## Two unproven prerequisites
- **C0 — holomorphy of `PhiMinus` at `s=1`** (⟺ `g` at `z=0`). NOT proven; every holomorphy lemma
  excludes `s=1`. `Bfn=(s−1)ζ`, `Bderiv` are set up (`ZetaPoleCancel.v`) but the derivative at the
  point `s=1` is not discharged. Needs `(s−1)ζ(s) → 1` (residue) so `Bfn(1)=1≠0`, `Bfn`/`Bderiv`
  holomorphic at 1, then `PhiMinus=−Bderiv/Bfn` holomorphic at 1. Depends on the zeta continuation
  `zF` — check whether `(s−1)ζ` extends to 1 in `CZetaHolo.v`.
- **The truncated-disk Cauchy formula** (the contour wall, below).

## Brick decomposition (each a file; ~2000 lines total — a multi-session milestone)

### The contour wall (region-restricted Cauchy) — bricks 1–2 DONE
**Brick 1 ✅ `CGoursatConv.v`** — `tri_int_conv`: region Goursat for a non-degenerate closed
triangle (signed-area `InTri` + limit-stable sign conditions; axiom-clean).
**Brick 2 ✅ `CPrimConv.v`** — `Convex`/`Open`, `convex_hull_subset`, `tri_split_vertex`,
`tri_int_conv_all` (all triangles in an open convex `U`; degenerate case split through an off-line
apex `w = v0 + λ·i·(v2−v0) ∈ U`), and the `ConvexPrim` section: `PrimC_deriv`
(`is_Cderiv PrimC z (F z)` on `U`) + `pathint_loop_conv` (closed C¹ loop in `U` ⇒ `pathint F = 0`).
Axiom-clean.

**Brick 3 ✅ `CGoursatExcept.v` — DONE, axiom-clean.** `seg_split_param` (general Chasles) →
`tri_corner_split` → `tri_except_vertex` (ML shrink + `p ∉ hull` via barycentric coords) →
`extract_t`/`seg_chasles_collinear` → `tri_int_collinear` → **`tri_int_except`** (exceptional point
anywhere) → **`pathint_loop_except`** (removable-singularity loop-zero on a convex region). This is
the loop-zero engine for brick 5.

**Brick 3 (original scoping, now delivered):**
- `seg_split_param` : `seg_int f a c = seg_int f a (seg a c δ) + seg_int f (seg a c δ) c` for
  `δ∈[0,1]` (generalises `CSegInt.seg_concat` from δ=½; same `Cintf_cov` + affine-map plumbing).
  Gives `tri_int_collinear` (degenerate ⇒ 0 for merely-continuous `h`).
- `tri_except_vertex` : `h` continuous, holo on `U∖{p}`, `p` a vertex ⇒ `tri_int h p a b = 0`.
  Cut a small corner triangle `(p, seg p a δ, seg p b δ)`; the two `p`-avoiding pieces vanish (see
  reformulation below), the two collinear slivers vanish (`tri_int_collinear`), the corner is
  ML-bounded (`tri_int_ML`, `perim→0`) ⇒ 0.
- **Recommended reformulation to avoid convex-nbhd construction:** give `tri_int_conv`/`_all` a
  variant taking holomorphy on the CLOSED triangle `InTri(v0,v1,v2)` (brick 1 already does), so a
  `p`-free sub-triangle uses `h` holo on `InTri(sub) ⊆ U∖{p}` directly — no open convex `U'∌p`
  needed. Only degenerate `p`-free subs need the off-line apex (choose it `≠ p` via `Open`).
- `tri_int_except` (`p` anywhere in `U`) via `tri_split_vertex` through `p`; then `pathint_loop_except`
  (rerun brick 2's `PrimC` with `tri_int_except`).

### The contour wall — original brick list (unchanged detail)
1. **`CGoursatConv.v` — region Goursat.** `tri_int h v0 v1 v2 = 0` for `h` globally continuous
   (`CcontC h`) but holomorphic only on the closed triangle. Copy `CGoursat.goursat`; weaken `Hhol`
   to `forall z, InTri v0 v1 v2 z -> exists d, is_Cderiv h z d`; the ONE new obligation is
   `InTri v0 v1 v2 zc` (the nested limit `zc` lies in the closed triangle). Cleanest: barycentric /
   signed-area (`cross`) characterization — `InTri` = three `cross`-sign conditions, each closed
   (continuous `≥0`, preserved under the limit `V0(seqT n) → zc`). Handle the degenerate
   (collinear) case. **The main risk brick.**
2. **`CPrimConv.v` — primitive on a convex region.** `F` holomorphic on convex `U` ⇒ base-point
   `Prim z := seg_int F z0 z` satisfies `is_Cderiv Prim z (F z)` on `U` (via `CGoursatConv` on the
   triangle `z0,z,z+k ⊆ U`), hence `∮_loop F = 0` on `U` (`pathint_primitive_loop`).
3. **`CGoursatExcept.v` — one exceptional point.** `h` continuous everywhere, holomorphic on
   `U∖{p}` ⇒ `tri_int h = 0`: subdivide so `p` is a vertex of a small sub-triangle, region-Goursat
   on the `p`-avoiding pieces (they tile `△`), ML-bound the small piece → 0. Gives a primitive of a
   removable-singularity function on the convex region.
4. **`CTruncWind.v` — `∮_C dz/z = 2πi`** for the truncated contour. Either explicit (arc angle
   `2θ₀` + chord `∫ i dy/(−δ+iy)`, arctan/log cancelling to `2πi`) or `= ∮_{full circle} −
   ∮_{left cap}` where the left-cap loop = 0 (bricks 2–3, `1/z` holomorphic off 0, 0 not in cap).
5. **`CTruncCauchy.v` — `∮_C F/z = 2πi·F(0)`** for `F` holomorphic on the truncated disk:
   `(F(z)−F(0))/z` continuous + holomorphic off 0 ⇒ loop 0 (brick 3) ⇒ `∮_C F/z = F(0)∮dz/z` (4).

### Bricks 4–5 — precise ready-to-execute construction (all stdlib pieces CONFIRMED present)
Parametrise the truncated contour by `R>0` and half-angle `α∈(π/2,π)` with `δ := −R·cos α > 0`,
`Y := R·sin α > 0`; endpoints `P := arc R α = mkC (−δ) Y` (top), `Q := arc R (−α) = mkC (−δ) (−Y)`
(bottom). Contour `C` = arc `arc R` over `[−α, α]` (through 0) then chord `seg P Q` over `[0,1]`.

**Brick 4 ✅ `CTruncWind.v` — DONE, axiom-clean.** `trunc_winding : ∮_C dz/z = mkC 0 (2π)` (`= 2πi`),
EXACTLY as designed below (chord result `mkC 0 (−2·atan(y/a))`, `a=R cos α`, `y=R sin α`; identity
`2α − 2·atan(y/a) = 2π` via `atan(tan α)=α−π`, `tan(α−π)=tan α` from `sin_minus/cos_minus` since
`tan_PI_minus` is absent). `Nfun_deriv`/`Ginn_deriv` proved from the ε–δ definition directly (the
`derivable_pt_lim_scal`/`mult_real_fct` unification against explicit lambdas is flaky).

Original design — via EXPLICIT computation (avoids the
convex-`1/z`-primitive, which fails since `CcontC Cinv` is false — `Cinv` is discontinuous at 0):
- Arc part: `pathint (arc R)(arc' R) Cinv (−α) α = mkC 0 (2α)` — integrand `= Ci` by
  `CWinding.arc_over_id`, then `Cintf_const_ab`. (Clean, ~10 lines.)
- Chord part: `pathint (seg P Q)(seg' P Q) Cinv 0 1 = mkC 0 (2·atan (Y/δ))`. On the chord
  `seg P Q s = mkC (−δ) (Y(1−2s))`, `seg' = mkC 0 (−2Y)`, so the integrand is
  `mkC (−2Y²(1−2s)/N) (2δY/N)` with `N = δ²+Y²(1−2s)²`. Evaluate the two `RiemannInt`s by
  `ContinuousCoV.FTC_antideriv` (`RiemannInt = G b − G a` from `antiderivative f G a b`):
    - Re integrand antiderivative `G_Re s := ½·ln N` (`G_Re' = −2Y²(1−2s)/N`,
      `derivable_pt_lim_ln` + chain); `Re = ½(ln N(1) − ln N(0)) = 0` (`N(0)=N(1)=δ²+Y²`).
    - Im integrand antiderivative `G_Im s := −atan (Y(1−2s)/δ)` (`G_Im' = 2δY/N`,
      `derivable_pt_lim_atan` + chain, inner `s ↦ Y(1−2s)/δ`); `Im = 2·atan(Y/δ)`.
  Build each `antiderivative` in the `exists pr:derivable_pt, f=derive_pt` form (mirror
  `CSegInt.seg_reverse`'s `Hanti`). (~90 lines.)
- Identity `2α + 2·atan(Y/δ) = 2π`: `Y/δ = −tan α = tan(PI−α)` (`tan_PI_minus`, needs `cos α≠0`),
  `π−α ∈ (−π/2,π/2)` so `atan(tan(π−α)) = π−α` (`atan_tan`) ⇒ `atan(Y/δ)=π−α`. (~20 lines.)

**Brick 5 ✅ `CTruncCauchy.v` — DONE, axiom-clean (conditional).** `trunc_cauchy` proves
`∮_arc F/z + ∮_chord F/z = Cmul (F 0) (mkC 0 (2π))`. Rather than construct the piecewise `φ` and its
global continuity (the hard removable-at-0 fact), the theorem is a `Section` that TAKES `φ`'s
exceptional-point interface as hypotheses: `CcontC φ`, holo off 0, bounded/continuous near 0, and
agreement `φ = (F−F 0)/z` on the contour. The split `F/z = (F−F 0)/z + F 0·(1/z)` holds everywhere
by `ring` (distributivity — no `z≠0` needed, so no patch in the split); `∮_C φ = 0` telescopes via
`PrimE_deriv` (brick 3) + `pathint_FTC` on arc then chord (`P,Q` cancel); the `F 0/z` part is
`Cintf_cmul_l` + `trunc_winding` (brick 4). Remaining for the Newman app: discharge the `φ`
hypotheses (this IS the flagged global-`CcontC`/extension concern). Original design:

For `F : CcontC F` holomorphic on (a nbhd of)
the truncated disk (`0` interior). Split `F(z)/z = F(0)·(1/z) + φ(z)`, `φ := fun z => if z=C0 then
Fp 0 else Cmul (Cminus (F z)(F 0)) (Cinv z)` — the removable-singularity function; note the raw
formula gives `C0` at 0 (`Cmul C0 _`), so the `if z=C0` branch (value `Fp 0`) is REQUIRED for
continuity at 0. `φ` is globally continuous (`CcontC φ`, from `is_Cderiv F 0 (Fp 0)`) and holomorphic
off 0, so `pathint_loop_except` (brick 3) gives `∮_C φ = 0` by telescoping `PrimE` over the arc +
chord pieces (`pathint_FTC` each, endpoints `P,Q` cancel). Then per-piece linearity (`Cintf_cmul_l`,
`Cintf_sub`) ⇒ `∮_C F/z = F(0)·∮_C dz/z + ∮_C φ = F(0)·2πi` (brick 4). The global-`CcontC` demand on
`F`/`φ` is the same extension concern as the Newman application (brick 8) — a global continuous
extension of `g` off its domain, agreeing on the truncated disk.

### Newman + application
6. **`CNewmanKernel.v` ✅ DONE** — `newman_kernel R z = 1/z + z/R²`; on `|z|=R` it is the real
   `2·Re z/R²`, so `|K_R| = 2|Re z|/R²` (`Cmod_newman_kernel`). Axiom-clean.
7. **`CLaplace.v` — `g_T(z) = ∫₀^T f(t)e^{−zt}dt`** (via `Cintf` + `CExpKernel.cexpzt`), entire in
   `z` (differentiation under the integral — reuse `CLeibniz.leibniz_deriv`); the tail bound
   `|g(z) − g_T(z)| ≤ B·e^{−Re z·T}/Re z` for `Re z > 0`.
8. **`CNewman.v` — Newman's theorem.** Truncated contour (bricks 1–5), the identity
   `2πi(g(0)−g_T(0)) = ∮_C (g−g_T)e^{zT}K_R` (brick 5 + loop-zero of the `z/R²` part), the three
   ML estimates (right semicircle via brick 6; left arc `g` → 0 as `T→∞` via `|e^{zT}|=e^{Re z·T}`;
   left `g_T` deformation, entire), and the `R→∞`/`T→∞` limits ⇒ `∫₀^∞ f = g(0)` (`ImproperCv1`).
9. **Milestone D — apply Newman ⇒ PNT.** `f(t)=ψ(eᵗ)e^{−t}−1`, `g=PhiMinus∘(z+1)` holomorphic
   (needs C0); Laplace form of Φ (`phi_integral_rep` + `cov_local` `x=eᵗ`); Newman ⇒
   `∫₁^∞(ψ(x)−x)/x²dx` converges; Tauberian monotone squeeze ⇒ `ψ(x)/x → 1` ⇒
   `Un_cv (fun N => psi N/INR N) 1` ⇒ `PNTConditional.pi_asymp_of_psi` ⇒ PNT.

## Recommended build order
`CNewmanKernel` ✅ → **C0** (independent, unblocks the application) → **brick 1 (region Goursat,
the keystone/risk)** → 2 → 3 → 4 → 5 → 7 → 8 → 9. Bricks 6/7/C0 are independent of the wall and can
proceed in parallel.

## Note: the elementary alternative
`PsiAsymp.v` shows PNT is already axiom-clean **modulo the single lemma `avg_below (limsup Vrem)`**
(the Selberg/elementary route). C4 (the analytic route) is an independent, much larger path to the
same target `Un_cv (fun N => psi N/INR N) 1`.
