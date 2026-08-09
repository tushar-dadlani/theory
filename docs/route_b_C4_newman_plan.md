# C4 — Newman's analytic theorem (Zagier form) + Milestone D → PNT

## Where C2 landed, and the key architectural finding

C2 delivered Cauchy's integral formula **on a full circle** (`CUnifCont.cauchy_formula_full`),
for `F` holomorphic **everywhere** (`forall z, is_Cderiv F z (Fp z)`). **This does not apply to
Newman.** Newman's `g = PhiMinus = Φ − 1/(s−1)` is holomorphic only on `{0 < Re z, z≠1, ζ≠0}`
(incl. the line `Re s=1` except `s=1`; see `ZetaPoleCancel.phi_minus_holo`/`phi_minus_line_holo`).
A full circle of radius `R→∞` centered at 0 leaves that domain — which is exactly why Zagier uses
the **truncated disk** `C = ∂({|z|≤R} ∩ {Re z ≥ −δ})` (arc + vertical chord). So C4 needs
**region-restricted** contour machinery that the repo does not yet have: `goursat`, `Prim_deriv`,
`cauchy_integral_formula` are all stated for **global/entire** holomorphy.

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
