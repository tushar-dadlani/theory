# Route B, Milestone C — foundations DONE; Goursat (C2a) scoped & placed

Milestone C = Newman's analytic theorem (Zagier form). Strategy: foundations first,
Zagier truncated-disk contour, stage the Goursat/Cauchy wall.

## Foundations built (axiom-clean, committed, pushed)

| Brick | File | Content |
|------|------|---------|
| C1a | `CIntegral2.v` | general finite C-integral `Cintf f Hf a b`; `Ccont` algebra; Chasles additivity; reversal; ML `Cmod(Cintf) ≤ 2M(b−a)` |
| C1b | `CPathIntegral.v` | contour integral `pathint γ γ' f`; split/swap/ML; `seg` + `arc` paths (`Cmod_arc=r`) |
| C1c | `CPathFTC.v` | **path chain rule** `Cderiv_path_Re/Im`; **path FTC** `pathint_FTC` (primitive ⇒ `pathint = H(γb)−H(γa)`); **`pathint_primitive_loop`** (closed path + primitive ⇒ `pathint = 0`) |
| C3 | `CExpKernel.v` | `e^{zt}`: modulus `exp(Re z·t)`, t-derivative `z·e^{zt}`, continuity |

`pathint_primitive_loop` is the **engine of Cauchy's theorem** — the entire wall is built on it.

## C2a — Goursat's theorem: status

**Placement:** the FIRST brick of the C2 (Cauchy) stage, built on C1c's
`pathint_primitive_loop`. The single hardest brick of the milestone.

### C2a-1 — triangle boundary + segment reparametrization laws  ✅ DONE
- `CSegCoV.v` — `Cintf_cov`, the C-valued increasing change of variables.
- `CSegInt.v` — `seg_int` (segment integral for a continuity-preserving `CcontC f`);
  **concatenation** `seg_concat : seg_int a c = seg_int a (mid a c) + seg_int (mid a c) c`
  (Cintf_additive + Cintf_cov on the two increasing halves); **reversal**
  `seg_reverse : seg_int b a = −seg_int a b` (reflection `∫₀¹−φ(1−u)=−∫₀¹φ` via FTC).

### C2a-2 — bisection identity  ✅ DONE
- `CTriangle.v` — `tri_int` (triangle boundary integral) and
  `tri_bisect : tri_int(T) = Σ_{i=1}^4 tri_int(Tᵢ)` for the four medial sub-triangles.
  Proof: `seg_concat` splits outer edges at midpoints, `seg_reverse` cancels the three medial
  edges, then `ring`. Axiom-clean.

### C2a-3 — reduce Goursat to a small remainder  ✅ DONE
- `CGoursatFTC.v` — `seg_FTC`; `tri_int_primitive_zero` (a function with a global primitive
  has zero triangle integral, by telescoping).
- `CGoursatLin.v` — `Cintf_add`/`seg_int_add`/`tri_int_add` (integrand linearity).
- `CGoursatML.v` — `perim`/`diam`; `seg_int_ML`; `tri_int_ML` (`Cmod(tri_int f) ≤ 2·sup|f|·perim`).
- `CGoursatAffine.v` (C2a-4a) — `affine_tri_zero`: the affine approximant `Aff z = c0+c1(z−zc)`
  has primitive `AffH z = c0 z + c1(z−zc)²/2`, so `tri_int(Aff) = 0`.

  Together: for holomorphic `h`, `tri_int(h) = tri_int(Aff) + tri_int(rem) = tri_int(rem)`
  (`tri_int_add` + `affine_tri_zero`), and `|tri_int(rem)| ≤ 2·sup|rem|·perim` (`tri_int_ML`).

### C2a-4b — Goursat's theorem  ✅ DONE
- `CGoursatGeom.v` — the sub-triangles have half the diameter; corners move by <= half a diameter.
- `CGeomCauchy.v` — `geom_cauchy_cv`: a real sequence with geometric increments converges with
  an explicit rate (R-completeness core for the vertex sequences).
- `CGoursat.v` — `goursat : tri_int h v0 v1 v2 = 0` for `h` holomorphic (`is_Cderiv` everywhere).
  The nested-triangle argument: `nextT` picks the worst sub-triangle, the tracked corner is
  Cauchy → limit `zc`; every boundary point lies within `3·diam·(1/2)^n` of `zc`; at `zc`,
  `h = affine + remainder`, affine integrates to 0 (`affine_tri_zero`), remainder is
  `O(ε·diam)` (`tri_int_ML`); the `≥/4ⁿ` lower bound (`tin`) vs the `≤ O(ε·diam²·(1/4)ⁿ)` ML
  bound forces `tri_int(h) ≤ 18ε·diam²` for all `ε`, hence `= 0`.  Axiom-clean.

**Goursat — the foundational hard theorem of the contour-integration wall — is complete.**

### C2b — primitive of a holomorphic function + loop zero  ✅ DONE
- `CPrimitive.v` — `seg_int` algebra (`seg_int_const/opp/sub`, `Cintf_const01`); the base-point
  primitive `Prim z := seg_int F z0 z`; `Prim_diff : Prim(z+k)−Prim(z) = ∫_z^{z+k}F` (Goursat
  kills the triangle `z0,z,z+k`; `seg_reverse`); **`Prim_deriv : is_Cderiv Prim z (F z)`**
  (the increment `∫_z^{z+k}(F(w)−F(z))dw` is `o(k)` by `is_Cderiv_cont` + `seg_int_ML`);
  **`pathint_loop_holo`**: the loop integral of a holomorphic `F` over any closed `C¹` path
  is `0` (`Prim_deriv` + `pathint_primitive_loop`). Axiom-clean.

### C2c — the winding integral  ✅ DONE
- `CWinding.v` — `Cintf_const_ab`; `arc_over_id`: on `z = r e^{iθ}`, `(1/z)·z' = i` (constant,
  via `cos²+sin²=1`); **`winding_dz_z : ∮_{|z|=r} dz/z = 2πi`**. Axiom-clean.

### C2d — Cauchy integral formula  ⏳ NEXT (the removable-singularity wall)
`∮_C F(z)/z dz = 2πi·F(0)` for `F` holomorphic on the region. Reduces (C2b+C2c) to
`∮_C φ = 0` where `φ(z)=(F(z)−F(0))/z`, `φ(0):=F′(0)`. **`φ` is continuous everywhere but only
holomorphic off `0`** — so C2b's `pathint_loop_holo` (needs holomorphy *everywhere*) does not
apply directly. The honest route is the classical **exceptional-point Goursat** (continuous on
the triangle, holomorphic except at one point ⇒ `tri_int = 0`), which in turn needs a
**region-version of `goursat`** (holomorphy only at the triangle's interior/hull points):
  1. `goursat_hull` — relax `Hhol : forall z, ...` to `forall z, in_hull v0 v1 v2 z -> ...`.
     The current proof already uses `Hhol` at exactly one point, the nested limit `zc`; the new
     obligation is `in_hull v0 v1 v2 zc` (each `seqT` vertex is a convex combination of `v0v1v2`
     by induction; the hull is closed, `zc = lim V0(seqT n)`). Global continuity `CcontC h` is
     kept (no integral-infrastructure refactor).
  2. `goursat_except` — `h` continuous on `△`, holomorphic off `p∈△`: subdivide so `p` is a
     vertex of a small sub-triangle, `goursat_hull` on the `p`-avoiding pieces (they tile `△`,
     internal edges cancel), ML-bound the small piece (`tri_int_ML` + continuity → `0` as it
     shrinks).
  3. C2d proper: `φ` continuous (removable at `0`, value `F′(0)`), holomorphic off `0`;
     `goursat_except` ⇒ primitive on the region ⇒ `∮_C φ = 0`; then
     `∮_C F/z = F(0)·∮_C dz/z + ∮_C φ = 2πi·F(0)` (C2c). This is a multi-brick body (convex-hull
     machinery + subdivision tiling), comparable in size to the original Goursat.

**Alternative route for C2d (mean-value / Leibniz) — may be cleaner.** For the *circle* contour,
`∮_{|z|=R} F/z dz = i∫₀^{2π} F(Re^{iθ})dθ`, so the formula is the mean-value property
`(1/2π)∫₀^{2π}F(re^{iθ})dθ = F(0)`. Set `M(r) := ∫₀^{2π}F(re^{iθ})dθ`; `M(0)=2πF(0)`. Then
`M'(r) = ∫₀^{2π}F′(re^{iθ})e^{iθ}dθ`, and since `d/dθ[F(re^{iθ})] = ir·F′(re^{iθ})e^{iθ}`, FTC +
periodicity give `∫₀^{2π}F′(re^{iθ})e^{iθ}dθ = 0` — equivalently `∮_{|z|=r}F′ = 0`, which is
**exactly C2b** (`F` is a primitive of `F′`, `pathint_primitive_loop`). So `M′(r)=0 ⇒ M` constant
`⇒ M(R)=M(0)`. This avoids convex-hull/tiling machinery entirely; its one new ingredient is the
**Leibniz rule** `d/dr ∫₀^{2π}f(r,θ)dθ = ∫₀^{2π}∂_r f dθ` (differentiation under the RiemannInt,
for `f,∂_r f` jointly continuous) — a single self-contained real-analysis lemma. Recommended
route unless Newman needs the truncated-disk (non-circle) contour, in which case the
exceptional-point Goursat above is required.

**Chosen route: mean-value/Leibniz. Full blueprint (all axiom-clean; `Heine` confirmed to use
only the four Reals axioms, so 2D uniform continuity is achievable without choice/epsilon):**
Let `M(r) := Cintf (fun θ => F(arc r θ)) 0 (2π)` (a C-valued integral). Target `M(R) = M(0)`.
- **Block 1 — reduction (pure C2c reuse).** `∮_{|z|=R} F/z = Cmul Ci (M R)`: the integrand is
  `F(arc R θ)·(Cinv(arc R θ)·arc'(R θ)) = F(arc R θ)·Ci` by `arc_over_id`; pull the constant `Ci`
  out with a `Cintf_cmul_l` helper (RiemannInt linearity). Also `M(0) = Cmul (RtoC 2π) (F C0)`
  (`arc 0 θ = C0`, `Cintf_const_ab`). So the formula `= 2πi·F(0)` follows once `M(R)=M(0)`.
- **Block 2 — `∮_{|z|=r} F' dz = 0` (pure C2b reuse).** `F` is a primitive of `F'`, so
  `pathint_primitive_loop` gives it directly (the arc is a closed C¹ path:
  `arc r 0 = arc r 2π`, `d/dθ Re/Im(arc r θ) = Re/Im(arc' r θ)` are scaled `sin/cos` derivatives).
- **Block 3 — the chain rule (pure C1c reuse).** `d/dr F(arc r θ) = Cmul (F'(arc r θ)) (mkC cosθ sinθ)`
  via `Cderiv_path_Re/Im` with the path `r ↦ arc r θ` (its r-derivative is `mkC cosθ sinθ`,
  `derivable_pt_lim (fun r => r·cosθ) = cosθ`).
- **Block 4 — Leibniz (the one new theorem).** `M'(r) = Cintf (fun θ => d/dr F(arc r θ)) 0 (2π)`.
  Core is easy (`Cintf` linearity + `Cintf_ML`): `M(r)−M(r0)−M'(r0)(r−r0) = ∫[o(r−r0)]dθ`, bounded
  by `2π·(uniform o)`. The ONE hard input is the **uniform-in-θ bound**, which the `seg`-FTC
  reduces to **uniform-in-θ continuity of `ρ ↦ F'(arc ρ θ)` at `ρ=r0`**
  (`F(w+Δ)−F(w)−F'(w)Δ = ∫_{seg w (w+Δ)}(F'−F'(w))`, ML-bounded by `sup_ρ|F'(arc ρ θ)−F'(arc r0 θ)|`).
  That sup-continuity is 2D uniform continuity on the compact `[r0−δ,r0+δ]×[0,2π]`; build it
  axiom-clean by mimicking `Rtopology.Heine`'s finite-open-cover construction for the 2-parameter
  map (avoid the sequential/`ValAdh` route — extracting the sequence from the negation would need
  a choice axiom, breaking axiom-cleanliness).
- **Block 5 — assembly.** Block 2 ⇒ `M'(r) = (1/(ir))∮_{|z|=r}F' = 0` for `r>0`; `M` continuous
  (Leibniz ⇒ differentiable ⇒ continuous) with `M'≡0` on `(0,R]` ⇒ `M` constant (component-wise
  `null_derivative`/MVT) ⇒ `M(R)=M(0)`. Combine with Block 1 ⇒ `∮_{|z|=R}F/z = 2πi·F(0)`.

Estimated size ~250–350 lines, dominated by Block 4's Heine-style 2D uniform continuity. Blocks
1–3 are near-verbatim reuse of C2b/C2c/C1c and can be committed independently first.

### C2d — Cauchy's integral formula on a circle  ✅ (modulo one standard hypothesis)
Executed the mean-value/Leibniz route:
- `CMeanValue.v` (Blocks 2+3) — `circint_Fp_zero` (`∮_{|z|=r}F′=0`), `Farc_r_deriv` (radial chain rule).
- **`CLeibniz.v` (Block 4)** — `leibniz_deriv`: differentiation under the finite C-integral, from a
  uniform first-order estimate (`RInt_scal`/`RInt_sub`/`Cintf_cmul_l`/`Cintf_sub` + `Cintf_ML`;
  componentwise `Cmod_Re`/`Cmod_Im`). Reusable, no topology. Axiom-clean.
- **`CCauchyFormula.v` (Blocks 1+4+5)** — `cauchy_integral_formula`:
  `∮_{|z|=R} F/z = 2πi·F(0)`. `M(r)=∫₀^{2π}F(arc r θ)dθ`; `Fdphi_unif` supplies Leibniz's uniform
  estimate via **seg-FTC** (`seg_FTC`+`seg_int_const`+`seg_int_sub`+`seg_int_ML`) bounded by the 2D
  uniform continuity; `Mder_zero` (`∮F′=0` + C-field cancellation) ⇒ `M′≡0` ⇒ `M_const` (`MVT_cor2`)
  ⇒ `M(R)=M(0)=2πF(0)` (`meanval0`+`winding_F_over_z`+`arc_over_id`). Axiom-clean, with **one
  section hypothesis** `Harc_uc` = 2D uniform continuity of `Fp∘arc` over `[0,2π]`.
- **`CUnifCont.v` (Block A)** ✅ — `deriv_lip1`⇒`cos_lip`/`sin_lip` (MVT), `arc_joint_cont` (joint
  continuity of `arc`), and the finite-open-cover step **`arc_Fp_unif`**: mirrors `Rtopology.Heine`
  choice-free — the cover radius at `θ*` is `lub {Ebox θ* radii}` (`completeness`), a finite
  subcover of `[0,2π]` (`compact_P3` + a `disc`-family, `open_set_P6`/`disc_P1`) gives
  `δ = min` over the `domain_finite` list (`fold_right Rmin`). Discharges `Harc_uc` from `Fp`
  pointwise-continuous. Wrapper **`cauchy_formula_full`**: `∮_{|z|=R}F/z = 2πi·F(0)` with the
  natural hypothesis "`Fp` continuous" and NO `Harc_uc`. Axiom-clean.

**C2d — Cauchy's integral formula on a circle — is COMPLETE and axiom-clean.**

### Remaining Milestone C/D
- C4: Newman's analytic theorem (contour estimates on `CPathIntegral`/`CExpKernel`).
- Milestone D: Newman ⇒ `ψ~x` ⇒ `pi_asymp_of_psi` ⇒ PNT (with C0 = holomorphy at `s=1`).
