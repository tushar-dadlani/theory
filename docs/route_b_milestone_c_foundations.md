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

### Remaining Milestone C/D
- C2b: holomorphic on a convex set ⇒ has a primitive ⇒ `∮_loop = 0` (define the primitive by a
  base-point integral; path-independence from `goursat` via triangulation).
- C2c: `∮_C dz/z = 2πi` (explicit winding of the truncated-disk contour).
- C2d: Cauchy integral formula `∮_C F/z = 2πi·F(0)` (`(F(z)−F(0))/z` removable + C2b + C2c).
- C4: Newman's analytic theorem (contour estimates on `CPathIntegral`/`CExpKernel`).
- Milestone D: Newman ⇒ `ψ~x` ⇒ `pi_asymp_of_psi` ⇒ PNT (with C0 = holomorphy at `s=1`).
