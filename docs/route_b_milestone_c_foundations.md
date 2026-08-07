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

### C2a-3, C2a-4 — remaining Goursat pieces
- C2a-3: the affine map `z ↦ h(z*)+h'(z*)(z−z*)` has explicit primitive
  `h(z*)·z + h'(z*)·(z−z*)²/2`, so its loop integral over any closed triangle is 0
  (`CPathFTC.pathint_primitive_loop`); hence `tri_int(T,h) = tri_int(T, remainder)`,
  `|remainder| ≤ ε|z−z*|`. Needs the triangle boundary as a single closed path (join the 3
  `seg` into one `pathint` over `[0,3]`, or sum the segment FTCs).
- C2a-4 (crux): nested triangles shrink to `z*` (completeness on Re/Im); the squeeze
  `|tri_int(T)|/4ⁿ ≤ ε·(diam·perim)/4ⁿ` (via `pathint_ML`/a `tri_int` ML bound) ⇒ `tri_int(T)=0`.
  The nested-triangle completeness limit is the feasibility crux of the whole wall.

## Remaining after C2a
C2b (primitive on convex ⇒ `∮_loop=0`) → C2c (`∮_C dz/z = 2πi`, truncated disk) →
C2d (Cauchy formula `∮_C F/z = 2πi·F(0)`) → C4 (`Newman.v`) → Milestone D (D1 single-∫ Φ rep,
D2 Laplace/CoV + C0 holomorphy-at-1, D3 Newman⇒convergence, D4 Tauberian squeeze) ⇒
`Un_cv (psi N/INR N) 1` ⇒ `pi_asymp_of_psi` ⇒ PNT.
