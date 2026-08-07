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

## C2a — Goursat's theorem: `∮_{∂△} h = 0` for `h` holomorphic on a triangle

**Placement:** the FIRST brick of the C2 (Cauchy) stage, built directly on C1c. Everything
downstream (C2b primitive-on-convex, C2c winding, C2d Cauchy integral formula, C4 Newman)
depends on it. It is the single hardest brick of the milestone.

**The proof (bisection), decomposed into sub-bricks:**

- **C2a-1 triangle boundary** (`CTriangle.v`): represent a triangle by 3 vertices `v0,v1,v2`;
  its boundary integral `tri_int h v0 v1 v2 := pathint(seg v0 v1) + pathint(seg v1 v2) +
  pathint(seg v2 v0)` (sum of 3 `pathint` over `seg`, C1b). Orientation/reversal via
  `pathint_swap`. Perimeter and diameter functions; basic bounds.

- **C2a-2 bisection identity** (`CGoursatBisect.v`): the 4 medial sub-triangles (edge
  midpoints `m01,m12,m20`); prove `tri_int(T) = Σ_{i=1}^4 tri_int(Ti)` — the inner edges
  are each traversed twice in opposite directions and cancel (`pathint_swap` +
  `pathint_split` on `seg`, since a segment reversed is its negative and midpoint-splitting a
  segment is `pathint_split`). Hence `∃ i, |tri_int(Ti)| ≥ |tri_int(T)|/4`, with
  `diam(Ti)=diam/2`, `perim(Ti)=perim/2`. Finicky but purely algebraic.

- **C2a-3 the affine primitive** (in `CGoursat.v`): the affine map `z ↦ h(z*)+h'(z*)(z−z*)`
  has the explicit primitive `H(z) = h(z*)·z + h'(z*)·(z−z*)²/2` (an `is_Cderiv`, via the
  existing calculus). So its loop integral over ANY closed triangle is `0` by
  `pathint_primitive_loop` (C1c). Thus `tri_int(T,h) = tri_int(T, remainder)` where
  `remainder(z) = h(z) − [h(z*)+h'(z*)(z−z*)]`, and `|remainder(z)| ≤ ε·|z−z*|` near `z*`
  (from `is_Cderiv h z*`).

- **C2a-4 nested limit + squeeze** (`CGoursat.v`): the nested triangles `T ⊃ T^(1) ⊃ …` have
  `diam(T^(n)) = diam/2^n → 0`; by completeness (Cauchy on the `Re/Im` components, or a
  nested-compact argument) they shrink to a point `z*` inside `T`. Combine
  `|tri_int(T)|/4^n ≤ |tri_int(T^(n))| = |tri_int(T^(n),remainder)| ≤ ε·diam(T^(n))·perim(T^(n))
  = ε·(diam·perim)/4^n` (ML bound `pathint_ML`, C1b), giving `|tri_int(T)| ≤ ε·diam·perim`
  for every `ε>0`, hence `tri_int(T)=0`.

**Risk / cost:** the largest brick of the project. The bisection combinatorics (C2a-2) are
tedious but mechanical; the genuine risk is C2a-4 (the nested-triangle completeness limit on
the custom field) — that is the piece to prove out FIRST as the feasibility test for the whole
wall. Reusable inputs already in hand: `pathint_primitive_loop`, `pathint_ML`, `pathint_split`,
`pathint_swap`, `seg`, the full `is_Cderiv` calculus.

## Remaining after C2a
C2b (primitive on convex ⇒ `∮_loop=0`) → C2c (`∮_C dz/z = 2πi`, truncated disk) →
C2d (Cauchy formula `∮_C F/z = 2πi·F(0)`) → C4 (`Newman.v`) → Milestone D (D1 single-∫ Φ rep,
D2 Laplace/CoV + C0 holomorphy-at-1, D3 Newman⇒convergence, D4 Tauberian squeeze) ⇒
`Un_cv (psi N/INR N) 1` ⇒ `pi_asymp_of_psi` ⇒ PNT.
