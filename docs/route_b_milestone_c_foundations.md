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

### C2a-4b — the nested-triangle completeness squeeze  (REMAINING crux; all inputs built)
Assemble Goursat's theorem `tri_int(h) = 0` for `h` holomorphic on a neighborhood of the closed
triangle. Precise structure (each input now exists):
1. **Sequence**: `worst_sub : (C·C·C) → (C·C·C)` picks, among the 4 medial sub-triangles
   (`tri_bisect`), the one of largest `Cmod(tri_int h ·)` (`Rle_dec`). `Tn := iter worst_sub n T`.
2. **Lower bound**: `Cmod(tri_int(T_{n+1})) ≥ Cmod(tri_int(Tn))/4` (bisection: `|Σ_4| ≤ 4·max`),
   so `Cmod(tri_int(Tn)) ≥ Cmod(tri_int(T))/4ⁿ` (induction).
2'. **Geometry**: each medial sub has half the edge lengths ⇒ `diam(worst_sub X)=diam X/2`,
    `perim = perim/2` ⇒ `diam(Tn)=diam T/2ⁿ`, `perim(Tn)=perim T/2ⁿ` (pure `Cmod`/midpoint algebra).
3. **Limit**: the vertex sequences are Cauchy (`|Δvertex| ≤ diam(Tn) = diam/2ⁿ`, geometric) ⇒
   converge to `zc` (R-completeness on `Re`/`Im` components); `|vertex(Tn) − zc| ≤ 2·diam(Tn)`.
4. **Remainder bound**: `h` holomorphic at `zc` (`is_Cderiv h zc c1`) ⇒ `∀ε∃δ`, `|z−zc|<δ ⇒
   |rem z| ≤ ε|z−zc|` where `rem z = h z − Aff z`, `Aff` from `(h zc, c1)`. For `z` on `∂Tn`
   (convex combo of 2 vertices), `|z−zc| ≤ 2·diam(Tn)`; pick `n` with `2·diam(Tn) < δ`.
5. **Squeeze**: `Cmod(tri_int(T))/4ⁿ ≤ Cmod(tri_int(Tn)) = Cmod(tri_int(rem,Tn)) ≤
   2·(ε·2·diam(Tn))·perim(Tn) = 8ε·diam·perim/4ⁿ` ⇒ `Cmod(tri_int(T)) ≤ 8ε·diam·perim`
   `∀ε>0` ⇒ `tri_int(T) = 0`.

Large (~300 lines) but every ingredient is in place; the completeness limit (step 3) is the
one genuinely delicate part (Cauchy sequence in C via the two R-component sequences).

### Then: C2b–C2d (Cauchy integral formula) → C4 (Newman) → Milestone D → PNT.
