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

### C2a-1 — triangle boundary + segment reparametrization laws
- **DONE (core):** `CSegCoV.v` — `Cintf_cov`, the C-valued change of variables
  `∫_a^b g'(t)·G(g t) dt = ∫_{g a}^{g b} G` for an increasing C¹ substitution `g`
  (componentwise from `LocalCoV.cov_local`, witnesses bridged by `RiemannInt_P18`).
  Axiom-clean. This is the reparametrization engine.
- **Remaining:** `seg_int` (a segment integral wrapper), segment **concatenation**
  `seg_int a c = seg_int a m + seg_int m c` (via `Cintf_additive` + `Cintf_cov` on the two
  increasing halves `v↦v/2`, `v↦(1+v)/2`), segment **reversal** `seg_int b a = −seg_int a b`
  (a reflection variant `∫₀¹φ(1−u)du = ∫₀¹φ`; `cov_local` is increasing-only, so this needs a
  small dedicated reflection CoV), and `tri_int` + perimeter/diameter. Each threads an
  f-continuity hypothesis (automatic for holomorphic f).

### C2a-2 — bisection identity `tri_int(T) = Σ_{i=1}^4 tri_int(Tᵢ)`
Pure edge combinatorics on top of C2a-1's concatenation + reversal: each outer edge splits at
its midpoint (concatenation) into two half-edges shared by sub-triangles; the three inner
(medial) edges are each traversed twice in opposite directions and cancel (reversal). Yields
`∃i, |tri_int(Tᵢ)| ≥ |tri_int(T)|/4` with halved diameter/perimeter. Tedious but mechanical
once the segment laws are in place.

**Then:** C2a-3 (affine primitive ⇒ loop 0, via C1c) + C2a-4 (nested-triangle completeness
squeeze — the feasibility crux) finish Goursat.

## Remaining after C2a
C2b (primitive on convex ⇒ `∮_loop=0`) → C2c (`∮_C dz/z = 2πi`, truncated disk) →
C2d (Cauchy formula `∮_C F/z = 2πi·F(0)`) → C4 (`Newman.v`) → Milestone D (D1 single-∫ Φ rep,
D2 Laplace/CoV + C0 holomorphy-at-1, D3 Newman⇒convergence, D4 Tauberian squeeze) ⇒
`Un_cv (psi N/INR N) 1` ⇒ `pi_asymp_of_psi` ⇒ PNT.
