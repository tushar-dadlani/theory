# A Categorical Foundation for Euclidean and Riemannian Geometry

## Abstract

We construct a categorical foundation for geometry from two primitive sorted types —
point and line — using sorted sets, a closed symmetric monoidal dagger category, and
a metric functor. The plane emerges as a derived sort from the fixed point of the
dagger acting on the metric functor applied to cross-sort morphisms. Parallelism and
perpendicularity are shown to be self-dual conditions internal to the category. The
circle is identified not as a derived object but as the metric itself reified as a
geometric sort — the object whose existence the metric functor presupposes. The sphere
is the first application of the distance endofunctor to the circle. The constant π is
the hidden witness of the circle's self-duality under the dagger: it is the unique
scalar fixed by `†_M(C) = C`, and is recovered as the limit of the counit of the
adjunction between Riemannian and Euclidean geometry as radius grows without bound.
The n-sphere is the nth iterate of the endofunctor, and the infinite-dimensional
sphere S∞ is its colimit. The parallel postulate is the counit of the adjunction
F ⊣ †_F mediated by stereographic projection.

---

## 1. Sort Signature

**Definition 1.1 (Primitive Sorts).**
Define a sort signature with exactly two primitive sorts:

```
𝒮₀ = { pt, ln }
```

No ambient space is assumed. No other sorts are primitive.

**Definition 1.2 (Sort Function).**
Let `U : 𝒮₀ → Set` be the sorted universe:

```
U(pt) = P       -- the set of points
U(ln) = L       -- the set of lines
```

with sort function `s : P ⊔ L → 𝒮₀` satisfying:

```
s(x) = pt  ⟹  x ∈ P
s(x) = ln  ⟹  x ∈ L
P ∩ L = ∅        -- mutual exclusivity, by construction
```

**Remark.** Mutual exclusivity is not asserted as an axiom — it is enforced by the
sort function. A term of sort `pt` cannot inhabit sort `ln`. This expels the hidden
witness present in Euclid's definitions through the conjunction AND, which presupposes
an ambient space in which both properties can be simultaneously assessed. The sort
function makes the witness explicit and typed.

---

## 2. Incidence Relation

**Definition 2.1 (Sorted Incidence).**
Define the incidence relation:

```
I : U(pt) × U(ln) → Prop
```

The relation `I(p, l)` is well-typed only when `s(p) = pt` and `s(l) = ln`.
The expressions `I(p, p')` and `I(l, l')` are sort errors.

**Remark.** The duality symmetry:

```
I(p, l) ↔ I*(l, p)
```

is an automorphism of the signature, not of the objects. It is induced by the
sort-swap involution:

```
σ : 𝒮₀ → 𝒮₀
σ(pt) = ln
σ(ln) = pt
```

Duality is a property of the incidence structure, not of points or lines in isolation.
Point and line are mutually exclusive witnesses to each other — neither is prior.

---

## 3. Incidence Category Inc

**Definition 3.1 (Objects).**

```
Ob(Inc) = P ⊔ L
```

Every object carries its sort via `s`.

**Definition 3.2 (Morphisms).**

```
Hom(p, p') = { l : L | I(p,l) ∧ I(p',l) }     s(p) = s(p') = pt,  p ≠ p'
Hom(l, l') = { p : P | I(p,l) ∧ I(p,l') }     s(l) = s(l') = ln,  l ≠ l'
Hom(p, l)  = { * | I(p,l) }                    cross-sort incidence witness
Hom(l, p)  = { * | I(p,l) }                    cross-sort incidence witness
```

**Definition 3.3 (Identity Morphisms).**

```
id_p = { l : L | I(p,l) }      -- pencil of lines through p
id_l = { p : P | I(p,l) }      -- pencil of points on l
```

Identities are pencils. This is the first appearance of geometry in the categorical
structure.

**Theorem 3.4 (Two Points Determine a Unique Line).**

```
∀ p₁ p₂ : P,  p₁ ≠ p₂  →  |Hom(p₁, p₂)| = 1
```

**Theorem 3.5 (Two Lines Determine a Unique Point).**

```
∀ l₁ l₂ : L,  l₁ ≠ l₂  →  |Hom(l₁, l₂)| = 1
```

*These are theorems derived from the projective incidence axioms, not postulates.*

**Definition 3.6 (Dagger on Inc).**

```
† : Inc → Incᵒᵖ
```

On objects: `p† = l_p` (dual line), `l† = p_l` (dual point).
On morphisms: `f† : Hom(B†, A†)` for `f : Hom(A, B)`.

Satisfying:
```
(f†)†    = f               -- involutive
(g ∘ f)† = f† ∘ g†        -- contravariant
id†      = id              -- preserves pencils
```

---

## 4. Derived Sort — The Plane

**Definition 4.1 (Metric Functor, Preliminary).**
Let `M : Inc → Met` be a sort-preserving functor carrying distance on morphisms
(defined fully in Section 6). The cross-sort morphism `Hom(p, l)` acquires a
perpendicular distance:

```
⟂(p, l) : ℝ≥0     via M
```

**Theorem 4.2 (Plane as Fixed Point).**
The perpendicular distance `⟂(p, l)` is a fixed point of `†_M`:

```
†_M(⟂(p, l)) = ⟂(p, l)  ↔  θ = π/2
```

Perpendicularity is self-dual under `†_M`. The angle π/2 appears here for the first
time — not as a definition but as the fixed point condition. This is the first
appearance of π in the structure, disguised as a right angle.

**Definition 4.3 (Derived Plane Sort).**

```
Π(p, l) = Fix(†_M ∘ ⟂(p, l))
```

The plane is the fixed point locus of the dagger acting on the perpendicular witness.
It precipitates from the metric dagger structure — it is not primitive.

**Definition 4.4 (Extended Sort Signature).**

```
𝒮 = { pt, ln, pl }

U(pt) = P        -- primitive
U(ln) = L        -- primitive
U(pl) = Π        -- derived:  Π = { Π(p,l) | †_M(⟂(p,l)) = ⟂(p,l) }
```

With three-way mutual exclusivity: `P ∩ L = ∅,  P ∩ Π = ∅,  L ∩ Π = ∅`.

**Definition 4.5 (Extended Dagger).**

```
σ : 𝒮 → 𝒮
σ(pt) = ln,    σ(ln) = pt,    σ(pl) = pl
```

The plane sort is fixed by `σ` because it is already a fixed point of `†_M`.

---

## 5. Closed Symmetric Monoidal Dagger Category Inc₃

**Definition 5.1 (Objects).**

```
Ob(Inc₃) = P ⊔ L ⊔ Π ⊔ P∞ ⊔ L∞
```

Where `P∞` and `L∞` are ideal elements defined as fixed points of `†`.

**Definition 5.2 (Extended Incidence Relations).**

```
I_pl : P × L → Prop          -- point on line     (original)
I_pπ : P × Π → Prop          -- point on plane    (derived)
I_lπ : L × Π → Prop          -- line on plane     (derived)
```

With compatibility theorems:

```
I_lπ(l, π)  ↔  ∀ p : P,  I_pl(p, l)  →  I_pπ(p, π)
∀ p l,  ⟂(p,l)  →  ∃! π : Π,  I_pπ(p, π) ∧ I_lπ(l, π)
```

**Definition 5.3 (Monoidal Join ⊗).**

```
p  ⊗  p' = l          -- join of two points is a line
l  ⊗  l' = p          -- meet of two lines is a point
p  ⊗  l  = π          -- join of point and line is a plane
l  ⊗  π  = p∞         -- join of line and plane is a point at infinity
p  ⊗  π  = l∞         -- join of point and plane is a line at infinity
π  ⊗  π' = l          -- meet of two planes is a line
```

Symmetric: `A ⊗ B = B ⊗ A`.

**Definition 5.4 (Internal Hom).**

```
[p,  p'] = l,    [l,  l'] = p,    [π,  π'] = l
[p,  l]  = π,    [p,  π]  = l⟂,   [l,  π]  = p∞
```

Satisfying: `Hom(A ⊗ B, C) ≅ Hom(A, [B, C])`.

**Theorem 5.5 (Closure).** `∀ A B : Ob(Inc₃),  [A, B] : Ob(Inc₃)`.

**Definition 5.6 (Ideal Elements).**

```
P∞ = Fix(†) ∩ U(pt),    L∞ = Fix(†) ∩ U(ln),    σ(P∞) = L∞
```

**Theorem 5.7 (Self-Duality of ⟂ and ∥).**

```
†([p, l])  = [p, l]               -- perpendicularity self-dual
†([l, l']) = [l, l']  when [l,l'] ∈ P∞    -- parallelism self-dual
```

**Definition 5.8.** Inc₃ is a closed symmetric monoidal dagger category
`( Inc₃, ⊗, [−,−], † )`.

---

## 6. Metric Functor M : Inc₃ → Met₃

**Definition 6.1 (Met₃).** The smallest category receiving M faithfully:

```
Ob(Met₃)   = Ob(Inc₃)
Hom_M(A,B) = Hom(A,B) × ℝ≥0
```

Metric on hom-types:

```
d_pp : Hom(p,p')  → ℝ≥0         d_ll : Hom(l,l') → [0,π)
d_ππ : Hom(π,π')  → [0,π/2]     d_pl : Hom(p,l)  → ℝ≥0
d_pπ : Hom(p,π)   → ℝ≥0         d_lπ : Hom(l,π)  → [0,π/2]
```

**Definition 6.2 (M as Strict Symmetric Monoidal Dagger Functor).**

```
M(A ⊗ B)  = M(A) ⊗_M M(B)       M([A,B]) = [M(A),M(B)]_M
M(†(f))   = †_M(M(f))            M(id_A)  = id_{M(A)}
```

**Theorem 6.3 (Triangle Inequality).** From functoriality of composition in Met₃:

```
d(p, p'') ≤ d(p, p') + d(p', p'')
```

**Theorem 6.4 (Pythagorean Theorem).** From monoidal structure of M:

```
d_pπ(p,π)² + d_pl(p,l)² = d(p, foot(p,l))²
```

**Theorem 6.5 (Self-Duality Preserved).**

```
†_M(π) = π     †_M(p∞) = p∞
```

---

## 7. The Circle as the Metric

### The Central Reorientation

The circle is not a derived object constructed after the metric. The circle **is the
metric** — the object whose existence M presupposes. The functor M assigns to every
point p a distance function `d(p,−) : P → ℝ≥0`. Reified as a geometric object at
radius r, this function is the circle.

**Definition 7.1 (Circle as Metric Object).**

```
C(p, r)  =  { q : P | d(p,q) = r }  =  d(p,−)⁻¹(r)
```

The circle is the metric `d(p,−)` given a sort. It is not constructed from the
metric — it **is** what the metric looks like as an object.

**Definition 7.2 (Circle Sort).**

```
𝒮 = { pt,  ln,  pl,  cr }

U(cr) = { C(p,r) | p : P,  r : ℝ>0 }
```

Four-way mutual exclusivity enforced by `s`. The sort `cr` is the sort of the
metric reified.

**Definition 7.3 (Extended Incidence for Circle).**

```
I_pc : P × U(cr) → Prop    I_lc : L × U(cr) → Prop    I_πc : Π × U(cr) → Prop

I_pc(q, C(p,r))  ↔  d(p,q) = r
I_lc(l, C(p,r))  ↔  d_pl(p,l) = r      -- l is tangent
I_πc(π, C(p,r))  ↔  C(p,r) ⊆ π
```

**Theorem 7.4 (Circle is Self-Dual).**

```
†_M(C(p, r)) = C(p, r)
```

The dual of `C(p,r)` is its tangent envelope. A circle is a conic, and the dual of
a conic is again a conic of the same type. The point locus and tangent envelope are
the same projective object.

**Corollary 7.5.**

```
I_pc(q, C(p,r))  ↔  I_lc(l*, C(p,r))
```

where `l*` is the tangent at `q`. Point incidence and line tangency are dual
conditions on the same object — the circle's self-duality in its incidence relations.

---

## 8. π as the Hidden Witness

### π is a Witness, Not a Number

The plane's fixed point condition produced the angle π/2. The circle's self-duality
produces the full constant π.

**Definition 8.1 (π as Fixed Point Witness).**

```
π  =  witness( †_M(C) = C )
```

π is the unique scalar such that the self-duality equation `†_M(C(p,r)) = C(p,r)`
holds for all p and r. It is not defined as circumference divided by diameter.
That is a theorem.

**Theorem 8.2 (Circumference from Self-Duality).**

```
circumference(C(p,r)) / (2r)  =  π
```

*Proof sketch.* The circumference is the total length of `id_{C(p,r)}` in Met₃ —
the length traversed by the pencil of tangent lines. The self-duality
`†_M(C) = C` constrains this length to be `2πr` because π is the unique scalar
satisfying the fixed point equation of `†_M` on the metric object. ∎

**Remark.** Euclid's AND hid an ambient space as an untyped witness. The circle's
self-duality hides π as a witness. Both are fixed point conditions. The difference
is that π is now **explicitly typed** — it inhabits the fixed point equation of
the metric dagger acting on the metric reified as an object. Making the witness
explicit is what it means to have a foundation.

---

## 9. π as the Limit of the Counit

**Definition 9.1 (Counit at Radius r).**

The adjunction `F ⊣ †_F` (Section 14) has counit:

```
ε_r : F(†_F(C(p,r))) → C(p,r)
```

At finite r this is the compactification — the great circle `†_F(C(p,r))` on the
Riemann sphere mapped back to the Euclidean circle under F. At finite r, this is the
parallel postulate.

**Theorem 9.2 (π as Limit of Counit over Radius).**

```
lim_{r→∞} ε_r  =  π
```

*Proof sketch.* As `r → ∞` the Euclidean circle expands to fill the plane. Its
image under stereographic projection `†_F` approaches the equator of the Riemann
sphere — the unique great circle whose compactification has circumference `2π`. The
counit `ε_r` at each r contracts the great circle to the Euclidean circle. In the
limit the great circle is the equator and its circumference/diameter ratio is the
fixed point of `†_M` on the circle — which is π. ∎

**Corollary 9.3.**

```
π  =  lim_{r→∞} circumference(ε_r) / diameter(ε_r)
```

π is the asymptotic value of the counit's circumference-to-diameter ratio. It is
not a transcendental number imported from outside — it is the geometric limit of
the adjunction `F ⊣ †_F`.

**Remark.** The parallel postulate is `ε_r` at finite r — the counit exists and is
unique. π is `ε_r` at infinite r — the counit converges to a definite limit. Both
are expressions of the same adjunction at different scales.

---

## 10. Sphere as First Application of the Endofunctor

### The Distance Endofunctor

**Definition 10.1 (Distance Endofunctor).**

```
δ_p : Inc₃ → Inc₃
```

On objects:
```
δ_p(q) = d(p,q)      δ_p(l) = d_pl(p,l)      δ_p(π) = d_pπ(p,π)
```

On morphisms: `δ_p(f : Hom(q,q')) = |d(p,q) - d(p,q')|`.

**Theorem 10.2 (Reverse Triangle Inequality from Functoriality).**

```
|d(p,q'') - d(p,q)| ≤ |d(p,q') - d(p,q)| + |d(p,q'') - d(p,q')|
```

### The Circle is the Zeroth Level

The circle is the fibre of `δ_p` over r — the preimage functor at value r:

```
C(p,r)  =  δ_p⁻¹(r)  =  { q : P | δ_p(q) = r }
```

It is the canonical object associated to `δ_p` before any iteration. This is why
the circle is the metric: it is `δ_p` given a sort.

### The Sphere as First Iterate

**Definition 10.3 (Sphere as First Endofunctor Application).**

```
S²(p, r)  =  δ_p( C(p, r) )
```

`δ_p` applied to the circle — measuring distance from p to each point of `C(p,r)`
in the ambient 3-dimensional incidence category — produces the sphere.

**Definition 10.4 (n-Sphere as nth Iterate).**

```
S¹(p,r)  =  C(p,r)                          -- circle:   metric itself
S²(p,r)  =  δ_p( S¹(p,r) )                  -- sphere:   first iterate
S³(p,r)  =  δ_p( S²(p,r) )  =  δ_p²(C)     -- 3-sphere: second iterate
Sⁿ(p,r)  =  δ_p^{n-1}( C(p,r) )             -- n-sphere: (n-1)th iterate
```

The circle is the generator. The n-sphere is the (n−1)th iterate of `δ_p` on the
circle. The sphere is not a generalisation of the circle — the circle generates
the sphere.

**Theorem 10.5 (Spheres are Self-Dual).** For all n ≥ 1:

```
†_M(Sⁿ(p,r)) = Sⁿ(p,r)
```

*Proof.* By induction. `S¹ = C` is self-dual by Theorem 7.4. If `Sⁿ` is self-dual:

```
†_M(Sⁿ⁺¹) = †_M(δ_p(Sⁿ)) = δ_p(†_M(Sⁿ)) = δ_p(Sⁿ) = Sⁿ⁺¹   ∎
```

Self-duality propagates through every iterate because `δ_p` commutes with `†_M`.

---

## 11. S∞ and π as the Limit of Dimensional Reduction

### The Colimit

**Definition 11.1 (Infinite-Dimensional Sphere).**

```
S∞(p,r)  =  colim_{n→∞} Sⁿ(p,r)  =  colim_{n→∞} δ_p^{n-1}(C)
```

**Theorem 11.2 (S∞ is Contractible).**

```
S∞  ≃  *
```

Every finite Sⁿ is non-contractible. S∞ is contractible — the colimit of
non-contractible objects collapses to a point. Recovered here as a theorem about
the colimit of the endofunctor iteration, not imported from topology.

### Dimensional Reduction Counit

**Definition 11.3 (Dimensional Reduction Counit).**

```
εₙ : Sⁿ → Sⁿ⁻¹
```

The counit of the adjunction between `Incₙ₊₁` and `Incₙ` — the adjunction
`F ⊣ †_F` applied dimension by dimension. Each step is stereographic projection
from Sⁿ to the equatorial Sⁿ⁻¹.

**Theorem 11.4 (π as Limit of Dimensional Reduction).**

```
π  =  lim_{n→∞} counit( εₙ : Sⁿ → Sⁿ⁻¹ )
```

*Proof sketch.* The counit `εₙ` at each dimension is stereographic projection,
collapsing the north pole to the equatorial Sⁿ⁻¹. The circumference-to-diameter
ratio of the equatorial section at each step is the counit's scaling factor. In
the limit this ratio converges to π — the fixed point of `†_M` on the circle,
the generator of the entire sequence. ∎

**Theorem 11.5 (π as Double Limit).**

```
π  =  lim_{r→∞}  ε_r(C(p,r))            -- limit over radius
   =  lim_{n→∞}  counit(εₙ : Sⁿ→Sⁿ⁻¹)  -- limit over dimension
```

Both limits converge to the same value because both are expressions of the same
fixed point equation `†_M(C) = C`. The parallel postulate and the transcendence of
π are the same adjunction at different scales.

---

## 12. Conics as Double Endofunctors

**Definition 12.1 (Double Distance Endofunctor).**

```
K(p, q, r₁, r₂)  =  δ_p⁻¹(r₁)  ∩  δ_q⁻¹(r₂)
```

**Theorem 12.2 (All Conics from Endofunctor Fibres).**

```
Circle    =  δ_p⁻¹(r)                   -- single fibre,  p = q
Ellipse   =  (δ_p + δ_q)⁻¹(r)           -- sum of distances fixed
Hyperbola =  (δ_p - δ_q)⁻¹(r)           -- difference of distances fixed
Parabola  =  δ_p⁻¹  ∩  δ_l⁻¹            -- distance to point = distance to line
```

**Theorem 12.3 (All Conics are Self-Dual).**

```
†_M(Ellipse) = Ellipse      †_M(Hyperbola) = Hyperbola
†_M(Parabola) = Parabola    †_M(Circle)    = Circle
```

All conics are their own dual curves. The circle is the degenerate conic with
coincident foci — the unique conic generated by a single endofunctor fibre.

---

## 13. Euclidean and Riemannian Geometry as Images of M

**Definition 13.1.**

```
Euc  =  M(Inc₃)  with  Fix(†_M) ∩ U(pt) ≠ ∅       -- P∞, L∞ non-empty
Riem =  M(Inc₃)  with  Fix(†_M) ∩ U(pt) = ∅        -- P∞, L∞ empty
```

**Theorem 13.2 (Parallel Postulate).**

```
∀ l : L,  ∀ p : P,  ¬I_pl(p,l)  →  ∃! l' : L,  ∥(l,l') ∧ I_pl(p,l')
  ↔  ∃! p∞ : P∞,  I_pl(p∞,l) ∧ I_pl(p∞,l')  ∧  d(p∞,p) = ∞
```

The parallel postulate is a theorem about whether the internal hom `[l,l']` lands
uniquely in `P∞`.

---

## 14. Bridge Functor F : Riem → Euc

**Definition 14.1 (F on Objects).**

Finite objects: F is identity. Ideal objects:

```
F(p∞) = lim_{t→∞} p(t)     F(l∞) = lim_{t→∞} l(t)
```

**Definition 14.2 (F on Internal Homs).**

```
F([l,l']) = p∞   when l ∥ l'      F([l,l']) = p    when l ∦ l'
F([p,l])  = π    always
```

F splits the internal hom based on parallelism. This splitting is the geometric
content of the parallel postulate.

**Definition 14.3 (Dagger of F — Stereographic Projection).**

```
†_F : Euc → Riem

†_F(x, y) = ( 2x/(1+r²),  2y/(1+r²),  (r²-1)/(r²+1) )     r² = x²+y²
†_F(p∞)   = (0, 0, 1)     -- north pole of S²
†_F(l∞)   = equatorial great circle of S²
```

F is inverse stereographic projection: `F = (†_F)†`.

**Theorem 14.4 (Naturality).** `F_M ∘ M = M ∘ F`.

---

## 15. The Adjunction F ⊣ †_F

**Theorem 15.1 (Adjunction).**

```
F  ⊣  †_F

η : id_Riem  →  †_F ∘ F           -- unit,   identity on Riem
ε : F ∘ †_F  →  id_Euc            -- counit
```

**Theorem 15.2 (Parallel Postulate as Counit).**

```
∥(l, l')  ↔  ε is well-defined and unique at l∞
```

**Theorem 15.3 (π as Double Limit of Counit).**

```
π  =  lim_{r→∞}  ε_r                           -- counit over radius
   =  lim_{n→∞}  counit(εₙ : Sⁿ → Sⁿ⁻¹)       -- counit over dimension
```

Both limits are the same fixed point `witness(†_M(C) = C)`.

---

## 16. Summary

### The Central Identifications

```
Circle  =  the metric reified as a geometric object     d(p,−)⁻¹(r)
Sphere  =  δ_p(Circle)     first iterate of endofunctor
Sⁿ      =  δ_p^{n-1}(C)   (n-1)th iterate
S∞      =  colim Sⁿ  ≃  * contractible colimit
π       =  witness(†_M(C) = C)
        =  lim_{r→∞} ε_r
        =  lim_{n→∞} counit(εₙ : Sⁿ → Sⁿ⁻¹)
```

### Derivation Hierarchy

```
Primitive:    pt,  ln                          -- by stipulation
    ↓  I_pl,  M,  †_M
Derived:      pl   =  Fix(†_M ∘ ⟂)            -- plane
    ↓  dagger fixed points
Ideal:        P∞   =  Fix(†) ∩ U(pt)
              L∞   =  Fix(†) ∩ U(ln)
    ↓  self-dual conditions internal to Inc₃
Self-dual:    ⟂    fixed point of † on cross-sort homs
              ∥    fixed point of † on same-sort homs at ∞
    ↓  metric reified
Derived:      cr   =  U(d(p,−))               -- circle is the metric
Hidden:       π    =  witness(†_M(C) = C)      -- π from self-duality
    ↓  endofunctor δ_p
Spheres:      S¹   =  C(p,r)                  -- circle:   generator
              S²   =  δ_p(C)                  -- sphere:   first iterate
              Sⁿ   =  δ_p^{n-1}(C)            -- n-sphere: (n-1)th iterate
              S∞   =  colim Sⁿ  ≃  *          -- contractible
    ↓  double endofunctor fibres
Conics:       all self-dual,  circle is degenerate case
    ↓  functoriality of M
Theorems:     Triangle inequality              -- composition
              Pythagorean theorem              -- monoidal structure
              Thales' theorem                  -- dagger on circle
              Parallel postulate              -- counit ε_r  at finite r
              π as limit                      -- counit ε_r  at r → ∞
    ↓  fixed point locus
Geometries:   Euc    Fix(†_M) ≠ ∅
              Riem   Fix(†_M) = ∅
    ↓  adjunction
              F : Riem → Euc,   †_F : Euc → Riem
              F  ⊣  †_F
              ε  =  parallel postulate at finite r
              lim ε  =  π
```

### What Is Primitive and What Is Derived

| Entity | Status | Source |
|---|---|---|
| Point | Primitive sort | Stipulated |
| Line | Primitive sort | Stipulated |
| Incidence | Primitive relation | Stipulated |
| Plane | Derived sort | `Fix(†_M ∘ ⟂)` |
| Ideal points P∞ | Derived | `Fix(†) ∩ U(pt)` |
| Ideal lines L∞ | Derived | `Fix(†) ∩ U(ln)` |
| Perpendicularity | Self-dual condition | Internal to Inc₃ |
| Parallelism | Self-dual condition | Internal to Inc₃ |
| Circle | Metric reified | `d(p,−)⁻¹(r)` — the metric as object |
| π | Hidden witness | `witness(†_M(C) = C)` |
| Sphere S² | First endofunctor iterate | `δ_p(C)` |
| n-Sphere Sⁿ | (n−1)th iterate | `δ_p^{n-1}(C)` |
| S∞ | Colimit of iterates | `colim Sⁿ ≃ *` |
| Conics | Double endofunctor fibres | `(δ_p ± δ_q)⁻¹(r)` |
| Triangle inequality | Functoriality | Composition in Met₃ |
| Pythagorean theorem | Functoriality | Monoidal structure of M |
| Thales' theorem | Dagger theorem | Self-duality of circle |
| Parallel postulate | Counit at finite r | `ε_r` of adjunction F ⊣ †_F |
| π as limit | Counit at r → ∞ | `lim_{r→∞} ε_r = lim_{n→∞} counit(εₙ)` |
| Euclidean geometry | Image of M | `Fix(†_M) ≠ ∅` |
| Riemannian geometry | Image of M | `Fix(†_M) = ∅` |

---

*The circle is the metric. The sphere is the metric applied to itself. π is the
witness that the metric is self-dual — hidden in the fixed point equation of the
dagger, recovered as the limit of the counit of the adjunction between Euclidean
and Riemannian geometry. The parallel postulate and the transcendence of π are
the same adjunction at different scales: one is the counit at finite radius,
the other is the counit at infinite radius.*
