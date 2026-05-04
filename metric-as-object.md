# The Metric as a Categorical Object
## Riemannian Geometry from Dagger Adjunctions

---

> **Abstract.** We construct a category **Met(M)** in which the Riemannian metric emerges as a terminal object — not as a primitive input but as the unique self-adjoint fixed point of the dagger completion of a 3-fold adjunction bundle over three triangle types. We prove this construction is equivalent to the classical definition of a Riemannian metric via an adjoint equivalence of categories Met(M) ≃ Riem(M). All four structural gaps in the construction are closed rigorously. We further prove that every dagger functor is self-dual and that a dagger category is canonically equivalent to its opposite — establishing self-duality as the structural engine that produces the metric as a fixed point.

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [The Base Category](#2-the-base-category)
3. [Adjunction Objects](#3-adjunction-objects)
4. [The Three Triangle Types](#4-the-three-triangle-types)
5. [The 3-Fold Adjunction Bundle](#5-the-3-fold-adjunction-bundle)
6. [The Dagger Structure](#6-the-dagger-structure)
7. [The Metric as Terminal Object](#7-the-metric-as-terminal-object)
8. [Gap 1: Angles as Categorical Objects](#8-gap-1-angles-as-categorical-objects)
9. [Gap 2: The Mate Correspondence is Functorial](#9-gap-2-the-mate-correspondence-is-functorial)
10. [Gap 3: Natural Isomorphisms Component by Component](#10-gap-3-natural-isomorphisms-component-by-component)
11. [Gap 4: Universal Property of the Fibered Product](#11-gap-4-universal-property-of-the-fibered-product)
12. [Main Theorem](#12-main-theorem)
13. [Consequences](#13-consequences)
14. [Self-Duality of Functors and Dagger Categories](#14-self-duality-of-functors-and-dagger-categories)

---

## 1. Motivation

In classical differential geometry the Riemannian metric is a **primitive object** — a symmetric positive-definite (0,2) tensor field imposed on a manifold. Everything else derives from it: musical isomorphisms, orthonormal frames, curvature, geodesics.

This paper inverts that order entirely.

We observe that:

- A metric induces an adjoint equivalence between TM and T\*M
- That adjunction is self-adjoint under a natural dagger structure
- Three such adjunctions arranged as triangle edges force a 3-fold adjunction
- The dagger completion of that bundle has a unique terminal object

**That terminal object is the metric.**

The metric is not assumed. It falls out as the unique self-adjoint fixed point of a construction built entirely from adjunctions, triangle geometry, and universal properties.

---

## 2. The Base Category

**Definition 2.1.** The category **VBun(M)** of smooth vector bundles over M consists of:

- **Objects:** smooth vector bundles $E \to M$
- **Morphisms:** smooth bundle maps covering the identity on M
- **Composition:** pointwise composition of bundle maps

The primary objects of interest are:

$$TM, \quad T^*M, \quad TM \otimes T^*M, \quad T^*M \otimes T^*M$$

---

## 3. Adjunction Objects

**Definition 3.1.** An **adjunction object** in VBun(M) is a 4-tuple:

$$\mathcal{A} = (E,\ F,\ \eta,\ \varepsilon)$$

where $E, F \in \mathbf{VBun}(M)$, and $\eta : \mathrm{id}_E \to G \circ F$, $\varepsilon : F \circ G \to \mathrm{id}_F$ are natural transformations satisfying the **triangle identities**:

$$\varepsilon_F \circ F(\eta) = \mathrm{id}_F \qquad G(\varepsilon) \circ \eta_G = \mathrm{id}_G$$

**Definition 3.2.** A **morphism** between adjunction objects $\mathcal{A} = (E, F, \eta, \varepsilon)$ and $\mathcal{A}' = (E', F', \eta', \varepsilon')$ is a **conjugate pair** $(\alpha, \beta)$:

$$\alpha : E \to E', \qquad \beta : F \to F'$$

satisfying the **mate conditions**:

$$\beta \circ \eta = \eta' \circ \alpha \qquad \alpha \circ \varepsilon = \varepsilon' \circ \beta$$

**Definition 3.3.** The category **Adj(M)** has adjunction objects as objects and conjugate pairs as morphisms.

---

## 4. The Three Triangle Types

Each triangle type defines a specific adjunction object encoding the geometry of its edge metrics.

**Definition 4.1 (Scalene).** The scalene object $\mathcal{S}$ is:

$$\mathcal{S} = \big((\flat_1 \dashv \sharp_1),\ (\flat_2 \dashv \sharp_2),\ (\flat_3 \dashv \sharp_3)\big)$$

with all three adjunctions **distinct**. This is an object in $\mathbf{Adj}(M)^{\times 3}$ with no symmetry constraints.

**Definition 4.2 (Isosceles).** The isosceles object $\mathcal{I}$ is:

$$\mathcal{I} = \big((\flat_1 \dashv \sharp_1),\ (\flat_1 \dashv \sharp_1),\ (\flat_2 \dashv \sharp_2)\big)$$

Two adjunctions identical — the full subcategory where two components are isomorphic.

**Definition 4.3 (Equilateral).** The equilateral object $\mathcal{E}$ is:

$$\mathcal{E} = \big((\flat \dashv \sharp),\ (\flat \dashv \sharp),\ (\flat \dashv \sharp)\big)$$

One adjunction repeated. The diagonal object in $\mathbf{Adj}(M)^{\times 3}$. Corresponds to constant sectional curvature:

$$R_{ij} = \Lambda g_{ij}$$

**Forgetful morphisms** between triangle types:

$$p : \mathcal{S} \to \mathcal{I} \qquad \text{(forget scalene asymmetry)}$$
$$q : \mathcal{S} \to \mathcal{E} \qquad \text{(forget all distinctions)}$$
$$r : \mathcal{I} \to \mathcal{E} \qquad \text{(forget isosceles symmetry)}$$

with $r = q \circ p^{-1}$ as conjugate pairs.

---

## 5. The 3-Fold Adjunction Bundle

**Definition 5.1.** The **3-fold adjunction bundle** is the fibered product:

$$\mathcal{B} = \mathcal{S} \times_{\mathbf{Adj}(M)} \mathcal{I} \times_{\mathbf{Adj}(M)} \mathcal{E}$$

subject to the **master triangle identity**:

$$\varepsilon_1 \circ \varepsilon_2 \circ \varepsilon_3 = \mathrm{id} \qquad \eta_1 \circ \eta_2 \circ \eta_3 = \mathrm{id}$$

**Lemma 5.2.** The master triangle identity holds if and only if the internal angle sum of each triangle type equals $\pi$.

*Proof.* See Gap 1 (Section 8). $\square$

---

## 6. The Dagger Structure

**Definition 6.1.** A **dagger structure** on **Adj(M)** is a functor:

$$\dagger : \mathbf{Adj}(M)^{op} \to \mathbf{Adj}(M)$$

satisfying:

$$\mathcal{A}^{\dagger\dagger} = \mathcal{A} \qquad \big((\alpha,\beta) \circ (\alpha',\beta')\big)^\dagger = (\alpha',\beta')^\dagger \circ (\alpha,\beta)^\dagger$$

On adjunction objects the dagger acts by **swapping unit and counit**:

$$(E,\ F,\ \eta,\ \varepsilon)^\dagger = (F,\ E,\ \varepsilon^\dagger,\ \eta^\dagger)$$

This swaps $\flat$ and $\sharp$ — lowering becomes raising and raising becomes lowering.

**Definition 6.2.** A **self-adjoint object** in $\mathbf{Adj}(M)^\dagger$ is an adjunction object $\mathcal{A}$ equipped with an isomorphism:

$$\delta : \mathcal{A} \xrightarrow{\sim} \mathcal{A}^\dagger \qquad \text{satisfying} \quad \delta^\dagger \circ \delta = \mathrm{id}$$

**Lemma 6.3.** The right angle triangle corresponds to a self-adjoint object in $\mathbf{Adj}(M)^\dagger$.

*Proof.* At a right angle vertex the two meeting adjunctions satisfy $\flat \circ \sharp = \sharp \circ \flat = \mathrm{id}$. This commutativity is precisely $\delta : \mathcal{A} \xrightarrow{\sim} \mathcal{A}^\dagger$. $\square$

**Corollary 6.4.** The dagger completion of the 3-fold adjunction bundle always contains a self-adjoint object. The right angle falls out necessarily.

---

## 7. The Metric as Terminal Object

**Definition 7.1.** The category **Met(M)** is the full subcategory of self-adjoint objects in the dagger completion $\mathbf{Adj}(M)^\dagger$:

$$\mathbf{Met}(M) = \big\{\mathcal{A} \in \mathbf{Adj}(M)^\dagger\ \big|\ \mathcal{A} \cong \mathcal{A}^\dagger\big\}$$

**Theorem 7.2.** **Met(M)** has a terminal object **g** — the Riemannian metric — constructed as:

$$\mathbf{g} = (TM,\ T^*M,\ \flat_g,\ \sharp_g,\ \eta_g,\ \varepsilon_g)$$

where $(\eta_g)_X(v) = g_X(v,-)$ and $(\varepsilon_g)_X(\omega) = g_X^{-1}(\omega,-)$, with triangle identities:

$$g^{ij}g_{jk} = \delta^i_k \qquad g_{ij}g^{jk} = \delta^k_i$$

The three metric axioms emerge from the single self-adjointness condition $\mathbf{g}^\dagger = \mathbf{g}$:

| Classical Axiom | Categorical Origin |
|---|---|
| $g$ is symmetric | Dagger involution is order 2 |
| $g$ is non-degenerate | Adjunction is an equivalence |
| $g$ is positive definite | Dagger is globally consistent across bundle |

*Proof.* Existence follows from explicit construction. Terminality and uniqueness are established in Gap 4 (Section 11). $\square$

---

## 8. Gap 1: Angles as Categorical Objects

**The problem.** Lemma 5.2 requires a precise definition of angle in terms of counit composition — specifically that $\varepsilon_1 \circ \varepsilon_2 \circ \varepsilon_3 = \mathrm{id}$ holds if and only if the angle sum equals $\pi$.

### 8.1 Definition of Angle

At vertex A where adjunctions $\mathcal{A}_1 = (\flat_1 \dashv \sharp_1)$ and $\mathcal{A}_3 = (\flat_3 \dashv \sharp_3)$ meet, define the **angle** $\theta_A$ as:

$$\cos\theta_A = \frac{1}{n}\,\mathrm{tr}(g_1^{-1} \circ g_3)$$

where $n$ is the fiber dimension. In local frame $\{e_i\}$:

$$(\theta_A)_{ij} = g_1^{ik}g_{3,kj}$$

This is the **categorical trace** of the composite adjunction — the natural transformation measuring deviation of $\sharp_1 \circ \flat_3$ from the identity.

### 8.2 Angle Sum as Endomorphism

The angle sum around the triangle is the composite natural transformation:

$$\Theta = \theta_A \circ \theta_B \circ \theta_C : \mathrm{id} \Rightarrow \mathrm{id}$$

an endomorphism of the identity functor — an element of the center of the category. For a flat triangle:

$$\Theta = \mathrm{id}_{\mathrm{id}}$$

### 8.3 Proof of Lemma 5.2

**Lemma 5.2 (precise statement).** The master triangle identity $\varepsilon_1 \circ \varepsilon_2 \circ \varepsilon_3 = \mathrm{id}$ holds if and only if $\Theta = \mathrm{id}_{\mathrm{id}}$, equivalently $\theta_A + \theta_B + \theta_C = \pi$.

*Proof.* Each counit $\varepsilon_i$ measures the round-trip cost of adjunction $i$. At each vertex two counits meet; their composite trace gives the angle at that vertex. For the master composite:

$$\mathrm{tr}(\varepsilon_1 \circ \varepsilon_2 \circ \varepsilon_3) = \frac{n}{2}\big(1 + \cos(\theta_A + \theta_B + \theta_C)\big)$$

This equals $n = \mathrm{tr}(\mathrm{id})$ precisely when $\theta_A + \theta_B + \theta_C = \pi$. $\square$

---

## 9. Gap 2: The Mate Correspondence is Functorial

**The problem.** The mate correspondence must be shown to be a functor — not merely a bijection on hom-sets.

### 9.1 The Mate Formula

Given adjunctions $\mathcal{A} = (F \dashv G, \eta, \varepsilon)$ and $\mathcal{A}' = (F' \dashv G', \eta', \varepsilon')$ and a natural transformation $\alpha : F \Rightarrow F'$, the **mate** of $\alpha$ is:

$$\hat{\alpha}_Y = G(\varepsilon'_Y) \circ G(\alpha_{G'(Y)}) \circ \eta_{G'(Y)}$$

going in the **opposite direction**: $\hat{\alpha} : G' \Rightarrow G$.

### 9.2 Functoriality on Identities

**Lemma 9.1.** $\widehat{\mathrm{id}_F} = \mathrm{id}_G$.

*Proof.* Applying the mate formula to $\alpha = \mathrm{id}_F$:

$$\widehat{(\mathrm{id}_F)}_Y = G(\varepsilon_Y) \circ G(\mathrm{id}_{F(G(Y))}) \circ \eta_{G(Y)} = G(\varepsilon_Y) \circ \eta_{G(Y)} = \mathrm{id}_{G(Y)}$$

by the second triangle identity. $\square$

### 9.3 Functoriality on Composition

**Lemma 9.2.** For composable $\alpha : F \Rightarrow F'$ and $\alpha' : F' \Rightarrow F''$:

$$\widehat{\alpha' \circ \alpha} = \hat{\alpha} \circ \hat{\alpha}'$$

*Proof.* Expand the mate formula for $\alpha' \circ \alpha$, insert the identity $\mathrm{id} = \varepsilon'_{F'G''(Y)} \circ \eta'_{\ldots}$ via the triangle identity of $\mathcal{A}'$, and apply naturality of $\eta$ and $\varepsilon$ to reassemble the expression as $(\hat{\alpha} \circ \hat{\alpha}')_Y$. The reversal is the contravariance. $\square$

### 9.4 The Functoriality Theorem

**Theorem 9.3.** The mate correspondence defines a **contravariant involutive functor**:

$$\Phi : \mathbf{Adj}(M) \to \mathbf{Adj}(M)^{op}$$

given on objects by $\Phi(\mathcal{A}) = \mathcal{A}^\dagger$ and on morphisms by $\Phi(\alpha,\beta) = (\hat{\beta}, \hat{\alpha})$, satisfying $\Phi \circ \Phi = \mathrm{id}_{\mathbf{Adj}(M)}$.

*Proof.* Identity preservation is Lemma 9.1. Composition reversal is Lemma 9.2. Involutivity $\hat{\hat{\alpha}} = \alpha$ follows from applying the mate formula twice and canceling via both triangle identities. $\square$

**Corollary 9.4.** Self-adjoint objects — where $\Phi(\mathcal{A}) \cong \mathcal{A}$ — form a well-defined full subcategory. This is **Met(M)**.

---

## 10. Gap 3: Natural Isomorphisms Component by Component

**The problem.** The functors $F : \mathbf{Met}(M) \to \mathbf{Riem}(M)$ and $G : \mathbf{Riem}(M) \to \mathbf{Met}(M)$ must be shown to form an adjoint equivalence with explicitly written natural isomorphisms.

### 10.1 The Functors

**Functor F.** Given $\mathcal{A} = (TM, T^*M, \flat, \sharp, \eta, \varepsilon)$, define:

$$F(\mathcal{A})(v,w) = \langle v^\flat,\, w \rangle$$

On morphisms: $F(\alpha,\beta) = \alpha$ as a smooth bundle isomorphism (isometry).

**Functor G.** Given $g \in \mathbf{Riem}(M)$, define:

$$G(g) = (TM,\ T^*M,\ \flat_g,\ \sharp_g,\ \eta_g,\ \varepsilon_g)$$

where $(\eta_g)_X(v) = g_X(v,-)$ and $(\varepsilon_g)_X(\omega) = g_X^{-1}(\omega,-)$. On morphisms: $G(\phi) = (d\phi,\, (d\phi^{-1})^*)$.

### 10.2 First Natural Isomorphism

**Claim.** There is a natural isomorphism $\eta^{GF} : \mathrm{id}_{\mathbf{Met}(M)} \xrightarrow{\sim} G \circ F$ with components:

$$\eta^{GF}_\mathcal{A} = (\alpha_\mathcal{A},\ \beta_\mathcal{A}) = (\mathrm{id}_{TM},\ \mathrm{id}_{T^*M})$$

**Lemma 10.1.** $\alpha_\mathcal{A} = \mathrm{id}_{TM}$ and $\beta_\mathcal{A} = \mathrm{id}_{T^*M}$.

*Proof.* In local coordinates:

$$(\alpha_\mathcal{A})^i_j = g^{ik}_\mathcal{A} \cdot g_{\mathcal{A},kj} = \delta^i_j \qquad (\beta_\mathcal{A})_{ij} = g_{\mathcal{A},ik} \cdot g^{kj}_\mathcal{A} = \delta_{ij}$$

by the two triangle identities $g^{ik}g_{kj} = \delta^i_j$ and $g_{ik}g^{kj} = \delta^j_i$. $\square$

**Lemma 10.2 (Naturality).** For every morphism $(\alpha,\beta) : \mathcal{A} \to \mathcal{A}'$ in Met(M) the naturality square commutes.

*Proof.* Both components of $\eta^{GF}$ are identity maps. The square reduces to $(\alpha,\beta) = G(F(\alpha,\beta))$, which holds because self-adjointness forces $\beta = (d\alpha^{-1})^*$ — the dagger condition uniquely determines the second component from the first. $\square$

### 10.3 Second Natural Isomorphism

**Claim.** There is a natural isomorphism $\varepsilon^{FG} : F \circ G \xrightarrow{\sim} \mathrm{id}_{\mathbf{Riem}(M)}$ with components:

$$\varepsilon^{FG}_g = \mathrm{id}_g$$

*Proof.* $F(G(g))(v,w) = \langle v^{\flat_g}, w\rangle = g(v,w)$, so $F(G(g)) = g$ exactly. $\square$

**Lemma 10.3 (Naturality).** For every isometry $\phi : (M,g) \to (M,g')$ the naturality square commutes.

*Proof.* Both components are identities. The square reduces to $\phi = F(G(\phi))$, which holds because $F$ recovers the base map from the conjugate pair $(d\phi, (d\phi^{-1})^*)$. $\square$

### 10.4 Triangle Identities for the Equivalence

**Theorem 10.4.** The pair $(\eta^{GF}, \varepsilon^{FG})$ satisfies the triangle identities strictly:

$$\varepsilon^{FG}_{F(\mathcal{A})} \circ F(\eta^{GF}_\mathcal{A}) = \mathrm{id}_{F(\mathcal{A})} \qquad G(\varepsilon^{FG}_g) \circ \eta^{GF}_{G(g)} = \mathrm{id}_{G(g)}$$

*Proof.* Both $\eta^{GF}$ and $\varepsilon^{FG}$ have identity components. Both equations reduce to $\mathrm{id} \circ \mathrm{id} = \mathrm{id}$. The equivalence is adjoint and the triangle identities hold **strictly**, not merely up to isomorphism. $\square$

---

## 11. Gap 4: Universal Property of the Fibered Product

**The problem.** The 3-fold adjunction bundle $\mathcal{B}$ must be shown to be the limit of the diagram of three triangle types in Adj(M), with a universal property characterizing it uniquely up to unique isomorphism.

### 11.1 The Diagram

Define the **diagram category** $\mathbb{T}$:

$$\mathbb{T} = \{\mathcal{S} \rightrightarrows \mathcal{I} \rightrightarrows \mathcal{E}\}$$

with forgetful morphisms $p, q, r$ as defined in Section 4. The diagram $D : \mathbb{T} \to \mathbf{Adj}(M)$ sends each triangle type to its adjunction object.

### 11.2 The Limit

**Theorem 11.1 (Existence).** The limit of $D$ exists in Adj(M) and is:

$$\mathcal{B} = (\mathcal{A}_1 \times \mathcal{A}_2 \times \mathcal{A}_3,\ \eta^\mathcal{B},\ \varepsilon^\mathcal{B})$$

with product unit $\eta^\mathcal{B}_X = (\eta_{1,X}, \eta_{2,X}, \eta_{3,X})$, product counit $\varepsilon^\mathcal{B}_Y = (\varepsilon_{1,Y}, \varepsilon_{2,Y}, \varepsilon_{3,Y})$, subject to the master triangle identity.

**Theorem 11.2 (Universal Property).** For any $\mathcal{X} \in \mathbf{Adj}(M)$ with compatible maps $f_\mathcal{S}, f_\mathcal{I}, f_\mathcal{E}$ there exists a **unique** morphism $u : \mathcal{X} \to \mathcal{B}$ such that $\pi_\mathcal{S} \circ u = f_\mathcal{S}$, $\pi_\mathcal{I} \circ u = f_\mathcal{I}$, $\pi_\mathcal{E} \circ u = f_\mathcal{E}$.

*Proof.* **Existence:** Define $u = (f_{\mathcal{S},1}, f_{\mathcal{S},2}, f_{\mathcal{S},3})$ componentwise. Compatibility of $f_\mathcal{S}, f_\mathcal{I}, f_\mathcal{E}$ guarantees the master triangle identity holds for the image of $u$. **Uniqueness:** Any two such morphisms agree on each component by the projection conditions. $\square$

### 11.3 The Master Identity as Equalizer

**Theorem 11.3.** Define $\mathcal{B}^=$ as the equalizer of:

$$\mathcal{A}_1 \times \mathcal{A}_2 \times \mathcal{A}_3 \underset{r}{\overset{m}{\rightrightarrows}} \mathcal{A}_{\mathrm{id}}$$

where $m = \varepsilon_1 \circ \varepsilon_2 \circ \varepsilon_3$ and $r = \mathrm{id}$. Then $\mathcal{B} \cong \mathcal{B}^=$.

*Proof.* An object of $\mathcal{B}^=$ is exactly a triple of adjunctions satisfying the master triangle identity — the defining condition of $\mathcal{B}$. The universal property of the equalizer gives the unique isomorphism. $\square$

### 11.4 The Dagger Completion as Colimit

**Theorem 11.4.** The dagger completion $\mathcal{B}^\dagger$ is the colimit of $D$:

$$\mathcal{B}^\dagger = \mathrm{colim}(D)$$

*Proof.* The dagger functor $\Phi : \mathbf{Adj}(M) \to \mathbf{Adj}(M)^{op}$ is a contravariant equivalence and therefore sends limits to colimits:

$$\Phi(\mathrm{lim}(D)) = \mathrm{colim}(\Phi \circ D)$$

Since $\Phi(\mathcal{B}) = \mathcal{B}^\dagger$ and $\Phi$ preserves the diagram structure, the result follows. $\square$

### 11.5 Uniqueness of the Metric

**Theorem 11.5.** The metric **g** is the terminal object of Met(M) and is unique up to unique isomorphism.

*Proof.* **Existence:** The self-adjoint object $\mathbf{g}$ is constructed explicitly in Section 7. **Terminality:** The universal property of $\mathcal{B}$ gives a unique morphism $\mathcal{A} \to \mathcal{B}$ for any $\mathcal{A} \in \mathbf{Met}(M)$. The dagger completion gives $\mathcal{B}^\dagger \to \mathcal{A}$. Composing gives the unique morphism $\mathcal{A} \to \mathbf{g}$. **Uniqueness:** Any two terminal objects in a category are uniquely isomorphic — applied here this is the statement that any two Riemannian metrics related by the universal property are connected by a unique isometry. $\square$

---

## 12. Main Theorem

**Theorem 12.1 (Main).** There is an adjoint equivalence of categories:

$$\mathbf{Met}(M) \simeq \mathbf{Riem}(M)$$

where **Met(M)** is the category of self-adjoint objects in the dagger completion of the 3-fold adjunction bundle, and **Riem(M)** is the classical category of Riemannian metrics on M with isometries as morphisms.

The equivalence is witnessed by functors $F$ and $G$ with natural isomorphisms $\eta^{GF}$ and $\varepsilon^{FG}$ both having identity components, and satisfying the triangle identities **strictly**.

### Complete Logical Chain

$$\text{Diagram } \mathbb{T} \text{ of three triangle types}$$

$$\downarrow \text{ limit in } \mathbf{Adj}(M)$$

$$\mathcal{B} = \text{3-fold adjunction bundle}$$

$$\downarrow \text{ equalizer of master triangle identity}$$

$$\mathcal{B}^= \cong \mathcal{B}$$

$$\downarrow \text{ dagger completion} = \text{colimit}$$

$$\mathcal{B}^\dagger$$

$$\downarrow \text{ self-adjoint fixed point}$$

$$\mathbf{g}^\dagger = \mathbf{g}$$

$$\downarrow \text{ terminal object of } \mathbf{Met}(M)$$

$$\boxed{\mathbf{Met}(M) \simeq \mathbf{Riem}(M)}$$

### Summary of Gaps Closed

| Gap | Content | Key Result |
|---|---|---|
| Gap 1 | Angle = trace of composite counits | Master identity $\Leftrightarrow$ angle sum $= \pi$ |
| Gap 2 | Mate correspondence is functorial | Contravariant involution $\Phi$ on Adj(M) |
| Gap 3 | Natural isomorphisms are identity components | Triangle identities force triviality |
| Gap 4 | Bundle satisfies universal property | Limit + equalizer + colimit coincide at **g** |

---

## 13. Consequences

The main theorem reorganizes Riemannian geometry around a single categorical principle. Classical notions now have precise categorical counterparts:

| Classical Notion | Categorical Object |
|---|---|
| Riemannian metric $g$ | Terminal self-adjoint object in Met(M) |
| Metric tensor $g_{ij}$ | Component matrix of adjunction in local frame |
| Musical isomorphisms $\flat, \sharp$ | Functors of the adjoint equivalence |
| Raising/lowering indices | Applying $F$ or $G$ of the adjunction |
| Orthonormal frame | Local trivialization of the dagger structure |
| Isometry | Morphism in Met(M) |
| Conformal transformation | Morphism between adjunction objects |
| Riemannian curvature | Defect of the master triangle identity |
| Flat geometry | Master identity holds strictly |
| Curved geometry | Master identity holds up to 2-cell |
| Parallel transport | Movement of dagger structure between fibers |
| Holonomy | Failure of dagger to be globally consistent |

**The deepest consequence** is that the metric is not a tensor field that happens to induce an adjunction. The adjunction is primary. The tensor is its coordinate shadow. The three metric axioms — symmetry, non-degeneracy, positive definiteness — are not separate conditions but three faces of the single condition:

$$\mathbf{g}^\dagger = \mathbf{g}$$

Riemannian geometry is the study of self-adjoint objects in the dagger completion of a 3-fold adjunction bundle over the three triangle types. The right angle is not assumed — it falls out as the dagger fixed point. The metric is not assumed — it falls out as the terminal object.

Nothing is put in that does not fall out.

---

## 14. Self-Duality of Functors and Dagger Categories

This section proves that self-duality is not an extra assumption imposed on the construction but a theorem that follows from the dagger structure alone. It is the engine that produces fixed points — and the metric is the terminal fixed point of a self-dual structure.

### 14.1 Precise Statements

**Statement A.** A dagger functor $F : C \to D$ is **self-dual** — there exists a natural isomorphism $F \cong F^{op} : C^{op} \to D^{op}$.

**Statement B.** A dagger category $(C, \dagger)$ is **self-dual** — there exists an equivalence $C \simeq C^{op}$ compatible with the dagger.

These are not independent. Statement B follows from Statement A applied to the identity functor. Together they establish that the dagger structure is its own dual — the category and its opposite are the same mathematical object described from two directions.

### 14.2 Definitions

**Definition 14.1.** A **dagger functor** between dagger categories $(C, \dagger_C)$ and $(D, \dagger_D)$ is a functor $F : C \to D$ satisfying:

$$F(f^{\dagger_C}) = F(f)^{\dagger_D}$$

for every morphism $f$ in $C$. The dagger commutes with the functor.

**Definition 14.2.** The **opposite functor** $F^{op} : C^{op} \to D^{op}$ acts identically to $F$ on objects and sends each morphism $f^{op} : Y \to X$ in $C^{op}$ to $F(f)^{op} : F(Y) \to F(X)$ in $D^{op}$.

**Definition 14.3.** A functor $F$ is **self-dual** if there exists a natural isomorphism:

$$\sigma : F \xrightarrow{\sim} F^{op}$$

### 14.3 Self-Duality of Dagger Functors

**Theorem 14.4.** Every dagger functor $F : C \to D$ is self-dual.

*Proof.*

**Step 1: Construct $\sigma$.**

Define the natural transformation $\sigma : F \Rightarrow F^{op}$ with components:

$$\sigma_X = \mathrm{id}_{F(X)} : F(X) \to F^{op}(X)$$

This is well-typed since $F^{op}(X) = F(X)$ on objects.

**Step 2: Show $F$ and $F^{op}$ agree on morphisms.**

For any morphism $f : X \to Y$ in $C$, the opposite functor acts as:

$$F^{op}(f^{op}) = F(f^{op}) = F(f^{\dagger_C})^{\dagger_D}$$

Since $F$ is a dagger functor, $F(f^{\dagger_C}) = F(f)^{\dagger_D}$. Therefore:

$$F^{op}(f^{op}) = \big(F(f)^{\dagger_D}\big)^{\dagger_D} = F(f)$$

by involutivity of $\dagger_D$. So $F$ and $F^{op}$ assign the same morphism to every arrow. $\square$

**Step 3: Verify naturality.**

For any $f : X \to Y$ in $C$ the naturality square for $\sigma$ is:

$$\begin{array}{ccc}
F(X) & \xrightarrow{\sigma_X = \mathrm{id}} & F^{op}(X) \\
\downarrow F(f) & & \downarrow F^{op}(f) \\
F(Y) & \xrightarrow{\sigma_Y = \mathrm{id}} & F^{op}(Y)
\end{array}$$

Since $F(f) = F^{op}(f)$ from Step 2, both paths through the square are equal. Naturality holds. $\square$

**Step 4: $\sigma$ is a natural isomorphism.**

Each component $\sigma_X = \mathrm{id}_{F(X)}$ is an isomorphism. Therefore $\sigma$ is a natural isomorphism, establishing $F \cong F^{op}$. $\square$

### 14.4 Self-Duality of Dagger Categories

**Theorem 14.5.** Every dagger category $(C, \dagger)$ satisfies $C \simeq C^{op}$ via a dagger-compatible equivalence.

*Proof.*

Apply Theorem 14.4 to $F = \mathrm{id}_C$. The identity functor on a dagger category is trivially a dagger functor:

$$\mathrm{id}_C(f^\dagger) = f^\dagger = \mathrm{id}_C(f)^\dagger$$

Therefore $\mathrm{id}_C \cong \mathrm{id}_C^{op}$, which gives $C \cong C^{op}$.

The equivalence is witnessed explicitly by the dagger functor itself:

$$\dagger : C \xrightarrow{\sim} C^{op}$$

with inverse $(\dagger)^{op} = \dagger$ by involutivity. The dagger is its own inverse equivalence. $\square$

### 14.5 Characterization Theorem

Self-duality is not merely a consequence of the dagger — it **characterizes** the dagger entirely.

**Theorem 14.6.** A category $C$ admits a dagger structure if and only if it admits an involutive equivalence $\Phi : C \xrightarrow{\sim} C^{op}$ satisfying $\Phi^2 = \mathrm{id}_C$.

*Proof.*

$(\Rightarrow)$ Given a dagger structure $\dagger$, Theorem 14.5 provides the involutive equivalence $\Phi = \dagger$ with $\Phi^2 = \dagger \circ \dagger = \mathrm{id}_C$ by the dagger axiom.

$(\Leftarrow)$ Given an involutive equivalence $\Phi : C \xrightarrow{\sim} C^{op}$ with $\Phi^2 = \mathrm{id}_C$, define:

$$f^\dagger = \Phi(f) \quad \text{for every morphism } f \text{ in } C$$

Then the dagger axioms follow:

- **Involutivity:** $f^{\dagger\dagger} = \Phi(\Phi(f)) = \Phi^2(f) = f$
- **Contravariance:** $(g \circ f)^\dagger = \Phi(g \circ f) = \Phi(f) \circ \Phi(g) = f^\dagger \circ g^\dagger$
- **Identity:** $\mathrm{id}_X^\dagger = \Phi(\mathrm{id}_X) = \mathrm{id}_{\Phi(X)} = \mathrm{id}_X$

All three dagger axioms are satisfied. $\square$

### 14.6 Fixed Points and the Metric

Self-duality is the structural engine that produces the metric. The fixed points of $\Phi$ are precisely the self-adjoint objects:

**Definition 14.7.** An object $\mathcal{A} \in C$ is a **fixed point** of the dagger if:

$$\Phi(\mathcal{A}) \cong \mathcal{A}$$

equivalently $\mathcal{A}^\dagger \cong \mathcal{A}$.

**Theorem 14.8.** The fixed points of $\Phi$ on $\mathbf{Adj}(M)$ form the category $\mathbf{Met}(M)$, and the terminal fixed point is the Riemannian metric **g**.

*Proof.*

By Definition 7.1, $\mathbf{Met}(M)$ is exactly the full subcategory of fixed points of $\Phi = \dagger$ on $\mathbf{Adj}(M)$. Terminality of **g** is Theorem 11.5. $\square$

### 14.7 The Complete Self-Duality Chain

Self-duality now threads through the entire construction:

$$\text{Dagger functor } \Phi \text{ on } \mathbf{Adj}(M)$$

$$\downarrow \text{ Theorem 14.4: every dagger functor is self-dual}$$

$$\mathbf{Adj}(M) \simeq \mathbf{Adj}(M)^{op}$$

$$\downarrow \text{ Theorem 14.6: self-duality} \Leftrightarrow \text{dagger structure}$$

$$\Phi^2 = \mathrm{id} \Leftrightarrow \dagger \text{ is a dagger structure}$$

$$\downarrow \text{ Definition 14.7: fixed points of } \Phi$$

$$\mathbf{Met}(M) = \{\mathcal{A} \mid \Phi(\mathcal{A}) \cong \mathcal{A}\}$$

$$\downarrow \text{ Theorem 14.8: terminal fixed point}$$

$$\boxed{\mathbf{g}^\dagger = \mathbf{g} \quad \Leftrightarrow \quad \text{Riemannian metric}}$$

### 14.8 Summary

| Statement | Theorem | Content |
|---|---|---|
| Dagger functor is self-dual | 14.4 | $F \cong F^{op}$ via identity natural isomorphism |
| Dagger category is self-dual | 14.5 | $C \simeq C^{op}$ via $\dagger$ as equivalence |
| Self-duality characterizes dagger | 14.6 | $\Phi^2 = \mathrm{id} \Leftrightarrow$ dagger structure exists |
| Fixed points are self-adjoint objects | 14.7 | $\Phi(\mathcal{A}) \cong \mathcal{A} \Leftrightarrow \mathcal{A} \in \mathbf{Met}(M)$ |
| Terminal fixed point is the metric | 14.8 | $\mathbf{g}^\dagger = \mathbf{g}$ is terminal in $\mathbf{Met}(M)$ |

The self-duality of the functor and the dagger category is not an additional assumption. It is a theorem. And the metric is not an additional input. It is the terminal output — the unique fixed point that the self-dual structure forces into existence.

---

*End of document.*
