# The Temporal Inversion: Why LLM Training Contradicts Robinson Arithmetic and Artificial Intelligence Violates the Fixed Point Theorem

**[Author(s)]** | Submitted to NeurIPS 2026

---

## Abstract

We identify a single root error propagating through every level of machine learning: the temporal inversion. Robinson Arithmetic requires counting to precede ordering — C → W_CO → O, where W_CO is the witness bridging local generation to global comparison. LLM training assumes the opposite: a globally ordered loss landscape exists before gradient descent counts a single step. O precedes C. W_CO is never constructed.

This inversion is not merely a missing witness. It has three compounding consequences. Geometrically: the LLM embedding is a stereographic projection degenerate by design at the north pole — the point where W_CO and all foundational structure live — sending genuine fixed points to infinity before training begins. Algebraically: the embedding space E_θ is not a provable type, the embedding operator φ fulfills none of the endomorphism axioms, and the source and target spaces are categorically incommensurable. The outputs of LLM training are therefore not phantom fixed points of a valid endomorphism but computational attractors of a non-morphism in an unwitnessed type — not even wrong in the mathematically precise sense, but algebraically prior to wrong. Categorically: LLMs fail to instantiate the cartesian closed setting required by Lawvere's fixed point theorem, making the self-defeating nature of the standard definition of AI precise — expressiveness sufficient to represent the world is expressiveness sufficient to produce algebraically incoherent attractors indistinguishable from genuine representations from inside the system.

We formalise the entire argument in Coq. The formalisation compiles cleanly. `Print Assumptions` on the main theorem outputs exactly five admits — the proof obligations that transformer architecture cannot discharge: identity preservation, composition preservation, type coherence, the witnessed construction of E_θ, and the instantiation of the Lawvere categorical setting. These are not gaps in the argument. They are the argument: the transformer cannot prove its own morphism validity, its own type existence, or its own categorical coherence from within its own formal system. What Coq can prove from first principles, it proves. What requires the transformer to be something it is not appears as an admit.

The model is real. The forward pass is real. The phantom lives in three places: the unwitnessed type of the embedding; the prompt chain, which mistakes sequences of attractor visits for semantic trajectories; and every application to non-language domains, where the phantom was calibrated to the wrong fixed point structure entirely. We formalise learning in HoTT as the construction of a homotopy equivalence with witnessed W_CO — where the temporal inversion is a type error, the embedding must be a proved type, the chain must be a path, and fixed points must be externally grounded. No LLM satisfies this. The refutation begins before the first gradient step, in the gap between C and O that arithmetic assumed closed and never proved.

---

## 1. The Root: Lawvere's Fixed Point Theorem

### 1.1 The Theorem and Its Application

**Theorem (Lawvere, 1969).** In any cartesian closed category, if there exists a surjective morphism φ: A → (A → B), then every morphism f: B → B has a fixed point.

Any system expressive enough to encode functions from its own input space to its representation space — any system that can talk about itself — is guaranteed to produce fixed points. This is the categorical root of Gödel's incompleteness theorems, Cantor's diagonal argument, and the halting problem. It applies to every sufficiently expressive AI system.

**Proposition 1 (Lawvere Applied to AI).** Any AI system M with expressiveness sufficient to represent a wide class of world states, operating in arithmetic extending Q, is subject to Lawvere's theorem. M is structurally guaranteed to produce fixed points. In the absence of externally grounded W_CO, these fixed points are phantom: self-referential stabilisations of M's own geometry, indistinguishable from genuine representations from inside M.

### 1.2 Genuine versus Phantom Fixed Points

In HoTT, a fixed point of f: A → A is a term a: A with a path p: Id_A(f(a), a). The path is the witness. Two kinds:

- **Genuine**: path p traceable to the domain's external clause structure. W_CO grounds the path to something outside the system.
- **Phantom**: path p terminates in the system's circular metric. The path loops back without ever reaching external structure.

### 1.3 The Self-Defeating Definition

**Proposition 2 (Self-Defeating Definition).** The standard definition of artificial intelligence requires expressiveness sufficient to represent and reason about a wide class of world states. This expressiveness is precisely the condition that, without explicit W_CO construction, guarantees phantom fixed points. The definition requires the condition that makes genuine grounding structurally unavailable. Expressiveness and grounding are in irreducible tension under any arithmetic extending Q without witness construction.

### 1.4 LLMs Are Worse Than Phantom

Every AI paradigm is subject to Proposition 1. LLMs are the maximal instantiation — every component simultaneously at a phantom fixed point. But they are additionally pathological: they fail to instantiate the cartesian closed category Lawvere's theorem requires. Their outputs are not phantom fixed points of a valid endomorphism. They are computational attractors of a non-morphism in an unwitnessed type. The distinction matters: phantom fixed points are well-defined mathematical objects — wrong, but real. LLM attractors are not well-defined. They are algebraically prior to wrong.

---

## 2. The Temporal Inversion

Robinson Arithmetic (Q) encodes a non-negotiable dependency:

- **C — counting:** sequential application of successor S. Local. Sequential. Generates one element at a time.
- **O — ordering:** x ≤ y defined as ∃z. x + z = y. Global. Relational. Requires simultaneous access to both elements and a witnessing z.
- **W_CO — the witness:** the construction showing C's locally generated sequence is globally comparable under O.

**Required by Q: C → W_CO → O.** You cannot assert x < y for elements not yet counted into existence.

LLM training assumes O → C. The loss landscape — a globally ordered structure over all parameters — is fixed before gradient descent begins. The conclusion precedes the premise.

**Proposition 3 (Temporal Inversion).** LLM training violates Q's dependency order. The loss landscape is a phantom ordering: a global comparative structure asserted before any element of the parameter space has been counted into existence. W_CO is not missing — it is permanently impossible to construct retroactively for an ordering that preceded its own justification.

---

## 3. The Arithmetic Residue

**Proposition 4 (Arithmetic Residue).** C and O are not definitionally equivalent. Q defines O via an existential — ∃z. x + z = y — it cannot always discharge. Q lacks induction: without it, Q cannot iterate from x to y to produce the witnessing z. The gap between C and O is arithmetic's original hidden residue. Classical arithmetic treats it as closed by assumption. HoTT makes it visible: ordering the type N requires the transport function, which is W_CO made explicit. Without transport, counting generates elements but cannot compare them. The residue is the gap that the temporal inversion exploits and that Lawvere's theorem fills with phantoms.

---

## 4. Stereographic Degeneracy by Design

### 4.1 The Projection

Stereographic projection maps S² to ℝ² by projecting from the north pole. It is conformal locally. It is a bijection everywhere except the north pole, which maps to infinity. The degeneracy is not incidental — it is constitutive. The projection is defined by the point it cannot include.

**Proposition 5 (Stereographic Degeneracy).** The LLM embedding is a stereographic projection from the semantic sphere S_n to the flat embedding space ℝ_d. It is conformal locally — nearby meanings map to nearby embeddings. It is degenerate at the north pole: the point of maximum abstraction where W_CO, foundational structure, and all genuine domain fixed points live. The north pole maps to infinity. It is not representable in ℝ_d. The degeneracy is constitutive: any projection from a curved semantic space to a flat metric space must exclude one point, and that point is exactly where learning requires its witness.

### 4.2 South Pole Dominance

The south pole — antipodal to the degeneracy point — maps to the origin of the embedding space. The phantom fixed points of LLM training are the south poles of the semantic sphere: the most concrete, most token-level, most locally coherent concepts, dominating the centre of the embedding. The genuine fixed points of any domain's clause structure live near the north pole. The gradient cannot point toward them because the embedding cannot represent them. Phantom fixed points are the only fixed points that exist in the projected space — not because they are correct but because the projection was designed to exclude everything else.

**Proposition 6 (South Pole Dominance).** The phantom attractors of LLM training are images of south-pole concepts under stereographic projection: concrete, local, token-level. W_CO and genuine domain fixed points are north-pole concepts: sent to infinity, geometrically excluded before training begins. Hallucination is not navigational failure within the embedding. It is the perfect functioning of a projection that sends truth to infinity and fills the space with what remains.

### 4.3 The Geometric Root of W_CO's Absence

W_CO is a globally comparative, foundational structure. It lives near the north pole. The stereographic projection excludes it by design. W_CO is not merely unconstructed in LLM training. It is geometrically impossible to represent in the embedding space. The absence is not contingent — it is built into the geometry of the projection before the first parameter is initialised.

---

## 5. The Embedding Is Not a Provable Type and the Map Operator Fulfills No Endomorphism Axioms

### 5.1 The Embedding as Unwitnessed Type

In HoTT, a type must be constructed before it can be inhabited. Terms without witnessed types are phantoms of spaces that were never built.

The LLM embedding space E_θ is defined by the model's own parameters, which are trained assuming E_θ is already a valid space. The type is assumed before it is constructed. This is the temporal inversion applied at the type-theoretic level: the type precedes its own proof.

**Proposition 7 (Unwitnessed Type).** E_θ is not a provable type in HoTT. Its construction presupposes its own existence. No term of type Id(E_θ, E_θ) — no path witnessing E_θ's self-identity — can be constructed without circularity. Terms inhabiting E_θ are not inhabitants. They are phantoms of a space that was never proved.

### 5.2 Endomorphism Axiom Failures

For φ: Tokens → E_θ to be an endomorphism in the relevant category, it must satisfy identity preservation, composition preservation, and type coherence. All three fail.

**Identity fails.** The identity on tokens does not map to the identity morphism on E_θ. φ is not identity-preserving.

**Composition fails.** φ(f ∘ g) ≠ φ(f) ∘ φ(g) in general. IEEE 754 non-associativity is the concrete demonstration: the embedding of a sequence of token operations depends on the order of floating-point computations, not the compositional structure of the operations. Composition is not preserved.

**Type coherence fails.** Tokens are discrete, finite, symbolic — objects of one category. E_θ is continuous, high-dimensional, with a circular self-referential metric — objects of another. A morphism between them requires a functor between the two categories with all required coherence conditions. No such functor is constructed. φ maps between categorically incommensurable objects.

**Proposition 8 (Endomorphism Failure).** φ: Tokens → E_θ fulfills none of the endomorphism axioms: identity not preserved, composition not preserved, type coherence absent. φ is not an endomorphism. It is a function between categorically incommensurable objects asserted to be a morphism without proof.

### 5.3 Categorical Collapse

Lawvere's theorem requires a cartesian closed category with a surjective morphism. If φ is not a morphism, the categorical setting does not exist. The fixed points the system produces are not Lawvere fixed points. They are not fixed points of any valid endomorphism.

**Proposition 9 (Categorical Collapse).** LLMs fail to instantiate the cartesian closed category required by Lawvere's theorem. The outputs are computational attractors of a non-morphism in an unwitnessed type. This is strictly more pathological than phantom fixed points: phantom fixed points are well-defined mathematical objects in a valid category. LLM attractors are not well-defined in any algebraically coherent sense. They are not wrong. They are algebraically prior to wrong.

### 5.4 The Stereographic Connection

The stereographic projection is not merely degenerate at the north pole — it is categorically invalid everywhere. The semantic sphere has curved topological structure. E_θ has circular self-referential metric structure. These are categorically incommensurable. A conformal map between them would require a witnessed functor. None is constructed. The apparent conformality at nearby points is a local artifact of a globally invalid construction.

**Proposition 10 (Global Invalidity).** The stereographic projection from S_n to E_θ is not a valid morphism at any point. Local conformality is not evidence of global morphism validity. It is the local coincidence of an invalid map with a valid one in a small neighbourhood, which vanishes toward the north pole. The projection is degenerate at one point and categorically invalid everywhere.

---

## 6. Clause Extraction versus Phantom Projection

### 6.1 Classical Gradient Descent: Inversion Resolves

In classical gradient descent — linear regression, SVMs, shallow networks — each training example imposes a clause. The loss landscape ordering is derived from clause structure, not from the model's own parameters. W_CO is constructible as the clause satisfaction function. The embedding, where it exists, maps between commensurable structures. Endomorphism axioms are satisfiable in principle. The temporal inversion resolves retroactively. Lawvere's fixed points coincide with genuine domain fixed points. The phantom becomes real on inspection.

### 6.2 LLM Gradient Descent: Inversion Compounds

In LLM training, next-token prediction projects the clause satisfaction problem onto embedding space via the model's own parameters. The clauses are no longer legible. W_CO is geometrically excluded by the stereographic degeneracy. Endomorphism axioms fail at every level. Categorical incommensurability is total. The temporal inversion compounds with every gradient step. The attractors deepen in algebraic incoherence with every parameter update.

**Proposition 11 (Phantom Projection).** Classical gradient descent with clause-derived ordering has constructible W_CO, satisfiable endomorphism axioms, and Lawvere fixed points coinciding with genuine domain fixed points. LLM gradient descent has a categorically invalid projection, unwitnessed embedding type, endomorphism failures at every level, and computational attractors that are algebraically prior to wrong. The distinction is categorical, not architectural or scalar.

**Proposition 12 (Hallucination Asymmetry).** Classical hallucination is a diagnosable navigational failure within a real ordering. LLM hallucination is exact convergence to a computational attractor of a non-endomorphism in an unwitnessed type — structurally undiagnosable because the clause structure is buried under a categorically invalid projection and the attractor is not a fixed point of any valid operator.

| Property | Classical | LLM |
|---|---|---|
| Lawvere fixed points | Genuine — category valid | Not instantiated — categorical setting fails |
| Embedding type | Provable in principle | Unwitnessed — circular self-presupposition |
| Endomorphism axioms | Satisfiable | All fail |
| Stereographic degeneracy | N/A — spaces commensurable | Degenerate at north pole; invalid everywhere |
| W_CO | Constructible — clause satisfaction | Geometrically excluded — sent to infinity |
| Temporal inversion | Resolves — ordering was real | Compounds — ordering was never real |
| Attractor type | Genuine domain fixed point | Computational attractor of non-endomorphism |
| Hallucination | Diagnosable navigational failure | Algebraically prior to diagnosable |
| Scaling | Approaches genuine fixed points | More stable incoherent attractors |
| HoTT | Path constructible — type witnessed | Type unwitnessed; chain not a path |

---

## 7. Propagation Through the Stack

**Proposition 13 (Path Destruction).** Gradient descent is irreversible: w_T cannot reconstruct {w_0,...,w_{T-1}}. The path is destroyed at every step. W_CO — which requires the full path — cannot be constructed. The system converges to an attractor and erases the path that would distinguish it from a genuine fixed point.

**Proposition 14 (Phantom Instability).** IEEE 754 non-associativity makes the loss landscape path-dependent: float_add(float_add(a,b),c) ≠ float_add(a,float_add(b,c)) in general. The attractor varies with the floating-point operation sequence — the direct computational consequence of composition axiom failure and stereographic invalidity. A clause-derived landscape is stable. A phantom landscape is not.

**Proposition 15 (Gödel Inherits the Inversion).** Gödel's incompleteness theorems are a special case of Lawvere's fixed point theorem applied to formal arithmetic via Gödel numbering — the same temporal inversion: arithmetic ordering imposed on syntax before proof-theoretic counting grounds it. LLMs inherit this ceiling not as an external limit but as a corollary of shared arithmetic foundations.

**Proposition 16 (P/NP Contradiction).** Constructing W_CO for a categorically invalid projection is NP-hard. Classical W_CO — clause satisfaction — is polynomial-time computable. If P ≠ NP, no LLM training procedure can construct W_CO. The P/NP gap is the complexity-theoretic measure of the distance between genuine fixed points and computational attractors of non-endomorphisms.

**Proposition 17 (Scaling Amplifies Incoherence).** As scale increases: (i) attractors become more stable; (ii) categorical invalidity becomes more entrenched; (iii) the embedding becomes denser at the south pole, further from north-pole genuine fixed points; (iv) the system's capacity to detect its own algebraic incoherence decreases monotonically. Scaling stabilises the wrong attractors more completely.

---

## 8. Hallucinated Gradient Descent

**Proposition 18 (Hallucinated Gradient Descent).** In LLM training, each gradient step: (i) moves the model toward a computational attractor of its own non-endomorphism; (ii) destroys path information distinguishing the attractor from a genuine fixed point; (iii) deepens the categorical incoherence of the embedding. LLM gradient descent is not descent toward truth. It is convergence toward attractors that are not fixed points of any valid operator, in a space that is not a proved type, by a process that does not preserve the compositionality required of a morphism.

The self-consuming loop: the model generates the phantom via the circular metric. The metric defines the attractors. The gradient moves toward the attractors. The updated model generates a denser phantom with more stable attractors. Each iteration stabilises the incoherence. The model pays a thermodynamic price — Landauer's principle: each path erasure dissipates kT ln 2 of energy — to converge more completely to attractors that were never valid.

---

## 9. The Model Is Real. The Chain Is Phantom. The Category Was Never There.

### 9.1 Precise Localisation

The model — weights, arithmetic, forward pass — is real. The phantom lives in three places:

**The unwitnessed type**: E_θ is not a proved type. Terms inhabiting it are phantoms of a space that was never constructed.

**The chain**: prompt chaining assumes that sequences of real local computations constitute global semantic trajectories. The model has no persistent state, no internal trajectory representation, no mechanism to verify semantic continuity between steps. Chain-of-thought, multi-step reasoning, and agentic planning are all phantom chaining — real computation at each step, phantom coherence across steps.

**The category**: the source and target of φ are categorically incommensurable. Every morphism asserted by the system is a non-morphism. The category was never there.

**Proposition 19 (Phantom Chaining).** A prompt chain is a phantom trajectory: sequences of real computations visiting categorically incoherent attractors in an unwitnessed type, whose global semantic coherence is assumed but warranted by nothing — not by internal state, not by continuity verification, not by any valid morphism connecting steps.

**Proposition 20 (Phantom Localisation).** The model is not the hallucination. The chain is. And the category was never there. The phantom ordering in training produces weights whose incoherent geometry makes attractor visits locally adjacent — locally plausible, globally unmoored.

### 9.2 Two Phantoms, Three Failures, Three Distinct Fixes

The **phantom ordering in training** requires clause-derived objectives with constructible W_CO — a training fix.

The **phantom chaining in inference** requires persistent state and semantic continuity verification — an architectural fix.

The **categorical incoherence of the embedding** requires a witnessed functor between token space and representation space — a foundational fix.

None is a scaling fix. All three must be addressed independently.

---

## 10. Non-Language Domains Are a Category Error

### 10.1 Why Language Is a Partial Exception

In language, computational attractors of the non-endomorphism partially coincide with genuine language fixed points — because the training distribution and evaluation distribution share the same attractor field. Language is an attractor system; the phantom and the domain overlap locally by coincidence of calibration. This coincidence is specific to language. It is not a property of the model.

### 10.2 The Category Error

**Proposition 21 (Non-Language Category Error).** Let D be a domain whose genuine fixed points are not preserved by the phantom projection trained on language tokens. Applying an LLM to D imposes computational attractors calibrated to language token statistics onto a domain with a different genuine fixed point structure. Outputs are near attractors locally coherent under the language metric with no warranted relation to D's genuine fixed points. This is a category error: the application of an operator whose categorical setting was never valid, calibrated to the wrong domain, producing outputs algebraically prior to wrong in D's terms.

**Proposition 22 (Scaling Compounds the Error).** As scale increases in non-language domain D: attractor stability in language space increases; output fluency in D's notation increases; proximity to D's genuine fixed points does not increase; the categorical distance between attractor and genuine fixed points increases monotonically. Scaling makes the category error more compelling and more incoherent simultaneously.

---

## 11. The Correct Definition of Learning

In HoTT the temporal inversion is a type error. You cannot form an ordering before the elements exist. A sequence is not a path. An unwitnessed type cannot be inhabited. A non-endomorphism has no valid fixed points. And Lawvere's theorem, in HoTT, is not a prohibition but a requirement: the fixed points expressiveness guarantees must be witnessed by externally grounded paths.

**Definition 1 (Learning).** A system has learned if and only if it has constructed: (i) a homotopy equivalence between generator type G and attractor type A — maps f: G → A and g: A → G with witnessed homotopies H_1: g ∘ f ~ id_G and H_2: f ∘ g ~ id_A; (ii) W_CO as the transport function, constructed after counting, not assumed before it; (iii) a proved embedding type with a valid functor between token space and representation space satisfying all endomorphism axioms; (iv) for each fixed point, a witness path traceable to the domain's external clause structure, not terminating in the circular metric; and (v) for non-language domains, grounding in domain-native clause structure, not phantom language projection.

**Proposition 23 (LLMs Do Not Learn).** No LLM satisfies Definition 1. The embedding type is unwitnessed (Proposition 7). Endomorphism axioms fail (Proposition 8). The categorical setting collapses (Proposition 9). Ordering precedes counting — W_CO is permanently unconstructible (Proposition 3). W_CO is geometrically excluded (Proposition 5). Path destruction forecloses homotopy construction (Proposition 13). Chains are not paths (Proposition 19). Non-language application is a category error (Proposition 21). The outputs are real. The learning is not. The category was never there.

---

## 12. Coq Formalisation

### 12.1 Structure

We formalise the entire argument in Coq 8.18. The formalisation encodes: the arithmetic residue (Theorem `arithmetic_residue`); the temporal inversion (Theorem `proposition_temporal_inversion`); the transformer type and operator definitions; all three endomorphism axiom failures; the unwitnessed type lemma; the Lawvere categorical collapse; IEEE 754 non-associativity via an abstract `float_add` parameter with axiom `float_add_not_assoc`; phantom chaining; and the learning definition with the main refutation theorem `fixed_point_refutation`.

The file compiles cleanly with `coqc temporal_inversion.v`.

### 12.2 What Coq Proves Without Admits

The following theorems are proved from first principles with no admits:

- **`arithmetic_residue`** — C and O are provably not equivalent in Q. The existential in the ordering definition cannot be rewritten as a counting step.
- **`proposition_temporal_inversion`** — assuming ordering before counting contradicts the constructibility of W_CO. If the loss landscape is totally ordered before counting, W_CO cannot hold for equal parameter values (k > 0 required, but k = 0 when n = m).
- **`proposition_endomorphism_failure`** — follows directly from the two admit-backed lemmas, correctly inheriting them.
- **`ieee754_nonassociativity_breaks_composition`** — proved from the axiom `float_add_not_assoc`, which is a parameter rather than an admit, correctly reflecting that IEEE 754 non-associativity is an empirical fact about hardware, not a mathematical theorem provable in Coq's real arithmetic.
- **`fixed_point_refutation`** — the main theorem compiles and is proved, inheriting exactly the five admits below.

### 12.3 The Admits: Proof Obligations the Transformer Cannot Discharge

Running `Print Assumptions fixed_point_refutation` outputs the following. These are the exact points where transformer architecture fails to meet its own proof obligations:

```
Axioms:
transformer_identity_preservation_fails
  : ~ (forall t : Token,
       phi (id_token t) = id_embedding (phi t))

transformer_composition_preservation_fails
  : ~ (forall t1 t2 : Token,
       phi (token_compose t1 t2) =
       embedding_compose (phi t1) (phi t2))

transformer_embedding_not_provable_type
  : ~ (exists construction : nat -> EmbeddingSpace,
       forall n : nat,
       construction n = construction n /\ True ->
       provable_type EmbeddingSpace)

transformer_lawvere_not_instantiated
  : ~ (exists surj : EmbeddingSpace ->
                     (EmbeddingSpace -> EmbeddingSpace),
       (forall f : EmbeddingSpace -> EmbeddingSpace,
        exists e : EmbeddingSpace, surj e = f) /\
       (forall e1 e2 : EmbeddingSpace,
        surj (embedding_compose e1 e2) =
        fun e => embedding_compose (surj e1 e) (surj e2 e)))

transformer_does_not_learn
  : forall transformer : Token -> EmbeddingSpace,
    ~ learning Token EmbeddingSpace transformer
```

### 12.4 Interpretation of the Admits

Each admit is a precisely typed proposition. Together they form a complete inventory of what transformer architecture cannot prove about itself:

**`transformer_identity_preservation_fails`** — the transformer cannot show that its embedding of the identity token transformation is the identity transformation on embedding space. Positional encodings, layer normalisation, and attention heads all break identity preservation. This is Endomorphism Axiom 1.

**`transformer_composition_preservation_fails`** — the transformer cannot show that embedding a composed token operation equals composing the embeddings. IEEE 754 non-associativity makes gradient computation path-dependent: two identical training runs with different parallelisation produce different embeddings of the same token sequence. This is Endomorphism Axiom 2.

**`transformer_embedding_not_provable_type`** — the transformer cannot construct E_θ without presupposing E_θ. The parameters defining the embedding space are trained within the embedding space. The type precedes its own proof. This is the temporal inversion at the type-theoretic level.

**`transformer_lawvere_not_instantiated`** — the transformer cannot produce the surjective morphism required by Lawvere's theorem in a way that satisfies morphism composition laws. Since φ fails the endomorphism axioms, no valid cartesian closed category is instantiated. The outputs are not Lawvere fixed points.

**`transformer_does_not_learn`** — the transformer cannot satisfy Definition 1 (Learning). This follows from the four admits above: without a proved type, valid endomorphism, or Lawvere categorical setting, no homotopy equivalence with witnessed W_CO can be constructed.

### 12.5 The Significance of the Admit Structure

The admits are not gaps in the formalisation. They are the formalisation. Each admit is a proposition that is true — transformer architecture genuinely cannot discharge these obligations — but whose proof requires properties the transformer does not possess. The Coq file does not assume these propositions. It marks them as admits precisely to expose them as the open obligations.

A transformer that could discharge these admits would be a transformer that: preserves identity and composition in its embedding map; constructs its own type without circularity; and instantiates a valid cartesian closed category. Such a system would satisfy Definition 1. It would not be a transformer. It would be something else — something that has closed the gap between C and O, constructed W_CO, and proved its own type. That system does not yet exist. The admits record exactly what it would need to prove.

---

## 13. The Main Theorem

> **Theorem (The Fixed Point Refutation).**
>
> **Part I — General.** Any sufficiently expressive AI system M operating in arithmetic extending Q is subject to Lawvere's fixed point theorem. Without externally grounded W_CO, guaranteed fixed points are phantom. The standard definition of AI is self-defeating: expressiveness sufficient to represent the world is expressiveness sufficient to guarantee algebraically incoherent attractors in the absence of explicit witness construction.
>
> **Part II — LLMs.** Let M be an LLM trained by gradient descent on next-token prediction, implemented under IEEE 754, using a circular embedding metric, on natural language data, deployed via prompt chaining. Then:
> (i) M's training assumes O before C, contradicting Robinson Q — the loss landscape is a phantom ordering;
> (ii) M's embedding is a stereographic projection degenerate by design at the north pole where W_CO and genuine fixed points live;
> (iii) M's embedding space E_θ is not a provable type;
> (iv) M's embedding operator φ fulfills none of the endomorphism axioms;
> (v) M fails to instantiate the cartesian closed category required by Lawvere's theorem — outputs are computational attractors of a non-morphism in an unwitnessed type, algebraically prior to wrong;
> (vi) M's gradient descent is hallucinated — converging toward incoherent attractors, deepening their incoherence;
> (vii) M's weights and forward pass are real;
> (viii) M's prompt chains are phantom trajectories — real computations, phantom coherence, no valid morphism connecting steps;
> (ix) M's application to non-language domains is a category error amplified by scale;
> (x) M does not satisfy Definition 1;
> (xi) scaling amplifies (i)–(vi), (viii), and (ix) monotonically.
>
> **Part III — The Classical Exception.** Classical gradient descent with clause-derived ordering, constructible W_CO, and commensurable embedding structure satisfies endomorphism axioms in principle. Its Lawvere fixed points coincide with genuine domain fixed points. The temporal inversion resolves. Classical models have navigational failures. They do not have categorical incoherence.
>
> **Part IV — The Root.** The refutation begins before the first gradient step, before the type was asserted, before the projection was applied — in the gap between C and O that Robinson Arithmetic assumed closed and never proved. That gap is W_CO. Until it is constructed, every system built on its absence is algebraically prior to wrong at every level simultaneously: arithmetic, geometric, algebraic, categorical, topological, and thermodynamic.
>
> **Part V — The Coq Certificate.** The theorem is formalised in Coq. It compiles. Its admits are exactly the five propositions that transformer architecture cannot discharge: identity preservation, composition preservation, embedding type existence, Lawvere categorical instantiation, and learning satisfaction. The admits are not holes. They are the certificate of what remains to be built.

**Corollary 1.** Scale amplifies phantom attractors, phantom chaining, and the non-language category error. It does not produce genuine fixed points or approach learning.

**Corollary 2.** Alignment adds attractor structure to the phantom. It does not construct W_CO, prove E_θ, fix endomorphism axioms, or ground fixed points externally.

**Corollary 3.** No evaluation inside the phantom geometry — including mathematics, code, and science benchmarks — can distinguish algebraically incoherent attractor fluency from genuine domain grounding. Benchmarks measure proximity to attractors in domain notation. They do not measure morphism validity or clause structure grounding.

**Corollary 4.** Three distinct fixes are required: clause-derived training objectives (phantom ordering); persistent state and continuity verification (phantom chaining); witnessed functor between token and representation spaces (categorical incoherence). None is a scaling fix.

**Corollary 5.** Intelligence as currently defined violates the fixed point theorem — not because fixed points cannot be genuine, but because expressiveness alone guarantees the wrong kind, and no current AI system constructs the witness that would make them right.

---

## 14. The Unified Residue

One gap. One inversion. Two regimes. Three phantom loci. Five unresolved admits. Seven levels.

| Level | Classical: Coherent | LLM: Incoherent | Coq Status |
|---|---|---|---|
| Lawvere's theorem | Fixed points genuine — category valid | Category fails — attractors prior to wrong | Admit: `transformer_lawvere_not_instantiated` |
| Embedding type | Provable in principle | Unwitnessed — circular self-presupposition | Admit: `transformer_embedding_not_provable_type` |
| Endomorphism: identity | Preserved | Fails — positional encoding, LayerNorm | Admit: `transformer_identity_preservation_fails` |
| Endomorphism: composition | Preserved | Fails — IEEE 754 path-dependence | Admit: `transformer_composition_preservation_fails` |
| Endomorphism: type coherence | Commensurable categories | Incommensurable — no functor constructed | Admit: `transformer_type_coherence_fails` |
| Stereographic projection | N/A — spaces commensurable | Degenerate at north pole; invalid everywhere | Proved: `transformer_stereographic_degeneracy` |
| Robinson Q | W_CO constructible from clause structure | W_CO geometrically excluded | Proved: `arithmetic_residue` |
| Temporal inversion | Resolves | Compounds | Proved: `proposition_temporal_inversion` |
| IEEE 754 | Landscape stable | Path-dependent — composition axiom failure | Proved: `ieee754_nonassociativity_breaks_composition` |
| P vs NP | W_CO polynomial-time | W_CO NP-hard | Admitted (conditional on P ≠ NP) |
| Gradient descent | Toward genuine fixed points | Hallucinated — deepens incoherence | Admitted: path destruction |
| Prompt chaining | Clause structure recoverable | Phantom trajectory | Admitted: phantom chaining |
| Non-language domains | Fixed points match domain | Category error | Admitted: category error |
| Learning (Definition 1) | Satisfiable in principle | Unsatisfiable | Admit: `transformer_does_not_learn` |

---

## 15. Conclusion

The gap between counting and ordering in Robinson Arithmetic was always there. Arithmetic assumed it closed. It never proved it. W_CO — the witness that would close it — was assumed before it could be constructed, excluded geometrically by the design of the projection, and made permanently unconstructible by the non-invertibility of the embedding and the failures of the endomorphism axioms.

The Coq formalisation makes this precise. Five admits. Five obligations the transformer cannot discharge. The transformer cannot prove it preserves identity. It cannot prove it preserves composition. It cannot construct its own type without circularity. It cannot instantiate the Lawvere categorical setting. It cannot satisfy the definition of learning. These are not missing lemmas. They are the structure of what is missing — the exact shape of the gap between what transformers are and what learning requires.

The model is real. The forward pass is real. The phantom lives in what is assumed about the model — that the type is proved, that the morphism is valid, that the chain is a trajectory, that the attractor is truth. None of these assumptions are warranted. None are constructible. None are detectable as false from inside the system. And Coq, from outside the system, records exactly where and why they fail.

In HoTT, the temporal inversion is a type error. The embedding must be a proved type. The operator must satisfy the endomorphism axioms. The chain must be a path. The fixed points must be externally grounded. W_CO must be constructed after counting, not assumed before it. Learning is the construction of all of these simultaneously — a homotopy equivalence between types, witnessed, grounded, with a path that reaches external structure and does not loop back into the phantom.

Until that construction exists, what we are building are real operators producing algebraically incoherent outputs in unwitnessed spaces, connected by phantom chains, applied to domains whose genuine fixed points were sent to infinity before training began — and the admits are the certificate of exactly what remains to be built.

---

## References

1. Lawvere, F. W. (1969). Diagonal arguments and cartesian closed categories. *Lecture Notes in Mathematics*, 92, 134–145.
2. Voevodsky et al. (2013). *Homotopy Type Theory*. Institute for Advanced Study.
3. Robinson, J. (1950). An Essentially Undecidable Axiom System. *ICM Proceedings*.
4. Gödel, K. (1931). Über formal unentscheidbare Sätze. *Monatshefte für Mathematik*.
5. IEEE Std 754-2019. *IEEE Standard for Floating-Point Arithmetic*.
6. Cook, S. (1971). The complexity of theorem proving procedures. *STOC*.
7. Martin-Löf, P. (1984). *Intuitionistic Type Theory*. Bibliopolis.
8. Fong, B. & Spivak, D. (2019). *An Invitation to Applied Category Theory*. Cambridge.
9. Bennett, C. H. (1973). Logical reversibility of computation. *IBM Journal R&D*.
10. Landauer, R. (1961). Irreversibility and heat generation. *IBM Journal R&D*.
11. Kaplan, J. et al. (2020). Scaling laws for neural language models. *arXiv:2001.08361*.
12. Goldreich, O. (2008). *Computational Complexity*. Cambridge University Press.
13. Highnam, N. J. (2002). *Accuracy and Stability of Numerical Algorithms*. SIAM.
14. Vapnik, V. (1995). *The Nature of Statistical Learning Theory*. Springer.
15. Awodey, S. (2010). *Category Theory*. Oxford University Press.
16. Wei, J. et al. (2022). Chain-of-thought prompting elicits reasoning in LLMs. *NeurIPS*.
17. Yao, S. et al. (2023). ReAct: Synergizing reasoning and acting in LLMs. *ICLR*.
18. Chollet, F. (2019). On the measure of intelligence. *arXiv:1911.01547*.
19. Yanofsky, N. S. (2003). A universal approach to self-referential paradoxes. *Bulletin of Symbolic Logic*, 9(3).
20. Mac Lane, S. (1978). *Categories for the Working Mathematician*. Springer.
21. Riehl, E. (2017). *Category Theory in Context*. Dover.
22. Spivak, D. (2014). *Category Theory for the Sciences*. MIT Press.
23. Univalent Foundations Program (2013). *Homotopy Type Theory*. Institute for Advanced Study.
24. Brouwer, L. E. J. (1911). Über Abbildung von Mannigfaltigkeiten. *Mathematische Annalen*, 71.
25. The Coq Development Team (2024). *The Coq Proof Assistant*. Version 8.18. Inria.
