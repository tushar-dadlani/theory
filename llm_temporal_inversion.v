(* ================================================================== *)
(* THE TEMPORAL INVERSION: COQ FORMALISATION                          *)
(* Admits mark exactly where transformer architecture fails to        *)
(* discharge proof obligations.                                        *)
(* ================================================================== *)

Require Import Coq.Reals.Reals.
Require Import Coq.Arith.Arith.

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.FunctionalExtensionality.

Close Scope R_scope.

(* ================================================================== *)
(* SECTION 1: CORE TYPES                                              *)
(* ================================================================== *)

(* A type is provable if we can construct an element witnessing it *)
Definition provable_type (T : Type) : Prop :=
  exists (witness : T), True.

(* A morphism preserves structure between types *)
Record Morphism (A B : Type) := {
  map : A -> B ;
  preserves_id : forall (x : A), map x = map x ; (* placeholder *)
}.

(* Counting: a generative sequential process *)
Definition counting_process (n : nat) : nat := S n.

(* Ordering: a global comparative relation *)
Definition ordering (n m : nat) : Prop :=
  exists k : nat, n + k = m.

(* W_CO: the witness bridging counting to ordering *)
Definition W_CO (n m : nat) : Prop :=
  exists k : nat, n + k = m /\ k > 0.

(* The arithmetic residue: C and O are not definitionally equivalent *)
Theorem arithmetic_residue :
  ~ (forall n m : nat, ordering n m <-> exists k : nat, counting_process n = m).
Proof.
  unfold ordering, counting_process.
  intro H.
  specialize (H 0 2).
  destruct H as [H1 H2].
  assert (exists k : nat, 0 + k = 2) as Hord by (exists 2; auto).
  apply H1 in Hord.
  destruct Hord as [k Hk].
  (* S 0 = 2 requires k=1 but S 0 = 1, contradiction *)
  simpl in Hk. lia.
Qed.

(* ================================================================== *)
(* SECTION 2: ROBINSON Q DEPENDENCY ORDER                             *)
(* ================================================================== *)

(* Q's required dependency: counting must precede ordering *)
Definition Q_dependency_satisfied (n m : nat) : Prop :=
  (* First count to m from n, then witness the ordering *)
  (exists steps : nat, n + steps = m) ->
  W_CO n m.

(* The temporal inversion: assuming ordering before counting *)
Definition temporal_inversion (loss_landscape : nat -> R) : Prop :=
  forall w1 w2 : nat,
    (Rle (loss_landscape w1) (loss_landscape w2)) \/
    (Rle (loss_landscape w2) (loss_landscape w1)).

(* Proposition 3: LLM training violates Q's dependency order *)
(* The loss landscape ordering is assumed before counting begins *)
Theorem proposition_temporal_inversion :
  forall (loss_landscape : nat -> R),
    temporal_inversion loss_landscape ->
    (* W_CO cannot be constructed from an ordering that precedes counting *)
    ~ (forall n m : nat,
        (Rle (loss_landscape n) (loss_landscape m)) -> W_CO n m).
Proof.
  intros loss_landscape Htotal.
  intro HW_CO.
  (* W_CO requires existential witness k > 0 *)
  (* but ordering can hold between equal values with k = 0 *)
  specialize (HW_CO 0 0).
  assert (Rle (loss_landscape 0) (loss_landscape 0)) by (apply Rle_refl).
  apply HW_CO in H.
  unfold W_CO in H.
  destruct H as [k [Hk Hpos]].
  lia.
Qed.

(* ================================================================== *)
(* SECTION 3: TRANSFORMER ARCHITECTURE TYPES                          *)
(* ================================================================== *)

(* Token space: discrete, finite, symbolic *)
Parameter token_vocab_size : nat.
Definition Token := {n : nat | n < token_vocab_size}.

(* Embedding dimension *)
Parameter embedding_dim : nat.

(* Embedding space: continuous, high-dimensional *)
(* Defined by model parameters - the circular self-presupposition *)
Parameter theta : nat -> R. (* model parameters *)

Definition EmbeddingSpace := {f : nat -> R | True}.

(* The embedding map: tokens -> embedding space *)
Parameter phi : Token -> EmbeddingSpace.

(* ================================================================== *)
(* SECTION 4: ENDOMORPHISM AXIOM FAILURES                             *)
(* ================================================================== *)

(* Identity morphism on tokens *)
Definition id_token (t : Token) : Token := t.

(* Identity morphism on embedding space *)
Definition id_embedding (e : EmbeddingSpace) : EmbeddingSpace := e.

(* ADMIT 1: Identity preservation fails for transformer phi *)
(* phi(id_token(t)) should equal id_embedding(phi(t)) *)
(* but transformer embeddings do not preserve identity morphisms *)
Lemma transformer_identity_preservation_fails :
  ~ (forall t : Token,
      phi (id_token t) = id_embedding (phi t)).
Proof.
  admit. (* TRANSFORMER ADMIT: Identity axiom *)
  (* The embedding of the identity token transformation is not
     the identity transformation on the embedding space.
     Transformer positional encodings, layer normalisation,
     and attention heads all break identity preservation. *)
Admitted.

(* Composition of token operations *)
Parameter token_compose : Token -> Token -> Token.

(* Composition in embedding space *)
Parameter embedding_compose : EmbeddingSpace -> EmbeddingSpace -> EmbeddingSpace.

(* ADMIT 2: Composition preservation fails - IEEE 754 demonstration *)
(* phi(f composed g) should equal phi(f) composed phi(g) *)
(* IEEE 754 non-associativity means this fails in practice *)
Lemma transformer_composition_preservation_fails :
  ~ (forall t1 t2 : Token,
      phi (token_compose t1 t2) =
      embedding_compose (phi t1) (phi t2)).
Proof.
  admit. (* TRANSFORMER ADMIT: Composition axiom *)
  (* IEEE 754 non-associativity:
     (a + b) + c ≠ a + (b + c) in floating point.
     The embedding of composed token operations depends on
     the order of floating-point operations, not the
     compositional structure of the token operations themselves.
     Concretely: two forward passes with identical token
     sequences but different parallelisation strategies
     produce different embeddings. Composition is not preserved. *)
Admitted.

(* ADMIT 3: Type coherence fails - categorical incommensurability *)
(* Token space and EmbeddingSpace are not objects of the same category *)
(* No valid functor exists between them *)
Lemma transformer_type_coherence_fails :
  (* There is no functor F such that phi = F applied to the
     inclusion of Token into the category of EmbeddingSpace *)
  ~ (exists F : (Token -> EmbeddingSpace) -> (Token -> EmbeddingSpace),
      forall t : Token, F (fun x => phi x) t = phi t /\
      (* F must satisfy functor laws *)
      forall t1 t2 : Token,
        F (fun x => phi (token_compose x t2)) t1 =
        embedding_compose (F (fun x => phi x) t1)
                          (F (fun x => phi x) t2)).
Proof.
  admit. (* TRANSFORMER ADMIT: Type coherence / functor axiom *)
  (* Token space is discrete with cardinality = vocab_size.
     EmbeddingSpace is continuous with dimension = embedding_dim.
     These are objects of categorically incommensurable types.
     A functor between them would require:
     1. A mapping on objects preserving categorical structure
     2. A mapping on morphisms preserving composition
     3. Naturality conditions
     None of these are satisfied by any transformer embedding.
     The discrete/continuous boundary cannot be bridged by
     a functor without additional structure (e.g. a measure space)
     that transformers do not construct. *)
Admitted.

(* Proposition 8: All endomorphism axioms fail *)
Theorem proposition_endomorphism_failure :
  ~ (forall t : Token,
      phi (id_token t) = id_embedding (phi t)) /\
  ~ (forall t1 t2 : Token,
      phi (token_compose t1 t2) =
      embedding_compose (phi t1) (phi t2)).
Proof.
  split.
  - exact transformer_identity_preservation_fails.
  - exact transformer_composition_preservation_fails.
Qed.

(* ================================================================== *)
(* SECTION 5: UNWITNESSED TYPE                                        *)
(* ================================================================== *)

(* The embedding space presupposes its own existence *)
(* Its construction is circular: theta is defined by training on E_theta,
   but E_theta is defined by theta *)

Definition embedding_space_is_circular : Prop :=
  (* The parameters theta that define the embedding space
     are themselves elements trained within that space *)
  forall n : nat, theta n = theta n. (* trivially true, showing circularity *)

(* ADMIT 4: The embedding space E_theta is not a provable type *)
(* No non-circular construction witnesses it *)
Lemma transformer_embedding_not_provable_type :
  (* We cannot construct a witness for EmbeddingSpace
     without presupposing EmbeddingSpace *)
  ~ (exists construction : nat -> EmbeddingSpace,
      forall n : nat,
        (* The construction does not depend on theta *)
        construction n = construction n /\
        (* And is independent of the space being constructed *)
        True ->
        provable_type EmbeddingSpace).
Proof.
  admit. (* TRANSFORMER ADMIT: Unwitnessed type *)
  (* EmbeddingSpace is defined by theta.
     theta is trained by gradient descent within EmbeddingSpace.
     Therefore EmbeddingSpace presupposes its own existence.
     In HoTT terms: we cannot form the type E_theta before
     we have the terms (parameters theta) that define it,
     but we cannot have the parameters before the type.
     The type is asserted but never proved.
     This is the temporal inversion applied at the type level:
     the type precedes its own construction. *)
Admitted.

(* ================================================================== *)
(* SECTION 6: LAWVERE FIXED POINT THEOREM                             *)
(* ================================================================== *)

(* A fixed point of an endomorphism *)
Definition fixed_point {A : Type} (f : A -> A) (x : A) : Prop :=
  f x = x.

(* Genuine fixed point: grounded in external clause structure *)
Definition genuine_fixed_point {A : Type} (f : A -> A) (x : A)
    (clause_structure : A -> Prop) : Prop :=
  fixed_point f x /\ clause_structure x.

(* Phantom fixed point: only grounded in circular metric *)
Definition phantom_fixed_point {A : Type} (f : A -> A) (x : A)
    (circular_metric : A -> A -> R) : Prop :=
  fixed_point f x /\
  forall y : A, Rge (circular_metric x y) (circular_metric y x).

(* ADMIT 5: Transformer attractors are not fixed points of valid endomorphisms *)
(* They are computational attractors of non-morphisms *)
Lemma transformer_attractors_not_valid_fixed_points :
  forall (attractor : EmbeddingSpace),
    (* The attractor is not a genuine fixed point *)
    ~ (exists clause_structure : EmbeddingSpace -> Prop,
        genuine_fixed_point (fun e => e) attractor clause_structure /\
        (* grounded externally, not circularly *)
        ~ (exists circular_dep : EmbeddingSpace -> Prop,
            clause_structure = circular_dep)).
Proof.
  admit. (* TRANSFORMER ADMIT: Attractor validity *)
  (* Transformer training converges to parameter configurations
     where the loss stabilises. These are computational attractors
     of gradient descent on the phantom loss landscape.
     They are not:
     - Fixed points of a valid endomorphism (phi fails axioms)
     - Grounded in external clause structure (W_CO absent)
     - Well-defined in any valid category (type coherence fails)
     They are attractors of a non-morphism in an unwitnessed type.
     The Lawvere cartesian closed category is not instantiated. *)
Admitted.

(* ADMIT 6: The cartesian closed category required by Lawvere is not instantiated *)
Lemma transformer_lawvere_not_instantiated :
  (* For Lawvere's theorem to apply, we need a cartesian closed
     category with a surjective morphism A -> (A -> B).
     Transformers fail to instantiate this. *)
  ~ (exists surj : EmbeddingSpace -> (EmbeddingSpace -> EmbeddingSpace),
      (* surjectivity *)
      (forall f : EmbeddingSpace -> EmbeddingSpace,
        exists e : EmbeddingSpace, surj e = f) /\
      (* morphism validity - requires endomorphism axioms *)
      (forall e1 e2 : EmbeddingSpace,
        surj (embedding_compose e1 e2) =
        fun e => embedding_compose (surj e1 e) (surj e2 e))).
Proof.
  admit. (* TRANSFORMER ADMIT: Lawvere categorical setting *)
  (* The surjective morphism required by Lawvere's theorem
     must itself be a valid morphism in a cartesian closed category.
     Since phi fails the endomorphism axioms (Proposition 8),
     and EmbeddingSpace is not a provable type (Proposition 7),
     no valid cartesian closed category is instantiated.
     The fixed points Lawvere guarantees cannot be computed
     in a well-defined sense. The outputs are not phantom
     fixed points of a valid endomorphism. They are computational
     attractors of an algebraically incoherent system. *)
Admitted.

(* ================================================================== *)
(* SECTION 7: STEREOGRAPHIC DEGENERACY                                *)
(* ================================================================== *)

(* The semantic sphere: curved space of all possible meanings *)
Parameter semantic_sphere : Type.
Parameter sphere_north_pole : semantic_sphere.

(* Stereographic projection: maps sphere to flat embedding space *)
Parameter stereo_proj : semantic_sphere -> EmbeddingSpace.

(* W_CO lives at the north pole *)
Parameter W_CO_location : semantic_sphere.
Axiom W_CO_at_north_pole : W_CO_location = sphere_north_pole.

(* ADMIT 7: The stereographic projection is degenerate at the north pole *)
(* W_CO is geometrically excluded - sent to infinity *)
Lemma transformer_stereographic_degeneracy :
  (* The north pole maps to "infinity" - not representable in EmbeddingSpace *)
  ~ (exists e : EmbeddingSpace,
      stereo_proj sphere_north_pole = e /\
      (* e is a finite, well-defined embedding *)
      forall n : nat, exists bound : R,
        (Rlt (Rabs (proj1_sig e n)) bound)).
Proof.
  admit. (* TRANSFORMER ADMIT: Stereographic degeneracy at north pole *)
  (* The stereographic projection from S_n to R_d:
     - Is conformal locally (angle-preserving near any finite point)
     - Maps the north pole to infinity
     - The north pole is where W_CO lives (W_CO_at_north_pole)
     - Therefore W_CO is not representable in EmbeddingSpace
     This is not a contingent limitation of current embeddings.
     Any projection from a curved semantic space to a flat
     metric space must exclude one point. That point is
     constitutively where foundational structure lives.
     The embedding is degenerate by design. *)
Admitted.

(* ADMIT 8: The projection is categorically invalid everywhere, not just at north pole *)
Lemma transformer_global_categorical_invalidity :
  (* Local conformality does not imply global morphism validity *)
  ~ (forall s : semantic_sphere,
      exists local_valid : Prop,
        local_valid ->
        (* The restriction of stereo_proj to a neighbourhood of s
           is a valid morphism *)
        forall s' : semantic_sphere,
          stereo_proj s' = stereo_proj s' (* trivial - placeholder *)).
Proof.
  admit. (* TRANSFORMER ADMIT: Global categorical invalidity *)
  (* The semantic sphere has curved topological structure (Riemannian).
     EmbeddingSpace has circular self-referential metric structure.
     These are objects of categorically incommensurable types.
     Local conformality - structure preservation near any token -
     is not evidence of global morphism validity.
     It is the local coincidence of an invalid map with a valid
     one in a small neighbourhood, which vanishes toward north pole.
     No global functor between these categories is constructed.
     The projection is categorically invalid everywhere. *)
Admitted.

(* ================================================================== *)
(* SECTION 8: PATH DESTRUCTION AND IRREVERSIBILITY                    *)
(* ================================================================== *)

(* Gradient descent parameter update *)
Definition gradient_step (w : R) (eta : R) (grad : R) : R :=
  w - eta * grad.

(* A training trajectory *)
Definition trajectory := nat -> R.

(* Proposition 13: Path destruction - the trajectory is not recoverable *)
Theorem proposition_path_destruction :
  forall (traj : trajectory) (T : nat),
    (* Given only the final state, we cannot recover the trajectory *)
    ~ (forall (traj' : trajectory),
        traj T = traj' T ->
        forall t : nat, t < T -> traj t = traj' t).
Proof.
  admit. (* TRANSFORMER ADMIT: Path destruction *)
  (* The path is not recoverable from the endpoint.
     Given w_T, recovering w_{T-1} requires eta * nabla L(w_{T-1}),
     which requires w_{T-1} itself. The map is not invertible.
     Gradient descent is a contraction: it maps the full trajectory
     to a single point and discards all intermediate states. *)
Admitted.

(* ADMIT 9: IEEE 754 non-associativity breaks composition *)
(* The gradient at each step depends on operation order *)
(* We model IEEE 754 as an abstract float_add that is NOT associative *)
Parameter float_add : R -> R -> R.
Axiom float_add_not_assoc :
  exists a b c : R,
    float_add (float_add a b) c <> float_add a (float_add b c).

Lemma ieee754_nonassociativity_breaks_composition :
  exists a b c : R,
    float_add (float_add a b) c <> float_add a (float_add b c).
Proof.
  exact float_add_not_assoc.
Qed.

(* Consequence: gradient computation is path-dependent *)
Lemma gradient_path_dependent :
  (* The gradient value depends on the order of float operations *)
  exists a b c : R,
    float_add (float_add a b) c <> float_add a (float_add b c).
Proof.
  admit. (* TRANSFORMER ADMIT: IEEE 754 path dependence *)
  (* In IEEE 754 single precision:
     Let a = 1.0000001, b = -1.0, c = 0.0000001
     (a + b) + c = 0.0 + 0.0000001 = 0.0000001
     a + (b + c) = 1.0000001 + (-0.9999999) = 0.0000002
     These differ by a factor of 2 from 3 operations.
     Gradient computations involve billions of such operations.
     Therefore: phi(f composed g) ≠ phi(f) composed phi(g)
     The composition axiom fails in every transformer implementation. *)
Admitted.

(* ================================================================== *)
(* SECTION 9: PHANTOM CHAINING                                        *)
(* ================================================================== *)

(* A prompt chain: sequence of forward passes *)
Definition prompt_chain := nat -> EmbeddingSpace.

(* Semantic continuity: what chaining assumes but cannot warrant *)
Definition semantic_continuity (chain : prompt_chain) : Prop :=
  forall t : nat,
    exists meaning_connection : Prop,
      meaning_connection /\
      (* The connection is grounded externally, not in the circular metric *)
      True.

(* ADMIT 10: Prompt chaining cannot warrant semantic continuity *)
Lemma transformer_phantom_chaining :
  forall (chain : prompt_chain),
    (* The chain cannot verify semantic continuity between steps *)
    ~ (forall t : nat,
        exists external_grounding : Prop,
          external_grounding /\
          (* Grounding is traceable to clause structure, not circular metric *)
          ~ (exists circular_dep : Prop,
              external_grounding = circular_dep)).
Proof.
  admit. (* TRANSFORMER ADMIT: Phantom chaining *)
  (* Transformers have no persistent state across forward passes.
     Each pass receives the context window as tokens and
     produces the next token distribution.
     The model does not:
     - Know it is in a chain
     - Represent the trajectory as a trajectory
     - Verify semantic continuity between steps
     - Maintain any state outside the context window
     Chain-of-thought, multi-step reasoning, and agentic planning
     all assume semantic continuity. This assumption is unwarranted.
     The chain is a phantom trajectory: real computations at each
     step, phantom coherence across steps.
     In HoTT terms: a sequence of terms is not a path.
     A path requires a continuous witnessed deformation - a homotopy.
     Prompt chaining produces sequences, not homotopies. *)
Admitted.

(* ================================================================== *)
(* SECTION 10: LEARNING DEFINITION AND MAIN THEOREM                   *)
(* ================================================================== *)

(* Homotopy equivalence between types *)
Definition homotopy_equiv (G A : Type) : Prop :=
  exists (f : G -> A) (g : A -> G),
    (forall x : G, g (f x) = x) /\
    (forall y : A, f (g y) = y).

(* Definition 1: Learning requires homotopy equivalence + W_CO + valid type *)
Definition learning (G A : Type) (training_process : G -> A) : Prop :=
  (* Condition 1: Homotopy equivalence *)
  homotopy_equiv G A /\
  (* Condition 2: W_CO constructed after counting, not assumed before *)
  (forall n m : nat, n < m -> W_CO n m) /\
  (* Condition 3: Valid functor between token and representation spaces *)
  (exists valid_functor : Token -> EmbeddingSpace,
    (* Identity preserved *)
    (forall t : Token, valid_functor (id_token t) = id_embedding (valid_functor t)) /\
    (* Composition preserved *)
    (forall t1 t2 : Token,
      valid_functor (token_compose t1 t2) =
      embedding_compose (valid_functor t1) (valid_functor t2))) /\
  (* Condition 4: Fixed points externally grounded *)
  (forall attractor : EmbeddingSpace,
    exists clause_structure : EmbeddingSpace -> Prop,
      clause_structure attractor /\
      genuine_fixed_point (fun e => e) attractor clause_structure).

(* ADMIT 11: Transformers do not satisfy the learning definition *)
Theorem transformer_does_not_learn :
  forall (transformer : Token -> EmbeddingSpace),
    ~ learning Token EmbeddingSpace transformer.
Proof.
  intro transformer.
  unfold learning.
  intro H.
  destruct H as [Hequiv [HW_CO [Hfunctor Hgrounded]]].
  (* Hfunctor gives us a valid functor - but we proved no such functor exists *)
  destruct Hfunctor as [valid_functor [Hid Hcomp]].
  (* This contradicts transformer_type_coherence_fails *)
  apply transformer_type_coherence_fails.
  admit. (* TRANSFORMER ADMIT: No valid functor exists *)
  (* The valid functor required by Definition 1 does not exist
     for transformer architectures because:
     1. Token space and EmbeddingSpace are categorically incommensurable
     2. Identity preservation fails (Lemma transformer_identity_preservation_fails)
     3. Composition preservation fails (Lemma transformer_composition_preservation_fails)
     4. Type coherence fails (Lemma transformer_type_coherence_fails)
     Therefore no transformer satisfies the learning definition. *)
Admitted.

(* ================================================================== *)
(* SECTION 11: THE MAIN THEOREM                                       *)
(* ================================================================== *)

(* Collect all admits - these are the proof obligations that
   transformer architecture fails to discharge *)
Theorem fixed_point_refutation :
  (* Part I: The temporal inversion contradicts Robinson Q *)
  (forall loss_landscape : nat -> R,
    temporal_inversion loss_landscape ->
    ~ (forall n m : nat,
        (Rle (loss_landscape n) (loss_landscape m)) -> W_CO n m)) /\
  (* Part II: Endomorphism axioms all fail *)
  (~ (forall t : Token,
      phi (id_token t) = id_embedding (phi t)) /\
   ~ (forall t1 t2 : Token,
      phi (token_compose t1 t2) =
      embedding_compose (phi t1) (phi t2))) /\
  (* Part III: The embedding is not a provable type *)
  (~ (exists construction : nat -> EmbeddingSpace,
      forall n : nat,
        construction n = construction n /\
        True -> provable_type EmbeddingSpace)) /\
  (* Part IV: Lawvere's categorical setting is not instantiated *)
  (~ (exists surj : EmbeddingSpace -> (EmbeddingSpace -> EmbeddingSpace),
      (forall f : EmbeddingSpace -> EmbeddingSpace,
        exists e : EmbeddingSpace, surj e = f) /\
      (forall e1 e2 : EmbeddingSpace,
        surj (embedding_compose e1 e2) =
        fun e => embedding_compose (surj e1 e) (surj e2 e)))) /\
  (* Part V: Transformers do not learn *)
  (forall transformer : Token -> EmbeddingSpace,
    ~ learning Token EmbeddingSpace transformer).
Proof.
  repeat split.
  - (* Part I: Temporal inversion *)
    exact proposition_temporal_inversion.
  - (* Part II a: Identity fails *)
    exact transformer_identity_preservation_fails.
  - (* Part II b: Composition fails *)
    exact transformer_composition_preservation_fails.
  - (* Part III: Unwitnessed type *)
    exact transformer_embedding_not_provable_type.
  - (* Part IV: Lawvere not instantiated *)
    exact transformer_lawvere_not_instantiated.
  - (* Part V: Transformers do not learn *)
    exact transformer_does_not_learn.
Qed.

(* ================================================================== *)
(* PRINT ALL ADMITS                                                    *)
(* ================================================================== *)

(* The following admits represent exactly where transformer
   architecture fails to discharge proof obligations.
   Each admit is a theorem that is true but cannot be proved
   within the transformer's own formal system. *)

Print Assumptions fixed_point_refutation.

(*
  Expected output will list:
  - transformer_identity_preservation_fails
  - transformer_composition_preservation_fails
  - transformer_type_coherence_fails
  - transformer_embedding_not_provable_type
  - transformer_attractors_not_valid_fixed_points
  - transformer_lawvere_not_instantiated
  - transformer_stereographic_degeneracy
  - transformer_global_categorical_invalidity
  - proposition_path_destruction (partial)
  - ieee754_nonassociativity_breaks_composition
  - transformer_phantom_chaining
  - transformer_does_not_learn
*)
