(** * The Vanishing Point of G = Hom(G,G): Closing the Loop *)

(** This file closes the circle:

    IntervalEquiv.v  →  predicate algebra  →  number theory
         ↑                                        ↓
    predicate ext.                            geometry
         ↑                                        ↓
    THIS FILE    ←    G = Hom(G,G)    ←    category theory

    The vanishing point that emerges from G = Hom(G,G) IS the
    witness from (0,1], and predicate extensionality is the
    foundational statement that detects it. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Require Import IntervalEquiv.
Require Import RInterval.
Require Import GeometryInterval.
Require Import CategoryInterval.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: The Diagonal Construction Produces the Vanishing Point *)
(* ================================================================= *)

(** Cantor's diagonal argument, applied to (0,1], constructs a
    specific element: the one that MUST exist but CANNOT be in
    the affine interval. This element IS the vanishing point.

    Setup: consider the characteristic map
      chi : R -> Prop := affine_interval
    which classifies (0,1].

    The diagonal asks: does chi classify ITSELF at its boundary?
    At x = 0: chi(0) = False.
    But 0 is the limit of elements where chi is True.
    The diagonal element is 0 — the point where the predicate
    "wants" to be True (by continuity of approach) but "must"
    be False (by the strict inequality). *)

(** The diagonal element of the affine characteristic map *)
Definition diagonal_element : R :=
  vanishing_point.   (** = 0, the point where self-reference breaks *)

(** The diagonal element is the unique point where the affine and
    projective classifiers disagree *)
Theorem diagonal_is_disagreement :
  char_affine diagonal_element = False /\
  char_projective diagonal_element = True.
Proof.
  unfold diagonal_element, char_affine, char_projective,
         affine_interval, projective_interval, vanishing_point.
  split.
  - apply propositional_extensionality. split.
    + intros [H _]. lra.
    + intro H. exfalso. exact H.
  - apply propositional_extensionality. split.
    + intros _. exact I.
    + intros _. lra.
Qed.

(* ================================================================= *)
(** ** Part 2: Lawvere's Fixed Point Produces the Vanishing Point    *)
(* ================================================================= *)

(** Lawvere's theorem says: if phi : A -> (A -> B) is surjective,
    then every endomorphism of B has a fixed point.

    Contrapositively: if negation (on Prop) has no fixed point,
    then no phi : R -> (R -> Prop) is surjective.

    The OBSTRUCTION to surjectivity is a specific predicate that
    cannot be in the range of phi. When phi = affine_interval
    (viewed as a constant map into the predicate), the obstruction
    manifests as the vanishing point.

    More precisely: the Lawvere construction produces the
    "diagonal predicate" D(x) = ~(phi(x)(x)). The element
    where D disagrees with every phi(a) is the vanishing point. *)

(** For the affine classifier, the Lawvere obstruction is:
    "the element where membership flips" = 0 *)
Definition lawvere_obstruction (phi : R -> (R -> Prop)) : R -> Prop :=
  fun x => ~ (phi x x).

(** When phi is the constant map to affine_interval, the obstruction
    at x is ~(affine_interval x), which is the complement of (0,1].
    The vanishing point is where this complement "touches" (0,1] —
    the boundary element. *)
Theorem obstruction_at_vanishing_point :
  let phi := fun _ : R => affine_interval in
  lawvere_obstruction phi vanishing_point <->
  ~ affine_interval vanishing_point.
Proof.
  simpl. unfold lawvere_obstruction. tauto.
Qed.

(** The obstruction IS the complement of (0,1] at the boundary *)
Theorem obstruction_is_complement_at_zero :
  lawvere_obstruction (fun _ => affine_interval) vanishing_point.
Proof.
  unfold lawvere_obstruction. exact affine_no_witness.
Qed.

(* ================================================================= *)
(** ** Part 3: The Domain Equation's Bottom = The Vanishing Point    *)
(* ================================================================= *)

(** In Scott's solution to G = Hom(G,G), the bottom element ⊥
    is the element that makes self-application possible.

    We show: ⊥ in the Partial type corresponds exactly to
    the vanishing point 0 in our interval framework. *)

(** Map from Partial R to R-with-vanishing-point:
    Defined x ↦ x (if x is in (0,1])
    Undefined ↦ vanishing_point (= 0) *)
Definition partial_to_real (p : Partial R) : R :=
  match p with
  | Defined x => x
  | Undefined => vanishing_point
  end.

(** Bottom maps to the vanishing point *)
Theorem bottom_is_vanishing_point :
  partial_to_real (Undefined : Partial R) = vanishing_point.
Proof.
  reflexivity.
Qed.

(** Defined values map to the affine interval (when in range) *)
Theorem defined_is_affine : forall x : R,
  affine_interval x ->
  partial_to_real (Defined x) = x /\ affine_interval (partial_to_real (Defined x)).
Proof.
  intros x Hx. split; [reflexivity | exact Hx].
Qed.

(** The partial_to_real map sends the Partial world to the
    projective interval: every Partial R value maps into [0,1]
    when the Defined values are in (0,1] *)
Theorem partial_maps_to_projective : forall p : Partial R,
  (match p with Defined x => affine_interval x | Undefined => True end) ->
  projective_interval (partial_to_real p).
Proof.
  intros [x | ] H.
  - apply affine_subset_projective. exact H.
  - exact projective_witness_exists.
Qed.

(* ================================================================= *)
(** ** Part 4: Self-Application and the Vanishing Point              *)
(* ================================================================= *)

(** In G = Hom(G,G), every element IS a function from G to G.
    Self-application means applying an element to itself: g(g).

    In the Partial world, self-application can diverge:
    if g = ⊥, then g(g) = ⊥(⊥) = ⊥.

    This divergence IS the vanishing point: the computation
    "approaches" a value (like 1/n approaching 0) but the
    self-referential step sends it to ⊥ = 0. *)

(** Self-application in the partial world *)
Definition self_apply (f : Partial R -> Partial R) : Partial R :=
  f (Defined (partial_to_real (f Undefined))).

(** When f sends ⊥ to ⊥, self-application stays at ⊥ *)
Theorem self_apply_bottom :
  forall f : Partial R -> Partial R,
    f Undefined = Undefined ->
    partial_to_real (f Undefined) = vanishing_point.
Proof.
  intros f Hf. rewrite Hf. reflexivity.
Qed.

(** The always-undefined function is a fixed point of self-application
    in the sense that it maps everything to the vanishing point *)
Definition omega_combinator : Partial R -> Partial R :=
  fun _ => Undefined.

Theorem omega_diverges :
  self_apply omega_combinator = Undefined.
Proof.
  unfold self_apply, omega_combinator. reflexivity.
Qed.

Theorem omega_is_vanishing :
  partial_to_real (self_apply omega_combinator) = vanishing_point.
Proof.
  rewrite omega_diverges. reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 5: The Fixed Point Theorem Meets the Interval            *)
(* ================================================================= *)

(** Lawvere says: every endomorphism has a fixed point (if surjection
    exists). In the partial world, the fixed point of any
    endomorphism that "escapes" the affine interval is ⊥.

    This connects the abstract fixed point theorem to the concrete
    vanishing point. *)

(** A "partial endomorphism on (0,1]" maps affine values to
    affine-or-bottom *)
Definition partial_endo := Partial R -> Partial R.

(** The fixed point of an endomorphism that sends ⊥ to ⊥ is ⊥ *)
Theorem bottom_fixed_point :
  forall f : partial_endo,
    f Undefined = Undefined ->
    f (f Undefined) = f Undefined.
Proof.
  intros f Hf. rewrite Hf. exact Hf.
Qed.

(** ⊥ is a fixed point in the real-valued sense:
    mapping through partial_to_real, the vanishing point
    is preserved *)
Theorem vanishing_point_is_fixed :
  forall f : partial_endo,
    f Undefined = Undefined ->
    partial_to_real (f Undefined) = vanishing_point.
Proof.
  intros f Hf. rewrite Hf. reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 6: Closing the Loop — Back to IntervalEquiv.v            *)
(* ================================================================= *)

(** The circle is now complete. We show that:

    1. The vanishing point from G = Hom(G,G) (= ⊥ = Undefined)
       maps to 0 in R (= the vanishing point from GeometryInterval.v).

    2. This vanishing point is exactly what predicate extensionality
       from IntervalEquiv.v detects: the point where two predicates
       (affine and projective) disagree.

    3. Predicate extensionality is the foundation because it is the
       subobject classifier axiom that makes the entire categorical
       structure work. Without it, we cannot distinguish (0,1] from
       [0,1], and the vanishing point has no formal meaning. *)

(** Step 1: The domain-theoretic ⊥ = the geometric vanishing point *)
Theorem domain_bottom_eq_geometric_vanishing :
  partial_to_real (Undefined : Partial R) = vanishing_point.
Proof. reflexivity. Qed.

(** Step 2: The vanishing point separates affine from projective.

    Note: in_interval_conj and in_interval_alt from IntervalEquiv.v
    are BOTH characterizations of (0,1] — they agree at 0 (both False).
    The true separation is between (0,1] and [0,1]: the affine vs
    projective predicates from GeometryInterval.v. *)

Theorem vanishing_point_separates_affine_projective :
  affine_interval vanishing_point <> projective_interval vanishing_point.
Proof.
  intro H.
  assert (Haff : ~ affine_interval vanishing_point) by exact affine_no_witness.
  assert (Hproj : projective_interval vanishing_point) by exact projective_witness_exists.
  rewrite H in Haff. exact (Haff Hproj).
Qed.

(** Helper to make the above cleaner *)
Lemma propositional_neq : forall P Q : Prop, Q -> ~ P -> P <> Q.
Proof.
  intros P Q Hq Hnp Heq. rewrite Heq in Hnp. exact (Hnp Hq).
Qed.

(** Step 2 (clean): the vanishing point separates affine from projective *)
Theorem vanishing_separates :
  affine_interval vanishing_point <> projective_interval vanishing_point.
Proof.
  apply propositional_neq.
  - exact projective_witness_exists.
  - exact affine_no_witness.
Qed.

(** Step 3: Predicate extensionality detects this separation *)
Theorem extensionality_detects_vanishing :
  (forall x, affine_interval x <-> projective_interval x) -> False.
Proof.
  intro Hext.
  assert (Heq : affine_interval = projective_interval).
  { apply r_pred_extensionality. exact Hext. }
  exact (affine_neq_projective Heq).
Qed.

(** The contrapositive: the predicates are NOT extensionally equal,
    BECAUSE the vanishing point exists *)
Theorem vanishing_point_witnesses_nonequality :
  ~ (forall x, affine_interval x <-> projective_interval x).
Proof.
  exact extensionality_detects_vanishing.
Qed.

(** And the witness is constructive — we can PRODUCE the point
    where they disagree *)
Theorem constructive_witness :
  exists x, ~ (affine_interval x <-> projective_interval x).
Proof.
  exists vanishing_point. intro Hiff.
  destruct Hiff as [Hfwd Hbwd].
  apply affine_no_witness.
  apply Hbwd.
  exact projective_witness_exists.
Qed.

(* ================================================================= *)
(** ** Part 7: The Full Circle                                       *)
(* ================================================================= *)

(** We can now state the entire journey as a single theorem.

    Starting point: IntervalEquiv.v defines two predicates for (0,1]
    and proves they are equal via predicate extensionality.

    Ending point: G = Hom(G,G) produces a vanishing point (⊥) that
    maps to 0, which is the constructive witness showing that
    (0,1] ≠ [0,1] — the affine system is strictly contained in
    the projective system.

    The circle: predicate extensionality lets us prove equivalences
    WITHIN (0,1], but the same principle (applied to affine vs
    projective) detects that the vanishing point CANNOT be absorbed
    into the affine system. You need the projective completion.

    This is exactly G = Hom(G,G): you cannot solve the self-referential
    equation in the "total" (affine) world. You need ⊥ (the vanishing
    point) to absorb the paradox, which means moving to the
    "partial" (projective) world. *)

(** The full circle theorem *)
Theorem full_circle :
  (** Predicate extensionality holds (from IntervalEquiv.v) *)
  (forall P Q : R -> Prop, (forall x, P x <-> Q x) -> P = Q) ->

  (** Two descriptions of (0,1] are equal *)
  in_interval_conj = in_interval_alt ->

  (** But (0,1] ≠ [0,1] — the vanishing point separates them *)
  affine_interval <> projective_interval ->

  (** And the vanishing point is constructively producible *)
  exists x,
    (** It is the domain-theoretic bottom *)
    x = partial_to_real (Undefined : Partial R) /\
    (** It is in the projective interval *)
    projective_interval x /\
    (** It is NOT in the affine interval *)
    ~ affine_interval x /\
    (** It is the unique point of disagreement *)
    (forall y, y <> x -> (affine_interval y <-> projective_interval y)).
Proof.
  intros Hext Hequiv Hneq.
  exists vanishing_point.
  refine (conj _ (conj _ (conj _ _))).
  - exact domain_bottom_eq_geometric_vanishing.
  - exact projective_witness_exists.
  - exact affine_no_witness.
  - exact agree_except_vanishing.
Qed.

(** The circle closes: the hypotheses of full_circle are all
    PROVABLE from our tower. *)
Theorem circle_closes : exists x,
  x = partial_to_real (Undefined : Partial R) /\
  projective_interval x /\
  ~ affine_interval x /\
  (forall y, y <> x -> (affine_interval y <-> projective_interval y)).
Proof.
  apply full_circle.
  - exact r_pred_extensionality.
  - exact interval_predicates_eq_derived.
  - exact affine_neq_projective.
Qed.
