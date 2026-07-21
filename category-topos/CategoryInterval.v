(** * Category Theory: The Tower as a Category, Toward G = Hom(G,G) *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Require Import IntervalEquiv.
Require Import RInterval.
Require Import GeometryInterval.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: Category — Objects, Morphisms, Composition            *)
(* ================================================================= *)

(** A category consists of:
    - Objects
    - Morphisms between objects (Hom sets)
    - Identity morphisms
    - Composition that is associative with identity *)

Record Category := mkCategory {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  id : forall A, Hom A A;
  compose : forall {A B C}, Hom B C -> Hom A B -> Hom A C;
  compose_assoc : forall A B C D
    (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose h (compose g f) = compose (compose h g) f;
  compose_id_l : forall A B (f : Hom A B),
    compose (id B) f = f;
  compose_id_r : forall A B (f : Hom A B),
    compose f (id A) = f
}.

(* ================================================================= *)
(** ** Part 2: The Subobject Classifier — Predicates as Truth Values *)
(* ================================================================= *)

(** In a topos, the subobject classifier Ω maps each element to a
    truth value. In our setting, Ω = Prop, and a predicate P : X -> Prop
    classifies the subobject {x | P x}.

    Predicate extensionality (which we derived!) is exactly the
    statement that the subobject classifier is well-behaved:
    two classifying maps that agree pointwise are equal. *)

Definition Omega := Prop.

(** The subobject classifier has two global elements: true and false *)
Definition omega_true : Omega := True.
Definition omega_false : Omega := False.

(** A "characteristic map" classifies a subobject *)
Definition char_map (X : Type) := X -> Omega.

(** Predicate extensionality IS the subobject classifier axiom:
    equal extensions → equal classifying maps *)
Theorem subobject_classifier_ext :
  forall (X : Type) (P Q : char_map X),
    (forall x, P x <-> Q x) -> P = Q.
Proof.
  intros X P Q Hext.
  apply functional_extensionality. intro x.
  apply propositional_extensionality.
  exact (Hext x).
Qed.

(** The (0,1] predicate as a classifying map *)
Definition char_affine : char_map R := affine_interval.
Definition char_projective : char_map R := projective_interval.

(** The classifying maps differ at exactly one point *)
Theorem classifier_gap :
  char_affine <> char_projective /\
  (forall x, x <> 0 -> (char_affine x <-> char_projective x)).
Proof.
  split.
  - exact affine_neq_projective.
  - exact agree_except_vanishing.
Qed.

(* ================================================================= *)
(** ** Part 3: Exponential Objects — Hom as Internal Object          *)
(* ================================================================= *)

(** In a cartesian closed category (and hence in a topos), for any
    two objects A and B, the exponential B^A (= Hom(A,B)) is itself
    an object in the category.

    In Set/Type, B^A = A -> B (the function space). *)

Definition Exp (A B : Type) : Type := A -> B.

(** The evaluation map: given (f, a) where f : A -> B, produce f(a) *)
Definition eval {A B : Type} : Exp A B * A -> B :=
  fun p => (fst p) (snd p).

(** Currying: the adjunction Hom(A × B, C) ≅ Hom(A, C^B) *)
Definition curry {A B C : Type} (f : A * B -> C) : A -> Exp B C :=
  fun a b => f (a, b).

Definition uncurry {A B C : Type} (f : A -> Exp B C) : A * B -> C :=
  fun p => f (fst p) (snd p).

(** The adjunction isomorphism *)
Theorem curry_uncurry : forall (A B C : Type) (f : A -> Exp B C),
  curry (uncurry f) = f.
Proof.
  intros. apply functional_extensionality. intro a.
  apply functional_extensionality. intro b.
  reflexivity.
Qed.

Theorem uncurry_curry : forall (A B C : Type) (f : A * B -> C),
  uncurry (curry f) = f.
Proof.
  intros. apply functional_extensionality. intros [a b].
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 4: Toward G = Hom(G, G) — The Reflexive Domain           *)
(* ================================================================= *)

(** The equation G = Hom(G, G) = G -> G asks for a type that is
    isomorphic to its own function space. This is the domain equation
    of the untyped lambda calculus.

    In Set, Cantor's theorem says |G| < |G -> Bool|, so no set
    satisfies G ≅ (G -> G) unless G is trivial.

    But in a topos of "partial" or "continuous" objects, solutions
    exist. Our (0,1] framework provides the key insight:
    the vanishing point is the fixed point that Cantor forbids. *)

(** An isomorphism between types *)
Definition Iso (A B : Type) : Prop :=
  exists (to : A -> B) (from : B -> A),
    (forall b, to (from b) = b) /\ (forall a, from (to a) = a).

(** Cantor's theorem: no surjection from A to (A -> Prop) *)
Theorem cantor : forall (A : Type) (f : A -> (A -> Prop)),
  ~ (forall P : A -> Prop, exists a, f a = P).
Proof.
  intros A f Hsurj.
  (* The diagonal predicate: D(x) = ~(f(x)(x)) *)
  set (D := fun x => ~ (f x x)).
  destruct (Hsurj D) as [a Ha].
  (* Now: D a <-> ~ (f a a), but f a = D, so f a a <-> D a *)
  assert (Hiff : D a <-> f a a).
  { rewrite Ha. unfold D. tauto. }
  unfold D in Hiff.
  (* D a = ~(f a a) and D a <-> f a a give a contradiction *)
  tauto.
Qed.

(** Consequence: no Iso between A and (A -> Prop) for non-empty A *)
Theorem no_set_reflexive_prop : forall (A : Type),
  (exists a : A, True) ->
  ~ Iso A (A -> Prop).
Proof.
  intros A [a _] [to [from [Hto_from Hfrom_to]]].
  apply (cantor A to).
  intro P. exists (from P).
  rewrite Hto_from. reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 5: Lawvere's Fixed Point Theorem                         *)
(* ================================================================= *)

(** Lawvere's theorem: if there is a surjection A -> (A -> B),
    then every endomorphism of B has a fixed point.

    This is the categorical core of:
    - Cantor's diagonal argument (B = Prop, no surjection exists)
    - The halting problem (B = Bool, no deciding surjection exists)
    - Our vanishing point (B = Prop, the fixed point is the
      membership status of 0) *)

Theorem lawvere_fixed_point :
  forall (A B : Type) (phi : A -> (A -> B)),
    (forall f : A -> B, exists a, phi a = f) ->
    forall g : B -> B, exists b : B, g b = b.
Proof.
  intros A B phi Hsurj g.
  set (h := fun x => g (phi x x)).
  destruct (Hsurj h) as [a Ha].
  exists (phi a a).
  (* phi a = h, so phi a a = h a = g (phi a a) *)
  assert (Heq : phi a a = g (phi a a)).
  { pattern (phi a) at 1. rewrite Ha. reflexivity. }
  symmetry. exact Heq.
Qed.

(** Contrapositive: if some endomorphism of B has NO fixed point,
    then no surjection A -> (A -> B) can exist *)
Theorem lawvere_no_surjection :
  forall (A B : Type),
    (exists g : B -> B, forall b, g b <> b) ->
    forall phi : A -> (A -> B),
      ~ (forall f : A -> B, exists a, phi a = f).
Proof.
  intros A B [g Hno_fix] phi Hsurj.
  destruct (lawvere_fixed_point A B phi Hsurj g) as [b Hfix].
  exact (Hno_fix b Hfix).
Qed.

(* ================================================================= *)
(** ** Part 6: The (0,1] Connection — Vanishing Point as Fixed Point *)
(* ================================================================= *)

(** The vanishing point problem IS a fixed point problem.

    Consider the endomorphism on Prop:
      negate : Prop -> Prop := fun P => ~P

    This has no fixed point (no P such that ~P = P) in classical logic.
    By Lawvere, this means: no type G can surject onto G -> Prop.

    Now consider (0,1]: the predicate "is x in (0,1]?" maps
    each real to a truth value. The vanishing point 0 is where
    this map "wants" to have a fixed point but can't — in the
    affine system, the predicate oscillates between
    "almost true" (for 1/n) and "false" (at 0 itself). *)

(** negation has no fixed point *)
Theorem negation_no_fixpoint :
  forall P : Prop, (~ P) <> P.
Proof.
  intros P H.
  pose proof (fun Hnp : ~P => eq_rect (~P) (fun Q => Q) Hnp P H) as fwd.
  pose proof (fun Hp : P => eq_rect P (fun Q => Q) Hp (~P) (eq_sym H)) as bwd.
  assert (Hp : P) by (apply fwd; intro Hp; exact (bwd Hp Hp)).
  exact (bwd Hp Hp).
Qed.

(** Therefore: no type G satisfies G ≅ (G -> Prop) *)
Theorem no_reflexive_in_Set :
  forall G : Type,
    (exists g : G, True) ->
    ~ Iso G (G -> Prop).
Proof.
  exact no_set_reflexive_prop.
Qed.

(** But partial/continuous solutions CAN exist. The (0,1]
    framework shows how:

    Define G as the type of "partial elements" — elements that
    may or may not reach their vanishing point.

    A partial element is either:
    - Defined (in the affine interval) — the computation converges
    - Undefined (the vanishing point) — the computation diverges *)

Inductive Partial (A : Type) : Type :=
  | Defined : A -> Partial A
  | Undefined : Partial A.

Arguments Defined {A}.
Arguments Undefined {A}.

(** A "partial function" is a function that may diverge *)
Definition PartialFun (A B : Type) := A -> Partial B.

(** The lifting monad — extending a total function to partial *)
Definition lift {A B : Type} (f : A -> B) : A -> Partial B :=
  fun a => Defined (f a).

(** The "bottom" element — always undefined (the vanishing point) *)
Definition bottom {A B : Type} : A -> Partial B :=
  fun _ => Undefined.

(** In the partial world, we CAN define a self-application-like
    structure. A partial endomorphism can "apply" to itself because
    divergence (the vanishing point) absorbs the paradox. *)

(** Step function: apply a partial function to a partial value *)
Definition partial_apply {A : Type}
  (f : Partial (A -> Partial A)) (x : Partial A) : Partial A :=
  match f with
  | Defined g =>
    match x with
    | Defined a => g a
    | Undefined => Undefined
    end
  | Undefined => Undefined
  end.

(** The vanishing point (Undefined) acts as the absorbing element:
    applying anything to Undefined gives Undefined.
    This is the categorical analog of 0 in (0,1] — the point
    that makes self-reference possible by "absorbing" the paradox
    that would otherwise lead to contradiction. *)

Theorem undefined_absorbs_left : forall (A : Type) (x : Partial A),
  partial_apply (Undefined : Partial (A -> Partial A)) x = Undefined.
Proof. reflexivity. Qed.

Theorem undefined_absorbs_right : forall (A : Type)
  (f : Partial (A -> Partial A)),
  partial_apply f Undefined = Undefined.
Proof. intros. destruct f; reflexivity. Qed.

(** The parallel with (0,1]:
    - Defined values = points in (0,1] (affine, well-defined)
    - Undefined = the vanishing point 0 (projective completion)
    - partial_apply with Undefined = approaching the vanishing point
    - The self-referential G = Hom(G,G) is "solved" by allowing
      Undefined as a valid result — the computation may diverge

    This is exactly Scott's insight: the domain equation G ≅ (G -> G)
    has solutions when you allow partial/continuous functions, because
    the "bottom" element (⊥ = Undefined = vanishing point) absorbs
    the Cantor paradox. *)
