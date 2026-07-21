(** * BoundaryTheorem.v — Layer 3.5b: Category of boundary theorems

    The Gap IS the Morphism: each millennium problem generates a
    BoundaryTheorem record where bt_gap : bt_boundary -> bt_problem
    is the irreducible mathematical content, and bt_gap_dual says
    the boundary is necessary (not just sufficient).

    This file defines:
    - BoundaryTheorem record (problem, boundary, gap, dual)
    - BTMorphism record (commuting squares)
    - Category structure (identity, composition, laws)
    - Product (conjunction) and coproduct (disjunction)
    - Projections + universal property
    - Gap composition (chaining)
    - Trivial boundary constructor
    - Gap width and classification

    Axiom audit:
    - All definitions and theorems in this file are PROVABLE [category a]
    - Uses Classical_Prop for product dual (De Morgan)
    - Uses proof_irrelevance and functional_extensionality for category laws
    - No new axioms introduced
*)

Require Import ClosedSystems.
Require Import KappaInvariant.
Require Import ObstructionGroup.
From Stdlib Require Import Reals.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import FunctionalExtensionality.

Open Scope R_scope.

(* ================================================================= *)
(** ** BoundaryTheorem: the core record *)
(* ================================================================= *)

(** A BoundaryTheorem packages a millennium problem as:
    - bt_problem:  the conjecture (e.g., RiemannHypothesis)
    - bt_boundary: the boundary separating System+ from System-
    - bt_gap:      the gap morphism (boundary -> problem)
    - bt_gap_dual: the contravariant dual (~boundary -> ~problem)

    bt_gap IS the irreducible mathematical content.
    bt_gap_dual says the boundary is NECESSARY, not just sufficient. *)

Record BoundaryTheorem : Type := mkBT {
  bt_problem   : Prop;
  bt_boundary  : Prop;
  bt_gap       : bt_boundary -> bt_problem;
  bt_gap_dual  : ~bt_boundary -> ~bt_problem
}.

(* ================================================================= *)
(** ** BTMorphism: commuting squares between boundary theorems *)
(* ================================================================= *)

(** A morphism between boundary theorems maps boundaries to boundaries
    and problems to problems. The commutativity condition
    (on_problem . gap_A = gap_B . on_boundary) is free in Prop
    via proof irrelevance. *)

Record BTMorphism (A B : BoundaryTheorem) : Type := mkBTMorph {
  on_boundary : bt_boundary A -> bt_boundary B;
  on_problem  : bt_problem A -> bt_problem B
}.

(* ================================================================= *)
(** ** Identity morphism — PROVABLE [category a] *)
(* ================================================================= *)

Definition bt_id (A : BoundaryTheorem) : BTMorphism A A :=
  mkBTMorph A A (fun b => b) (fun p => p).

(* ================================================================= *)
(** ** Composition — PROVABLE [category a] *)
(* ================================================================= *)

Definition bt_compose (A B C : BoundaryTheorem)
  (f : BTMorphism A B) (g : BTMorphism B C) : BTMorphism A C :=
  mkBTMorph A C
    (fun b => on_boundary B C g (on_boundary A B f b))
    (fun p => on_problem B C g (on_problem A B f p)).

(* ================================================================= *)
(** ** Category laws — PROVABLE [category a]
    Hold by proof_irrelevance + functional_extensionality *)
(* ================================================================= *)

(** Helper: BTMorphism equality reduces to component equality *)
Lemma btmorph_eq : forall (A B : BoundaryTheorem) (f g : BTMorphism A B),
  on_boundary A B f = on_boundary A B g ->
  on_problem A B f = on_problem A B g ->
  f = g.
Proof.
  intros A B [fb fp] [gb gp]. simpl.
  intros Hb Hp. subst. reflexivity.
Qed.

Theorem bt_left_id : forall (A B : BoundaryTheorem) (f : BTMorphism A B),
  bt_compose A A B (bt_id A) f = f.
Proof.
  intros A B f. apply btmorph_eq; reflexivity.
Qed.

Theorem bt_right_id : forall (A B : BoundaryTheorem) (f : BTMorphism A B),
  bt_compose A B B f (bt_id B) = f.
Proof.
  intros A B f. apply btmorph_eq; reflexivity.
Qed.

Theorem bt_assoc : forall (A B C D : BoundaryTheorem)
  (f : BTMorphism A B) (g : BTMorphism B C) (h : BTMorphism C D),
  bt_compose A C D (bt_compose A B C f g) h =
  bt_compose A B D f (bt_compose B C D g h).
Proof.
  intros. apply btmorph_eq; reflexivity.
Qed.

(* ================================================================= *)
(** ** Product (conjunction) — PROVABLE [category a] *)
(* ================================================================= *)

(** Product of two boundary theorems: boundary = bA /\ bB,
    problem = pA /\ pB. The gap is the conjunction of gaps.
    The dual requires classical logic (De Morgan). *)

Definition bt_product (A B : BoundaryTheorem) : BoundaryTheorem :=
  mkBT
    (bt_problem A /\ bt_problem B)
    (bt_boundary A /\ bt_boundary B)
    (fun bAB => conj (bt_gap A (proj1 bAB)) (bt_gap B (proj2 bAB)))
    (fun nbAB pAB =>
      nbAB (conj
        (match (classic (bt_boundary A)) with
         | or_introl bA => bA
         | or_intror nbA => False_ind _ (bt_gap_dual A nbA (proj1 pAB))
         end)
        (match (classic (bt_boundary B)) with
         | or_introl bB => bB
         | or_intror nbB => False_ind _ (bt_gap_dual B nbB (proj2 pAB))
         end))).

(* ================================================================= *)
(** ** Coproduct (disjunction) — PROVABLE [category a] *)
(* ================================================================= *)

(** Coproduct of two boundary theorems: boundary = bA \/ bB,
    problem = pA \/ pB. The dual works constructively. *)

Definition bt_sum (A B : BoundaryTheorem) : BoundaryTheorem :=
  mkBT
    (bt_problem A \/ bt_problem B)
    (bt_boundary A \/ bt_boundary B)
    (fun bAB => match bAB with
                | or_introl bA => or_introl (bt_gap A bA)
                | or_intror bB => or_intror (bt_gap B bB)
                end)
    (fun nbAB pAB =>
      match pAB with
      | or_introl pA => nbAB (or_introl
          (match classic (bt_boundary A) with
           | or_introl bA => bA
           | or_intror nbA => False_ind _ (bt_gap_dual A nbA pA)
           end))
      | or_intror pB => nbAB (or_intror
          (match classic (bt_boundary B) with
           | or_introl bB => bB
           | or_intror nbB => False_ind _ (bt_gap_dual B nbB pB)
           end))
      end).

(* ================================================================= *)
(** ** Projections — PROVABLE [category a] *)
(* ================================================================= *)

Definition bt_proj1 (A B : BoundaryTheorem) :
  BTMorphism (bt_product A B) A :=
  mkBTMorph (bt_product A B) A
    (fun bAB => proj1 bAB)
    (fun pAB => proj1 pAB).

Definition bt_proj2 (A B : BoundaryTheorem) :
  BTMorphism (bt_product A B) B :=
  mkBTMorph (bt_product A B) B
    (fun bAB => proj2 bAB)
    (fun pAB => proj2 pAB).

(* ================================================================= *)
(** ** Pairing (universal property of product) — PROVABLE [category a] *)
(* ================================================================= *)

Definition bt_pair (A B C : BoundaryTheorem)
  (f : BTMorphism C A) (g : BTMorphism C B) :
  BTMorphism C (bt_product A B) :=
  mkBTMorph C (bt_product A B)
    (fun bc => conj (on_boundary C A f bc) (on_boundary C B g bc))
    (fun pc => conj (on_problem C A f pc) (on_problem C B g pc)).

(* ================================================================= *)
(** ** Universal property proofs — PROVABLE [category a] *)
(* ================================================================= *)

Theorem bt_product_universal_1 :
  forall (A B C : BoundaryTheorem)
         (f : BTMorphism C A) (g : BTMorphism C B),
    bt_compose C (bt_product A B) A (bt_pair A B C f g) (bt_proj1 A B) = f.
Proof.
  intros A B C f g. destruct f as [fb fp].
  apply btmorph_eq; apply functional_extensionality; intro x;
    apply proof_irrelevance.
Qed.

Theorem bt_product_universal_2 :
  forall (A B C : BoundaryTheorem)
         (f : BTMorphism C A) (g : BTMorphism C B),
    bt_compose C (bt_product A B) B (bt_pair A B C f g) (bt_proj2 A B) = g.
Proof.
  intros A B C f g. destruct g as [gb gp].
  apply btmorph_eq; apply functional_extensionality; intro x;
    apply proof_irrelevance.
Qed.

Theorem bt_product_unique :
  forall (A B C : BoundaryTheorem)
         (f : BTMorphism C A) (g : BTMorphism C B)
         (h : BTMorphism C (bt_product A B)),
    (forall bc, proj1 (on_boundary C (bt_product A B) h bc) = on_boundary C A f bc) ->
    (forall bc, proj2 (on_boundary C (bt_product A B) h bc) = on_boundary C B g bc) ->
    (forall pc, proj1 (on_problem C (bt_product A B) h pc) = on_problem C A f pc) ->
    (forall pc, proj2 (on_problem C (bt_product A B) h pc) = on_problem C B g pc) ->
    h = bt_pair A B C f g.
Proof.
  intros A B C f g [hb hp] H1 H2 H3 H4. simpl in *.
  unfold bt_pair. apply btmorph_eq;
    apply functional_extensionality; intro x;
    apply proof_irrelevance.
Qed.

(* ================================================================= *)
(** ** Gap composition (chaining) — PROVABLE [category a] *)
(* ================================================================= *)

(** Chain two boundary theorems through a link: if the problem of A
    implies the boundary of B, then we get a composed gap
    boundary_A -> problem_B. The dual must be provided explicitly
    since it cannot be derived from components in general. *)

Definition bt_chain (A B : BoundaryTheorem)
  (link : bt_problem A -> bt_boundary B)
  (dual : ~bt_boundary A -> ~bt_problem B) : BoundaryTheorem :=
  mkBT
    (bt_problem B)
    (bt_boundary A)
    (fun bA => bt_gap B (link (bt_gap A bA)))
    dual.

(* ================================================================= *)
(** ** Trivial boundary — PROVABLE [category a] *)
(* ================================================================= *)

(** A boundary theorem where the boundary is True (always satisfied).
    The gap is trivially the proof itself. Width = 0. *)

Definition trivial_boundary (P : Prop) (proof : P) : BoundaryTheorem :=
  mkBT P True (fun _ => proof) (fun nT => False_ind _ (nT I)).

(* ================================================================= *)
(** ** Gap width — PROVABLE [category a] *)
(* ================================================================= *)

(** Gap width measures the "distance" between boundary and problem.
    - Width 0: boundary = True (trivial boundary, problem is proved)
    - Width 1: boundary = problem (identity gap) or specific condition
    - Width n: boundary requires n bridge axioms to reach problem

    We encode width as a natural number annotation. *)

Definition gap_width : BoundaryTheorem -> nat := fun _ => 0%nat.
  (* Default 0; overridden per-problem in BoundaryAudit.v *)

(* ================================================================= *)
(** ** Classified boundary theorem — annotated with width *)
(* ================================================================= *)

Record ClassifiedBT : Type := mkClassifiedBT {
  cbt_bt    : BoundaryTheorem;
  cbt_width : nat;
  cbt_name  : nat    (* problem identifier 1-7 *)
}.

(* ================================================================= *)
(** ** Injection morphisms for coproduct — PROVABLE [category a] *)
(* ================================================================= *)

Definition bt_inl (A B : BoundaryTheorem) :
  BTMorphism A (bt_sum A B) :=
  mkBTMorph A (bt_sum A B)
    (fun bA => or_introl bA)
    (fun pA => or_introl pA).

Definition bt_inr (A B : BoundaryTheorem) :
  BTMorphism B (bt_sum A B) :=
  mkBTMorph B (bt_sum A B)
    (fun bB => or_intror bB)
    (fun pB => or_intror pB).
