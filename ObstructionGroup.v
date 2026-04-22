(** * ObstructionGroup.v — Layer 3: Sha (obstruction) groups

    Defines an abstract abelian group structure representing the
    obstruction to a closed system reaching the terminal object.
    When Sha is trivial, the system is "solved."

    Axiom audit:
    - sha_of_system:            [category c] obstruction functor, new mathematics
    - sha_trivial_iff_terminal: [category c] main structural axiom, new mathematics
      Uses CSKappaMorphism (kappa-preserving), not bare CSMorphism.
*)

From MillenniumKappa Require Import foundations.ClosedSystems.
From MillenniumKappa Require Import foundations.KappaInvariant.
From MillenniumKappa Require Import foundations.BoundaryAxiom.
From Stdlib Require Import Reals.
From Stdlib Require Import List.
Import ListNotations.

Open Scope R_scope.

(* ================================================================= *)
(** ** Sha group: abstract abelian group with decidable equality *)
(* ================================================================= *)

Record ShaGroup : Type := mkShaGroup {
  sha_carrier : Type;
  sha_zero    : sha_carrier;
  sha_add     : sha_carrier -> sha_carrier -> sha_carrier;
  sha_neg     : sha_carrier -> sha_carrier;
  sha_dec_eq  : forall (x y : sha_carrier), {x = y} + {x <> y};
  sha_add_comm : forall x y, sha_add x y = sha_add y x;
  sha_add_assoc : forall x y z,
    sha_add (sha_add x y) z = sha_add x (sha_add y z);
  sha_add_zero : forall x, sha_add x sha_zero = x;
  sha_add_neg  : forall x, sha_add x (sha_neg x) = sha_zero
}.

(* ================================================================= *)
(** ** Finiteness and triviality predicates *)
(* ================================================================= *)

Definition sha_is_finite (G : ShaGroup) : Prop :=
  exists (l : list (sha_carrier G)),
    forall x : sha_carrier G, In x l.

Definition sha_is_trivial (G : ShaGroup) : Prop :=
  forall x : sha_carrier G, x = sha_zero G.

(* ================================================================= *)
(** ** Obstruction functor — AXIOM [category c]

    Assigns to each closed system its obstruction group. This is
    the core new mathematical construction: Sha measures how far
    a system is from reaching the terminal object. *)
(* ================================================================= *)

Axiom sha_of_system : ClosedSystem -> ShaGroup.

(* ================================================================= *)
(** ** Sha trivial iff kappa-terminal — AXIOM [category c]

    Sha is trivial iff there exists a KAPPA-PRESERVING morphism
    to TerminalCS. Since TerminalCS has kappa = 1, this means
    Sha is trivial iff kappa C = 1.

    This uses CSKappaMorphism (not bare CSMorphism) to carry
    real content. With bare morphisms the RHS would be trivially
    true for all systems (just map everything to tt). *)
(* ================================================================= *)

Axiom sha_trivial_iff_terminal :
  forall C : ClosedSystem,
    sha_is_trivial (sha_of_system C) <-> inhabited (CSKappaMorphism C TerminalCS).

(* ================================================================= *)
(** ** Sha of terminal is trivial — consequence *)
(* ================================================================= *)

Lemma sha_terminal_trivial :
  sha_is_trivial (sha_of_system TerminalCS).
Proof.
  apply sha_trivial_iff_terminal.
  constructor.
  exact (csk_id TerminalCS).
Qed.

(* ================================================================= *)
(** ** Infiniteness predicate — dual of finiteness *)
(* ================================================================= *)

Definition sha_is_infinite (G : ShaGroup) : Prop :=
  ~ sha_is_finite G.

(* ================================================================= *)
(** ** Infinite implies not trivial — PROVABLE [category a] *)
(* ================================================================= *)

Lemma sha_infinite_implies_not_trivial :
  forall G : ShaGroup, sha_is_infinite G -> ~ sha_is_trivial G.
Proof.
  intros G Hinf Htriv.
  apply Hinf.
  exists (sha_zero G :: nil)%list.
  intro x. rewrite (Htriv x). simpl. left. reflexivity.
Qed.

(* ================================================================= *)
(** ** Infinite implies not finite — tautological [category a] *)
(* ================================================================= *)

Lemma sha_infinite_implies_not_finite :
  forall G : ShaGroup, sha_is_infinite G -> ~ sha_is_finite G.
Proof.
  intros G H. exact H.
Qed.
