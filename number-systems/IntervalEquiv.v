(** * Predicate Extensional Equivalence for the Interval (0,1] *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(** Predicate 1: (0,1] via direct conjunction of strict lower and non-strict upper bound *)
Definition in_interval_conj (x : R) : Prop :=
  0 < x /\ x <= 1.

(** Predicate 2: (0,1] via negation of the complement for the lower bound *)
Definition in_interval_alt (x : R) : Prop :=
  ~ (x <= 0) /\ x <= 1.

(** Axiom: Predicate extensionality —
    two predicates over R are equal if they hold for the same elements *)
Axiom predicate_extensionality :
  forall (P Q : R -> Prop), (forall x : R, P x <-> Q x) -> P = Q.

(** Lemma: The two interval predicates are extensionally equivalent *)
Lemma interval_predicates_equiv :
  forall x : R, in_interval_conj x <-> in_interval_alt x.
Proof.
  intro x. unfold in_interval_conj, in_interval_alt.
  split; intros H.
  - destruct H as [Hlt Hle]. split; [lra | exact Hle].
  - destruct H as [Hnle Hle]. split; [lra | exact Hle].
Qed.

(** Theorem: The two predicates are provably equal via predicate extensionality *)
Theorem interval_predicates_eq :
  in_interval_conj = in_interval_alt.
Proof.
  apply predicate_extensionality.
  exact interval_predicates_equiv.
Qed.
