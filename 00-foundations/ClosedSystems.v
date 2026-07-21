(** * ClosedSystems.v — Layer 0: Categorical foundation for closed systems

    This module defines the basic objects (ClosedSystem) and two kinds
    of morphisms:
    - CSMorphism: bare state maps (always exist)
    - CSKappaMorphism: kappa-preserving maps (carry real content)

    The terminal object TerminalCS has kappa = 1. The universal property
    (terminal_universal) provides bare morphisms; kappa-preserving
    morphisms to TerminalCS require kappa = 1.

    Axiom audit:
    - terminal_universal:   [category c] foundational postulate
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

Open Scope R_scope.

(* ================================================================= *)
(** ** Closed System: the basic object *)
(* ================================================================= *)

Record ClosedSystem : Type := mkCS {
  cs_state    : Type;
  cs_Z        : R;            (* partition function *)
  cs_N        : R;            (* count / degrees of freedom *)
  cs_geometry : R;            (* geometric invariant *)
  cs_Z_pos    : cs_Z > 0;
  cs_N_pos    : cs_N > 0;
  cs_geo_pos  : cs_geometry > 0
}.

(* ================================================================= *)
(** ** Bare morphisms: state maps *)
(* ================================================================= *)

Record CSMorphism (C1 C2 : ClosedSystem) : Type := mkCSMorph {
  csm_map : cs_state C1 -> cs_state C2
}.

(* ================================================================= *)
(** ** Identity morphism — PROVABLE [category a] *)
(* ================================================================= *)

Lemma cs_id (C : ClosedSystem) : CSMorphism C C.
Proof.
  exact (mkCSMorph C C (fun x => x)).
Qed.

(* ================================================================= *)
(** ** Composition of morphisms — PROVABLE [category a] *)
(* ================================================================= *)

Lemma cs_compose (C1 C2 C3 : ClosedSystem)
  (f : CSMorphism C1 C2) (g : CSMorphism C2 C3) : CSMorphism C1 C3.
Proof.
  exact (mkCSMorph C1 C3 (fun x => csm_map C2 C3 g (csm_map C1 C2 f x))).
Qed.

(* ================================================================= *)
(** ** Terminal object — concrete definition [category a] *)
(* ================================================================= *)

Definition TerminalCS : ClosedSystem :=
  mkCS unit 1 1 1 Rlt_0_1 Rlt_0_1 Rlt_0_1.

(* ================================================================= *)
(** ** Universal property of terminal — AXIOM [category c]

    Every closed system admits a (bare) morphism to TerminalCS.
    This is now consistent: bare morphisms carry no kappa constraint,
    so the axiom does not force kappa = 1. *)
(* ================================================================= *)

Axiom terminal_universal : forall C : ClosedSystem, CSMorphism C TerminalCS.
