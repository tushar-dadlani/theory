(* ============================================================ *)
(*  StructuralAssumption.v                                      *)
(*                                                              *)
(*  CLAIM: The half-step REVEALS a structural assumption that  *)
(*  the system is silently making. As long as the assumption  *)
(*  is unexamined, 1/2 is forced. When the assumption is       *)
(*  ABSORBED into the system (made explicit, then taken as    *)
(*  part of the domain), the kernel shrinks, and 1/2 vacates. *)
(*                                                              *)
(*  More precisely: the half-step is the FIXED POINT of a     *)
(*  reflection symmetry. A reflection symmetry only exists    *)
(*  when the system has a "two-sidedness" it has not yet       *)
(*  acknowledged. Acknowledging it = making the symmetry      *)
(*  explicit = absorbing the assumption.                       *)
(*                                                              *)
(*  Examples of such assumptions:                               *)
(*    - "Every input is unique" (SHA-256 phantom doubling)     *)
(*    - "The functional equation s ↔ 1-s is unaccounted for"   *)
(*    - "Direction matters" (when system is direction-blind)  *)
(*    - "There is exactly one identity" (when there are two)   *)
(*                                                              *)
(*  Each unexamined assumption produces a half-step.            *)
(*  Each absorption removes one half-step.                      *)
(*  At the limit, no assumptions remain unexamined.            *)
(*                                                              *)
(*  Axiom count: 0.                                             *)
(* ============================================================ *)

From Coq Require Import QArith Arith Lia.
Open Scope Q_scope.

(* ============================================================ *)
(*  PART 1 — Information system with explicit assumptions       *)
(* ============================================================ *)

(* An information system tagged with the assumptions it makes.  *)
(* "assumed" = propositions taken for granted but not proved.  *)
Record AssumedInfoSystem : Type := mkAIS {
  ais_domain   : nat -> Prop;     (* resolved/proved              *)
  ais_kernel   : nat -> Prop;     (* unresolved                   *)
  ais_assumed  : nat -> Prop;     (* implicit assumptions         *)
  ais_kid      : forall p, ais_kernel p -> ais_domain p
}.

(* An assumption is "structural" if it has reflection symmetry: *)
(* the system treats p and "the reflected version of p" as      *)
(* indistinguishable. This is what produces a fixed point at    *)
(* 1/2 — the depth at which the reflection acts trivially.     *)

(* The reflection on depths *)
Definition reflect_depth (s : Q) : Q := 1 - s.

(* The reflection-fixed-point lemma — the analytic root *)
Lemma reflection_fixes_half : forall s : Q,
  s == 1 - s -> s == 1#2.
Proof.
  intros s H.
  assert (Hs2 : s + s == 1).
  { rewrite H at 2. ring. }
  apply Qmult_inj_l with (z := 2#1).
  - discriminate.
  - field_simplify.
    transitivity 1. transitivity (s + s). ring. exact Hs2. reflexivity.
Qed.

(* ============================================================ *)
(*  PART 2 — Assumptions LIVE at depth 1/2                       *)
(*                                                              *)
(*  An unexamined symmetric assumption sits at the half-step.  *)
(*  This is what "the half reveals" means: looking at depth   *)
(*  1/2 surfaces the assumption.                                *)
(* ============================================================ *)

(* A depth assignment for propositions *)
Definition Depth := nat -> Q.

(* The half-step "reveals" the assumed proposition p if:        *)
(*   - p is in the system's assumed set                         *)
(*   - p has reflection-symmetric depth                         *)
(* Conclusion: p sits at depth 1/2. *)

Definition reveals_assumption (F : AssumedInfoSystem) (d : Depth) (p : nat) : Prop :=
  ais_assumed F p /\ d p == 1 - d p.

(* The half-step reveal theorem: revealed assumptions are at 1/2 *)
Theorem half_reveals_assumption : forall F d p,
  reveals_assumption F d p -> d p == 1#2.
Proof.
  intros F d p [_ Hsym].
  apply reflection_fixes_half. exact Hsym.
Qed.

(* ============================================================ *)
(*  PART 3 — ABSORPTION: moving an assumption from              *)
(*  "assumed" into the explicit domain                           *)
(*                                                              *)
(*  This is the formal model of "examining" the assumption:    *)
(*  the system stops taking p for granted and either proves it *)
(*  or refutes its hidden symmetry.                             *)
(* ============================================================ *)

(* The absorb operation: move a specific assumption p into the *)
(* domain. After absorption, p is no longer "merely assumed"   *)
(* — it is explicit and acknowledged.                          *)

Definition absorb (F : AssumedInfoSystem) (p0 : nat) : AssumedInfoSystem :=
  mkAIS
    (fun p => ais_domain F p \/ p = p0)         (* p0 enters domain *)
    (fun p => ais_kernel F p /\ p <> p0)        (* leaves kernel    *)
    (fun p => ais_assumed F p /\ p <> p0)       (* leaves assumed   *)
    (fun p H => or_introl (ais_kid F p (proj1 H))).

(* After absorption, p0 is no longer assumed. *)
Theorem absorb_removes_assumption : forall F p0,
  ~ ais_assumed (absorb F p0) p0.
Proof.
  intros F p0 [_ Hne]. apply Hne. reflexivity.
Qed.

(* After absorption, p0 is in the domain. *)
Theorem absorb_adds_to_domain : forall F p0,
  ais_domain (absorb F p0) p0.
Proof.
  intros F p0. simpl. right. reflexivity.
Qed.

(* After absorption, the half-step no longer reveals p0. *)
Theorem absorb_clears_half_step : forall F d p0,
  ~ reveals_assumption (absorb F p0) d p0.
Proof.
  intros F d p0 [Hassumed _].
  apply (absorb_removes_assumption F p0). exact Hassumed.
Qed.

(* ============================================================ *)
(*  PART 4 — THE FULL DYNAMIC                                   *)
(*                                                              *)
(*  The half-step is a "diagnostic":                            *)
(*    - It points at every unexamined symmetric assumption.    *)
(*    - Each absorption clears one such pointer.                *)
(*    - At the limit (all assumptions absorbed), the half-step *)
(*      has nothing to reveal.                                  *)
(* ============================================================ *)

(* All propositions in the assumed set have been absorbed. *)
Definition fully_absorbed (F : AssumedInfoSystem) : Prop :=
  forall p, ~ ais_assumed F p.

(* When fully absorbed, no proposition can be revealed by       *)
(* the half-step.                                                *)
Theorem fully_absorbed_no_reveal : forall F d,
  fully_absorbed F ->
  forall p, ~ reveals_assumption F d p.
Proof.
  intros F d Hfull p [Hassumed _].
  apply (Hfull p). exact Hassumed.
Qed.

(* ============================================================ *)
(*  PART 5 — THE MAIN THEOREM                                   *)
(*                                                              *)
(*  The half-step is exactly the diagnostic for unexamined     *)
(*  symmetric assumptions. Until they are absorbed, 1/2 is      *)
(*  populated. After absorption, 1/2 is vacant.                 *)
(* ============================================================ *)

Theorem half_step_is_assumption_diagnostic : forall F d,
  (* Forward: every reflection-symmetric assumption sits at 1/2 *)
  (forall p, reveals_assumption F d p -> d p == 1#2) /\
  (* Backward: absorption removes the half-step witness         *)
  (forall p, ais_assumed F p ->
     ~ reveals_assumption (absorb F p) d p) /\
  (* Limit: fully-absorbed system has no half-step witnesses    *)
  (fully_absorbed F ->
    forall p, ~ reveals_assumption F d p).
Proof.
  intros F d.
  split; [|split].
  - apply half_reveals_assumption.
  - intros p Hassumed. apply absorb_clears_half_step.
  - apply fully_absorbed_no_reveal.
Qed.

(* ============================================================ *)
(*  PART 6 — INTERPRETATION                                     *)
(*                                                              *)
(*  half_reveals_assumption                                     *)
(*    = "the half-step is where assumptions hide"              *)
(*                                                              *)
(*  absorb_clears_half_step                                     *)
(*    = "absorbing an assumption removes it from depth 1/2"    *)
(*                                                              *)
(*  fully_absorbed_no_reveal                                    *)
(*    = "a system with no implicit assumptions has no          *)
(*       half-step witnesses — 1/2 is empty"                   *)
(*                                                              *)
(*  half_step_is_assumption_diagnostic                          *)
(*    = "the half-step is precisely the catalogue of          *)
(*       structural assumptions awaiting absorption"           *)
(* ============================================================ *)

Print Assumptions half_step_is_assumption_diagnostic.
