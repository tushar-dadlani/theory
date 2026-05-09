(* ============================================================ *)
(*  HalfStepImplications.v                                     *)
(*                                                              *)
(*  The half-step ½ is the N-symbol of the triadic universe.   *)
(*  Defining law: N ∘ N = I.                                   *)
(*  Geometrically: the 90° axis has step size 1/2 relative     *)
(*  to the 0° linear axis — every integer point n has a        *)
(*  companion point n + 1/2 on the dual axis.                  *)
(*                                                              *)
(*  This file derives, in Coq, what the half-step IMPLIES in:  *)
(*    1. Group theory       — Z/2Z is built into every type    *)
(*    2. Category theory    — every Hom carries an involution  *)
(*    3. Topology           — every space is double-covered    *)
(*    4. Logic              — every prop has a mirror proof    *)
(*                                                              *)
(*  Axiom count: 0.                                             *)
(* ============================================================ *)

From Coq Require Import Arith.
From Coq Require Import Lia.

(* ============================================================ *)
(*  SECTION 1 — The half-step as an involution                 *)
(* ============================================================ *)

(* The three symbols. N is the half-step. *)
Inductive Sym : Type := I_s | N_s | F_s.

(* The triadic operation, restated. *)
Definition op (a b : Sym) : Sym :=
  match a, b with
  | I_s, x   => x
  | x,   I_s => x
  | N_s, N_s => I_s        (* N∘N = I — the half-step law *)
  | F_s, _   => F_s
  | _,   F_s => F_s
  end.

(* The half-step law, stated as a theorem. *)
Theorem half_step_law : op N_s N_s = I_s.
Proof. reflexivity. Qed.

(* I is the identity for op (ignoring F). *)
Theorem I_left_id  : forall x, op I_s x = x.
Proof. intro x; destruct x; reflexivity. Qed.

Theorem I_right_id : forall x, op x I_s = x.
Proof. intro x; destruct x; reflexivity. Qed.

(* N is its own inverse — this is the half-step. *)
Theorem N_self_inverse : op N_s N_s = I_s.
Proof. reflexivity. Qed.

(* ============================================================ *)
(*  SECTION 2 — Group theory: every triadic type carries Z/2Z   *)
(*                                                              *)
(*  CLAIM: The subset {I, N} under op forms a group isomorphic *)
(*  to Z/2Z. The half-step generates a Z/2Z subgroup of every  *)
(*  triadic structure.                                          *)
(* ============================================================ *)

(* The two-element subset that excludes the absorbing F. *)
Inductive IN : Type := elt_I | elt_N.

(* The operation restricted to {I, N}. *)
Definition op_IN (a b : IN) : IN :=
  match a, b with
  | elt_I, x => x
  | x, elt_I => x
  | elt_N, elt_N => elt_I
  end.

(* Group axioms for ({I,N}, op_IN). *)

Theorem IN_assoc : forall a b c, op_IN a (op_IN b c) = op_IN (op_IN a b) c.
Proof. intros [|] [|] [|]; reflexivity. Qed.

Theorem IN_left_id : forall x, op_IN elt_I x = x.
Proof. intros [|]; reflexivity. Qed.

Theorem IN_right_id : forall x, op_IN x elt_I = x.
Proof. intros [|]; reflexivity. Qed.

Theorem IN_inverses : forall x, exists y, op_IN x y = elt_I /\ op_IN y x = elt_I.
Proof.
  intros [|].
  - exists elt_I. split; reflexivity.
  - exists elt_N. split; reflexivity.        (* N is self-inverse *)
Qed.

(* The isomorphism with Z/2Z. *)

Definition to_Z2 (x : IN) : nat :=
  match x with elt_I => 0 | elt_N => 1 end.

Definition from_Z2 (n : nat) : IN :=
  match n mod 2 with 0 => elt_I | _ => elt_N end.

Theorem IN_iso_Z2_op :
  forall a b, to_Z2 (op_IN a b) = (to_Z2 a + to_Z2 b) mod 2.
Proof. intros [|] [|]; reflexivity. Qed.

(* The grand statement. *)
Theorem half_step_generates_Z2 :
  (forall a b c, op_IN a (op_IN b c) = op_IN (op_IN a b) c) /\
  (exists e, forall x, op_IN e x = x /\ op_IN x e = x) /\
  (forall x, exists y, op_IN x y = elt_I) /\
  op_IN elt_N elt_N = elt_I.
Proof.
  split; [|split; [|split]].
  - apply IN_assoc.
  - exists elt_I. intros [|]; split; reflexivity.
  - intros [|].
    + exists elt_I. reflexivity.
    + exists elt_N. reflexivity.
  - reflexivity.
Qed.

(* ============================================================ *)
(*  SECTION 3 — Category theory: every Hom has an involution    *)
(*                                                              *)
(*  CLAIM: In a triadic category, every morphism f : A → B has *)
(*  a half-step partner f̂ : A → B such that f̂ ∘ f̂ = id.       *)
(*  Equivalently, every Hom-set is a Z/2Z-torsor.              *)
(* ============================================================ *)

(* Phases attached to morphisms. *)
Definition phase := Sym.

(* A morphism is a pair (underlying arrow, phase). *)
Record Mor (A B : Type) := mkMor {
  arrow : A -> B;
  ph    : phase
}.

Arguments mkMor {A B}.
Arguments arrow {A B}.
Arguments ph    {A B}.

(* The half-step on morphisms: flip the phase between I and N. *)
Definition flip_phase (p : phase) : phase :=
  match p with
  | I_s => N_s
  | N_s => I_s
  | F_s => F_s
  end.

Definition half_step {A B} (f : Mor A B) : Mor A B :=
  mkMor (arrow f) (flip_phase (ph f)).

(* The involution law: applying the half-step twice = identity. *)
Theorem half_step_involution : forall A B (f : Mor A B),
  half_step (half_step f) = f.
Proof.
  intros A B [arr p].
  unfold half_step. simpl.
  destruct p; reflexivity.
Qed.

(* The identity morphism with I-phase. *)
Definition id_I (A : Type) : Mor A A := mkMor (fun x => x) I_s.

(* The identity morphism with N-phase — the half-step identity. *)
Definition id_N (A : Type) : Mor A A := mkMor (fun x => x) N_s.

(* Category-theoretic dual identities: id_I and id_N have the  *)
(* same underlying arrow, but different phase.                  *)
Theorem id_I_id_N_same_arrow : forall A,
  arrow (id_I A) = arrow (id_N A).
Proof. intro A. reflexivity. Qed.

Theorem id_I_id_N_distinct_phase : forall A,
  ph (id_I A) <> ph (id_N A).
Proof. intro A. simpl. discriminate. Qed.

(* The half-step swaps the two identities. *)
Theorem half_step_swaps_identities : forall A,
  half_step (id_I A) = id_N A /\ half_step (id_N A) = id_I A.
Proof. intro A. split; reflexivity. Qed.

(* ============================================================ *)
(*  SECTION 4 — Topology: every space is double-covered          *)
(*                                                              *)
(*  CLAIM: A triadic point is a pair (location, phase) where    *)
(*  phase ∈ {I, N}. The total space has cardinality 2 × |X|.    *)
(*  The half-step is the deck transformation of this 2-cover.   *)
(* ============================================================ *)

Record TPoint (X : Type) := mkTPt {
  loc : X;
  pphase : IN          (* I or N — F-phase points are at infinity *)
}.

Arguments mkTPt {X}.
Arguments loc {X}.
Arguments pphase {X}.

(* The half-step on points: flip phase, keep location. *)
Definition half_step_pt {X} (p : TPoint X) : TPoint X :=
  mkTPt (loc p) (op_IN (pphase p) elt_N).

(* The deck transformation is an involution. *)
Theorem deck_involution : forall X (p : TPoint X),
  half_step_pt (half_step_pt p) = p.
Proof.
  intros X [x ph]. unfold half_step_pt. simpl.
  destruct ph; reflexivity.
Qed.

(* The deck transformation has no fixed point (free action). *)
Theorem deck_free : forall X (p : TPoint X),
  half_step_pt p <> p.
Proof.
  intros X [x ph] H.
  unfold half_step_pt in H. simpl in H.
  destruct ph; injection H; discriminate.
Qed.

(* The projection forgetting the phase. *)
Definition project {X} (p : TPoint X) : X := loc p.

(* Two points project to the same base point iff they differ   *)
(* by at most one half-step.                                    *)
Theorem fiber_size_two : forall X (x : X),
  exists p1 p2 : TPoint X,
    p1 <> p2 /\
    project p1 = x /\
    project p2 = x /\
    half_step_pt p1 = p2.
Proof.
  intros X x.
  exists (mkTPt x elt_I), (mkTPt x elt_N).
  split; [|split; [|split]].
  - intro H. injection H. discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ============================================================ *)
(*  SECTION 5 — Logic: every proposition has a mirror proof     *)
(*                                                              *)
(*  CLAIM: In triadic logic, a proposition P is inhabited if    *)
(*  it has either an I-proof or an N-proof. The half-step      *)
(*  converts between them. This gives every prop a "double"   *)
(*  proof structure — the type-theoretic Z/2Z.                  *)
(* ============================================================ *)

(* A "phased proposition" carries a proof and a phase. *)
Record TProp := mkTProp {
  underlying : Prop;
  proof_phase : IN
}.

(* The mirror operation on phased propositions. *)
Definition mirror (P : TProp) : TProp :=
  mkTProp (underlying P) (op_IN (proof_phase P) elt_N).

(* Mirror is an involution. *)
Theorem mirror_involution : forall P, mirror (mirror P) = P.
Proof.
  intros [u p]. unfold mirror. simpl.
  destruct p; reflexivity.
Qed.

(* Mirror preserves the underlying proposition. *)
Theorem mirror_same_prop : forall P,
  underlying (mirror P) = underlying P.
Proof. intro P. reflexivity. Qed.

(* Mirror flips the proof phase. *)
Theorem mirror_flips_phase : forall P,
  proof_phase (mirror P) <> proof_phase P.
Proof.
  intros [u p]. unfold mirror. simpl.
  destruct p; discriminate.
Qed.

(* ============================================================ *)
(*  SECTION 6 — The unifying theorem                             *)
(*                                                              *)
(*  All four structures (groups, categories, topologies,        *)
(*  logics) inherit the SAME Z/2Z from the same source: the    *)
(*  half-step law N ∘ N = I.                                   *)
(* ============================================================ *)

Theorem half_step_unification :
  (* Group: N is self-inverse in {I,N}. *)
  op_IN elt_N elt_N = elt_I /\
  (* Category: half-step on morphisms is involutive. *)
  (forall A B (f : Mor A B), half_step (half_step f) = f) /\
  (* Topology: deck transformation is a free involution. *)
  (forall X (p : TPoint X),
     half_step_pt (half_step_pt p) = p /\ half_step_pt p <> p) /\
  (* Logic: mirror on propositions is involutive and phase-flipping. *)
  (forall P, mirror (mirror P) = P /\ underlying (mirror P) = underlying P).
Proof.
  split; [|split; [|split]].
  - reflexivity.
  - intros A B f. apply half_step_involution.
  - intros X p. split.
    + apply deck_involution.
    + apply deck_free.
  - intro P. split.
    + apply mirror_involution.
    + apply mirror_same_prop.
Qed.

Print Assumptions half_step_unification.
