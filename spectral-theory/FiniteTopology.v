(* ================================================================= *)
(*  FiniteTopology.v                                                  *)
(*                                                                    *)
(*  A concrete CONTINUOUS MAP BETWEEN TWO FINITE TOPOLOGIES, axiom-    *)
(*  free -- the finite instance of PosetTopology.                     *)
(*                                                                    *)
(*  PosetTopology.continuous_of_monotone proves monotone => continuous *)
(*  for Alexandrov spaces on ARBITRARY carriers (the FreeDivMeet       *)
(*  instance is on the INFINITE F = nat*nat).  Here we pin it down to   *)
(*  genuinely FINITE spaces: finite carriers with enumerations, and a   *)
(*  concrete map whose continuity is checked by explicit preimages.    *)
(*                                                                    *)
(*  KEY FACT: on a finite set every topology is Alexandrov (finite      *)
(*  intersections = arbitrary intersections), so finite T0 spaces are   *)
(*  exactly finite posets -- our poset machinery captures ALL finite    *)
(*  topologies; the only thing added here is finiteness + an instance.  *)
(*                                                                    *)
(*  Spaces:                                                            *)
(*    two   = {L, R} with L <= R   (Sierpinski space; opens {},{R},all) *)
(*    three = {A, B, C} chain A<=B<=C (opens {},{C},{B,C},all)          *)
(*    map   f : three -> two,  A,B |-> L,  C |-> R  (monotone)          *)
(* ================================================================= *)

Require Import PosetTopology.
From Stdlib Require Import List.
Import ListNotations.

(* ================================================================= *)
(*  1.  TWO FINITE POSETS (= finite spaces)                          *)
(* ================================================================= *)

Inductive two   := L | R.
Inductive three := A | B | C.

Definition le2 (x y : two) : Prop :=
  match x, y with L, _ => True | R, R => True | R, L => False end.

Definition le3 (x y : three) : Prop :=
  match x, y with
  | A, _ => True
  | B, A => False | B, _ => True
  | C, C => True  | C, _ => False
  end.

Lemma le2_refl : forall x, le2 x x.
Proof. destruct x; exact I. Qed.
Lemma le2_trans : forall x y z, le2 x y -> le2 y z -> le2 x z.
Proof. destruct x, y, z; cbn; tauto. Qed.
Lemma le3_refl : forall x, le3 x x.
Proof. destruct x; exact I. Qed.
Lemma le3_trans : forall x y z, le3 x y -> le3 y z -> le3 x z.
Proof. destruct x, y, z; cbn; tauto. Qed.

(* finiteness of the carriers: a full enumeration of each *)
Definition elts2 : list two   := [L; R].
Definition elts3 : list three := [A; B; C].
Lemma finite2 : forall x, In x elts2. Proof. destruct x; simpl; auto. Qed.
Lemma finite3 : forall x, In x elts3. Proof. destruct x; simpl; auto. Qed.

(* ================================================================= *)
(*  2.  THE ALEXANDROV OPENS (up-sets)                               *)
(* ================================================================= *)

(* {R} is open (the up-set of R); the whole space is open *)
Lemma open_R : Op le2 (fun z => z = R).
Proof.
  intros x y Hx Hxy; subst x; destruct y;
    [ cbn in Hxy; contradiction | reflexivity ].
Qed.

Lemma open_full2 : Op le2 (fun _ => True).
Proof. intros x y _ _; exact I. Qed.

(* {L} is NOT open: the topology is genuinely coarser than discrete *)
Lemma not_open_L : ~ Op le2 (fun z => z = L).
Proof. intro H; specialize (H L R eq_refl I); discriminate. Qed.

(* {C} is open in three (the up-set of the top element C) *)
Lemma open_C3 : Op le3 (fun z => z = C).
Proof.
  intros x y Hx Hxy; subst x; destruct y; cbn in Hxy;
    solve [ contradiction | reflexivity ].
Qed.

(* ================================================================= *)
(*  3.  THE MAP OPERATOR AND ITS CONTINUITY                          *)
(* ================================================================= *)

Definition f (x : three) : two := match x with A => L | B => L | C => R end.

Lemma f_mono : forall a b, le3 a b -> le2 (f a) (f b).
Proof. destruct a, b; cbn; tauto. Qed.

Definition preimf (V : two -> Prop) : three -> Prop := fun x => V (f x).

(* continuity: the preimage of every open is open.  This is exactly     *)
(* PosetTopology.continuous_of_monotone le3 le2 f f_mono.               *)
Theorem f_continuous : forall V, Op le2 V -> Op le3 (preimf V).
Proof.
  intros V HV x y Hx Hxy; unfold preimf in *; eapply HV;
    [ exact Hx | apply f_mono; exact Hxy ].
Qed.

(* continuity verified CONCRETELY: the preimage of the open {R} is the   *)
(* open {C} -- and {C} is indeed open, so f is continuous by computation. *)
Lemma preim_R_is_C : forall x, preimf (fun z => z = R) x <-> x = C.
Proof.
  destruct x; unfold preimf; cbn; split; intro H;
    solve [ reflexivity | discriminate ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — a continuous map between two finite topologies   *)
(* ----------------------------------------------------------------- *)

Theorem finite_topology :
  (* two finite posets = two finite (Alexandrov) spaces *)
  (forall x, le2 x x) /\ (forall x y z, le2 x y -> le2 y z -> le2 x z)
  /\ (forall x, le3 x x) /\ (forall x y z, le3 x y -> le3 y z -> le3 x z)
  /\ (forall x, In x elts2) /\ (forall x, In x elts3)
  (* the topology is genuinely coarser than discrete: {L} is not open *)
  /\ (~ Op le2 (fun z => z = L))
  (* the map operator is monotone, hence continuous *)
  /\ (forall a b, le3 a b -> le2 (f a) (f b))
  /\ (forall V, Op le2 V -> Op le3 (preimf V))
  (* and its continuity computed: preimage of the open {R} is the open {C} *)
  /\ (forall x, preimf (fun z => z = R) x <-> x = C).
Proof.
  split; [ exact le2_refl | ].
  split; [ exact le2_trans | ].
  split; [ exact le3_refl | ].
  split; [ exact le3_trans | ].
  split; [ exact finite2 | ].
  split; [ exact finite3 | ].
  split; [ exact not_open_L | ].
  split; [ exact f_mono | ].
  split; [ exact f_continuous | exact preim_R_is_C ].
Qed.

Print Assumptions finite_topology.

(* ================================================================= *)
(*  END FiniteTopology.v                                              *)
(*  A concrete continuous map f : three -> two between two finite       *)
(*  Alexandrov spaces (finite carriers, coarser-than-discrete opens),   *)
(*  continuity via PosetTopology and by explicit preimage computation.  *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
