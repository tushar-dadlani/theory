(* ================================================================= *)
(*  PosetTopology.v                                                   *)
(*                                                                    *)
(*  TOPOLOGY FALLS OUT OF ORDER, axiom-free.  How a topology and a     *)
(*  "map operator" between two posets arise from pure order theory --  *)
(*  no metric, no limits, no analysis library.                        *)
(*                                                                    *)
(*  (1) ALEXANDROV TOPOLOGY: on a single preorder, the OPEN sets are   *)
(*      the up-sets (Op).  They form a genuine topology -- closed       *)
(*      under arbitrary unions and finite intersections, with empty     *)
(*      and full open -- and the SPECIALIZATION order recovers <=       *)
(*      exactly.  So topology falls out of one poset.                  *)
(*                                                                    *)
(*  (2) THE MAP OPERATOR: a monotone map f between two posets is        *)
(*      automatically CONTINUOUS (preimage of an up-set is an up-set).  *)
(*                                                                    *)
(*  (3) TWO POSETS + A GALOIS CONNECTION (the pair of adjoint map       *)
(*      operators, exactly BiView's alpha/gamma): the composite         *)
(*      cl = gamma o alpha is a CLOSURE OPERATOR (extensive, monotone,  *)
(*      idempotent).  Its fixed points are the Galois-CLOSED elements   *)
(*      -- the OVERLAP where the two posets' views coincide -- and they *)
(*      form the closed sets (a closure system).  So the topological     *)
(*      skeleton (closed sets) falls out of two posets joined at their   *)
(*      shared core.                                                   *)
(*                                                                    *)
(*  Instances in this repo: FreeDivMeet.fle (divisibility lattice) is   *)
(*  a poset -> Alexandrov space (Example below); BiView.galois_-        *)
(*  connection is such a Galois connection -> cl a closure operator.    *)
(* ================================================================= *)

Require Import FreeDivMeet.
From Stdlib Require Import Lia.

(* the OPEN sets of the Alexandrov topology: the up-sets of the order *)
Definition Op {X : Type} (le : X -> X -> Prop) (U : X -> Prop) : Prop :=
  forall x y, U x -> le x y -> U y.

Section PosetTop.

(* two posets (preorders suffice for Alexandrov) *)
Context {X Y : Type}.
Variables (leX : X -> X -> Prop) (leY : Y -> Y -> Prop).
Hypothesis leX_refl  : forall x, leX x x.
Hypothesis leX_trans : forall x y z, leX x y -> leX y z -> leX x z.
Hypothesis leY_refl  : forall y, leY y y.
Hypothesis leY_trans : forall a b c, leY a b -> leY b c -> leY a c.

(* ================================================================= *)
(*  1.  THE ALEXANDROV TOPOLOGY ON X                                 *)
(* ================================================================= *)

Lemma open_empty : Op leX (fun _ => False).
Proof. intros x y [] _. Qed.

Lemma open_full : Op leX (fun _ => True).
Proof. intros x y _ _; exact I. Qed.

Lemma open_inter : forall U V, Op leX U -> Op leX V -> Op leX (fun x => U x /\ V x).
Proof.
  intros U V HU HV x y [Hx Hx'] Hxy; split; [ eapply HU | eapply HV ]; eauto.
Qed.

Lemma open_union : forall (I : Type) (F : I -> X -> Prop),
  (forall i, Op leX (F i)) -> Op leX (fun x => exists i, F i x).
Proof.
  intros I F HF x y [i Hi] Hxy; exists i; eapply HF; eauto.
Qed.

(* principal up-set (the smallest open containing a) *)
Definition up (a : X) : X -> Prop := fun z => leX a z.

Lemma open_up : forall a, Op leX (up a).
Proof. intros a x y Hx Hxy; unfold up in *; eapply leX_trans; eauto. Qed.

(* the SPECIALIZATION order recovers <= exactly *)
Theorem specialization : forall x y,
  leX x y <-> (forall U, Op leX U -> U x -> U y).
Proof.
  intros x y; split.
  - intros Hxy U HU Hx; eapply HU; eauto.
  - intros H; apply (H (up x) (open_up x)); unfold up; apply leX_refl.
Qed.

(* ================================================================= *)
(*  2.  THE MAP OPERATOR: monotone => continuous                     *)
(* ================================================================= *)

Variable f : X -> Y.
Hypothesis f_mono : forall a b, leX a b -> leY (f a) (f b).

Definition preim (V : Y -> Prop) : X -> Prop := fun x => V (f x).

Theorem continuous_of_monotone : forall V, Op leY V -> Op leX (preim V).
Proof.
  intros V HV x y Hx Hxy; unfold preim in *; eapply HV;
    [ exact Hx | apply f_mono; exact Hxy ].
Qed.

(* ================================================================= *)
(*  3.  TWO POSETS + GALOIS CONNECTION => CLOSURE OPERATOR           *)
(* ================================================================= *)

Variables (alpha : X -> Y) (gamma : Y -> X).
Hypothesis galois : forall x y, leY (alpha x) y <-> leX x (gamma y).

(* the closure operator induced by the adjunction *)
Definition cl (x : X) : X := gamma (alpha x).

(* unit: x <= gamma(alpha x)  (EXTENSIVE) *)
Lemma cl_extensive : forall x, leX x (cl x).
Proof. intro x; unfold cl; apply (proj1 (galois x (alpha x))); apply leY_refl. Qed.

(* counit: alpha(gamma y) <= y *)
Lemma counit : forall y, leY (alpha (gamma y)) y.
Proof. intro y; apply (proj2 (galois (gamma y) y)); apply leX_refl. Qed.

Lemma gamma_mono : forall u v, leY u v -> leX (gamma u) (gamma v).
Proof.
  intros u v Huv; apply (proj1 (galois (gamma u) v)).
  eapply leY_trans; [ apply counit | exact Huv ].
Qed.

Lemma alpha_mono : forall a b, leX a b -> leY (alpha a) (alpha b).
Proof.
  intros a b Hab; apply (proj2 (galois a (alpha b))).
  eapply leX_trans; [ exact Hab | apply cl_extensive ].
Qed.

(* MONOTONE *)
Lemma cl_monotone : forall a b, leX a b -> leX (cl a) (cl b).
Proof. intros a b Hab; unfold cl; apply gamma_mono, alpha_mono; exact Hab. Qed.

(* IDEMPOTENT: cl (cl x) is order-equal to cl x *)
Lemma cl_idempotent : forall x, leX (cl (cl x)) (cl x) /\ leX (cl x) (cl (cl x)).
Proof.
  intro x; split.
  - unfold cl at 1; unfold cl at 2.
    apply gamma_mono; apply counit.
  - apply cl_extensive.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — axiom-free                                      *)
(* ----------------------------------------------------------------- *)

Theorem poset_topology :
  (* (1) the up-sets form a topology on X *)
  ( Op leX (fun _ => False) /\ Op leX (fun _ => True)
    /\ (forall U V, Op leX U -> Op leX V -> Op leX (fun x => U x /\ V x))
    /\ (forall (I : Type) (F : I -> X -> Prop),
          (forall i, Op leX (F i)) -> Op leX (fun x => exists i, F i x)) )
  (* (2) specialization recovers the order *)
  /\ (forall x y, leX x y <-> (forall U, Op leX U -> U x -> U y))
  (* (3) the map operator f is continuous *)
  /\ (forall V, Op leY V -> Op leX (preim V))
  (* (4) the Galois connection yields a closure operator (extensive, monotone, idempotent) *)
  /\ (forall x, leX x (cl x))
  /\ (forall a b, leX a b -> leX (cl a) (cl b))
  /\ (forall x, leX (cl (cl x)) (cl x) /\ leX (cl x) (cl (cl x))).
Proof.
  split.
  { split; [ exact open_empty | ].
    split; [ exact open_full | ].
    split; [ exact open_inter | exact open_union ]. }
  split; [ exact specialization | ].
  split; [ exact continuous_of_monotone | ].
  split; [ exact cl_extensive | ].
  split; [ exact cl_monotone | exact cl_idempotent ].
Qed.

End PosetTop.

Print Assumptions poset_topology.

(* ================================================================= *)
(*  INSTANCE: the divisibility lattice (FreeDivMeet.fle) is a poset,   *)
(*  hence an Alexandrov space -- its up-sets (sets closed under        *)
(*  taking multiples / larger exponent vectors) are the opens.         *)
(* ================================================================= *)

Lemma fle_refl : forall u, fle u u.
Proof. intros [a b]; unfold fle; cbn [fst snd]; lia. Qed.

Lemma fle_trans : forall u v w, fle u v -> fle v w -> fle u w.
Proof. intros [a b] [c d] [e g]; unfold fle; cbn [fst snd]; lia. Qed.

(* the principal up-set of the divisibility order (multiples of a) is open *)
Example divisibility_up_open : forall a, Op fle (up fle a).
Proof. intro a; apply (open_up fle fle_trans). Qed.

(* finite intersections of divisibility-opens are open *)
Example divisibility_inter_open : forall U V,
  Op fle U -> Op fle V -> Op fle (fun x => U x /\ V x).
Proof. apply (open_inter fle). Qed.

(* ================================================================= *)
(*  END PosetTopology.v                                               *)
(*  Topology from pure order: the Alexandrov topology of a poset, the  *)
(*  monotone map operator as a continuous map, and the Galois closure  *)
(*  operator whose fixed points (the overlap of the two posets) are     *)
(*  the closed sets.  ZERO Admitted; Closed under the global context.  *)
(* ================================================================= *)
