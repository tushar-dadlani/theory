(** * Rational Numbers and (0,1]: The Dense Layer *)

From Stdlib Require Import QArith.
From Stdlib Require Import Reals.
From Stdlib Require Import Qreals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Require Import IntervalEquiv.

Open Scope Q_scope.

(* ================================================================= *)
(** ** Characterizing Q ∩ (0,1]                                      *)
(* ================================================================= *)

(** A rational q is in (0,1] when 0 < q and q <= 1 *)
Definition q_in_interval (q : Q) : Prop :=
  0 < q /\ q <= 1.

(** --- Concrete witnesses --- *)

Theorem half_in_interval : q_in_interval (1#2).
Proof.
  unfold q_in_interval. split.
  - reflexivity.
  - unfold Qle. simpl. lia.
Qed.

Theorem third_in_interval : q_in_interval (1#3).
Proof.
  unfold q_in_interval. split.
  - reflexivity.
  - unfold Qle. simpl. lia.
Qed.

Theorem one_q_in_interval : q_in_interval 1.
Proof.
  unfold q_in_interval. split.
  - reflexivity.
  - unfold Qle. simpl. lia.
Qed.

(** --- Boundary exclusions --- *)

Theorem zero_q_not_in_interval : ~ q_in_interval 0.
Proof.
  unfold q_in_interval. intros [H _].
  apply (Qlt_irrefl 0). exact H.
Qed.

Theorem three_halves_not_in_interval : ~ q_in_interval (3#2).
Proof.
  unfold q_in_interval. intros [_ H].
  unfold Qle in H. simpl in H. lia.
Qed.

(* ================================================================= *)
(** ** Density: Between Any Two Rationals in (0,1], There's Another  *)
(* ================================================================= *)

(** The midpoint of two rationals *)
Definition Q_midpoint (q1 q2 : Q) : Q := (q1 + q2) / (2#1).

(** Midpoint is strictly between the two endpoints *)
Lemma Q_midpoint_between : forall q1 q2 : Q,
  q1 < q2 -> q1 < Q_midpoint q1 q2 /\ Q_midpoint q1 q2 < q2.
Proof.
  intros q1 q2 Hlt.
  unfold Q_midpoint.
  unfold Qdiv.
  split.
  - unfold Qlt in *. simpl in *.
    unfold Qinv. simpl.
    nia.
  - unfold Qlt in *. simpl in *.
    unfold Qinv. simpl.
    nia.
Qed.

(** If both endpoints are positive, the midpoint is positive *)
Lemma Q_midpoint_pos : forall q1 q2 : Q,
  0 < q1 -> 0 < q2 -> 0 < Q_midpoint q1 q2.
Proof.
  intros q1 q2 H1 H2.
  unfold Q_midpoint, Qdiv.
  unfold Qlt in *. simpl in *.
  unfold Qinv. simpl.
  nia.
Qed.

(** If both endpoints are <= 1, the midpoint is <= 1 *)
Lemma Q_midpoint_le_1 : forall q1 q2 : Q,
  q1 <= 1 -> q2 <= 1 -> Q_midpoint q1 q2 <= 1.
Proof.
  intros q1 q2 H1 H2.
  unfold Q_midpoint, Qdiv.
  unfold Qle in *. simpl in *.
  unfold Qinv. simpl.
  nia.
Qed.

(** The density theorem: between any two rationals in (0,1] with
    q1 < q2, the midpoint is also in (0,1] *)
Theorem q_density : forall q1 q2 : Q,
  q_in_interval q1 -> q_in_interval q2 -> q1 < q2 ->
  q_in_interval (Q_midpoint q1 q2) /\
  q1 < Q_midpoint q1 q2 /\
  Q_midpoint q1 q2 < q2.
Proof.
  intros q1 q2 [Hq1_pos Hq1_le] [Hq2_pos Hq2_le] Hlt.
  split.
  - unfold q_in_interval. split.
    + apply Q_midpoint_pos; assumption.
    + apply Q_midpoint_le_1; assumption.
  - apply Q_midpoint_between. exact Hlt.
Qed.

(* ================================================================= *)
(** ** Predicate Extensionality over Q — Derived, Not Assumed        *)
(* ================================================================= *)

(** Same derivation as for nat: functional + propositional
    extensionality yields predicate extensionality *)
Theorem q_pred_extensionality :
  forall (P1 P2 : Q -> Prop),
    (forall q : Q, P1 q <-> P2 q) ->
    P1 = P2.
Proof.
  intros P1 P2 Hext.
  apply functional_extensionality. intro q.
  apply propositional_extensionality.
  exact (Hext q).
Qed.

(* ================================================================= *)
(** ** Predicate Algebra over Q                                      *)
(* ================================================================= *)

Definition q_pred_empty : Q -> Prop := fun _ => False.
Definition q_pred_full : Q -> Prop := fun _ => True.

Definition q_pred_complement (P : Q -> Prop) : Q -> Prop :=
  fun q => ~ P q.

Definition q_pred_inter (P R : Q -> Prop) : Q -> Prop :=
  fun q => P q /\ R q.

Definition q_pred_union (P R : Q -> Prop) : Q -> Prop :=
  fun q => P q \/ R q.

(** Idempotence *)
Theorem q_inter_idempotent : forall P : Q -> Prop,
  q_pred_inter P P = P.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_inter. split.
  - intros [H _]. exact H.
  - intro H. split; exact H.
Qed.

Theorem q_union_idempotent : forall P : Q -> Prop,
  q_pred_union P P = P.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_union. split.
  - intros [H | H]; exact H.
  - intro H. left. exact H.
Qed.

(** Identity *)
Theorem q_inter_full_r : forall P : Q -> Prop,
  q_pred_inter P q_pred_full = P.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_inter, q_pred_full. split.
  - intros [H _]. exact H.
  - intro H. split; [exact H | exact I].
Qed.

Theorem q_union_empty_r : forall P : Q -> Prop,
  q_pred_union P q_pred_empty = P.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_union, q_pred_empty. split.
  - intros [H | []]. exact H.
  - intro H. left. exact H.
Qed.

(** Annihilation *)
Theorem q_inter_empty_r : forall P : Q -> Prop,
  q_pred_inter P q_pred_empty = q_pred_empty.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_inter, q_pred_empty. split.
  - intros [_ []].
  - intros [].
Qed.

Theorem q_union_full_r : forall P : Q -> Prop,
  q_pred_union P q_pred_full = q_pred_full.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_union, q_pred_full. split.
  - intros _. exact I.
  - intros _. right. exact I.
Qed.

(** Complement laws (require excluded middle) *)
Axiom classic_q : forall P : Prop, P \/ ~ P.

Theorem q_union_complement : forall P : Q -> Prop,
  q_pred_union P (q_pred_complement P) = q_pred_full.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_union, q_pred_complement, q_pred_full. split.
  - intros _. exact I.
  - intros _. apply classic_q.
Qed.

Theorem q_inter_complement : forall P : Q -> Prop,
  q_pred_inter P (q_pred_complement P) = q_pred_empty.
Proof.
  intro P. apply q_pred_extensionality. intro q.
  unfold q_pred_inter, q_pred_complement, q_pred_empty. split.
  - intros [H Hn]. exact (Hn H).
  - intros [].
Qed.

(** Commutativity *)
Theorem q_inter_comm : forall P R : Q -> Prop,
  q_pred_inter P R = q_pred_inter R P.
Proof.
  intros P R. apply q_pred_extensionality. intro q.
  unfold q_pred_inter. split; intros [H1 H2]; split; assumption.
Qed.

Theorem q_union_comm : forall P R : Q -> Prop,
  q_pred_union P R = q_pred_union R P.
Proof.
  intros P R. apply q_pred_extensionality. intro q.
  unfold q_pred_union. split; (intros [H | H]; [right | left]; exact H).
Qed.

(* ================================================================= *)
(** ** Two Equivalent (0,1] Predicates over Q, Proven Equal          *)
(* ================================================================= *)

(** Definition 1: direct bounds *)
Definition q_interval_direct (q : Q) : Prop :=
  0 < q /\ q <= 1.

(** Definition 2: negation style (matches the R version) *)
Definition q_interval_neg (q : Q) : Prop :=
  ~ (q <= 0) /\ q <= 1.

(** Equivalence — proved using Q order properties *)
Lemma q_interval_equiv : forall q : Q,
  q_interval_direct q <-> q_interval_neg q.
Proof.
  intro q. unfold q_interval_direct, q_interval_neg. split.
  - intros [Hlt Hle]. split; [| exact Hle].
    intro Hle0. apply (Qlt_irrefl 0).
    apply Qlt_le_trans with q; assumption.
  - intros [Hnle Hle]. split; [| exact Hle].
    destruct (Qlt_le_dec 0 q) as [H | H].
    + exact H.
    + exfalso. exact (Hnle H).
Qed.

(** Equality — derived from proven Q extensionality *)
Theorem q_interval_eq :
  q_interval_direct = q_interval_neg.
Proof.
  apply q_pred_extensionality.
  exact q_interval_equiv.
Qed.

(* ================================================================= *)
(** ** Connection to the Real-Valued (0,1]                           *)
(* ================================================================= *)

Open Scope R_scope.

(** Helper: Q2R 0 = 0 and Q2R 1 = 1 in R *)
Lemma Q2R_0 : Q2R 0 = 0%R.
Proof. unfold Q2R. simpl. lra. Qed.

Lemma Q2R_1 : Q2R 1 = 1%R.
Proof. unfold Q2R. simpl. lra. Qed.

(** The Q interval predicate agrees with the R interval predicate
    on embedded rationals *)
Theorem q_real_interval_agree : forall q : Q,
  q_in_interval q <-> (0 < Q2R q /\ Q2R q <= 1)%R.
Proof.
  intro q. unfold q_in_interval. split.
  - intros [Hlt Hle]. split.
    + rewrite <- Q2R_0. apply Qlt_Rlt. exact Hlt.
    + rewrite <- Q2R_1. apply Qle_Rle. exact Hle.
  - intros [Hlt Hle]. split.
    + apply Rlt_Qlt. rewrite Q2R_0. exact Hlt.
    + apply Rle_Qle. rewrite Q2R_1. exact Hle.
Qed.
