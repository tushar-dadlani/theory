(** * Predicate Algebra over R with (0,1] Examples *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Require Import IntervalEquiv.
Open Scope R_scope.

(* ================================================================= *)
(** ** General Predicate Algebra Operations                          *)
(* ================================================================= *)

(** The empty predicate — no real number satisfies it *)
Definition pred_empty : R -> Prop := fun _ => False.

(** The full predicate — every real number satisfies it *)
Definition pred_full : R -> Prop := fun _ => True.

(** Complement: everything not in P *)
Definition pred_complement (P : R -> Prop) : R -> Prop :=
  fun x => ~ P x.

(** Intersection: in both P and Q *)
Definition pred_inter (P Q : R -> Prop) : R -> Prop :=
  fun x => P x /\ Q x.

(** Union: in P or Q (or both) *)
Definition pred_union (P Q : R -> Prop) : R -> Prop :=
  fun x => P x \/ Q x.

(* ================================================================= *)
(** ** Core Predicate Algebra Laws (via predicate extensionality)    *)
(* ================================================================= *)

(** Idempotence of intersection: P /\ P = P *)
Theorem inter_idempotent : forall P : R -> Prop,
  pred_inter P P = P.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_inter. split.
  - intros [H _]. exact H.
  - intro H. split; exact H.
Qed.

(** Idempotence of union: P \/ P = P *)
Theorem union_idempotent : forall P : R -> Prop,
  pred_union P P = P.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_union. split.
  - intros [H | H]; exact H.
  - intro H. left. exact H.
Qed.

(** Intersection with full set: P /\ True = P *)
Theorem inter_full_r : forall P : R -> Prop,
  pred_inter P pred_full = P.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_inter, pred_full. split.
  - intros [H _]. exact H.
  - intro H. split; [exact H | exact I].
Qed.

(** Union with empty set: P \/ False = P *)
Theorem union_empty_r : forall P : R -> Prop,
  pred_union P pred_empty = P.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_union, pred_empty. split.
  - intros [H | []]. exact H.
  - intro H. left. exact H.
Qed.

(** Intersection with empty set: P /\ False = False *)
Theorem inter_empty_r : forall P : R -> Prop,
  pred_inter P pred_empty = pred_empty.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_inter, pred_empty. split.
  - intros [_ []].
  - intros [].
Qed.

(** Union with full set: P \/ True = True *)
Theorem union_full_r : forall P : R -> Prop,
  pred_union P pred_full = pred_full.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_union, pred_full. split.
  - intros _. exact I.
  - intros _. right. exact I.
Qed.

(** Union with complement: P \/ ~P = True (excluded middle required) *)
Axiom classic : forall P : Prop, P \/ ~ P.

Theorem union_complement : forall P : R -> Prop,
  pred_union P (pred_complement P) = pred_full.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_union, pred_complement, pred_full. split.
  - intros _. exact I.
  - intros _. apply classic.
Qed.

(** Intersection with complement: P /\ ~P = False *)
Theorem inter_complement : forall P : R -> Prop,
  pred_inter P (pred_complement P) = pred_empty.
Proof.
  intro P. apply predicate_extensionality. intro x.
  unfold pred_inter, pred_complement, pred_empty. split.
  - intros [H Hn]. exact (Hn H).
  - intros [].
Qed.

(** Commutativity of intersection *)
Theorem inter_comm : forall P Q : R -> Prop,
  pred_inter P Q = pred_inter Q P.
Proof.
  intros P Q. apply predicate_extensionality. intro x.
  unfold pred_inter. split; intros [H1 H2]; split; assumption.
Qed.

(** Commutativity of union *)
Theorem union_comm : forall P Q : R -> Prop,
  pred_union P Q = pred_union Q P.
Proof.
  intros P Q. apply predicate_extensionality. intro x.
  unfold pred_union. split; (intros [H | H]; [right | left]; exact H).
Qed.

(* ================================================================= *)
(** ** Concrete Examples with the (0,1] Interval                    *)
(* ================================================================= *)

(** (0,1] intersected with itself is (0,1] *)
Theorem interval_inter_self :
  pred_inter in_interval_conj in_interval_conj = in_interval_conj.
Proof.
  apply inter_idempotent.
Qed.

(** (0,1] union with itself is (0,1] *)
Theorem interval_union_self :
  pred_union in_interval_conj in_interval_conj = in_interval_conj.
Proof.
  apply union_idempotent.
Qed.

(** (0,1] intersected with the full set is (0,1] *)
Theorem interval_inter_full :
  pred_inter in_interval_conj pred_full = in_interval_conj.
Proof.
  apply inter_full_r.
Qed.

(** (0,1] union with its complement is the full set *)
Theorem interval_union_complement :
  pred_union in_interval_conj (pred_complement in_interval_conj) = pred_full.
Proof.
  apply union_complement.
Qed.

(** (0,1] intersected with its complement is empty *)
Theorem interval_inter_complement :
  pred_inter in_interval_conj (pred_complement in_interval_conj) = pred_empty.
Proof.
  apply inter_complement.
Qed.

(** The alternative (0,1] predicate also satisfies the same algebra,
    since it is equal to the original by predicate extensionality *)
Theorem interval_alt_inter_self :
  pred_inter in_interval_alt in_interval_alt = in_interval_alt.
Proof.
  apply inter_idempotent.
Qed.

(** Cross-predicate: intersecting the two equivalent (0,1] definitions
    yields either one, since they are equal *)
Theorem interval_cross_inter :
  pred_inter in_interval_conj in_interval_alt = in_interval_conj.
Proof.
  rewrite interval_predicates_eq.
  apply inter_idempotent.
Qed.
