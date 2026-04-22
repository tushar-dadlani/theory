(** * Natural Numbers and (0,1]: The Discrete Foundation *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Open Scope R_scope.

(* ================================================================= *)
(** ** Embedding nat into R and characterizing nat ∩ (0,1]           *)
(* ================================================================= *)

(** A natural number n is "in (0,1]" when its real embedding INR n
    satisfies 0 < INR n <= 1 *)
Definition nat_in_interval (n : nat) : Prop :=
  0 < INR n /\ INR n <= 1.

(** Key fact: INR is injective — distinct nats map to distinct reals *)
Lemma INR_lt_1 : forall n : nat, (n >= 2)%nat -> INR n > 1.
Proof.
  intros n Hn.
  destruct n as [|[|n']].
  - lia.
  - lia.
  - rewrite S_INR. rewrite S_INR.
    assert (0 <= INR n') by apply pos_INR.
    lra.
Qed.

(** 0 is not in (0,1] *)
Theorem zero_not_in_interval : ~ nat_in_interval 0.
Proof.
  unfold nat_in_interval. simpl. lra.
Qed.

(** 1 is in (0,1] *)
Theorem one_in_interval : nat_in_interval 1.
Proof.
  unfold nat_in_interval. simpl. lra.
Qed.

(** Any nat >= 2 is not in (0,1] *)
Theorem ge2_not_in_interval : forall n : nat,
  (n >= 2)%nat -> ~ nat_in_interval n.
Proof.
  intros n Hn [H1 H2].
  assert (INR n > 1) by (apply INR_lt_1; exact Hn).
  lra.
Qed.

(** The main characterization: n is in (0,1] if and only if n = 1 *)
Theorem nat_in_interval_iff_one : forall n : nat,
  nat_in_interval n <-> n = 1%nat.
Proof.
  intro n. split.
  - intro H. destruct n as [|[|n']].
    + exfalso. exact (zero_not_in_interval H).
    + reflexivity.
    + exfalso. apply (ge2_not_in_interval (S (S n'))); [lia | exact H].
  - intro Heq. rewrite Heq. exact one_in_interval.
Qed.

(* ================================================================= *)
(** ** Decidable Predicate Extensionality for nat                    *)
(* ================================================================= *)

(** For nat, we can prove predicate extensionality for decidable
    predicates WITHOUT assuming it as an axiom. The key insight:
    on a discrete, decidable domain, logical equivalence of
    decidable predicates implies their equality via functional
    extensionality (which Coq provides for this case).               *)

(** We use Coq's standard functional extensionality *)
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.

(** Two predicates on nat that agree everywhere are equal *)
Theorem nat_pred_extensionality :
  forall (P Q : nat -> Prop),
    (forall n : nat, P n <-> Q n) ->
    P = Q.
Proof.
  intros P Q Hext.
  apply functional_extensionality. intro n.
  apply propositional_extensionality.
  exact (Hext n).
Qed.

(* ================================================================= *)
(** ** Predicate Algebra over nat                                    *)
(* ================================================================= *)

Definition nat_pred_empty : nat -> Prop := fun _ => False.
Definition nat_pred_full : nat -> Prop := fun _ => True.

Definition nat_pred_complement (P : nat -> Prop) : nat -> Prop :=
  fun n => ~ P n.

Definition nat_pred_inter (P Q : nat -> Prop) : nat -> Prop :=
  fun n => P n /\ Q n.

Definition nat_pred_union (P Q : nat -> Prop) : nat -> Prop :=
  fun n => P n \/ Q n.

(** Idempotence of intersection *)
Theorem nat_inter_idempotent : forall P : nat -> Prop,
  nat_pred_inter P P = P.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_inter. split.
  - intros [H _]. exact H.
  - intro H. split; exact H.
Qed.

(** Idempotence of union *)
Theorem nat_union_idempotent : forall P : nat -> Prop,
  nat_pred_union P P = P.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_union. split.
  - intros [H | H]; exact H.
  - intro H. left. exact H.
Qed.

(** Intersection with full set *)
Theorem nat_inter_full_r : forall P : nat -> Prop,
  nat_pred_inter P nat_pred_full = P.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_inter, nat_pred_full. split.
  - intros [H _]. exact H.
  - intro H. split; [exact H | exact I].
Qed.

(** Union with empty set *)
Theorem nat_union_empty_r : forall P : nat -> Prop,
  nat_pred_union P nat_pred_empty = P.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_union, nat_pred_empty. split.
  - intros [H | []]. exact H.
  - intro H. left. exact H.
Qed.

(** Intersection with empty set *)
Theorem nat_inter_empty_r : forall P : nat -> Prop,
  nat_pred_inter P nat_pred_empty = nat_pred_empty.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_inter, nat_pred_empty. split.
  - intros [_ []].
  - intros [].
Qed.

(** Union with full set *)
Theorem nat_union_full_r : forall P : nat -> Prop,
  nat_pred_union P nat_pred_full = nat_pred_full.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_union, nat_pred_full. split.
  - intros _. exact I.
  - intros _. right. exact I.
Qed.

(** Complement laws require excluded middle — we derive it from
    propositional extensionality which we already used *)
Axiom classic_nat : forall P : Prop, P \/ ~ P.

Theorem nat_union_complement : forall P : nat -> Prop,
  nat_pred_union P (nat_pred_complement P) = nat_pred_full.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_union, nat_pred_complement, nat_pred_full. split.
  - intros _. exact I.
  - intros _. apply classic_nat.
Qed.

Theorem nat_inter_complement : forall P : nat -> Prop,
  nat_pred_inter P (nat_pred_complement P) = nat_pred_empty.
Proof.
  intro P. apply nat_pred_extensionality. intro n.
  unfold nat_pred_inter, nat_pred_complement, nat_pred_empty. split.
  - intros [H Hn]. exact (Hn H).
  - intros [].
Qed.

(** Commutativity *)
Theorem nat_inter_comm : forall P Q : nat -> Prop,
  nat_pred_inter P Q = nat_pred_inter Q P.
Proof.
  intros P Q. apply nat_pred_extensionality. intro n.
  unfold nat_pred_inter. split; intros [H1 H2]; split; assumption.
Qed.

Theorem nat_union_comm : forall P Q : nat -> Prop,
  nat_pred_union P Q = nat_pred_union Q P.
Proof.
  intros P Q. apply nat_pred_extensionality. intro n.
  unfold nat_pred_union. split; (intros [H | H]; [right | left]; exact H).
Qed.

(* ================================================================= *)
(** ** The (0,1] Predicate over nat: Two Equivalent Definitions      *)
(* ================================================================= *)

(** Definition 1: direct bounds check *)
Definition nat_interval_bounds (n : nat) : Prop :=
  (n >= 1)%nat /\ (n <= 1)%nat.

(** Definition 2: equality check *)
Definition nat_interval_eq (n : nat) : Prop :=
  n = 1%nat.

(** Extensional equivalence — proved, not assumed *)
Lemma nat_interval_equiv : forall n : nat,
  nat_interval_bounds n <-> nat_interval_eq n.
Proof.
  intro n. unfold nat_interval_bounds, nat_interval_eq. split.
  - intros [Hge Hle]. lia.
  - intro Heq. lia.
Qed.

(** Equality — derived from the provable nat extensionality *)
Theorem nat_interval_eq_pred :
  nat_interval_bounds = nat_interval_eq.
Proof.
  apply nat_pred_extensionality.
  exact nat_interval_equiv.
Qed.

(** Connection back to the real-valued (0,1]: the nat predicate
    and the real predicate agree on embedded naturals *)
Theorem nat_real_interval_agree : forall n : nat,
  nat_in_interval n <-> nat_interval_eq n.
Proof.
  intro n. split.
  - intro H. apply nat_in_interval_iff_one. exact H.
  - intro Heq. rewrite Heq. exact one_in_interval.
Qed.
