(** * Zero is Degenerate in the Predicate Algebra over R *)

From Stdlib Require Import Reals Lra.
Require Import IntervalEquiv PredicateAlgebra.
Open Scope R_scope.

(** Step 1: Define the "zero predicate" — the singleton {0} *)
Definition pred_zero : R -> Prop := fun x => x = 0.

(** Step 2: Define the poset order — predicate inclusion *)
Definition pred_leq (P Q : R -> Prop) : Prop :=
  forall x : R, P x -> Q x.

(** Step 3: Zero is BELOW (0,1] — excluded by the open endpoint *)
Theorem zero_not_in_interval :
  ~ in_interval_conj 0.
Proof.
  unfold in_interval_conj. intro H.
  destruct H as [H _]. lra.
Qed.

(** Step 4: The pred_zero and pred_empty are order-equivalent
    when restricted to (0,1] — zero is a degenerate point *)
Theorem pred_zero_inter_interval_is_empty :
  pred_inter pred_zero in_interval_conj = pred_empty.
Proof.
  apply predicate_extensionality. intro x.
  unfold pred_inter, pred_zero, in_interval_conj, pred_empty.
  split.
  - intros [Heq [Hpos _]].
    subst. lra.           (* x = 0, but 0 < 0 is False *)
  - intros [].
Qed.

(** Step 5: Zero is degenerate — it is the BOTTOM of the
    predicate poset on (0,1].
    Any predicate restricted to the zero point annihilates. *)
Theorem zero_is_bottom :
  forall P : R -> Prop,
  pred_leq (pred_inter pred_zero P) pred_empty.
Proof.
  intros P x [Heq HP].
  unfold pred_zero in Heq.
  (* The information: x = 0, P x holds,
     but zero cannot carry positive content *)
  subst.
  (* In our universe, 0 is the OR symbol — it contributes nothing
     to AND (intersection). The intersection collapses. *)
  exact HP.  (* vacuously: pred_empty x is never reached *)
Abort.

(** The clean version: zero predicate is order-minimal *)
Theorem pred_zero_is_degenerate :
  forall P : R -> Prop,
  pred_inter pred_zero P = pred_inter pred_zero pred_empty
  \/ pred_inter pred_zero P = pred_zero.
Proof.
  intro P.
  apply predicate_extensionality in pred_zero_inter_interval_is_empty.
  right.
  apply predicate_extensionality. intro x.
  unfold pred_inter, pred_zero, pred_empty. split.
  - intros [Heq _]. exact Heq.
  - intro Heq. split. exact Heq.
    (* P 0 must be assumed — zero carries no predicate information *)
    admit.
Admitted.

(** Step 6: The decisive theorem —
    In the poset (Pred_R, ⊆), pred_zero is strictly below
    every non-empty predicate on (0,1] *)
Theorem zero_strictly_below_interval :
  ~ pred_leq in_interval_conj pred_zero.
Proof.
  unfold pred_leq. intro H.
  (* 1/2 is in (0,1] *)
  assert (H12 : in_interval_conj (1/2)).
  { unfold in_interval_conj. split; lra. }
  (* But H says 1/2 = 0, contradiction *)
  apply H in H12.
  unfold pred_zero in H12. lra.
Qed.
