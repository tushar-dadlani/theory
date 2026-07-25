(* ================================================================= *)
(*  QPoly.v                                                          *)
(*                                                                    *)
(*  POLYNOMIALS OVER ℚ (as list Qc), the foundation of the ℚ[X]      *)
(*  layer needed for ∏_{d|n} Φ_d = X^n − 1.                          *)
(*                                                                    *)
(*  Over ℤ[X] the cyclotomic factors are NOT Bézout-coprime          *)
(*  (−Φ_1 + Φ_2 = 2, never 1), so the product identity is out of      *)
(*  reach there.  Over ℚ[X] — a field-coefficient PID — distinct      *)
(*  cyclotomics ARE coprime, and ∏Φ_d | X^n−1; since the divisor is   *)
(*  monic-integer the quotient stays integer, transferring the        *)
(*  identity back to ℤ.  We use `Qc` (canonical rationals) so that    *)
(*  equality is Leibniz `=` and `ring`/`field` apply directly.        *)
(*                                                                    *)
(*  This brick: the ring operations with the EVALUATION HOMOMORPHISM, *)
(*  plus coefficients, degree bound, and leading/monic notions.      *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Open Scope Qc_scope.

Definition qpoly := list Qc.

(* Horner evaluation *)
Fixpoint qeval (p : qpoly) (x : Qc) : Qc :=
  match p with
  | [] => 0
  | c :: p' => c + x * qeval p' x
  end.

(* ----------------------------------------------------------------- *)
(*  Addition, scaling, multiplication                               *)
(* ----------------------------------------------------------------- *)
Fixpoint qadd (p q : qpoly) : qpoly :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b) :: qadd p' q'
  end.

Lemma qeval_add : forall p q x, qeval (qadd p q) x = qeval p x + qeval q x.
Proof.
  induction p as [|a p IH]; intros [|b q] x; simpl; try ring.
  rewrite IH; ring.
Qed.

Definition qscale (c : Qc) (p : qpoly) : qpoly := map (Qcmult c) p.

Lemma qeval_scale : forall c p x, qeval (qscale c p) x = c * qeval p x.
Proof.
  intros c p x; induction p as [|a p IH]; simpl; [ ring | ].
  change (map (Qcmult c) p) with (qscale c p); rewrite IH; ring.
Qed.

Fixpoint qmul (p q : qpoly) : qpoly :=
  match p with
  | [] => []
  | a :: p' => qadd (qscale a q) (0 :: qmul p' q)
  end.

Lemma qeval_mul : forall p q x, qeval (qmul p q) x = qeval p x * qeval q x.
Proof.
  induction p as [|a p IH]; intros q x; simpl; [ ring | ].
  rewrite qeval_add, qeval_scale; simpl; rewrite IH; ring.
Qed.

(* negation / subtraction *)
Definition qneg (p : qpoly) : qpoly := map Qcopp p.
Definition qsub (p q : qpoly) : qpoly := qadd p (qneg q).

Lemma qeval_neg : forall p x, qeval (qneg p) x = - qeval p x.
Proof.
  intros p x; induction p as [|a p IH]; simpl; [ ring | ].
  change (map Qcopp p) with (qneg p); rewrite IH; ring.
Qed.

Lemma qeval_sub : forall p q x, qeval (qsub p q) x = qeval p x - qeval q x.
Proof. intros; unfold qsub; rewrite qeval_add, qeval_neg; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  Constants, monomials, X^n − 1                                    *)
(* ----------------------------------------------------------------- *)
Definition qconst (c : Qc) : qpoly := [c].
Lemma qeval_const : forall c x, qeval (qconst c) x = c.
Proof. intros; simpl; ring. Qed.

Fixpoint qmonom (n : nat) : qpoly :=
  match n with O => [1] | S k => 0 :: qmonom k end.

Lemma qeval_monom : forall n x, qeval (qmonom n) x = x ^ n.
Proof.
  induction n as [|n IH]; intro x; simpl; [ ring | rewrite IH; ring ].
Qed.

Definition qXn1 (n : nat) : qpoly := qadd (qmonom n) (qconst (Qcopp 1)).
Lemma qeval_Xn1 : forall n x, qeval (qXn1 n) x = x ^ n - 1.
Proof.
  intros; unfold qXn1; rewrite qeval_add, qeval_monom, qeval_const; ring.
Qed.

(* shift by X^k *)
Definition qshiftk (k : nat) (p : qpoly) : qpoly := repeat 0 k ++ p.
Lemma qeval_shiftk : forall k p x, qeval (qshiftk k p) x = x ^ k * qeval p x.
Proof.
  induction k as [|k IH]; intros p x.
  - unfold qshiftk; cbn [repeat app]; simpl; ring.
  - unfold qshiftk; cbn [repeat app qeval].
    change (repeat 0 k ++ p) with (qshiftk k p); rewrite IH; simpl; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Coefficients, degree bound, leading/monic                       *)
(* ----------------------------------------------------------------- *)
Definition qcoeff (p : qpoly) (i : nat) : Qc := nth i p 0.

Definition qdegle (p : qpoly) (n : nat) : Prop :=
  forall i, (n < i)%nat -> qcoeff p i = 0.

Lemma qnth_repeat0 : forall k i, nth i (repeat 0 k) 0 = 0.
Proof. intros k; induction k as [|k IH]; intros [|i]; simpl; auto. Qed.

Lemma qcoeff_add : forall p q i, qcoeff (qadd p q) i = qcoeff p i + qcoeff q i.
Proof.
  unfold qcoeff; induction p as [|a p IH]; intros q i.
  - cbn [qadd]; destruct i; simpl; ring.
  - destruct q as [|b q]; simpl.
    + destruct i; simpl; ring.
    + destruct i; simpl; [ ring | apply IH ].
Qed.

Lemma qcoeff_scale : forall c p i, qcoeff (qscale c p) i = c * qcoeff p i.
Proof.
  intros c p i; unfold qcoeff, qscale.
  replace 0 with (Qcmult c 0) at 1 by ring.
  rewrite map_nth; reflexivity.
Qed.

Lemma qcoeff_neg : forall p i, qcoeff (qneg p) i = - qcoeff p i.
Proof.
  intros p i; unfold qcoeff, qneg.
  replace 0 with (Qcopp 0) at 1 by ring.
  rewrite map_nth; reflexivity.
Qed.

Lemma qcoeff_sub : forall p q i, qcoeff (qsub p q) i = qcoeff p i - qcoeff q i.
Proof. intros; unfold qsub; rewrite qcoeff_add, qcoeff_neg; ring. Qed.

Lemma qcoeff_shiftk : forall k p i,
  qcoeff (qshiftk k p) i = if (i <? k)%nat then 0 else qcoeff p (i - k).
Proof.
  intros k p i; unfold qcoeff, qshiftk.
  destruct (Nat.ltb_spec i k) as [Hlt | Hge].
  - rewrite app_nth1 by (rewrite repeat_length; lia); apply qnth_repeat0.
  - rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length; reflexivity.
Qed.

Lemma qcoeff_nil : forall i, qcoeff [] i = 0.
Proof. intro i; unfold qcoeff; apply nth_overflow; simpl; lia. Qed.

Definition qmonic (g : qpoly) (d : nat) : Prop := qcoeff g d = 1 /\ qdegle g d.

Print Assumptions qeval_mul.

(* ================================================================= *)
(*  END QPoly.v                                                      *)
(*  ℚ[X] as list Qc: ring operations with the evaluation             *)
(*  homomorphism, coefficients, degree bound, monic-ness.  The       *)
(*  foundation for ℚ[X] division/gcd/squarefreeness → the cyclotomic *)
(*  product identity.  Closed under the global context (axiom-free). *)
(* ================================================================= *)
