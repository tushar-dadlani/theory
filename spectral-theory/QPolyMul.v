(* ================================================================= *)
(*  QPolyMul.v                                                       *)
(*                                                                    *)
(*  MULTIPLICATION ↔ COEFFICIENTS in ℚ[X] (brick 5c, degree part):  *)
(*  the ℚ port of PolyMonic.  Convolution formula for coeff(p·q),    *)
(*  the degree bound deg(p·q) ≤ deg p + deg q, and the leading        *)
(*  coefficient coeff(p·q)(dp+dq) = coeff p dp · coeff q dq.  With    *)
(*  QPolyDeg this gives deg(p·q) = deg p + deg q, hence a divisor of  *)
(*  a nonzero constant is itself constant — the last step of the      *)
(*  squarefreeness argument.  AXIOM-FREE.                            *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv.
Open Scope Qc_scope.

Definition qconv (p q : qpoly) (i : nat) : Qc :=
  fold_right Qcplus 0 (map (fun j => qcoeff p j * qcoeff q (i - j)) (seq 0 (S i))).

Lemma qcoeff_nil : forall j, qcoeff [] j = 0.
Proof. intro j; unfold qcoeff; apply nth_overflow; simpl; lia. Qed.

Lemma qfold_add_zero : forall (l : list nat) (f : nat -> Qc),
  (forall j, In j l -> f j = 0) -> fold_right Qcplus 0 (map f l) = 0.
Proof.
  induction l as [|a l IH]; intros f H; simpl; [ reflexivity | ].
  rewrite H by (left; reflexivity).
  rewrite IH by (intros j Hj; apply H; right; exact Hj); ring.
Qed.

Lemma qfold_app : forall l1 l2 : list Qc,
  fold_right Qcplus 0 (l1 ++ l2) = fold_right Qcplus 0 l1 + fold_right Qcplus 0 l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma qconv_cons : forall a p q i,
  qconv (a :: p) q i
  = a * qcoeff q i + (match i with O => 0 | S i' => qconv p q i' end).
Proof.
  intros a p q i; unfold qconv at 1.
  cbn [seq map fold_right].
  replace (qcoeff (a :: p) 0) with a by (unfold qcoeff; reflexivity).
  replace (i - 0)%nat with i by lia.
  f_equal.
  change (seq 1 i) with (seq (S 0) i); rewrite <- seq_shift, map_map.
  destruct i as [|i']; [ reflexivity | ].
  unfold qconv; reflexivity.
Qed.

Lemma qcoeff_qmul : forall p q i, qcoeff (qmul p q) i = qconv p q i.
Proof.
  induction p as [|a p IH]; intros q i.
  - cbn [qmul]; rewrite qcoeff_nil; symmetry.
    unfold qconv; apply qfold_add_zero; intros j _; rewrite qcoeff_nil; ring.
  - cbn [qmul]; rewrite qcoeff_add, qconv_cons, qcoeff_scale.
    destruct i as [|i'].
    + unfold qcoeff; simpl; ring.
    + replace (qcoeff (0 :: qmul p q) (S i')) with (qcoeff (qmul p q) i')
        by (unfold qcoeff; reflexivity).
      rewrite IH; ring.
Qed.

Lemma qdegle_qmul : forall p q dp dq,
  qdegle p dp -> qdegle q dq -> qdegle (qmul p q) (dp + dq).
Proof.
  intros p q dp dq Hp Hq i Hi.
  rewrite qcoeff_qmul; unfold qconv; apply qfold_add_zero.
  intros j Hj; rewrite in_seq in Hj.
  destruct (le_lt_dec j dp) as [Hjdp | Hjdp].
  - replace (qcoeff q (i - j)) with 0 by (symmetry; apply Hq; lia); ring.
  - replace (qcoeff p j) with 0 by (symmetry; apply Hp; lia); ring.
Qed.

Lemma qcoeff_qmul_top : forall p q dp dq,
  qdegle p dp -> qdegle q dq ->
  qcoeff (qmul p q) (dp + dq) = qcoeff p dp * qcoeff q dq.
Proof.
  intros p q dp dq Hp Hq; rewrite qcoeff_qmul; unfold qconv.
  replace (S (dp + dq)) with (dp + S dq)%nat by lia.
  rewrite seq_app, map_app, qfold_app.
  replace (0 + dp)%nat with dp by lia.
  rewrite (qfold_add_zero (seq 0 dp)).
  2:{ intros j Hj; rewrite in_seq in Hj.
      replace (qcoeff q (dp + dq - j)) with 0 by (symmetry; apply Hq; lia); ring. }
  cbn [seq map fold_right].
  rewrite (qfold_add_zero (seq (S dp) dq)).
  2:{ intros j Hj; rewrite in_seq in Hj.
      replace (qcoeff p j) with 0 by (symmetry; apply Hp; lia); ring. }
  replace (dp + dq - dp)%nat with dq by lia; ring.
Qed.

Print Assumptions qcoeff_qmul_top.

(* ================================================================= *)
(*  END QPolyMul.v                                                   *)
(*  Convolution / degree bound / leading coefficient of a product in *)
(*  ℚ[X].  Closed under the global context (axiom-free).             *)
(* ================================================================= *)
