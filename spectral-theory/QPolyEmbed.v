(* ================================================================= *)
(*  QPolyEmbed.v                                                     *)
(*                                                                    *)
(*  THE EMBEDDING ℤ[X] ↪ ℚ[X] (brick 6, bridge).                   *)
(*                                                                    *)
(*  emb p := map Z2Qc p sends an integer polynomial to a rational     *)
(*  one.  It is a ring homomorphism:                                 *)
(*     emb (p+q) = emb p + emb q,   emb (p·q) = emb p · emb q,        *)
(*     emb (X^n−1) = X^n−1,                                          *)
(*  and evaluation commutes at integer points:                       *)
(*     qeval (emb p) (Z2Qc a) = Z2Qc (eval p a).                     *)
(*  This lets the ℚ[X] squarefreeness/coprimality machinery act on    *)
(*  the (integer) cyclotomic polynomials, and transfer results back.  *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith ZArith.
Import ListNotations.
Require Import IntPoly QPoly QPolyDeriv.
Open Scope Qc_scope.

Definition Z2Qc (z : Z) : Qc := Q2Qc (inject_Z z).

(* --- Z2Qc is a ring homomorphism --- *)
Lemma Q2Qc_mult : forall a b, (Q2Qc a * Q2Qc b) = Q2Qc (a * b).
Proof.
  intros a b; unfold Qcmult; apply Q2Qc_eq_iff.
  change (this (Q2Qc a)) with (Qred a); change (this (Q2Qc b)) with (Qred b).
  rewrite !Qred_correct; reflexivity.
Qed.

Lemma Z2Qc_0 : Z2Qc 0 = 0.
Proof. reflexivity. Qed.

Lemma Z2Qc_1 : Z2Qc 1 = 1.
Proof. reflexivity. Qed.

Lemma Z2Qc_add : forall a b, Z2Qc (a + b) = Z2Qc a + Z2Qc b.
Proof.
  intros a b; unfold Z2Qc; rewrite Q2Qc_plus; apply Q2Qc_eq_iff.
  rewrite inject_Z_plus; reflexivity.
Qed.

Lemma Z2Qc_mul : forall a b, Z2Qc (a * b) = Z2Qc a * Z2Qc b.
Proof.
  intros a b; unfold Z2Qc; rewrite Q2Qc_mult; apply Q2Qc_eq_iff.
  rewrite inject_Z_mult; reflexivity.
Qed.

Lemma Z2Qc_opp : forall a, Z2Qc (- a) = - Z2Qc a.
Proof.
  intro a; assert (H : Z2Qc (- a) + Z2Qc a = 0)
    by (rewrite <- Z2Qc_add; replace (- a + a)%Z with 0%Z by ring; apply Z2Qc_0).
  transitivity (Z2Qc (- a) + Z2Qc a + (- Z2Qc a)); [ ring | rewrite H; ring ].
Qed.

Lemma Z2Qc_inj : forall a b, Z2Qc a = Z2Qc b -> a = b.
Proof.
  intros a b H; unfold Z2Qc in H; apply Q2Qc_eq_iff in H.
  unfold Qeq in H; simpl in H; lia.
Qed.

(* --- the embedding of polynomials --- *)
Definition emb (p : poly) : qpoly := map Z2Qc p.

Lemma emb_padd : forall p q, emb (padd p q) = qadd (emb p) (emb q).
Proof.
  induction p as [|a p IH]; intros [|b q]; simpl; try reflexivity.
  rewrite Z2Qc_add, IH; reflexivity.
Qed.

Lemma emb_pscale : forall c p, emb (pscale c p) = qscale (Z2Qc c) (emb p).
Proof.
  intros c p; induction p as [|a p IH]; simpl; [ reflexivity | ].
  unfold emb, pscale, qscale in *; simpl; rewrite Z2Qc_mul, IH; reflexivity.
Qed.

Lemma emb_cons0 : forall p, emb (0%Z :: p) = 0 :: emb p.
Proof. intro p; unfold emb; simpl; rewrite Z2Qc_0; reflexivity. Qed.

Lemma emb_pmul : forall p q, emb (pmul p q) = qmul (emb p) (emb q).
Proof.
  induction p as [|a p IH]; intros q; simpl; [ reflexivity | ].
  rewrite emb_padd, emb_pscale, emb_cons0, IH; reflexivity.
Qed.

Lemma emb_pmonom : forall n, emb (pmonom n) = qmonom n.
Proof.
  induction n as [|n IH]; [ reflexivity | ].
  cbn [pmonom qmonom]; rewrite emb_cons0, IH; reflexivity.
Qed.

Lemma emb_Xn1 : forall n, emb (Xn1 n) = qXn1 n.
Proof.
  intro n; unfold Xn1, qXn1; rewrite emb_padd, emb_pmonom; reflexivity.
Qed.

(* --- evaluation commutes at integer points --- *)
Lemma qeval_emb : forall p a, qeval (emb p) (Z2Qc a) = Z2Qc (eval p a).
Proof.
  induction p as [|c p IH]; intro a; [ reflexivity | ].
  cbn [emb map qeval eval]; rewrite IH, <- Z2Qc_mul, <- Z2Qc_add; reflexivity.
Qed.

Print Assumptions emb_pmul.
Print Assumptions qeval_emb.

(* ================================================================= *)
(*  END QPolyEmbed.v                                                 *)
(*  The ring homomorphism ℤ[X] ↪ ℚ[X], with evaluation commuting at  *)
(*  integer points.  Closed under the global context (axiom-free).   *)
(* ================================================================= *)
