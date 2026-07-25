(* ================================================================= *)
(*  PolyMonic.v                                                      *)
(*                                                                    *)
(*  MULTIPLICATION ↔ COEFFICIENTS in ℤ[X], and:                     *)
(*                                                                    *)
(*      the product of two MONIC polynomials is MONIC.               *)
(*                                                                    *)
(*  Establishes the convolution formula                              *)
(*      coeff (p·q) i = Σ_{j=0}^{i} coeff p j · coeff q (i−j),        *)
(*  the degree bound  deg(p·q) ≤ deg p + deg q, and the leading      *)
(*  coefficient  coeff (p·q) (dp+dq) = coeff p dp · coeff q dq.       *)
(*  Hence `monic_pmul`.  This is what makes the cyclotomic divisor    *)
(*  ∏_{d|n,d<n} Φ_d monic, so that PolyDiv.monic_div can define Φ_n. *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Require Import IntPoly PolyDiv.
Open Scope Z_scope.

(* the discrete convolution Σ_{j=0}^{i} coeff p j · coeff q (i−j) *)
Definition conv (p q : poly) (i : nat) : Z :=
  fold_right Z.add 0 (map (fun j => coeff p j * coeff q (i - j)) (seq 0 (S i))).

(* ----------------------------------------------------------------- *)
(*  Small folding helpers                                            *)
(* ----------------------------------------------------------------- *)
Lemma fold_add_zero : forall (l : list nat) (f : nat -> Z),
  (forall j, In j l -> f j = 0) -> fold_right Z.add 0 (map f l) = 0.
Proof.
  induction l as [|a l IH]; intros f H; simpl; [ reflexivity | ].
  rewrite H by (left; reflexivity).
  rewrite IH by (intros j Hj; apply H; right; exact Hj); ring.
Qed.

Lemma fold_app : forall l1 l2 : list Z,
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma coeff_nil : forall j, coeff [] j = 0.
Proof. intro j; unfold coeff; apply nth_overflow; simpl; lia. Qed.

(* ----------------------------------------------------------------- *)
(*  coeff of a product is the convolution                            *)
(* ----------------------------------------------------------------- *)
Lemma conv_cons : forall a p q i,
  conv (a :: p) q i
  = a * coeff q i + (match i with O => 0 | S i' => conv p q i' end).
Proof.
  intros a p q i; unfold conv at 1.
  cbn [seq map fold_right].
  replace (coeff (a :: p) 0) with a by (unfold coeff; reflexivity).
  replace (i - 0)%nat with i by lia.
  f_equal.
  change (seq 1 i) with (seq (S 0) i); rewrite <- seq_shift, map_map.
  destruct i as [|i']; [ reflexivity | ].
  unfold conv; reflexivity.
Qed.

Lemma coeff_pmul : forall p q i, coeff (pmul p q) i = conv p q i.
Proof.
  induction p as [|a p IH]; intros q i.
  - cbn [pmul]; rewrite coeff_nil; symmetry.
    unfold conv; apply fold_add_zero; intros j _; rewrite coeff_nil; ring.
  - cbn [pmul]; rewrite coeff_padd, conv_cons, coeff_pscale.
    destruct i as [|i'].
    + unfold coeff; simpl; ring.
    + replace (coeff (0 :: pmul p q) (S i')) with (coeff (pmul p q) i')
        by (unfold coeff; reflexivity).
      rewrite IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Degree bound and leading coefficient of a product               *)
(* ----------------------------------------------------------------- *)
Lemma degle_pmul : forall p q dp dq,
  degle p dp -> degle q dq -> degle (pmul p q) (dp + dq).
Proof.
  intros p q dp dq Hp Hq i Hi.
  rewrite coeff_pmul; unfold conv; apply fold_add_zero.
  intros j Hj; rewrite in_seq in Hj.
  destruct (le_lt_dec j dp) as [Hjdp | Hjdp].
  - replace (coeff q (i - j)) with 0 by (symmetry; apply Hq; lia); ring.
  - replace (coeff p j) with 0 by (symmetry; apply Hp; lia); ring.
Qed.

Lemma coeff_pmul_top : forall p q dp dq,
  degle p dp -> degle q dq ->
  coeff (pmul p q) (dp + dq) = coeff p dp * coeff q dq.
Proof.
  intros p q dp dq Hp Hq; rewrite coeff_pmul; unfold conv.
  replace (S (dp + dq)) with (dp + S dq)%nat by lia.
  rewrite seq_app, map_app, fold_app.
  replace (0 + dp)%nat with dp by lia.
  rewrite (fold_add_zero (seq 0 dp)).
  2:{ intros j Hj; rewrite in_seq in Hj.
      replace (coeff q (dp + dq - j)) with 0 by (symmetry; apply Hq; lia); ring. }
  cbn [seq map fold_right].
  rewrite (fold_add_zero (seq (S dp) dq)).
  2:{ intros j Hj; rewrite in_seq in Hj.
      replace (coeff p j) with 0 by (symmetry; apply Hp; lia); ring. }
  replace (dp + dq - dp)%nat with dq by lia; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE PRODUCT OF MONIC POLYNOMIALS IS MONIC                        *)
(* ----------------------------------------------------------------- *)
Theorem monic_pmul : forall p dp q dq,
  monic p dp -> monic q dq -> monic (pmul p q) (dp + dq).
Proof.
  intros p dp q dq [Hlp Hdp] [Hlq Hdq]; split.
  - rewrite coeff_pmul_top by assumption; rewrite Hlp, Hlq; ring.
  - apply degle_pmul; assumption.
Qed.

Print Assumptions monic_pmul.

(* ================================================================= *)
(*  END PolyMonic.v                                                  *)
(*  coeff of a product = convolution; deg(p·q) ≤ deg p + deg q;       *)
(*  leading coeff multiplies; hence the product of monics is monic.  *)
(*  Makes ∏_{d|n,d<n} Φ_d monic for the Φ_n definition.  Closed under *)
(*  the global context (axiom-free).                                 *)
(* ================================================================= *)
