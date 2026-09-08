(* ================================================================= *)
(*  HyperbolaDouble.v  --  RS Bt X is the double sum hyper_split acts *)
(*  on.  This is the joint that connects the ARITHMETIC side          *)
(*  (f = 1 * chi, a Z-valued divisor sum) to the COMBINATORIAL side   *)
(*  (HyperbolaSplit's rectangle-with-indicators).                      *)
(*                                                                    *)
(*    RS Bt X  =  RS (fun d => ach d * RS bh (X / d)) X               *)
(*                                                                    *)
(*  with ach d = chi(d)/sqrt d and bh e = 1/sqrt e.                    *)
(*                                                                    *)
(*  Three things have to line up.  (i) Totient.divisors n is LITERALLY *)
(*  filter (fun d => n mod d =? 0) (seq 1 n), the same indicator       *)
(*  hyper_iter uses, so sumf_filter converts one to the other with no  *)
(*  permutation argument.  (ii) IZR has to cross the sum, which is an  *)
(*  induction on seq 1 n.  (iii) sqrt d * sqrt (n/d) = sqrt n, which   *)
(*  holds EXACTLY when d | n -- this is why the weight splits as       *)
(*  chi(d)/sqrt d times 1/sqrt e with no leftover factor, and it is    *)
(*  the reason 1/sqrt n was the right thing to sum in the first place. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory List.
Require Import HopfGroupTensor Totient DirichletConv CRealChar CRealCharPos
        HyperbolaSplit HyperbolaLower.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- IZR across a sumf over seq 1 n.                          *)
(* ----------------------------------------------------------------- *)

Lemma IZR_sumf_seq : forall (G : nat -> Z) n,
  IZR (sumf (seq 1 n) G) = RS (fun d => IZR (G d)) n.
Proof.
  intros G n. induction n as [| n IH]; [ reflexivity | ].
  rewrite seq_S, sumf_app, plus_IZR, IH.
  replace (1 + n)%nat with (S n) by lia.
  cbn [RS]. cbn [sumf fold_right]. rewrite Z.add_0_r. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- sqrt splits exactly on divisors.                         *)
(* ----------------------------------------------------------------- *)

Lemma sqrt_div_mul : forall n d, (1 <= d)%nat -> (n mod d = 0)%nat ->
  sqrt (INR d) * sqrt (INR (n / d)) = sqrt (INR n).
Proof.
  intros n d Hd Hm.
  assert (Hn : n = (d * (n / d))%nat).
  { pose proof (Nat.div_mod_eq n d) as HE. lia. }
  transitivity (sqrt (INR (d * (n / d))%nat)).
  - rewrite mult_INR, sqrt_mult by apply pos_INR. reflexivity.
  - rewrite <- Hn. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the identity.                                           *)
(* ----------------------------------------------------------------- *)

Section Double.

Variable p g A : nat.

Definition ach (d : nat) : R := IZR (chz p g A d) / sqrt (INR d).
Definition bh (e : nat) : R := / sqrt (INR e).

Lemma fchi_RS : forall n, (1 <= n)%nat ->
  IZR (fchi p g A n)
  = RS (fun d => if (n mod d =? 0)%nat then IZR (chz p g A d) else 0) n.
Proof.
  intros n Hn.
  rewrite (fchi_div_sum p g A n Hn).
  unfold Totient.divisors. rewrite <- sumf_filter.
  rewrite (IZR_sumf_seq (fun d => if (n mod d =? 0)%nat then chz p g A d else 0%Z) n).
  apply RS_ext. intros d Hd.
  destruct (n mod d =? 0)%nat; reflexivity.
Qed.

Lemma sqrtn_pos : forall n, (1 <= n)%nat -> 0 < sqrt (INR n).
Proof.
  intros n Hn. apply sqrt_lt_R0.
  apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ].
Qed.

Lemma Bt_inner : forall n X, (1 <= n <= X)%nat ->
  Bt p g A n
  = RS (fun d => if (n mod d =? 0)%nat then ach d * bh (n / d)%nat else 0) X.
Proof.
  intros n X Hn.
  rewrite (RS_stab _ n X (proj2 Hn)).
  2: { intros d Hd.
       replace (n mod d =? 0)%nat with false; [ reflexivity | ].
       symmetry. apply Nat.eqb_neq. rewrite Nat.mod_small by lia. lia. }
  transitivity (RS (fun d => / sqrt (INR n)
                    * (if (n mod d =? 0)%nat then IZR (chz p g A d) else 0)) n).
  - rewrite RS_scal, <- (fchi_RS n (proj1 Hn)).
    unfold Bt, Rdiv. ring.
  - apply RS_ext. intros d Hd.
    destruct (n mod d =? 0)%nat eqn:E; [ | ring ].
    apply Nat.eqb_eq in E.
    assert (Hnd : (1 <= n / d)%nat).
    { pose proof (Nat.div_mod_eq n d) as HE. nia. }
    unfold ach, bh, Rdiv.
    assert (Hs : sqrt (INR d) * sqrt (INR (n / d)) = sqrt (INR n))
      by (apply sqrt_div_mul; [ lia | exact E ]).
    assert (Hd0 : sqrt (INR d) <> 0) by (apply Rgt_not_eq, sqrtn_pos; lia).
    assert (He0 : sqrt (INR (n / d)) <> 0) by (apply Rgt_not_eq, sqrtn_pos; lia).
    rewrite <- Hs, Rinv_mult. ring.
Qed.

Theorem Bt_double : forall X,
  RS (Bt p g A) X = RS (fun d => ach d * RS bh (X / d)%nat) X.
Proof.
  intro X. rewrite <- (hyper_iter ach bh X).
  apply RS_ext. intros n Hn. apply Bt_inner. exact Hn.
Qed.

End Double.

Print Assumptions Bt_double.

(* ================================================================= *)
(*  END HyperbolaDouble.v                                             *)
(* ================================================================= *)
