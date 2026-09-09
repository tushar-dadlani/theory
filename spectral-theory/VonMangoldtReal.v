(* ================================================================= *)
(*  VonMangoldtReal.v  --  Lambda * 1 = ln, over R.                   *)
(*                                                                    *)
(*    sum_{d | n} Lambda(d)  =  ln n            (Lambda d = ln vexp d)*)
(*                                                                    *)
(*  This is the arithmetic identity behind -L'/L = sum Lambda(n) chi(n)*)
(*  n^{-s}: multiplying that series by L(s,chi) convolves Lambda with  *)
(*  1, and the result has to be sum chi(n) ln n n^{-s} = -L'(s,chi).   *)
(*                                                                    *)
(*  NOTHING NEW IS PROVED ABOUT PRIMES.  The repo already has the      *)
(*  MULTIPLICATIVE form, DirichletVonMangoldtGen.vonmangoldt:          *)
(*                                                                    *)
(*      prod_{d | n} vexp(d) = n                                      *)
(*                                                                    *)
(*  where vexp d is p when d is a prime power p^k and 1 otherwise --   *)
(*  i.e. exp of the classical Lambda.  Taking logarithms turns the     *)
(*  product into the sum, and that is the whole file.  Working with    *)
(*  exp(Lambda) rather than Lambda is what let that identity be proved *)
(*  in nat (by mult_ind) in the first place; the cost is deferred to   *)
(*  here, and it is one induction.                                     *)
(*                                                                    *)
(*  Stated in the RS-with-indicator form so that HyperbolaSplit's      *)
(*  hyper_iter applies to it directly when the series get multiplied.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory List.
Require Import Totient DirichletVonMangoldt DirichletVexpSem DirichletVexpCoprime
        DirichletVonMangoldtGen HyperbolaSplit.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- real sums over lists.                                    *)
(* ----------------------------------------------------------------- *)

Definition Rsl (f : nat -> R) (l : list nat) : R :=
  fold_right (fun k acc => f k + acc) 0 l.

Lemma Rsl_app : forall (f : nat -> R) (l1 l2 : list nat), Rsl f (l1 ++ l2) = Rsl f l1 + Rsl f l2.
Proof.
  intros f l1 l2. unfold Rsl. induction l1 as [| a l1 IH]; simpl; [ ring | ].
  rewrite IH. ring.
Qed.

Lemma Rsl_filter : forall (f : nat -> R) (q : nat -> bool) (l : list nat),
  Rsl (fun k => if q k then f k else 0) l = Rsl f (filter q l).
Proof.
  intros f q l. unfold Rsl. induction l as [| a l IH]; [ reflexivity | ].
  simpl. destruct (q a); simpl; rewrite IH; ring.
Qed.

Lemma Rsl_seq_RS : forall (f : nat -> R) (n : nat), Rsl f (seq 1 n) = RS f n.
Proof.
  intros f n. induction n as [| n IH]; [ reflexivity | ].
  rewrite seq_S, Rsl_app, IH.
  replace (1 + n)%nat with (S n) by lia.
  replace (Rsl f [S n]) with (f (S n)) by (unfold Rsl; simpl; ring).
  replace (RS f (S n)) with (RS f n + f (S n)) by reflexivity. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- vexp is between 1 and n, and logs turn prodf into Rsl.   *)
(* ----------------------------------------------------------------- *)

Lemma vexp_ge1 : forall n, (1 <= vexp n)%nat.
Proof.
  intro n. unfold vexp. destruct (n <=? 1)%nat eqn:E; [ lia | ].
  apply Nat.leb_gt in E.
  destruct (strip n n (least_factor n) =? 1)%nat; [ | lia ].
  pose proof (least_factor_ge2 n ltac:(lia)). lia.
Qed.

Lemma vexp_le : forall n, (1 <= n)%nat -> (vexp n <= n)%nat.
Proof.
  intros n Hn. unfold vexp. destruct (n <=? 1)%nat eqn:E; [ lia | ].
  apply Nat.leb_gt in E.
  destruct (strip n n (least_factor n) =? 1)%nat; [ | lia ].
  apply least_factor_min; [ lia | lia | apply Nat.divide_refl ].
Qed.

Lemma prodf_ge1 : forall (F : nat -> nat) l,
  (forall d, In d l -> (1 <= F d)%nat) -> (1 <= prodf l F)%nat.
Proof.
  intros F l. unfold prodf. induction l as [| a l IH]; intro H; [ simpl; lia | ].
  simpl.
  assert (1 <= F a)%nat by (apply H; left; reflexivity).
  assert (1 <= fold_right (fun k acc => F k * acc) 1%nat l)%nat
    by (apply IH; intros d Hd; apply H; right; exact Hd).
  nia.
Qed.

Lemma ln_prodf : forall (F : nat -> nat) l,
  (forall d, In d l -> (1 <= F d)%nat) ->
  ln (INR (prodf l F)) = Rsl (fun d => ln (INR (F d))) l.
Proof.
  intros F l. unfold prodf, Rsl. induction l as [| a l IH]; intro H.
  - simpl. rewrite ?INR_1. apply ln_1.
  - assert (Ha : (1 <= F a)%nat) by (apply H; left; reflexivity).
    assert (Hl : (1 <= fold_right (fun k acc => F k * acc) 1%nat l)%nat).
    { pose proof (prodf_ge1 F l (fun d Hd => H d (or_intror Hd))) as HP.
      unfold prodf in HP. exact HP. }
    assert (HaR : 0 < INR (F a))
      by (apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); exact Ha ]).
    assert (HlR : 0 < INR (fold_right (fun k acc => (F k * acc)%nat) 1%nat l))
      by (apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); exact Hl ]).
    simpl. rewrite mult_INR, ln_mult by assumption.
    rewrite IH by (intros d Hd; apply H; right; exact Hd). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the identity.                                           *)
(* ----------------------------------------------------------------- *)

Lemma ln_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [H | H].
  - left. apply ln_increasing; assumption.
  - right. f_equal. exact H.
Qed.

Definition Lam (n : nat) : R := ln (INR (vexp n)).

Lemma Lam_nonneg : forall n, 0 <= Lam n.
Proof.
  intro n. unfold Lam. rewrite <- ln_1. apply ln_mono; [ lra | ].
  apply (le_INR 1). apply vexp_ge1.
Qed.

Lemma Lam_le_ln : forall n, (1 <= n)%nat -> Lam n <= ln (INR n).
Proof.
  intros n Hn. unfold Lam. apply ln_mono.
  - apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); apply vexp_ge1 ].
  - apply le_INR, vexp_le; exact Hn.
Qed.

Theorem vonmangoldt_R : forall n, (1 <= n)%nat ->
  RS (fun d => if (n mod d =? 0)%nat then Lam d else 0) n = ln (INR n).
Proof.
  intros n Hn.
  rewrite <- Rsl_seq_RS, Rsl_filter.
  assert (Hv : prodf (divisors n) vexp = n)
    by (change (prodf (divisors n) vexp) with (vmprod n); apply vonmangoldt; exact Hn).
  unfold Lam.
  change (filter (fun d => (n mod d =? 0)%nat) (seq 1 n)) with (divisors n).
  rewrite <- (ln_prodf vexp (divisors n)) by (intros d _; apply vexp_ge1).
  rewrite Hv. reflexivity.
Qed.

Print Assumptions vonmangoldt_R.

(* ================================================================= *)
(*  END VonMangoldtReal.v                                             *)
(* ================================================================= *)
