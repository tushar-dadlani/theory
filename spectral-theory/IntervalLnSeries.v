(* ================================================================= *)
(*  IntervalLn.v  --  a computable enclosure of ln at the integers.   *)
(*                                                                    *)
(*  ln x = 2 Lfun((x-1)/(x+1)) converges badly for large x (at x = 551 *)
(*  the argument is 0.996).  But the RATIO is always tame:            *)
(*                                                                    *)
(*      ln (j/(j-1)) = 2 Lfun (1/(2j-1)),   argument <= 1/3,          *)
(*                                                                    *)
(*  so the table is built by accumulation, ln j = ln (j-1) + that,     *)
(*  with Iround after each step.  The truncation error is dominated by *)
(*  the very first ratio (h = 1/3); every later one is negligible.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith.
Require Import IntervalArith IntervalArithFun IntervalAtan LnSeries.
Open Scope R_scope.

(* ---- the series over Q, with a power accumulator ---- *)

Fixpoint lserAcc (jj : nat) (q2 : Q) (n : nat) (pw acc : Q) : Q :=
  match jj with
  | O => acc
  | S j' =>
      lserAcc j' q2 (S n) (Qred (Qmult pw q2))
        (Qred (Qplus acc (Qdiv pw (qinj (2 * n + 1)))))
  end.

Definition LserQ (K : nat) (q : Q) : Q := lserAcc (S K) (Qmult q q) 0 q 0.

Lemma lserAcc_spec : forall jj x q2 n pw acc,
  Q2R q2 = x * x ->
  Q2R pw = x ^ (2 * n + 1) ->
  Q2R acc = psumR (fun k => / INR (2 * k + 1) * x ^ (2 * k + 1)) n ->
  Q2R (lserAcc jj q2 n pw acc)
  = psumR (fun k => / INR (2 * k + 1) * x ^ (2 * k + 1)) (n + jj).
Proof.
  induction jj as [| jj IH]; intros x q2 n pw acc Hq2 Hpw Hacc.
  - cbn [lserAcc]. rewrite Nat.add_0_r. exact Hacc.
  - cbn [lserAcc]. replace (n + S jj)%nat with (S n + jj)%nat by lia.
    apply IH; [ exact Hq2 | | ].
    + rewrite Q2R_Qred, Q2R_mult, Hpw, Hq2.
      replace (2 * S n + 1)%nat with (2 * n + 1 + 2)%nat by lia.
      rewrite (pow_add x (2 * n + 1) 2). ring.
    + rewrite Q2R_Qred, Q2R_plus, Hacc.
      rewrite Q2R_div by (apply qinj_ne0; lia).
      rewrite Hpw, Q2R_qinj.
      cbn [psumR]. unfold Rdiv. ring.
Qed.

Lemma LserQ_spec : forall K q, Q2R (LserQ K q) = Lser K (Q2R q).
Proof.
  intros K q. unfold LserQ, Lser.
  rewrite (lserAcc_spec (S K) (Q2R q) (Qmult q q) 0 q 0).
  - replace (0 + S K)%nat with (S K) by lia. apply psumR_sum.
  - rewrite Q2R_mult. reflexivity.
  - simpl. ring.
  - rewrite Q2R_zero. reflexivity.
Qed.

(* ---- the remainder as a rational ---- *)

Definition ErrQ (K : nat) (h : Q) : Q :=
  Qdiv (qpow h (2 * K + 3)) (Qminus 1 (Qmult h h)).

Lemma Q2R_ErrQ : forall K h, Q2R h * Q2R h < 1 ->
  Q2R (ErrQ K h) = (Q2R h) ^ (2 * K + 3) / (1 - (Q2R h) ^ 2).
Proof.
  intros K h Hh. unfold ErrQ.
  assert (Hd : ~ (Qminus 1 (Qmult h h) == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_minus, Q2R_mult, Q2R_one. lra. }
  rewrite Q2R_div by exact Hd.
  rewrite Q2R_qpow, Q2R_minus, Q2R_mult, Q2R_one.
  replace ((Q2R h) ^ 2) with (Q2R h * Q2R h) by ring. reflexivity.
Qed.

Definition Ilfun (K : nat) (h : Q) : Itv :=
  mkI (LserQ K h) (Qplus (LserQ K h) (ErrQ K h)).

Lemma Ilfun_sound : forall K h, 0 <= Q2R h < 1 ->
  Icontains (Ilfun K h) (Lfun (Q2R h)).
Proof.
  intros K h Hh.
  assert (Hsq : Q2R h * Q2R h < 1) by nra.
  destruct (Lser_remainder K (Q2R h) Hh) as [Hlo Hhi].
  unfold Ilfun, Icontains; simpl.
  rewrite Q2R_plus, LserQ_spec, (Q2R_ErrQ K h Hsq).
  lra.
Qed.

(* ---- the ratio ln (j/(j-1)) and the table ---- *)

Definition Ilnstep (K : nat) (i : nat) : Itv :=
  Imul (Iconst 2) (Ilfun K (Qinv (qinj (2 * i + 1)))).

Lemma INR_2i1 : forall i, INR (2 * i + 1) = 2 * INR i + 1.
Proof. intro i. rewrite plus_INR, mult_INR. simpl. ring. Qed.

Lemma Ilnstep_sound : forall K i, (1 <= i)%nat ->
  Icontains (Ilnstep K i) (ln (INR (S i) / INR i)).
Proof.
  intros K i Hi.
  assert (Hi0 : 0 < INR i) by (apply lt_0_INR; lia).
  assert (Hs : INR (S i) = INR i + 1) by (rewrite S_INR; reflexivity).
  assert (Hx : 0 < INR (S i) / INR i)
    by (apply Rdiv_lt_0_compat; [ rewrite Hs; lra | lra ]).
  assert (Hq : Q2R (Qinv (qinj (2 * i + 1))) = / (2 * INR i + 1)).
  { rewrite Q2R_inv by (apply qinj_ne0; lia).
    rewrite Q2R_qinj, INR_2i1. reflexivity. }
  assert (Hh : (INR (S i) / INR i - 1) / (INR (S i) / INR i + 1)
               = Q2R (Qinv (qinj (2 * i + 1)))).
  { rewrite Hq, Hs. field. lra. }
  unfold Ilnstep.
  rewrite (ln_from_L _ Hx), Hh.
  replace (2 * Lfun (Q2R (Qinv (qinj (2 * i + 1)))))
    with (Q2R 2 * Lfun (Q2R (Qinv (qinj (2 * i + 1)))))
    by (rewrite Q2R_two; reflexivity).
  apply Imul_sound; [ apply Iconst_sound | ].
  apply Ilfun_sound. rewrite Hq.
  assert (H1 : 1 <= INR i) by (rewrite <- INR_1; apply le_INR; lia).
  split; [ left; apply Rinv_0_lt_compat; lra | ].
  rewrite <- Rinv_1. apply Rinv_1_lt_contravar; lra.
Qed.

Fixpoint Ilntab (p K : nat) (j : nat) : Itv :=
  match j with
  | O => Iconst 0
  | S O => Iconst 0
  | S i => Iround p (Iadd (Ilntab p K i) (Ilnstep K i))
  end.

Theorem Ilntab_sound : forall p K j, (1 <= j)%nat ->
  Icontains (Ilntab p K j) (ln (INR j)).
Proof.
  intros p K j. induction j as [| j IH]; intro Hj; [ lia | ].
  destruct j as [| i].
  - cbn [Ilntab]. replace (INR 1) with 1 by (simpl; ring).
    rewrite ln_1. replace 0 with (Q2R 0) by apply Q2R_zero.
    apply Iconst_sound.
  - cbn [Ilntab].
    assert (Hpos : 0 < INR (S i)) by (apply lt_0_INR; lia).
    assert (Ha : 0 < INR (S (S i))) by (apply lt_0_INR; lia).
    assert (E : ln (INR (S (S i)))
                = ln (INR (S i)) + ln (INR (S (S i)) / INR (S i))).
    { rewrite <- (ln_quot2 _ _ Ha Hpos). ring. }
    rewrite E. apply Iround_sound, Iadd_sound;
      [ apply IH; lia | apply Ilnstep_sound; lia ].
Qed.
