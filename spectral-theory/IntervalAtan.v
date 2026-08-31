(* ================================================================= *)
(*  IntervalAtan.v  --  a computable interval enclosure of atan.      *)
(*                                                                    *)
(*  CertifiedPi.atan_enclose is a statement about the REAL alternating *)
(*  partial sums of Ratan_seq; it cannot be vm_computed.  Here the     *)
(*  same partial sums are built over Q (atanQ) and bridged to the real *)
(*  ones (atanQ_spec), so the alternating bracket becomes an Itv:      *)
(*                                                                    *)
(*     Iatan01 M q = [ S_(2M+1), S_(2M) ]   for 0 < q < 1             *)
(*                                                                    *)
(*  with width exactly the first omitted term, q^(4M+3)/(4M+3).       *)
(*  For q > 1 the series diverges, so Iatan reduces by atan q =        *)
(*  pi/2 - atan(1/q) (Ratan.atan_inv) against a certified pi/2.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia Qreals QArith.
Require Import IntervalArith CertifiedPi.
Open Scope R_scope.

Lemma Qle_R' : forall a b : Q, Qle_bool a b = true -> Q2R a <= Q2R b.
Proof. intros a b H. apply Qle_Rle, Qle_bool_iff. exact H. Qed.

Lemma Q2R_Qred : forall q, Q2R (Qred q) = Q2R q.
Proof. intro q. apply Qeq_eqR, Qred_correct. Qed.

Lemma Q2R_one : Q2R 1 = 1.
Proof. unfold Q2R; simpl; field. Qed.

Lemma Q2R_mone : Q2R (-1) = -1.
Proof. unfold Q2R; simpl; field. Qed.

Lemma Q2R_zero : Q2R 0 = 0.
Proof. unfold Q2R; simpl; field. Qed.

(* ---- powers and integers over Q ---- *)

Fixpoint qpow (q : Q) (n : nat) : Q :=
  match n with O => 1%Q | S m => Qmult q (qpow q m) end.

Lemma Q2R_qpow : forall q n, Q2R (qpow q n) = (Q2R q) ^ n.
Proof.
  intros q n. induction n as [| n IH]; simpl;
    [ apply Q2R_one | rewrite Q2R_mult, IH; reflexivity ].
Qed.

Definition qinj (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma Q2R_qinj : forall n, Q2R (qinj n) = INR n.
Proof.
  intro n. unfold qinj. rewrite INR_IZR_INZ.
  unfold Q2R, inject_Z; simpl. field.
Qed.

Lemma qinj_ne0 : forall n, (1 <= n)%nat -> ~ Qeq (qinj n) 0.
Proof.
  intros n Hn H.
  assert (HR : Q2R (qinj n) = Q2R 0) by (apply Qeq_eqR; exact H).
  rewrite Q2R_qinj, Q2R_zero in HR.
  assert (0 < INR n) by (apply lt_0_INR; lia). lra.
Qed.

(* ---- the alternating partial sums over Q, with an accumulator ----

   Recomputing q^(2n+1) per term would be O(M^2) big-number products,
   and without Qred the denominators multiply at every step.  The
   accumulator carries the power and the sign and reduces each one. *)

Fixpoint psumR (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S m => psumR f m + f m end.

Lemma psumR_sum : forall f N, psumR f (S N) = sum_f_R0 f N.
Proof.
  intros f N. induction N as [| N IH]; simpl; [ ring | ].
  simpl in IH. rewrite IH. reflexivity.
Qed.

Fixpoint atanAcc (j : nat) (q2 : Q) (n : nat) (pw sg acc : Q) : Q :=
  match j with
  | O => acc
  | S j' =>
      atanAcc j' q2 (S n) (Qred (Qmult pw q2)) (Qopp sg)
        (Qred (Qplus acc (Qmult sg (Qdiv pw (qinj (2 * n + 1))))))
  end.

Definition atanQ (M : nat) (q : Q) : Q := atanAcc (S M) (Qmult q q) 0 q 1 0.

Lemma atanAcc_spec : forall j x q2 n pw sg acc,
  Q2R q2 = x * x ->
  Q2R pw = x ^ (2 * n + 1) ->
  Q2R sg = (-1) ^ n ->
  Q2R acc = psumR (tg_alt (Ratan_seq x)) n ->
  Q2R (atanAcc j q2 n pw sg acc) = psumR (tg_alt (Ratan_seq x)) (n + j).
Proof.
  induction j as [| j IH]; intros x q2 n pw sg acc Hq2 Hpw Hsg Hacc.
  - cbn [atanAcc]. rewrite Nat.add_0_r. exact Hacc.
  - cbn [atanAcc]. replace (n + S j)%nat with (S n + j)%nat by lia.
    apply IH; [ exact Hq2 | | | ].
    + rewrite Q2R_Qred, Q2R_mult, Hpw, Hq2.
      replace (2 * S n + 1)%nat with (2 * n + 1 + 2)%nat by lia.
      rewrite (pow_add x (2 * n + 1) 2). ring.
    + rewrite Q2R_opp, Hsg. simpl. ring.
    + rewrite Q2R_Qred, Q2R_plus, Hacc, Q2R_mult, Hsg.
      rewrite Q2R_div by (apply qinj_ne0; lia).
      rewrite Hpw, Q2R_qinj.
      simpl psumR. unfold tg_alt, Ratan_seq. reflexivity.
Qed.

Lemma atanQ_spec : forall M q,
  Q2R (atanQ M q) = sum_f_R0 (tg_alt (Ratan_seq (Q2R q))) M.
Proof.
  intros M q. unfold atanQ.
  rewrite (atanAcc_spec (S M) (Q2R q) (Qmult q q) 0 q 1 0).
  - replace (0 + S M)%nat with (S M) by lia. apply psumR_sum.
  - rewrite Q2R_mult. reflexivity.
  - simpl. ring.
  - rewrite Q2R_one. simpl. ring.
  - rewrite Q2R_zero. reflexivity.
Qed.

(* ---- the enclosure on (0,1) ---- *)

Definition Iatan01 (M : nat) (q : Q) : Itv :=
  mkI (atanQ (S (2 * M)) q) (atanQ (2 * M) q).

Lemma Iatan01_sound : forall M q, 0 < Q2R q < 1 ->
  Icontains (Iatan01 M q) (atan (Q2R q)).
Proof.
  intros M q Hq. unfold Iatan01, Icontains; simpl.
  rewrite !atanQ_spec. apply atan_enclose. exact Hq.
Qed.

(* ---- the argument-halving identities ---- *)

Lemma d_minc : forall c x, derivable_pt_lim (fun y => y - c) x 1.
Proof.
  intros c x. replace 1 with (1 - 0) by ring.
  apply derivable_pt_lim_minus;
    [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
Qed.

Lemma d_plc : forall c x, derivable_pt_lim (fun y => y + c) x 1.
Proof.
  intros c x. replace 1 with (1 + 0) by ring.
  apply derivable_pt_lim_plus;
    [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
Qed.

Lemma atan_shift : forall q, -1 < q ->
  atan q = PI / 4 + atan ((q - 1) / (q + 1)).
Proof.
  intros q Hq.
  set (u := fun x : R => (x - 1) / (x + 1)).
  set (g := fun x : R => atan x - atan (u x)).
  assert (Hd : forall x, -1 < x -> derivable_pt_lim g x 0).
  { intros x Hx.
    assert (Hx1 : 0 < x + 1) by lra.
    assert (Hne : x + 1 <> 0) by lra.
    assert (Hin : derivable_pt_lim u x (2 / (x + 1) ^ 2)).
    { pose proof (derivable_pt_lim_div (fun y => y - 1) (fun y => y + 1) x 1 1
                    (d_minc 1 x) (d_plc 1 x) Hne) as H.
      unfold div_fct in H; cbv beta in H.
      replace (2 / (x + 1) ^ 2)
        with ((1 * (x + 1) - 1 * (x - 1)) / (x + 1) ²)
        by (unfold Rsqr; field; lra).
      exact H. }
    assert (Hcomp : derivable_pt_lim (fun y => atan (u y)) x
                      (/ (1 + (u x) ^ 2) * (2 / (x + 1) ^ 2))).
    { pose proof (derivable_pt_lim_comp u atan x (2 / (x + 1) ^ 2)
                    (/ (1 + (u x) ^ 2)) Hin (derivable_pt_lim_atan (u x))) as H.
      unfold comp in H. exact H. }
    assert (Heq : / (1 + (u x) ^ 2) * (2 / (x + 1) ^ 2) = / (1 + x ^ 2)).
    { unfold u.
      assert (Hden : 1 + ((x - 1) / (x + 1)) ^ 2
                     = (2 * x ^ 2 + 2) / (x + 1) ^ 2) by (field; lra).
      rewrite Hden.
      assert (Hx2 : 0 < 2 * x ^ 2 + 2) by nra.
      assert (Hsq : 0 < (x + 1) ^ 2) by nra.
      field; repeat split; try (apply Rgt_not_eq; lra); apply Rgt_not_eq; nra. }
    unfold g.
    replace 0 with (/ (1 + x ^ 2) - / (1 + (u x) ^ 2) * (2 / (x + 1) ^ 2))
      by (rewrite Heq; ring).
    apply derivable_pt_lim_minus; [ apply derivable_pt_lim_atan | exact Hcomp ]. }
  assert (Hg1 : g 1 = PI / 4).
  { unfold g, u. replace ((1 - 1) / (1 + 1)) with 0 by field.
    rewrite atan_0, atan_1. ring. }
  assert (Hconst : forall a b, -1 < a -> -1 < b -> g a = g b).
  { intros a b Ha Hb. destruct (Rtotal_order a b) as [H | [H | H]].
    - assert (HD : forall c, a <= c <= b -> derivable_pt_lim g c ((fun _ : R => 0) c))
        by (intros c Hc; apply Hd; lra).
      destruct (MVT_cor2 g (fun _ => 0) a b H HD) as [c [Hc _]]. lra.
    - subst; reflexivity.
    - assert (Hba : b < a) by lra.
      assert (HD : forall c, b <= c <= a -> derivable_pt_lim g c ((fun _ : R => 0) c))
        by (intros c Hc; apply Hd; lra).
      destruct (MVT_cor2 g (fun _ => 0) b a Hba HD) as [c [Hc _]]. lra. }
  assert (Hgq : g q = g 1) by (apply Hconst; lra).
  rewrite Hg1 in Hgq. unfold g, u in Hgq. lra.
Qed.

(* ---- the enclosure on (0,1), including 0 ---- *)

Lemma sum_tg0 : forall N, sum_f_R0 (tg_alt (Ratan_seq 0)) N = 0.
Proof.
  intro N. induction N as [| N IH]; cbn [sum_f_R0].
  - unfold tg_alt, Ratan_seq. rewrite pow_i by lia. unfold Rdiv. ring.
  - rewrite IH. unfold tg_alt, Ratan_seq. rewrite pow_i by lia.
    unfold Rdiv. ring.
Qed.

Lemma Iatan01_sound0 : forall M q, 0 <= Q2R q < 1 ->
  Icontains (Iatan01 M q) (atan (Q2R q)).
Proof.
  intros M q [H0 H1].
  destruct (Rle_lt_or_eq_dec 0 (Q2R q) H0) as [Hp | He].
  - apply Iatan01_sound. lra.
  - unfold Iatan01, Icontains; simpl.
    rewrite !atanQ_spec, <- He, !sum_tg0, atan_0. lra.
Qed.

Definition Iatan_sm (M : nat) (q : Q) : Itv :=
  if Qle_bool 0 q then Iatan01 M q else Ineg (Iatan01 M (Qopp q)).

Lemma Iatan_sm_sound : forall M q, -1 < Q2R q < 1 ->
  Icontains (Iatan_sm M q) (atan (Q2R q)).
Proof.
  intros M q [H1 H2]. unfold Iatan_sm.
  destruct (Qle_bool 0 q) eqn:Hb.
  - apply Iatan01_sound0.
    assert (H0 : Q2R 0 <= Q2R q) by (apply Qle_R'; exact Hb).
    rewrite Q2R_zero in H0. lra.
  - assert (Hnle : ~ (0 <= q)%Q).
    { intro Hc. apply Qle_bool_iff in Hc. rewrite Hc in Hb. discriminate. }
    assert (Hq : (q < 0)%Q) by (apply Qnot_le_lt; exact Hnle).
    assert (H0 : Q2R q <= Q2R 0) by (apply Qle_Rle, Qlt_le_weak; exact Hq).
    rewrite Q2R_zero in H0.
    assert (Hop : Q2R (Qopp q) = - Q2R q) by apply Q2R_opp.
    replace (atan (Q2R q)) with (- atan (- Q2R q))
      by (rewrite atan_opp; ring).
    apply Ineg_sound. rewrite <- Hop. apply Iatan01_sound0.
    rewrite Hop. lra.
Qed.

(* ---- pi/2 and pi/4 ---- *)

Definition Ihalfpi : Itv :=
  mkI (15707963266 # 10000000000) (15707963273 # 10000000000).

Lemma Ihalfpi_sound : Icontains Ihalfpi (PI / 2).
Proof.
  unfold Icontains, Ihalfpi; simpl.
  pose proof PI_lower as Hl. pose proof PI_upper as Hu.
  split; unfold Q2R; simpl; lra.
Qed.

Definition Iquarterpi : Itv :=
  mkI (7853981633 # 10000000000) (7853981637 # 10000000000).

Lemma Iquarterpi_sound : Icontains Iquarterpi (PI / 4).
Proof.
  unfold Icontains, Iquarterpi; simpl.
  pose proof PI_lower as Hl. pose proof PI_upper as Hu.
  split; unfold Q2R; simpl; lra.
Qed.

(* ---- small Q/R bridges ---- *)

Lemma Qlt_R : forall a b, Qle_bool a b = false -> Q2R b < Q2R a.
Proof.
  intros a b H.
  assert (Hnle : ~ (a <= b)%Q).
  { intro Hc. apply Qle_bool_iff in Hc. rewrite Hc in H. discriminate. }
  apply Qlt_Rlt, Qnot_le_lt. exact Hnle.
Qed.

Lemma Qne0_of_R : forall q, Q2R q <> 0 -> ~ (q == 0)%Q.
Proof.
  intros q H Hc. apply H. rewrite (Qeq_eqR q 0 Hc). apply Q2R_zero.
Qed.

Lemma Q2R_two : Q2R 2 = 2.
Proof. unfold Q2R; simpl; field. Qed.

Lemma Q2R_half : Q2R (1 # 2) = / 2.
Proof. unfold Q2R; simpl; field. Qed.

(* ---- the general enclosure: every argument reduced to |.| <= 1/2 ---- *)

Definition Iatan (M : nat) (q : Q) : Itv :=
  if Qle_bool 2 q then Isub Ihalfpi (Iatan_sm M (Qinv q))
  else if Qle_bool q (1 # 2) then Iatan_sm M q
  else Iadd Iquarterpi (Iatan_sm M (Qdiv (Qminus q 1) (Qplus q 1))).

Theorem Iatan_sound : forall M q, 0 < Q2R q ->
  Icontains (Iatan M q) (atan (Q2R q)).
Proof.
  intros M q Hpos. unfold Iatan.
  assert (Hq0 : ~ (q == 0)%Q) by (apply Qne0_of_R; lra).
  destruct (Qle_bool 2 q) eqn:H2.
  - (* q >= 2 : atan q = pi/2 - atan (1/q) *)
    assert (Hge : 2 <= Q2R q)
      by (pose proof (Qle_R' _ _ H2) as H; rewrite Q2R_two in H; lra).
    assert (Hinv : Q2R (Qinv q) = / Q2R q) by (apply Q2R_inv; exact Hq0).
    assert (Hb : 0 < / Q2R q <= / 2).
    { split; [ apply Rinv_0_lt_compat; lra | ].
      apply Rinv_le_contravar; lra. }
    replace (atan (Q2R q)) with (PI / 2 - atan (/ Q2R q))
      by (rewrite (atan_inv (Q2R q) Hpos); ring).
    apply Isub_sound; [ apply Ihalfpi_sound | ].
    rewrite <- Hinv. apply Iatan_sm_sound. rewrite Hinv. lra.
  - assert (Hlt2 : Q2R q < 2)
      by (pose proof (Qlt_R _ _ H2) as H; rewrite Q2R_two in H; lra).
    destruct (Qle_bool q (1 # 2)) eqn:Hh.
    + apply Iatan_sm_sound.
      pose proof (Qle_R' _ _ Hh) as H. rewrite Q2R_half in H. lra.
    + (* 1/2 < q < 2 : atan q = pi/4 + atan ((q-1)/(q+1)) *)
      assert (Hgt : / 2 < Q2R q)
        by (pose proof (Qlt_R _ _ Hh) as H; rewrite Q2R_half in H; lra).
      assert (Hp1 : ~ (Qplus q 1 == 0)%Q).
      { apply Qne0_of_R. rewrite Q2R_plus, Q2R_one. lra. }
      assert (Hval : Q2R (Qdiv (Qminus q 1) (Qplus q 1))
                     = (Q2R q - 1) / (Q2R q + 1)).
      { rewrite Q2R_div by exact Hp1.
        rewrite Q2R_minus, Q2R_plus, Q2R_one. reflexivity. }
      rewrite (atan_shift (Q2R q) ltac:(lra)).
      apply Iadd_sound; [ apply Iquarterpi_sound | ].
      rewrite <- Hval. apply Iatan_sm_sound. rewrite Hval.
      assert (Hd : 0 < Q2R q + 1) by lra.
      split.
      * apply Rmult_lt_reg_r with (Q2R q + 1); [ lra | ].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
      * apply Rmult_lt_reg_r with (Q2R q + 1); [ lra | ].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.
