(* ================================================================= *)
(*  ThetaEnclose.v  --  a certified interval for theta(t).            *)
(*                                                                    *)
(*    theta t = -(t/2) ln pi - Pang (1/4 + i t/2)                     *)
(*    Pang z  = atan(Im z/Re z) + gamma Im z                          *)
(*              + sum_{k>=1} [ atan(Im z/(k+Re z)) - Im z/k ]         *)
(*                                                                    *)
(*  Every ingredient is now certified: Iatan for the arctans,         *)
(*  LnConstants.lnPI_bounds and GammaConst.gamma_bounds for the two   *)
(*  constants, and GammaDir.Wangl_tail2 for the truncation.  The      *)
(*  partial sum is accumulated in Itv with Iround after each step.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia Qreals QArith.
Require Import ComplexField IntervalArith IntervalArithFun IntervalAtan
        CertifiedPi LnConstants GammaConst EulerMascheroni
        CPolarDir GammaDir GammaArg.
Open Scope R_scope.

(* ---- the two constants as intervals ---- *)

Definition IlnPI : Itv := mkI (1144668 # 1000000) (1144737 # 1000000).

Lemma IlnPI_sound : Icontains IlnPI (ln PI).
Proof.
  unfold Icontains, IlnPI; simpl.
  pose proof lnPI_bounds as [H1 H2]. split; unfold Q2R; simpl; lra.
Qed.

Definition Igamma : Itv := mkI (5765495 # 10000000) (5774830 # 10000000).

Lemma Igamma_sound : Icontains Igamma gamma.
Proof.
  unfold Icontains, Igamma; simpl.
  pose proof gamma_bounds as [H1 H2]. split; unfold Q2R; simpl; lra.
Qed.

(* ---- small numeric bridges ---- *)

Lemma Q2R_four : Q2R 4 = 4.
Proof. unfold Q2R; simpl; field. Qed.

Lemma Q2R_eight : Q2R 8 = 8.
Proof. unfold Q2R; simpl; field. Qed.

Lemma Q2R_sixteen : Q2R 16 = 16.
Proof. unfold Q2R; simpl; field. Qed.

(* ---- the k-th term ---- *)

Definition kq (m : nat) : Q := qinj (S m).

Lemma Q2R_kq : forall m, Q2R (kq m) = INR (S m).
Proof. intro m. unfold kq. apply Q2R_qinj. Qed.

Lemma kq_pos : forall m, 0 < Q2R (kq m).
Proof. intro m. rewrite Q2R_kq. apply lt_0_INR. lia. Qed.

Definition wargQ (tq : Q) (m : nat) : Q :=
  Qdiv (Qmult 2 tq) (Qplus (Qmult 4 (kq m)) 1).

Definition wsubQ (tq : Q) (m : nat) : Q := Qdiv tq (Qmult 2 (kq m)).

Lemma Q2R_wargQ : forall tq m,
  Q2R (wargQ tq m) = 2 * Q2R tq / (4 * INR (S m) + 1).
Proof.
  intros tq m. pose proof (kq_pos m) as Hk.
  assert (Hd : ~ (Qplus (Qmult 4 (kq m)) 1 == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_plus, Q2R_mult, Q2R_one, Q2R_four.
    rewrite Q2R_kq in *. lra. }
  unfold wargQ. rewrite Q2R_div by exact Hd.
  rewrite Q2R_mult, Q2R_plus, Q2R_mult, Q2R_one, Q2R_two, Q2R_four, Q2R_kq.
  reflexivity.
Qed.

Lemma Q2R_wsubQ : forall tq m, Q2R (wsubQ tq m) = Q2R tq / (2 * INR (S m)).
Proof.
  intros tq m. pose proof (kq_pos m) as Hk.
  assert (Hd : ~ (Qmult 2 (kq m) == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_mult, Q2R_two. lra. }
  unfold wsubQ. rewrite Q2R_div by exact Hd.
  rewrite Q2R_mult, Q2R_two, Q2R_kq. reflexivity.
Qed.

(* the point on the critical line *)
Definition zt (t : R) : C := mkC (/ 4) (t / 2).

Lemma wang_zt : forall t m, 0 < t ->
  wang (zt t) (S m)
  = atan (2 * t / (4 * INR (S m) + 1)) - t / (2 * INR (S m)).
Proof.
  intros t m Ht.
  assert (Hk : 0 < INR (S m)) by (apply lt_0_INR; lia).
  cbn [wang]. unfold zt; cbn [Re Im].
  assert (E : t / 2 / INR (S m) / (1 + / 4 / INR (S m))
              = 2 * t / (4 * INR (S m) + 1)) by (field; lra).
  rewrite E. f_equal. field; lra.
Qed.

Definition IwangQ (pr M : nat) (tq : Q) (m : nat) : Itv :=
  Iround pr (Isub (Iatan M (wargQ tq m)) (Iconst (wsubQ tq m))).

Lemma IwangQ_sound : forall pr M tq m, 0 < Q2R tq ->
  Icontains (IwangQ pr M tq m) (wang (zt (Q2R tq)) (S m)).
Proof.
  intros pr M tq m Ht.
  assert (Hk : 0 < INR (S m)) by (apply lt_0_INR; lia).
  rewrite (wang_zt (Q2R tq) m Ht).
  unfold IwangQ. apply Iround_sound.
  replace (2 * Q2R tq / (4 * INR (S m) + 1)) with (Q2R (wargQ tq m))
    by (rewrite Q2R_wargQ; reflexivity).
  replace (Q2R tq / (2 * INR (S m))) with (Q2R (wsubQ tq m))
    by (rewrite Q2R_wsubQ; reflexivity).
  apply Isub_sound; [ | apply Iconst_sound ].
  apply Iatan_sound. rewrite Q2R_wargQ.
  apply Rdiv_lt_0_compat; lra.
Qed.

(* ---- the truncated sum ---- *)

Fixpoint IwangsumQ (pr M : nat) (tq : Q) (n : nat) : Itv :=
  match n with
  | O => Iconst 0
  | S k => Iround pr (Iadd (IwangsumQ pr M tq k) (IwangQ pr M tq k))
  end.

Lemma IwangsumQ_sound : forall pr M tq n, 0 < Q2R tq ->
  Icontains (IwangsumQ pr M tq n) (wangsum (zt (Q2R tq)) n).
Proof.
  intros pr M tq n Ht. induction n as [| n IH].
  - cbn [IwangsumQ]. unfold wangsum; cbn [sum_f_R0 wang].
    replace 0 with (Q2R 0) by apply Q2R_zero. apply Iconst_sound.
  - cbn [IwangsumQ]. unfold wangsum in *. rewrite tech5.
    apply Iround_sound, Iadd_sound; [ exact IH | apply IwangQ_sound; exact Ht ].
Qed.

(* ---- the truncation error ---- *)

Definition BtailQ (tq : Q) (n : nat) : Q :=
  Qplus (Qdiv tq (Qmult 8 (qinj n)))
        (Qdiv (Qmult tq (Qmult tq tq)) (Qmult 16 (Qmult (qinj n) (qinj n)))).

Definition Itail (tq : Q) (n : nat) : Itv :=
  mkI (Qopp (BtailQ tq n)) (BtailQ tq n).

Lemma Itail_sound : forall tq n, 0 < Q2R tq -> (1 <= n)%nat ->
  Icontains (Itail tq n) (Wangl (zt (Q2R tq)) - wangsum (zt (Q2R tq)) n).
Proof.
  intros tq n Ht Hn.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hz1 : 0 < Re (zt (Q2R tq))) by (unfold zt; cbn [Re]; lra).
  assert (Hz2 : 0 <= Im (zt (Q2R tq))) by (unfold zt; cbn [Im]; lra).
  pose proof (Wangl_tail2 (zt (Q2R tq)) n Hz1 Hz2 Hn) as Hb.
  unfold zt in Hb; cbn [Re Im] in Hb.
  assert (Hd1 : ~ (Qmult 8 (qinj n) == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_mult, Q2R_eight, Q2R_qinj.
    apply Rgt_not_eq. lra. }
  assert (Hd2 : ~ (Qmult 16 (Qmult (qinj n) (qinj n)) == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_mult, Q2R_mult, Q2R_sixteen, Q2R_qinj.
    apply Rgt_not_eq. nra. }
  assert (HB : Q2R (BtailQ tq n)
               = / 4 * (Q2R tq / 2) / INR n + (Q2R tq / 2) ^ 3 / 2 / INR n ^ 2).
  { unfold BtailQ. rewrite Q2R_plus, !Q2R_div by assumption.
    rewrite !Q2R_mult, Q2R_eight, Q2R_sixteen, Q2R_qinj. field. lra. }
  unfold Itail, Icontains; simpl. rewrite Q2R_opp, HB. unfold zt.
  set (X := Wangl (mkC (/ 4) (Q2R tq / 2)) - wangsum (mkC (/ 4) (Q2R tq / 2)) n) in *.
  assert (H1 : X <= Rabs X) by apply Rle_abs.
  assert (H2 : - X <= Rabs X) by (rewrite <- Rabs_Ropp; apply Rle_abs).
  lra.
Qed.

(* ---- the whole angle ---- *)

Definition IWangl (pr M : nat) (tq : Q) (n : nat) : Itv :=
  Iadd (IwangsumQ pr M tq n) (Itail tq n).

Lemma IWangl_sound : forall pr M tq n, 0 < Q2R tq -> (1 <= n)%nat ->
  Icontains (IWangl pr M tq n) (Wangl (zt (Q2R tq))).
Proof.
  intros pr M tq n Ht Hn. unfold IWangl.
  replace (Wangl (zt (Q2R tq)))
    with (wangsum (zt (Q2R tq)) n
          + (Wangl (zt (Q2R tq)) - wangsum (zt (Q2R tq)) n)) by ring.
  apply Iadd_sound; [ apply IwangsumQ_sound; exact Ht
                    | apply Itail_sound; assumption ].
Qed.

Definition IPang (pr M Ma : nat) (tq : Q) (n : nat) : Itv :=
  Iround pr
    (Iadd (Iadd (Iatan Ma (Qmult 2 tq)) (Imul Igamma (Iconst (Qdiv tq 2))))
          (IWangl pr M tq n)).

Lemma IPang_sound : forall pr M Ma tq n, 0 < Q2R tq -> (1 <= n)%nat ->
  Icontains (IPang pr M Ma tq n) (Pang (zt (Q2R tq))).
Proof.
  intros pr M Ma tq n Ht Hn. unfold IPang. apply Iround_sound.
  unfold Pang, zt; cbn [Re Im].
  assert (Ha : Im (mkC (/ 4) (Q2R tq / 2)) / Re (mkC (/ 4) (Q2R tq / 2))
               = 2 * Q2R tq) by (cbn [Re Im]; field).
  cbn [Re Im] in Ha. rewrite Ha.
  apply Iadd_sound; [ apply Iadd_sound | ].
  - replace (2 * Q2R tq) with (Q2R (Qmult 2 tq))
      by (rewrite Q2R_mult, Q2R_two; reflexivity).
    apply Iatan_sound. rewrite Q2R_mult, Q2R_two. lra.
  - replace (gamma * (Q2R tq / 2)) with (gamma * Q2R (Qdiv tq 2)).
    + apply Imul_sound; [ apply Igamma_sound | apply Iconst_sound ].
    + rewrite Q2R_div by (apply Qne0_of_R; rewrite Q2R_two; lra).
      rewrite Q2R_two. reflexivity.
  - pose proof (IWangl_sound pr M tq n Ht Hn) as H. unfold zt in H. exact H.
Qed.

(* ---- theta itself ---- *)

Definition Itheta (pr M Ma : nat) (tq : Q) (n : nat) : Itv :=
  Iround pr
    (Iadd (Imul (Iconst (Qopp (Qdiv tq 2))) IlnPI) (Ineg (IPang pr M Ma tq n))).

Theorem Itheta_sound : forall pr M Ma tq n, 0 < Q2R tq -> (1 <= n)%nat ->
  Icontains (Itheta pr M Ma tq n) (theta (Q2R tq)).
Proof.
  intros pr M Ma tq n Ht Hn. unfold Itheta. apply Iround_sound.
  unfold theta. apply Iadd_sound.
  - replace (- (Q2R tq / 2) * ln PI) with (Q2R (Qopp (Qdiv tq 2)) * ln PI).
    + apply Imul_sound; [ apply Iconst_sound | apply IlnPI_sound ].
    + rewrite Q2R_opp, Q2R_div
        by (apply Qne0_of_R; rewrite Q2R_two; apply Rgt_not_eq; lra).
      rewrite Q2R_two. reflexivity.
  - apply Ineg_sound.
    pose proof (IPang_sound pr M Ma tq n Ht Hn) as H. unfold zt in H. exact H.
Qed.

(* ================================================================= *)
(*  A certified value at t = 26.                                      *)
(*                                                                    *)
(*  500 arctan terms, 4 series terms each (the reduced arguments are   *)
(*  all <= 1/2 in absolute value, so the bracket width per term is     *)
(*  (1/2)^19/19 ~ 1e-7), 40-bit rounding after every accumulation.     *)
(*                                                                    *)
(*  Width 0.035 rad, of which the truncation tail contributes 0.022    *)
(*  and the width of gamma contributes 13 * 9.3e-4 = 0.012; ln pi is   *)
(*  negligible at 9e-4.  Running time ~21 s.                          *)
(* ================================================================= *)

Lemma chk_theta26 :
  Qle_bool (5048 # 1000) (ilo (Itheta 40 4 4 26 500)) &&
  Qle_bool (ihi (Itheta 40 4 4 26 500)) (5084 # 1000) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem theta_26_bounds : 5048 / 1000 <= theta 26 <= 5084 / 1000.
Proof.
  assert (H26 : Q2R 26 = 26) by (unfold Q2R; simpl; field).
  assert (E1 : Q2R (5048 # 1000) = 5048 / 1000) by (unfold Q2R; simpl; field).
  assert (E2 : Q2R (5084 # 1000) = 5084 / 1000) by (unfold Q2R; simpl; field).
  assert (Hpos : 0 < Q2R 26) by (rewrite H26; lra).
  destruct (Itheta_sound 40 4 4 26 500 Hpos ltac:(lia)) as [Hlo Hhi].
  rewrite H26 in Hlo, Hhi.
  pose proof chk_theta26 as Hc.
  apply andb_true_iff in Hc. destruct Hc as [C1 C2].
  apply Qle_R' in C1. apply Qle_R' in C2.
  rewrite E1 in C1. rewrite E2 in C2.
  split; lra.
Qed.
