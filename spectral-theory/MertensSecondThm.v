(* ================================================================= *)
(*  MertensSecondThm.v                                                *)
(*                                                                    *)
(*  MERTENS' SECOND THEOREM (qualitative):                            *)
(*     sum_{p<=N} 1/p  =  ln ln N + O(1).                             *)
(*                                                                    *)
(*  Abel summation of mprime = sum_{p<=N}(ln p)/p (= ln N + O(1),     *)
(*  MertensTailBound.mertens_first_prime) against the weight 1/ln,    *)
(*  with the ln ln N produced by the iterated-log estimate            *)
(*  (MertensSecond.iterated_log_bracket).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound ChebyshevPrime VonMangoldtGlobal PrimePowerReindex
        MertensVonMangoldt MertensPrime MertensTailBound MertensSecond HarmonicSum.
Open Scope R_scope.

(* the mprime summand bb and the weight ff = 1/ln *)
Definition bb (n : nat) : R := tterm n / INR n.
Definition ff (n : nat) : R := / ln (INR n).

Lemma mprime_eq : forall N, mprime N = Rsum bb 1 N.
Proof. reflexivity. Qed.

Lemma mprime_succ : forall N, mprime (S N) = mprime N + bb (S N).
Proof. intro N; rewrite !mprime_eq; apply Rsum_succ. Qed.

(* the 1/p summand equals bb * ff  (also at non-primes and at 1) *)
Lemma prterm_eq : forall n, (1 <= n)%nat -> iterm n / INR n = bb n * ff n.
Proof.
  intros n Hn. unfold bb, ff, iterm, tterm.
  destruct (primeb n) eqn:E.
  - apply primeb_nprime in E.
    assert (Hn2 : (2 <= n)%nat) by (destruct E; lia).
    assert (Hln : ln (INR n) <> 0).
    { apply Rgt_not_eq. rewrite <- ln_1. apply ln_increasing;
        [ lra | rewrite <- INR_1; apply lt_INR; lia ]. }
    field. split; [ exact Hln | apply not_0_INR; lia ].
  - unfold Rdiv. rewrite !Rmult_0_l. ring.
Qed.

Lemma primeRecip_via_bb : forall N, primeRecip N = Rsum (fun n => bb n * ff n) 1 N.
Proof.
  intro N; unfold primeRecip. apply Rsum_ext.
  intros i Hi; apply in_seq in Hi; apply prterm_eq; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  ABEL SUMMATION (exact identity)                                  *)
(*    sum_{n=1}^{S M} bb n * ff n                                     *)
(*      = mprime(S M) * ff(S M)                                       *)
(*        - sum_{n=1}^{M} mprime n * (ff (S n) - ff n).               *)
(* ----------------------------------------------------------------- *)

Lemma abel_id : forall M,
  Rsum (fun n => bb n * ff n) 1 (S M)
  = mprime (S M) * ff (S M)
    - Rsum (fun n => mprime n * (ff (S n) - ff n)) 1 M.
Proof.
  induction M as [|M IH].
  - assert (Hm1 : mprime 1 = bb 1).
    { rewrite mprime_eq; unfold Rsum; cbn [seq map fold_right]; ring. }
    change (S 0) with 1%nat. rewrite Hm1.
    unfold Rsum; cbn [seq map fold_right]; ring.
  - rewrite (Rsum_succ (fun n => bb n * ff n) (S M)), IH.
    rewrite (Rsum_succ (fun n => mprime n * (ff (S n) - ff n)) M).
    rewrite (mprime_succ (S M)). ring.
Qed.

(* the exact identity on primeRecip *)
Theorem primeRecip_abel : forall M,
  primeRecip (S M)
  = mprime (S M) * ff (S M)
    - Rsum (fun n => mprime n * (ff (S n) - ff n)) 1 M.
Proof. intro M; rewrite primeRecip_via_bb; apply abel_id. Qed.

(* ----------------------------------------------------------------- *)
(*  Bounding: the main-term summand and ff monotonicity              *)
(* ----------------------------------------------------------------- *)

Lemma lnINR_pos : forall n, (2 <= n)%nat -> 0 < ln (INR n).
Proof.
  intros n Hn. rewrite <- ln_1. apply ln_increasing;
    [ lra | rewrite <- INR_1; apply lt_INR; lia ].
Qed.

Lemma ff_pos : forall n, (2 <= n)%nat -> 0 < ff n.
Proof. intros n Hn; unfold ff; apply Rinv_0_lt_compat, lnINR_pos; exact Hn. Qed.

Lemma ff_dec : forall n, (2 <= n)%nat -> ff (S n) <= ff n.
Proof.
  intros n Hn; unfold ff. apply Rinv_le_contravar; [ apply lnINR_pos; exact Hn | ].
  apply ln_le_mono; [ apply lt_0_INR; lia | apply le_INR; lia ].
Qed.

Definition Tterm (n : nat) : R := (ln (INR (S n)) - ln (INR n)) * ff (S n).

Lemma Tterm_bracket : forall n, (2 <= n)%nat -> gll (S n) <= Tterm n <= gll n.
Proof.
  intros n Hn. unfold Tterm, gll, ff.
  pose proof (harm_step n ltac:(lia)) as [Hlo Hhi].
  assert (Hlnn : 0 < ln (INR n)) by (apply lnINR_pos; lia).
  assert (HlnSn : 0 < ln (INR (S n))) by (apply lnINR_pos; lia).
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (HSn0 : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (HlnLE : ln (INR n) <= ln (INR (S n)))
    by (apply ln_le_mono; [ lra | apply le_INR; lia ]).
  assert (Hdiff0 : 0 <= ln (INR (S n)) - ln (INR n)) by lra.
  split.
  - rewrite Rinv_mult. apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | exact Hlo ].
  - rewrite Rinv_mult.
    apply Rmult_le_compat; [ exact Hdiff0 | left; apply Rinv_0_lt_compat; lra | exact Hhi | ].
    apply Rinv_le_contravar; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Rsum infrastructure for the final bound                          *)
(* ----------------------------------------------------------------- *)

Lemma Rsum_plus : forall f g a k, Rsum (fun n => f n + g n) a k = Rsum f a k + Rsum g a k.
Proof.
  intros f g a k; revert a; induction k as [|k IH]; intro a.
  - unfold Rsum; cbn [seq map fold_right]; ring.
  - rewrite !Rsum_succ_gen, IH; ring.
Qed.

Lemma Rsum_Rabs : forall f a k, Rabs (Rsum f a k) <= Rsum (fun n => Rabs (f n)) a k.
Proof.
  intros f a k; revert a; induction k as [|k IH]; intro a.
  - unfold Rsum; cbn [seq map fold_right]. rewrite Rabs_R0; lra.
  - rewrite !Rsum_succ_gen. eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat; [ apply IH | apply Rle_refl ].
Qed.

Lemma Rsum_telescope : forall g a k, Rsum (fun n => g n - g (S n)) a k = g a - g (a + k)%nat.
Proof.
  intros g a k; revert a; induction k as [|k IH]; intro a.
  - unfold Rsum; cbn [seq map fold_right]. rewrite Nat.add_0_r; ring.
  - rewrite Rsum_succ_gen, IH. replace (a + S k)%nat with (S (a + k)) by lia. ring.
Qed.

Lemma Rsum_peel1 : forall f k, (1 <= k)%nat ->
  Rsum f 1 k = (f 1%nat + Rsum f 2 (k - 1))%R.
Proof.
  intros f k Hk. replace k with (1 + (k - 1))%nat at 1 by lia.
  rewrite Rsum_split. f_equal. unfold Rsum; cbn [seq map fold_right]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  MERTENS' SECOND THEOREM                                          *)
(* ----------------------------------------------------------------- *)

Lemma ff_le2 : forall k, (2 <= k)%nat -> ff k <= ff 2.
Proof.
  intros k Hk; unfold ff; apply Rinv_le_contravar;
    [ apply lnINR_pos; lia | apply ln_le_mono; [ apply lt_0_INR; lia | apply le_INR; lia ] ].
Qed.

(* difference of the main-term summand from the ln ln increment is small *)
Lemma D_bound : forall n, (2 <= n)%nat ->
  Rabs (Tterm n - (Fll (S n) - Fll n)) <= gll n - gll (S n).
Proof.
  intros n Hn.
  pose proof (Tterm_bracket n Hn) as [Ht1 Ht2].
  pose proof (llstep n Hn) as [Hf1 Hf2].
  apply Rabs_le; lra.
Qed.

Lemma Rsum_opp : forall g a k, - Rsum g a k = Rsum (fun n => - g n) a k.
Proof.
  intros g a k. rewrite (Rsum_ext (fun n => - g n) (fun n => (-1) * g n)) by (intros; ring).
  rewrite <- Rsum_scale. ring.
Qed.

Lemma negMC_term : forall n, (2 <= n)%nat ->
  - (ln (INR n) * (ff (S n) - ff n)) = Tterm n.
Proof.
  intros n Hn. unfold Tterm, ff.
  assert (Hlnn : ln (INR n) <> 0) by (apply Rgt_not_eq, lnINR_pos; lia).
  assert (HlnSn : ln (INR (S n)) <> 0) by (apply Rgt_not_eq, lnINR_pos; lia).
  field. split; assumption.
Qed.

Lemma gll_nonneg : forall n, (2 <= n)%nat -> 0 <= gll n.
Proof.
  intros n Hn; unfold gll; left; apply Rinv_0_lt_compat, Rmult_lt_0_compat;
    [ apply lt_0_INR; lia | apply lnINR_pos; lia ].
Qed.

Theorem mertens_second : exists C, forall N, (2 <= N)%nat ->
  Rabs (primeRecip N - ln (ln (INR N))) <= C.
Proof.
  destruct mertens_first_prime as [C0 HC0].
  assert (Hff2 : 0 < ff 2) by (apply ff_pos; lia).
  assert (Hz1 : mprime 1 - ln (INR 1) = 0).
  { rewrite mprime_eq; unfold Rsum, bb, tterm; cbn [seq map fold_right].
    change (primeb 1) with false. rewrite INR_1, ln_1. field. }
  assert (HC0nn : 0 <= C0).
  { pose proof (HC0 1%nat ltac:(lia)) as H1. rewrite Hz1, Rabs_R0 in H1; exact H1. }
  exists (1 + 2 * (C0 * ff 2) + Rabs (Fll 2) + gll 2).
  intros N HN. destruct N as [|M]; [ lia | ]. assert (HM : (1 <= M)%nat) by lia.
  rewrite (primeRecip_abel M).
  change (ln (ln (INR (S M)))) with (Fll (S M)).
  set (MC := Rsum (fun n => ln (INR n) * (ff (S n) - ff n)) 1 M).
  set (EC := Rsum (fun n => (mprime n - ln (INR n)) * (ff (S n) - ff n)) 1 M).
  assert (Hdec : Rsum (fun n => mprime n * (ff (S n) - ff n)) 1 M = MC + EC).
  { unfold MC, EC; rewrite <- Rsum_plus; apply Rsum_ext; intros i _; ring. }
  rewrite Hdec.
  assert (HB : Rabs (mprime (S M) * ff (S M) - 1) <= C0 * ff 2).
  { assert (Hln : ln (INR (S M)) <> 0) by (apply Rgt_not_eq, lnINR_pos; lia).
    replace (mprime (S M) * ff (S M) - 1)
      with ((mprime (S M) - ln (INR (S M))) * ff (S M)) by (unfold ff; field; exact Hln).
    rewrite Rabs_mult.
    apply Rle_trans with (C0 * ff (S M)).
    - apply Rmult_le_compat; [ apply Rabs_pos | apply Rabs_pos | apply HC0; lia
      | rewrite (Rabs_right (ff (S M))); [ apply Rle_refl | apply Rle_ge, Rlt_le, ff_pos; lia ] ].
    - apply Rmult_le_compat_l; [ exact HC0nn | apply ff_le2; lia ]. }
  assert (HMCval : MC = Rsum (fun n => ln (INR n) * (ff (S n) - ff n)) 2 (M - 1)).
  { unfold MC. rewrite Rsum_peel1 by lia. rewrite INR_1, ln_1, Rmult_0_l, Rplus_0_l; reflexivity. }
  assert (HFll : Rsum (fun n => Fll (S n) - Fll n) 2 (M - 1) = Fll (S M) - Fll 2).
  { rewrite (Rsum_ext (fun n => Fll (S n) - Fll n) (fun n => - (Fll n - Fll (S n)))) by (intros; ring).
    rewrite <- Rsum_opp, Rsum_telescope. replace (2 + (M - 1))%nat with (S M) by lia. ring. }
  assert (HMC : Rabs (MC + (Fll (S M) - Fll 2)) <= gll 2).
  { rewrite HMCval, <- HFll.
    rewrite (Rsum_ext (fun n => ln (INR n) * (ff (S n) - ff n)) (fun n => - Tterm n))
      by (intros i Hi; apply in_seq in Hi; rewrite <- (negMC_term i) by lia; ring).
    rewrite <- Rsum_opp.
    replace (- Rsum Tterm 2 (M - 1) + Rsum (fun n => Fll (S n) - Fll n) 2 (M - 1))
      with (Rsum (fun n => Fll (S n) - Fll n) 2 (M - 1) - Rsum Tterm 2 (M - 1)) by ring.
    rewrite Rsum_minus.
    eapply Rle_trans; [ apply Rsum_Rabs | ].
    apply Rle_trans with (Rsum (fun n => gll n - gll (S n)) 2 (M - 1)).
    - apply Rsum_le. intros i Hi. apply in_seq in Hi.
      rewrite Rabs_minus_sym. apply D_bound; lia.
    - rewrite Rsum_telescope. replace (2 + (M - 1))%nat with (S M) by lia.
      pose proof (gll_nonneg (S M) ltac:(lia)); lra. }
  assert (HEC : Rabs EC <= C0 * ff 2).
  { unfold EC. rewrite Rsum_peel1 by lia. rewrite Hz1, Rmult_0_l, Rplus_0_l.
    eapply Rle_trans; [ apply Rsum_Rabs | ].
    apply Rle_trans with (Rsum (fun n => C0 * (ff n - ff (S n))) 2 (M - 1)).
    - apply Rsum_le. intros i Hi. apply in_seq in Hi.
      rewrite Rabs_mult. pose proof (ff_dec i ltac:(lia)) as Hfd.
      rewrite (Rabs_left1 (ff (S i) - ff i)) by lra.
      apply Rmult_le_compat; [ apply Rabs_pos | lra | apply HC0; lia | lra ].
    - rewrite <- Rsum_scale, Rsum_telescope. replace (2 + (M - 1))%nat with (S M) by lia.
      apply Rmult_le_compat_l; [ exact HC0nn | pose proof (ff_pos (S M) ltac:(lia)); lra ]. }
  assert (Htri : forall a b c d, Rabs (a - b - c + d) <= Rabs a + Rabs b + Rabs c + Rabs d).
  { intros a b c d. replace (a - b - c + d) with ((a + - b + - c) + d) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    replace (a + - b + - c) with ((a + - b) + - c) by ring.
    eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang | ].
    eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rplus_le_compat_r; apply Rabs_triang | ].
    rewrite !Rabs_Ropp. lra. }
  assert (Hd : Rabs (1 - Fll 2) <= 1 + Rabs (Fll 2)).
  { replace (1 - Fll 2) with (1 + - Fll 2) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_R1, Rabs_Ropp; lra. }
  replace (mprime (S M) * ff (S M) - (MC + EC) - Fll (S M))
    with ((mprime (S M) * ff (S M) - 1) - (MC + (Fll (S M) - Fll 2)) - EC + (1 - Fll 2)) by ring.
  eapply Rle_trans; [ apply Htri | ]. lra.
Qed.

Print Assumptions mertens_second.
