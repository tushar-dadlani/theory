(* ================================================================= *)
(*  MertensThirdThm.v                                                 *)
(*                                                                    *)
(*  MERTENS' THIRD THEOREM (logarithmic / qualitative form):          *)
(*     sum_{p<=N} ln(1 - 1/p)  =  - ln ln N + O(1),                    *)
(*  i.e.  prod_{p<=N}(1 - 1/p)  is of order  1/ln N.                   *)
(*                                                                    *)
(*  From ln(1-1/p) = -1/p - r_p  with  r_p = -ln(1-1/p) - 1/p >= 0,    *)
(*  we get  logProd N = - primeRecip N - Rrem N, where                *)
(*    - primeRecip N = ln ln N + O(1)          (mertens_second), and  *)
(*    - Rrem N = sum_{p<=N} r_p  is bounded (0 <= Rrem N <= 1),        *)
(*      because  r_p = (ln p - ln(p-1)) - 1/p  in [0, 1/(p(p-1))]      *)
(*      by the MVT bracket harm_step, and sum 1/(p(p-1)) telescopes.  *)
(*                                                                    *)
(*  All Qed; standard classical-Reals axioms only.  The EXACT         *)
(*  constant e^{-gamma} (Mertens 3 proper) needs the deep identity    *)
(*  M + P2 = gamma and is NOT established here.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound ChebyshevPrime PrimePowerReindex
        MertensPrime MertensVonMangoldt HarmonicSum MertensSecondThm.
Open Scope R_scope.

Definition logProd (N : nat) : R := Rsum (fun d => iterm d * ln (1 - / INR d)) 1 N.
Definition Rrem (N : nat) : R := Rsum (fun d => iterm d * (- ln (1 - / INR d) - / INR d)) 1 N.

Lemma ln_div : forall a b, 0 < a -> 0 < b -> ln (a / b) = ln a - ln b.
Proof.
  intros a b Ha Hb. unfold Rdiv. rewrite ln_mult; [ | lra | apply Rinv_0_lt_compat; lra ].
  rewrite ln_Rinv; [ ring | lra ].
Qed.

Lemma INR_pred : forall d, (1 <= d)%nat -> INR (d - 1) = INR d - 1.
Proof.
  intros d Hd. assert (INR d = INR (d - 1) + 1) by (rewrite <- S_INR; f_equal; lia). lra.
Qed.

(* the tail term r_d = -ln(1-1/d) - 1/d, bracketed by the MVT step *)
Lemma rterm_bracket : forall d, (2 <= d)%nat ->
  0 <= - ln (1 - / INR d) - / INR d <= / (INR d * (INR d - 1)).
Proof.
  intros d Hd.
  assert (Hposd : 0 < INR d) by (apply lt_0_INR; lia).
  assert (Hpos1 : 0 < INR (d - 1)) by (apply lt_0_INR; lia).
  pose proof (INR_pred d ltac:(lia)) as Hdd.
  assert (Hln : - ln (1 - / INR d) = ln (INR d) - ln (INR (d - 1))).
  { replace (1 - / INR d) with (INR (d - 1) / INR d) by (rewrite Hdd; field; lra).
    rewrite ln_div by lra. ring. }
  rewrite Hln.
  pose proof (harm_step (d - 1) ltac:(lia)) as [Hlo Hhi].
  replace (S (d - 1)) with d in Hlo, Hhi by lia.
  assert (Heq : / INR (d - 1) - / INR d = / (INR d * (INR d - 1)))
    by (rewrite Hdd; field; lra).
  split; [ lra | rewrite <- Heq; lra ].
Qed.

Lemma iterm_nonneg : forall d, 0 <= iterm d.
Proof. intro d; unfold iterm; destruct (primeb d); lra. Qed.

Lemma iterm_le1 : forall d, iterm d <= 1.
Proof. intro d; unfold iterm; destruct (primeb d); lra. Qed.

(* Rrem is bounded: 0 <= Rrem N <= 1 *)
Lemma Rrem_bound : forall N, (2 <= N)%nat -> 0 <= Rrem N <= 1.
Proof.
  intros N HN. split.
  - unfold Rrem. apply Rsum_nonneg. intros i Hi; apply in_seq in Hi.
    destruct (Nat.eq_dec i 1) as [->|Hne].
    + unfold iterm; change (primeb 1) with false; lra.
    + apply Rmult_le_pos; [ apply iterm_nonneg | apply (rterm_bracket i); lia ].
  - (* Rrem N <= sum bnd <= 1 *)
    apply Rle_trans with (Rsum (fun d => / (INR d * (INR d - 1))) 1 N).
    + unfold Rrem. apply Rsum_le. intros i Hi; apply in_seq in Hi.
      destruct (Nat.eq_dec i 1) as [->|Hne].
      * unfold iterm; change (primeb 1) with false. rewrite INR_1.
        replace (1 * (1 - 1)) with 0 by ring. rewrite Rinv_0. lra.
      * pose proof (rterm_bracket i ltac:(lia)) as [Hr0 Hr1].
        unfold iterm; destruct (primeb i); [ lra | ].
        rewrite Rmult_0_l. apply Rle_trans with (- ln (1 - / INR i) - / INR i); [ lra | exact Hr1 ].
    + (* sum_{d=1}^N 1/(d(d-1)) : peel d=1 (=0), then telescope to 1 - 1/N *)
      rewrite Rsum_peel1 by lia.
      rewrite INR_1. replace (1 * (1 - 1)) with 0 by ring. rewrite Rinv_0, Rplus_0_l.
      rewrite (Rsum_ext (fun d => / (INR d * (INR d - 1)))
                        (fun d => (fun n => / INR (n - 1)) d - (fun n => / INR (n - 1)) (S d)) 2 (N - 1)).
      * rewrite Rsum_telescope. replace (2 + (N - 1))%nat with (S N) by lia.
        cbn [Nat.sub]. rewrite Nat.sub_0_r. rewrite INR_1.
        assert (0 < / INR N) by (apply Rinv_0_lt_compat, lt_0_INR; lia). lra.
      * intros i Hi; apply in_seq in Hi.
        assert (Hi2 : (2 <= i)%nat) by lia.
        assert (Hposi : 0 < INR i) by (apply lt_0_INR; lia).
        assert (Hposi1 : 0 < INR (i - 1)) by (apply lt_0_INR; lia).
        pose proof (INR_pred i ltac:(lia)) as Hddi.
        replace (S i - 1)%nat with i by lia.
        rewrite Hddi. field. lra.
Qed.

(* logProd = -primeRecip - Rrem *)
Lemma logProd_decomp : forall N, logProd N = - primeRecip N - Rrem N.
Proof.
  intro N. unfold logProd.
  rewrite (Rsum_ext (fun d => iterm d * ln (1 - / INR d))
             (fun d => - (iterm d / INR d + iterm d * (- ln (1 - / INR d) - / INR d))) 1 N)
    by (intros i _; unfold Rdiv; ring).
  rewrite <- Rsum_opp, Rsum_plus. unfold primeRecip, Rrem. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  MERTENS' THIRD THEOREM (log form)                                *)
(* ----------------------------------------------------------------- *)

Theorem mertens_third : exists C, forall N, (2 <= N)%nat ->
  Rabs (logProd N + ln (ln (INR N))) <= C.
Proof.
  destruct mertens_second as [C2 H2].
  exists (C2 + 1). intros N HN.
  rewrite (logProd_decomp N).
  pose proof (Rrem_bound N HN) as [Rl Ru].
  replace (- primeRecip N - Rrem N + ln (ln (INR N)))
    with (- (primeRecip N - ln (ln (INR N))) + (- Rrem N)) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ]. rewrite !Rabs_Ropp.
  pose proof (H2 N HN) as HP.
  assert (HRR : Rabs (Rrem N) <= 1) by (rewrite Rabs_pos_eq; [ exact Ru | exact Rl ]).
  lra.
Qed.

Print Assumptions mertens_third.

(* ----------------------------------------------------------------- *)
(*  Toward the EXACT constant: the prime-power tail constant P2       *)
(*  exists (Rrem converges, monotone + bounded).                      *)
(* ----------------------------------------------------------------- *)

Lemma g_nonneg : forall d, 0 <= iterm d * (- ln (1 - / INR d) - / INR d).
Proof.
  intro d. destruct (le_lt_dec 2 d) as [Hd|Hd].
  - apply Rmult_le_pos; [ apply iterm_nonneg | apply (rterm_bracket d); lia ].
  - assert (Hi : iterm d = 0).
    { unfold iterm; destruct d as [|[|d']];
        [ change (primeb 0) with false | change (primeb 1) with false | lia ]; reflexivity. }
    rewrite Hi; lra.
Qed.

Lemma Rrem_le1 : forall N, Rrem N <= 1.
Proof.
  intros N. destruct (le_lt_dec 2 N) as [H|H]; [ apply (Rrem_bound N H) | ].
  assert (HR : Rrem N = 0).
  { destruct N as [|[|k]]; [ reflexivity | | lia ].
    unfold Rrem, Rsum; cbn [seq map fold_right]. change (iterm 1) with 0; ring. }
  rewrite HR; lra.
Qed.

Lemma Rrem_growing : Un_growing Rrem.
Proof.
  intro n. unfold Rrem. rewrite Rsum_succ. pose proof (g_nonneg (S n)). lra.
Qed.

Lemma Rrem_ub : has_ub Rrem.
Proof. exists 1. intros x [i ->]. apply Rrem_le1. Qed.

Lemma cv_le_ub' : forall u l M, Un_cv u l -> (forall n, u n <= M) -> l <= M.
Proof.
  intros u l M Hcv Hub. destruct (Rle_or_lt l M) as [Hle | Hlt]; [ exact Hle | ].
  exfalso. destruct (Hcv ((l - M) / 2) ltac:(lra)) as [K HK].
  specialize (HK K (Nat.le_refl K)); specialize (Hub K).
  unfold R_dist in HK; apply Rabs_def2 in HK; lra.
Qed.

(* P2 = sum_p sum_{k>=2} 1/(k p^k) exists as a real in [0,1]. *)
Theorem P2_exists : { P2 : R | Un_cv Rrem P2 /\ 0 <= P2 <= 1 }.
Proof.
  destruct (growing_cv Rrem Rrem_growing Rrem_ub) as [P2 HP2].
  exists P2. split; [ exact HP2 | split ].
  - pose proof (growing_ineq Rrem P2 Rrem_growing HP2 0%nat) as H0.
    unfold Rrem in H0; rewrite (Rsum_ext _ (fun _ => 0)) in H0 by (intros i Hi; apply in_seq in Hi; lia).
    revert H0; unfold Rsum; cbn [seq map fold_right]; lra.
  - apply (cv_le_ub' Rrem P2 1 HP2 Rrem_le1).
Qed.

Print Assumptions P2_exists.
