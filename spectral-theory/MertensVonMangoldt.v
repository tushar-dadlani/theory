(* ================================================================= *)
(*  MertensVonMangoldt.v  —  Mertens' theorem in von Mangoldt form.    *)
(*                                                                    *)
(*      | Sum_{d<=N} Lam(d)/d  -  ln N |  <=  Kup      (Kup = 2 ln2+2)  *)
(*                                                                    *)
(*  From the hyperbola identity  Sum_{d<=N} Lam(d) floor(N/d) = ln(N!)  *)
(*  (Chebyshev.order_swap_identity), replacing floor(N/d) by N/d costs  *)
(*  an error in [0, psi N] = [0, O(N)], and the elementary Stirling      *)
(*  bracket  N ln N - N <= ln(N!) <= N ln N  (a one-line induction)      *)
(*  pins  Sum Lam(d)/d = ln N + O(1).  First rung of the elementary      *)
(*  (Selberg) route to PNT.  Axiom-clean.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  Rsum helpers                                                   *)
(* ================================================================= *)

Lemma Rsum_succ : forall f N, Rsum f 1 (S N) = Rsum f 1 N + f (S N).
Proof.
  intros f N.
  assert (H : Rsum f 1 (N + 1) = Rsum f 1 N + Rsum f (1 + N) 1) by apply Rsum_split.
  replace (N + 1)%nat with (S N) in H by lia.
  replace (Rsum f (1 + N) 1) with (f (S N)) in H
    by (unfold Rsum; cbn [seq map fold_right]; replace (1 + N)%nat with (S N) by lia; ring).
  exact H.
Qed.

Lemma Rsum_ones : forall a n, Rsum (fun _ => 1) a n = INR n.
Proof.
  intros a n; revert a; induction n as [|n IH]; intro a.
  - reflexivity.
  - replace (Rsum (fun _ => 1) a (S n)) with (1 + Rsum (fun _ => 1) (S a) n)
      by (unfold Rsum; reflexivity).
    rewrite IH, S_INR; ring.
Qed.

Lemma Rsum_const : forall c a n, Rsum (fun _ => c) a n = c * INR n.
Proof.
  intros c a n.
  rewrite (Rsum_ext (fun _ => c) (fun _ => c * 1) a n) by (intros; ring).
  rewrite <- Rsum_scale, Rsum_ones; reflexivity.
Qed.

Lemma Tlog_Rsum : forall N, Tlog N = Rsum (fun n => ln (INR n)) 1 N.
Proof. reflexivity. Qed.

Lemma chsum_Rsum : forall N, chsum N = Rsum (fun d => Lam d * INR (N / d)) 1 N.
Proof. reflexivity. Qed.

Lemma ln2_nonneg : 0 <= ln 2.
Proof. rewrite <- ln_1; apply ln_le; lra. Qed.

(* ================================================================= *)
(*  1.  elementary Stirling:  N ln N - N <= ln(N!) <= N ln N           *)
(* ================================================================= *)

Lemma Tlog_upper : forall N, Tlog N <= INR N * ln (INR N).
Proof.
  intro N; rewrite Tlog_Rsum.
  apply Rle_trans with (Rsum (fun _ => ln (INR N)) 1 N).
  - apply Rsum_le; intros i Hi; apply in_seq in Hi.
    apply ln_le; [ apply lt_0_INR; lia | apply le_INR; lia ].
  - rewrite Rsum_const; apply Req_le; ring.
Qed.

Lemma Tlog_lower : forall N, (1 <= N)%nat -> INR N * ln (INR N) - INR N <= Tlog N.
Proof.
  induction N as [|N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 0) as [->|HN0].
  - rewrite Tlog_Rsum; unfold Rsum; cbn [seq map fold_right].
    rewrite INR_1, ln_1; lra.
  - rewrite Tlog_Rsum, Rsum_succ, <- Tlog_Rsum.
    set (LS := ln (INR (S N))).
    specialize (IH ltac:(lia)).
    assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
    assert (Hainv : INR N * / INR N = 1) by (apply Rinv_r; lra).
    assert (Hstep : LS <= ln (INR N) + / INR N).
    { unfold LS; rewrite S_INR.
      replace (INR N + 1) with (INR N * ((INR N + 1) / INR N)) at 1 by (field; lra).
      rewrite ln_mult by (try lra; apply Rdiv_lt_0_compat; lra).
      pose proof (ln_self1 ((INR N + 1) / INR N)
                    ltac:(apply Rdiv_lt_0_compat; lra)) as Hls.
      replace ((INR N + 1) / INR N - 1) with (/ INR N) in Hls by (field; lra); lra. }
    rewrite S_INR; nra.
Qed.

(* ================================================================= *)
(*  2.  the floor / fractional bridge                                 *)
(* ================================================================= *)

Lemma frac_bounds : forall N d, (1 <= d)%nat ->
  0 <= INR N / INR d - INR (N / d) < 1.
Proof.
  intros N d Hd; assert (HdR : 0 < INR d) by (apply lt_0_INR; lia).
  assert (Hle : (d * (N / d) <= N)%nat) by (apply Nat.mul_div_le; lia).
  assert (Hlt : (N < d * (N / d) + d)%nat).
  { pose proof (Nat.div_mod_eq N d) as Hdm;
      pose proof (Nat.mod_upper_bound N d ltac:(lia)); lia. }
  assert (Hlow : INR (N / d) <= INR N / INR d).
  { apply (Rmult_le_reg_r (INR d)); [ exact HdR | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    rewrite <- mult_INR; apply le_INR; rewrite Nat.mul_comm; exact Hle. }
  assert (Hhigh : INR N / INR d < INR (N / d) + 1).
  { apply (Rmult_lt_reg_r (INR d)); [ exact HdR | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    rewrite Rmult_plus_distr_r, Rmult_1_l, <- mult_INR, <- plus_INR.
    apply lt_INR; rewrite Nat.mul_comm; exact Hlt. }
  lra.
Qed.

Definition msum (N : nat) : R := Rsum (fun d => Lam d / INR d) 1 N.
Definition Ecorr (N : nat) : R :=
  Rsum (fun d => Lam d * (INR N / INR d - INR (N / d))) 1 N.

Lemma Ecorr_eq : forall N, INR N * msum N - chsum N = Ecorr N.
Proof.
  intro N; unfold msum, Ecorr; rewrite Rsum_scale, chsum_Rsum, Rsum_minus.
  apply Rsum_ext; intros d Hd; apply in_seq in Hd.
  assert (0 < INR d) by (apply lt_0_INR; lia); field; lra.
Qed.

Lemma msum_key : forall N, INR N * msum N = Tlog N + Ecorr N.
Proof.
  intro N; pose proof (Ecorr_eq N) as H; rewrite (order_swap_identity N); lra.
Qed.

Lemma Ecorr_nonneg : forall N, 0 <= Ecorr N.
Proof.
  intro N; unfold Ecorr; apply Rsum_nonneg; intros d Hd; apply in_seq in Hd.
  apply Rmult_le_pos; [ apply Lam_nonneg | pose proof (frac_bounds N d ltac:(lia)); lra ].
Qed.

Lemma Ecorr_le_psi : forall N, Ecorr N <= psi N.
Proof.
  intro N; unfold Ecorr; rewrite psi_Rsum; apply Rsum_le; intros d Hd; apply in_seq in Hd.
  pose proof (frac_bounds N d ltac:(lia)) as [Hf0 Hf1]; pose proof (Lam_nonneg d).
  apply Rle_trans with (Lam d * 1); [ apply Rmult_le_compat_l; lra | lra ].
Qed.

(* ================================================================= *)
(*  3.  Mertens in von Mangoldt form                                   *)
(* ================================================================= *)

Theorem mertens_lam : forall N, (1 <= N)%nat ->
  Rabs (msum N - ln (INR N)) <= Kup.
Proof.
  intros N HN.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  pose proof (msum_key N) as Hkey.
  pose proof (Tlog_lower N HN) as Hlo.
  pose proof (Tlog_upper N) as Hup.
  pose proof (Ecorr_nonneg N) as HE0.
  pose proof (Ecorr_le_psi N) as HEp.
  pose proof (psi_upper N) as Hpsi.
  assert (HKup1 : 1 <= Kup) by (unfold Kup; pose proof ln2_nonneg; lra).
  assert (Hbnd : - Kup <= msum N - ln (INR N) <= Kup) by (split; nra).
  unfold Rabs; destruct (Rcase_abs (msum N - ln (INR N))); lra.
Qed.

Print Assumptions mertens_lam.

(* ================================================================= *)
(*  END MertensVonMangoldt.v                                          *)
(*  Sum_{d<=N} Lam(d)/d = ln N + O(1) — Mertens (von Mangoldt form).    *)
(* ================================================================= *)
