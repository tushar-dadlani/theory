(* ================================================================= *)
(*  GammaConst.v  --  a certified bracket for Euler-Mascheroni gamma. *)
(*                                                                    *)
(*  The repo has only 0 <= gamma <= 1.  The naive bracket             *)
(*  H_N - ln(N+1) <= gamma <= H_N - ln N has width ln(1+1/N), so 1e-3 *)
(*  would need N ~ 1000 and an exact rational H_1000.  Shifting the    *)
(*  logarithm to the midpoint,                                        *)
(*                                                                    *)
(*      cseq N := H_N - ln (N + 1/2),                                 *)
(*                                                                    *)
(*  makes the error O(1/N^2) instead: cseq is decreasing to gamma and  *)
(*  cseq N - gamma <= 2/(15 N^2).  Twelve terms then give 9.3e-4.      *)
(*                                                                    *)
(*  The per-step decrement is exactly 2(Lfun h - h) with h=1/(2N+2),  *)
(*  which LnSeries.Lser_remainder (at K = 0, where Lser 0 h = h)      *)
(*  bounds by 2h^3/(1-h^2).  So the same MVT that certifies ln also    *)
(*  certifies gamma -- no separate Euler-Maclaurin machinery.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import HarmonicSum EulerMascheroni LnSeries LnConstants.
Open Scope R_scope.

Definition cseq (N : nat) : R := Harm N - ln (INR N + / 2).

Lemma INR_ge1 : forall N, (1 <= N)%nat -> 1 <= INR N.
Proof. intros N HN. rewrite <- INR_1. apply le_INR. exact HN. Qed.

(* ---- the per-step decrement ---- *)

Lemma cseq_step : forall N, (1 <= N)%nat ->
  cseq N - cseq (S N)
  = 2 * (Lfun (/ (2 * INR N + 2)) - / (2 * INR N + 2)).
Proof.
  intros N HN.
  assert (HN1 : 1 <= INR N) by (apply INR_ge1; exact HN).
  set (h := / (2 * INR N + 2)).
  assert (Hd : 0 < 2 * INR N + 2) by lra.
  assert (Hh0 : 0 < h) by (unfold h; apply Rinv_0_lt_compat; exact Hd).
  assert (E1 : 1 + h = (2 * INR N + 3) / (2 * INR N + 2))
    by (unfold h; field; lra).
  assert (E2 : 1 - h = (2 * INR N + 1) / (2 * INR N + 2))
    by (unfold h; field; lra).
  assert (P1 : 0 < (2 * INR N + 3) / (2 * INR N + 2)).
  { unfold Rdiv. apply Rmult_lt_0_compat;
      [ lra | apply Rinv_0_lt_compat; lra ]. }
  assert (P2 : 0 < (2 * INR N + 1) / (2 * INR N + 2)).
  { unfold Rdiv. apply Rmult_lt_0_compat;
      [ lra | apply Rinv_0_lt_compat; lra ]. }
  assert (Hlhs : ln (1 + h) - ln (1 - h)
                 = ln ((2 * INR N + 3) / (2 * INR N + 1))).
  { rewrite E1, E2, (ln_quot2 _ _ P1 P2). f_equal. field; lra. }
  assert (Hrhs : ln (INR N + 1 + / 2) - ln (INR N + / 2)
                 = ln ((2 * INR N + 3) / (2 * INR N + 1))).
  { assert (Q1 : 0 < INR N + 1 + / 2) by lra.
    assert (Q2 : 0 < INR N + / 2) by lra.
    rewrite (ln_quot2 _ _ Q1 Q2). f_equal. field; lra. }
  unfold cseq. rewrite Harm_rec, S_INR.
  assert (Hinv : / (INR N + 1) = 2 * h) by (unfold h; field; lra).
  rewrite Hinv.
  unfold Lfun. lra.
Qed.

(* ---- the decrement is small and nonnegative ---- *)

Lemma cseq_step_bound : forall N, (1 <= N)%nat ->
  0 <= cseq N - cseq (S N) <= (4 / 15) / INR (N + 1) ^ 3.
Proof.
  intros N HN.
  assert (HN1 : 1 <= INR N) by (apply INR_ge1; exact HN).
  set (h := / (2 * INR N + 2)).
  assert (Hd : 0 < 2 * INR N + 2) by lra.
  assert (Hh0 : 0 < h) by (unfold h; apply Rinv_0_lt_compat; exact Hd).
  assert (Hh4 : h <= / 4).
  { unfold h. apply Rinv_le_contravar; lra. }
  assert (Hh1 : h < 1) by lra.
  destruct (Lser_remainder 0 h (conj (Rlt_le _ _ Hh0) Hh1)) as [Hlo Hhi].
  assert (HL0 : Lser 0 h = h) by (unfold Lser; simpl; field).
  rewrite HL0 in Hlo, Hhi.
  rewrite (cseq_step N HN). fold h.
  replace (2 * 0 + 3)%nat with 3%nat in Hhi by lia.
  split; [ lra | ].
  assert (Hden : 15 / 16 <= 1 - h ^ 2) by nra.
  assert (Hpos : 0 < 1 - h ^ 2) by lra.
  assert (Hh3 : 0 <= h ^ 3) by (apply pow_le; lra).
  assert (Hstep : h ^ 3 / (1 - h ^ 2) <= (16 / 15) * h ^ 3).
  { apply Rmult_le_reg_r with (1 - h ^ 2); [ lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  assert (HNI : INR (N + 1) = INR N + 1) by (rewrite plus_INR; simpl; ring).
  assert (Hne1 : INR N + 1 <> 0) by (apply Rgt_not_eq; lra).
  assert (Hne2 : 2 * INR N + 2 <> 0) by (apply Rgt_not_eq; lra).
  assert (Hcube : (4 / 15) / INR (N + 1) ^ 3 = (32 / 15) * h ^ 3).
  { rewrite HNI. unfold h. field. repeat split; apply Rgt_not_eq; lra. }
  rewrite Hcube. lra.
Qed.

(* ---- telescoping:  sum of decrements from N is at most 2/(15 N^2) ---- *)

Lemma cseq_drop : forall N j, (1 <= N)%nat ->
  cseq N - cseq (N + j) <= (2 / 15) * (/ INR N ^ 2 - / INR (N + j) ^ 2).
Proof.
  intros N j HN. induction j as [| j IH].
  - rewrite Nat.add_0_r. lra.
  - assert (HNj : (1 <= N + j)%nat) by lia.
    assert (H1 : 1 <= INR (N + j)) by (apply INR_ge1; exact HNj).
    destruct (cseq_step_bound (N + j) HNj) as [_ Hb].
    assert (HS : INR (S (N + j)) = INR (N + j) + 1) by (rewrite S_INR; reflexivity).
    assert (Hm : INR (N + j + 1) = INR (N + j) + 1)
      by (rewrite plus_INR; simpl; ring).
    rewrite Hm in Hb.
    set (m := INR (N + j)) in *.
    assert (Hm0 : 0 < m) by lra.
    assert (Hkey : (4 / 15) / (m + 1) ^ 3 <= (2 / 15) * (/ m ^ 2 - / (m + 1) ^ 2)).
    { assert (Hpos : 0 < m ^ 2 * (m + 1) ^ 3) by nra.
      apply Rmult_le_reg_r with (m ^ 2 * (m + 1) ^ 3); [ exact Hpos | ].
      assert (EL : (4 / 15) / (m + 1) ^ 3 * (m ^ 2 * (m + 1) ^ 3) = (4 / 15) * m ^ 2)
        by (field; apply Rgt_not_eq; nra).
      assert (ER : (2 / 15) * (/ m ^ 2 - / (m + 1) ^ 2) * (m ^ 2 * (m + 1) ^ 3)
                   = (2 / 15) * ((m + 1) ^ 3 - m ^ 2 * (m + 1)))
        by (field; split; apply Rgt_not_eq; nra).
      rewrite EL, ER. nra. }
    replace (N + S j)%nat with (S (N + j)) by lia.
    rewrite HS. lra.
Qed.

(* ---- cseq converges to gamma ---- *)

Lemma inv_S_cv : Un_cv (fun n => / INR (S n)) 0.
Proof.
  intros eps Heps.
  destruct (archimed_cor1 eps Heps) as [N [HN Npos]].
  exists N. intros n Hn. unfold R_dist. rewrite Rminus_0_r.
  assert (H1 : 0 < INR (S n)) by (apply lt_0_INR; lia).
  rewrite Rabs_right by (left; apply Rinv_0_lt_compat; exact H1).
  apply Rle_lt_trans with (/ INR N); [ | exact HN ].
  apply Rinv_le_contravar; [ apply lt_0_INR; lia | apply le_INR; lia ].
Qed.

Lemma cseq_gseq : forall N, (1 <= N)%nat ->
  cseq N = gseq N - ln (1 + / (2 * INR N)).
Proof.
  intros N HN.
  assert (H1 : 1 <= INR N) by (apply INR_ge1; exact HN).
  unfold cseq, gseq.
  assert (E : INR N + / 2 = INR N * (1 + / (2 * INR N))) by (field; lra).
  rewrite E, ln_mult; [ ring | lra | ].
  assert (0 < / (2 * INR N)) by (apply Rinv_0_lt_compat; lra). lra.
Qed.

Lemma CV_cst : forall a : R, Un_cv (fun _ => a) a.
Proof.
  intros a eps Heps. exists 0%nat. intros n _. unfold R_dist.
  rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. exact Heps.
Qed.

Lemma Un_cv_ext2 : forall (u v : nat -> R) l,
  (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l He Hu eps Heps. destruct (Hu eps Heps) as [N HN].
  exists N. intros n Hn. rewrite <- (He n). apply HN; exact Hn.
Qed.

Lemma cseq_cv : Un_cv (fun n => cseq (S n)) gamma.
Proof.
  assert (Hu : Un_cv (fun n => / (2 * INR (S n))) 0).
  { assert (H := CV_mult (fun _ => / 2) (fun n => / INR (S n)) (/ 2) 0
                   (CV_cst (/ 2)) inv_S_cv).
    cbv beta in H. replace (/ 2 * 0) with 0 in H by ring.
    apply (Un_cv_ext2 (fun n => / 2 * / INR (S n))); [ | exact H ].
    intro n. assert (0 < INR (S n)) by (apply lt_0_INR; lia).
    rewrite Rinv_mult. reflexivity. }
  assert (Hone : Un_cv (fun n => 1 + / (2 * INR (S n))) 1).
  { assert (H := CV_plus (fun _ => 1) (fun n => / (2 * INR (S n))) 1 0
                   (CV_cst 1) Hu).
    cbv beta in H. replace (1 + 0) with 1 in H by ring. exact H. }
  assert (Hln : Un_cv (fun n => ln (1 + / (2 * INR (S n)))) 0).
  { replace 0 with (ln 1) by (apply ln_1).
    apply continuity_seq; [ | exact Hone ].
    apply derivable_continuous_pt.
    exists (/ 1). apply derivable_pt_lim_ln. lra. }
  assert (Hg : Un_cv (fun n => gseq (S n)) gamma) by apply gamma_is_limit.
  assert (H := CV_minus (fun n => gseq (S n))
                 (fun n => ln (1 + / (2 * INR (S n)))) gamma 0 Hg Hln).
  cbv beta in H. replace (gamma - 0) with gamma in H by ring.
  apply (Un_cv_ext2 (fun n => gseq (S n) - ln (1 + / (2 * INR (S n)))));
    [ | exact H ].
  intro n. symmetry. apply cseq_gseq. lia.
Qed.

(* ---- the bracket ---- *)

Lemma cseq_decreasing : Un_decreasing (fun n => cseq (S n)).
Proof.
  intro n. destruct (cseq_step_bound (S n) ltac:(lia)) as [Hb _]. lra.
Qed.

Lemma gamma_le_cseq : forall N, (1 <= N)%nat -> gamma <= cseq N.
Proof.
  intros N HN. destruct N as [| M]; [ lia | ].
  exact (decreasing_ineq (fun n => cseq (S n)) gamma cseq_decreasing cseq_cv M).
Qed.

Lemma Un_cv_shiftk : forall (u : nat -> R) l k,
  Un_cv u l -> Un_cv (fun n => u (k + n)%nat) l.
Proof.
  intros u l k H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. apply HN. lia.
Qed.

Lemma cseq_shift_cv : forall N, (1 <= N)%nat ->
  Un_cv (fun j => cseq (N + j)) gamma.
Proof.
  intros N HN. destruct N as [| M]; [ lia | ].
  assert (H := Un_cv_shiftk (fun n => cseq (S n)) gamma M cseq_cv).
  cbv beta in H.
  apply (Un_cv_ext2 (fun n => cseq (S (M + n)))); [ | exact H ].
  intro n. f_equal; lia.
Qed.

Lemma cv_ge_lb : forall u l m, Un_cv u l -> (forall n, m <= u n) -> m <= l.
Proof.
  intros u l m H Hb.
  destruct (Rle_or_lt m l) as [Hle | Hlt]; [ exact Hle | ].
  exfalso. destruct (H ((m - l) / 2) ltac:(lra)) as [N HN].
  specialize (HN N (Nat.le_refl N)). specialize (Hb N).
  unfold R_dist in HN. apply Rabs_def2 in HN. lra.
Qed.

Theorem cseq_bracket : forall N, (1 <= N)%nat ->
  cseq N - (2 / 15) / INR N ^ 2 <= gamma <= cseq N.
Proof.
  intros N HN. split; [ | apply gamma_le_cseq; exact HN ].
  apply (cv_ge_lb (fun j => cseq (N + j)) gamma);
    [ apply cseq_shift_cv; exact HN | ].
  intro j.
  pose proof (cseq_drop N j HN) as Hd.
  assert (Hp : 0 <= / INR (N + j) ^ 2).
  { apply Rlt_le, Rinv_0_lt_compat.
    assert (0 < INR (N + j)) by (apply lt_0_INR; lia). nra. }
  unfold Rdiv in *. lra.
Qed.

(* ---- evaluation at N = 12 ---- *)

Lemma Harm_12 : Harm 12 = 86021 / 27720.
Proof.
  assert (H0 : Harm 0 = 0) by reflexivity.
  do 12 rewrite Harm_rec. rewrite H0. simpl. field.
Qed.

Lemma ln_2516_bounds :
  4462868 / 10000000 <= ln (25 / 16) <= 4462894 / 10000000.
Proof.
  destruct (ln_enclosure (25 / 16) 3 ltac:(lra)) as [Hlo Hhi].
  assert (Hh : (25 / 16 - 1) / (25 / 16 + 1) = 9 / 41) by field.
  rewrite Hh in Hlo, Hhi. rewrite Lser_3 in Hlo, Hhi.
  simpl in Hhi. lra.
Qed.

Lemma ln_25_2 : ln (25 / 2) = 3 * ln 2 + ln (25 / 16).
Proof.
  assert (E : (25 / 2 : R) = 8 * (25 / 16)) by field.
  rewrite E, ln_mult by lra.
  assert (E8 : (8 : R) = 2 * (2 * 2)) by field.
  rewrite E8, ln_mult by lra. rewrite ln_mult by lra. ring.
Qed.

Theorem gamma_bounds :
  5765495 / 10000000 <= gamma <= 5774830 / 10000000.
Proof.
  destruct (cseq_bracket 12 ltac:(lia)) as [Hlo Hhi].
  assert (HI : INR 12 = 12) by (simpl; ring).
  unfold cseq in Hlo, Hhi.
  rewrite HI, Harm_12 in Hlo, Hhi.
  assert (E : (12 : R) + / 2 = 25 / 2) by field.
  rewrite E, ln_25_2 in Hlo, Hhi.
  destruct ln2_bounds as [A1 A2].
  destruct ln_2516_bounds as [B1 B2].
  lra.
Qed.
