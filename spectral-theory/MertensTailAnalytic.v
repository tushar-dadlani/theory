(* ================================================================= *)
(*  MertensTailAnalytic.v                                             *)
(*                                                                    *)
(*  The self-contained ANALYTIC core behind the higher-prime-power    *)
(*  tail bound (HigherPPTailBounded of MertensPrime.v):               *)
(*                                                                    *)
(*    - geom_tail_bound  : sum_{k=2}^N x^k <= x^2/(1-x)   (0<=x<1)     *)
(*        => per prime,  sum_{k>=2} (ln p)/p^k <= (ln p)/(p(p-1)).     *)
(*    - series_sum_bound : sum_{m=2}^{K+1} (ln m)/(m(m-1)) <= 8.       *)
(*        the convergent series majorising sum_p (ln p)/(p(p-1)),      *)
(*        via ln m <= 2 sqrt m and a sqrt telescoping.                 *)
(*                                                                    *)
(*  All Qed; only the standard classical-Reals axioms.                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import PrimePowerReindex.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Geometric per-prime bound                                        *)
(* ----------------------------------------------------------------- *)

Lemma geom_tail_bound : forall x N, 0 <= x -> x < 1 ->
  sum_f_R0 (fun k => x ^ k) N - 1 - x <= x ^ 2 / (1 - x).
Proof.
  intros x N Hx0 Hx1.
  rewrite (tech3 x N) by lra.
  assert (Hpow : 0 <= x ^ (S N)) by (apply pow_le; exact Hx0).
  assert (E : 1/(1-x) - 1 - x = x ^ 2 / (1 - x)) by (field; lra).
  assert (L : (1 - x ^ (S N))/(1-x) <= 1/(1-x)).
  { apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | lra ]. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  ln bounds                                                        *)
(* ----------------------------------------------------------------- *)

Lemma ln_le_sub1 : forall x, 0 < x -> ln x <= x - 1.
Proof.
  intros x Hx. destruct (Req_dec (x-1) 0) as [E|E].
  - replace x with 1 by lra. rewrite ln_1; lra.
  - rewrite <- (ln_exp (x-1)). apply Rlt_le, ln_increasing; [ exact Hx | ].
    pose proof (exp_ineq1 (x-1) E) as H. lra.
Qed.

Lemma ln_le_2sqrt : forall x, 0 < x -> ln x <= 2 * sqrt x.
Proof.
  intros x Hx.
  assert (Hs : 0 < sqrt x) by (apply sqrt_lt_R0; exact Hx).
  assert (Hln : ln x = 2 * ln (sqrt x)).
  { rewrite <- (sqrt_sqrt x) at 1 by lra. rewrite ln_mult by lra. ring. }
  pose proof (ln_le_sub1 (sqrt x) Hs) as Hb. rewrite Hln. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The sqrt telescoping term inequality                             *)
(* ----------------------------------------------------------------- *)

Lemma inv_m32_tele : forall m, (2 <= m)%nat ->
  / (INR m * sqrt (INR m)) <= 2 * (/ sqrt (INR (m-1)) - / sqrt (INR m)).
Proof.
  intros m Hm.
  set (a := sqrt (INR (m-1))). set (b := sqrt (INR m)).
  assert (Ha0 : 0 < a) by (apply sqrt_lt_R0, lt_0_INR; lia).
  assert (Hb0 : 0 < b) by (apply sqrt_lt_R0, lt_0_INR; lia).
  assert (Hane : a <> 0) by lra. assert (Hbne : b <> 0) by lra.
  assert (Ha2 : a*a = INR (m-1)) by (apply sqrt_sqrt, pos_INR).
  assert (Hb2 : b*b = INR m) by (apply sqrt_sqrt, pos_INR).
  assert (Hab : a <= b) by (apply sqrt_le_1; [ apply pos_INR | apply pos_INR | apply le_INR; lia ]).
  assert (HmS : INR m = INR (m - 1) + 1) by (rewrite <- (S_INR (m-1)); f_equal; lia).
  assert (Hbaa : b*b = a*a + 1) by (rewrite Hb2, HmS, <- Ha2; reflexivity).
  assert (Hfin : a <= 2*(b*b)*(b - a)) by nra.
  rewrite <- Hb2.
  apply Rmult_le_reg_r with (a * (b*b*b)); [ nra | ].
  replace (/ (b*b*b) * (a*(b*b*b))) with a by (field; auto).
  replace (2*(/a - /b) * (a*(b*b*b))) with (2*(b*b)*(b - a)) by (field; auto).
  exact Hfin.
Qed.

(* ----------------------------------------------------------------- *)
(*  Per-term bound: (ln m)/(m(m-1)) <= 8 (1/sqrt(m-1) - 1/sqrt m)     *)
(* ----------------------------------------------------------------- *)

Lemma series_term_bound : forall m, (2 <= m)%nat ->
  ln (INR m) / (INR m * (INR m - 1)) <= 8 * (/ sqrt (INR (m-1)) - / sqrt (INR m)).
Proof.
  intros m Hm.
  assert (Hm2 : 2 <= INR m) by (apply (le_INR 2); lia).
  set (s := sqrt (INR m)).
  assert (Hs0 : 0 < s) by (apply sqrt_lt_R0; lra).
  assert (Hs2 : s * s = INR m) by (apply sqrt_sqrt; lra).
  assert (Hlnm : ln (INR m) <= 2 * s) by (apply ln_le_2sqrt; lra).
  assert (Hlnpos : 0 <= ln (INR m)) by (rewrite <- ln_1; apply Rlt_le, ln_increasing; lra).
  pose proof (inv_m32_tele m Hm) as Htele. fold s in Htele.
  apply Rle_trans with (4 / (INR m * s)).
  - apply Rle_trans with (2 * s / (INR m * (INR m - 1))).
    + apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; lra | exact Hlnm ].
    + apply Rmult_le_reg_r with (INR m * (INR m - 1) * (INR m * s)); [ repeat apply Rmult_lt_0_compat; lra | ].
      replace (2*s/(INR m*(INR m-1)) * (INR m*(INR m-1)*(INR m*s)))
        with (2 * INR m * (s*s)) by (field; nra).
      replace (4/(INR m*s) * (INR m*(INR m-1)*(INR m*s)))
        with (4*(INR m*(INR m-1))) by (field; nra).
      rewrite Hs2; nra.
  - replace (8 * (/ sqrt (INR (m-1)) - / s)) with (4 * (2 * (/ sqrt (INR (m-1)) - / s))) by ring.
    replace (4 / (INR m * s)) with (4 * / (INR m * s)) by (field; nra).
    apply Rmult_le_compat_l; [ lra | exact Htele ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Telescoping and the series bound                                 *)
(* ----------------------------------------------------------------- *)

Lemma Rlsum_telescope : forall (g : nat -> R) n a,
  Rlsum (map (fun m => g m - g (S m)) (seq a n)) = g a - g (a + n)%nat.
Proof.
  intros g n. induction n as [|n IH]; intro a.
  - cbn [seq map]. unfold Rlsum; cbn [fold_right]. rewrite Nat.add_0_r. ring.
  - cbn [seq map]. rewrite Rlsum_cons, IH.
    replace (S a + n)%nat with (a + S n)%nat by lia. ring.
Qed.

Lemma series_sum_bound : forall K,
  Rlsum (map (fun m => ln (INR m) / (INR m * (INR m - 1))) (seq 2 K)) <= 8.
Proof.
  intro K.
  (* majorise termwise by the telescoping term *)
  apply Rle_trans with
    (Rlsum (map (fun m => 8 * / sqrt (INR (m-1)) - 8 * / sqrt (INR m)) (seq 2 K))).
  - apply Rlsum_map_le. intros m Hm. apply in_seq in Hm.
    pose proof (series_term_bound m ltac:(lia)) as Hb. lra.
  - (* telescoping with g m = 8 / sqrt (INR (m-1)) *)
    set (g := fun m => 8 * / sqrt (INR (m - 1))).
    rewrite (map_ext_in
      (fun m => 8 * / sqrt (INR (m-1)) - 8 * / sqrt (INR m))
      (fun m => g m - g (S m)) (seq 2 K)).
    + rewrite (Rlsum_telescope g K 2). unfold g.
      replace (2 - 1)%nat with 1%nat by lia. rewrite INR_1, sqrt_1, Rinv_1.
      assert (Hnn : 0 <= 8 * / sqrt (INR (2 + K - 1))).
      { apply Rmult_le_pos; [ lra | apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0, lt_0_INR; lia ]. }
      lra.
    + intros m Hm. apply in_seq in Hm. unfold g.
      replace (S m - 1)%nat with m by lia. reflexivity.
Qed.
