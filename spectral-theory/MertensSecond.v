(* ================================================================= *)
(*  MertensSecond.v                                                   *)
(*                                                                    *)
(*  Toward Mertens' second theorem  sum_{p<=N} 1/p = ln ln N + O(1).  *)
(*                                                                    *)
(*  ANALYTIC CORE (this file): the iterated-logarithm estimate        *)
(*     sum_{n=2}^N 1/(n ln n)  =  ln ln N + O(1),                      *)
(*  established by an MVT per-step bracket on F(t) = ln(ln t),         *)
(*  F'(t) = 1/(t ln t), exactly as HarmonicSum does 1/t via ln.       *)
(*  This is where the ln ln N of Mertens 2 comes from.                *)
(*                                                                    *)
(*  All Qed; only the standard classical-Reals axioms.                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound.
Open Scope R_scope.

(* g n = 1/(n ln n),  F n = ln (ln n) *)
Definition gll (n : nat) : R := / (INR n * ln (INR n)).
Definition Fll (n : nat) : R := ln (ln (INR n)).

Lemma ln_le_mono : forall a b, 0 < a -> a <= b -> ln a <= ln b.
Proof.
  intros a b Ha Hab. destruct (Req_dec a b) as [->|Hne];
    [ lra | apply Rlt_le, ln_increasing; lra ].
Qed.

(* t ln t is nondecreasing on [2,oo) *)
Lemma tlnt_mono : forall a b, 2 <= a -> a <= b -> a * ln a <= b * ln b.
Proof.
  intros a b Ha Hab.
  assert (Hlnb : 0 <= ln b) by (rewrite <- ln_1; apply ln_le_mono; lra).
  apply Rle_trans with (a * ln b).
  - apply Rmult_le_compat_l; [ lra | apply ln_le_mono; lra ].
  - apply Rmult_le_compat_r; [ exact Hlnb | exact Hab ].
Qed.

(* d/dt ln(ln t) = 1/(t ln t) *)
Lemma dLL : forall t, 1 < t -> derivable_pt_lim (fun u => ln (ln u)) t (/ (t * ln t)).
Proof.
  intros t Ht.
  assert (Hlt : 0 < ln t) by (rewrite <- ln_1; apply ln_increasing; lra).
  pose proof (derivable_pt_lim_comp ln ln t (/ t) (/ ln t)
                (derivable_pt_lim_ln t ltac:(lra))
                (derivable_pt_lim_ln (ln t) Hlt)) as Hc.
  replace (/ (t * ln t)) with (/ ln t * / t) by (field; lra). exact Hc.
Qed.

(* the per-step MVT bracket *)
Lemma llstep : forall n, (2 <= n)%nat ->
  gll (S n) <= Fll (S n) - Fll n <= gll n.
Proof.
  intros n Hn. unfold gll, Fll.
  assert (H1 : 2 <= INR n) by (apply (le_INR 2); lia).
  assert (HSlt : INR n < INR (S n)) by (rewrite S_INR; lra).
  destruct (MVT_cor2 (fun u => ln (ln u)) (fun t => / (t * ln t)) (INR n) (INR (S n)) HSlt
              (fun c Hc => dLL c ltac:(lra))) as [xi [Heq [Hlo Hhi]]].
  replace (INR (S n) - INR n) with 1 in Heq by (pose proof (S_INR n); lra).
  rewrite Rmult_1_r in Heq. rewrite Heq.
  assert (Hxi2 : 2 <= xi) by lra.
  assert (Hlnxi : 0 < ln xi) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (Hlnn : 0 < ln (INR n)) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (HlnSn : 0 < ln (INR (S n))) by (rewrite <- ln_1; apply ln_increasing; [ lra | rewrite S_INR; lra ]).
  assert (Hpn : 0 < INR n * ln (INR n)) by (apply Rmult_lt_0_compat; lra).
  assert (HpSn : 0 < INR (S n) * ln (INR (S n))) by (apply Rmult_lt_0_compat; [ rewrite S_INR; lra | lra ]).
  assert (Hpxi : 0 < xi * ln xi) by (apply Rmult_lt_0_compat; lra).
  split.
  - apply Rinv_le_contravar; [ exact Hpxi | ].
    apply tlnt_mono; [ exact Hxi2 | lra ].
  - apply Rinv_le_contravar; [ exact Hpn | ].
    apply tlnt_mono; [ exact H1 | lra ].
Qed.

(* Rsum one-step extension at a general base *)
Lemma Rsum_succ_gen : forall f a n, Rsum f a (S n) = Rsum f a n + f (a + n)%nat.
Proof.
  intros f a n. replace (S n) with (n + 1)%nat by lia.
  rewrite Rsum_split. f_equal. unfold Rsum; cbn [seq map fold_right]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Telescoping brackets: sum_{n} 1/(n ln n) ~ ln ln                 *)
(* ----------------------------------------------------------------- *)

(* UPPER:  sum_{n=3}^{K+2} 1/(n ln n) <= ln ln(K+2) - ln ln 2        *)
Lemma ILog_upper : forall K,
  Rsum (fun n => gll (S n)) 2 K <= Fll (2 + K) - Fll 2.
Proof.
  induction K as [|K IH].
  - unfold Rsum; cbn [seq map fold_right]. rewrite Nat.add_0_r. lra.
  - rewrite Rsum_succ_gen.
    pose proof (llstep (2 + K) ltac:(lia)) as [Hl _].
    replace (2 + S K)%nat with (S (2 + K)) by lia. lra.
Qed.

(* LOWER:  ln ln(K+2) - ln ln 2 <= sum_{n=2}^{K+1} 1/(n ln n)        *)
Lemma ILog_lower : forall K,
  Fll (2 + K) - Fll 2 <= Rsum gll 2 K.
Proof.
  induction K as [|K IH].
  - unfold Rsum; cbn [seq map fold_right]. rewrite Nat.add_0_r. lra.
  - rewrite Rsum_succ_gen.
    pose proof (llstep (2 + K) ltac:(lia)) as [_ Hr].
    replace (2 + S K)%nat with (S (2 + K)) by lia. lra.
Qed.

(* Packaged: the iterated-log sum is ln ln N up to a bounded error.    *)
(* sum_{n=2}^{N+1} 1/(n ln n) lies within [ln ln(N+2)-ln ln 2,         *)
(*  gll 2 + ln ln(N+2) - ln ln 2].                                    *)
Theorem iterated_log_bracket : forall K,
  Fll (2 + K) - Fll 2 <= Rsum gll 2 K
  /\ Rsum (fun n => gll (S n)) 2 K <= Fll (2 + K) - Fll 2.
Proof. intro K; split; [ apply ILog_lower | apply ILog_upper ]. Qed.

Print Assumptions iterated_log_bracket.
