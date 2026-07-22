(* ================================================================= *)
(*  NxnZero.v                                                         *)
(*                                                                    *)
(*  GAP-FILL (analysis): n * x^n -> 0 for 0 <= x < 1, over R -- the      *)
(*  lemma LadderDerivR flagged as missing (not in stdlib).            *)
(*                                                                    *)
(*  Proof: SECOND-ORDER Bernoulli  (1+h)^n >= 1 + n h + n(n-1)/2 h^2    *)
(*  (ber2, by induction) gives, for x = 1/(1+h) in (0,1),              *)
(*     n x^n <= 2 / ((n-1) h^2)  ->  0                                 *)
(*  by squeezing against 2/h^2 * /(n-1) (which -> 0 via cv_infty_cv_0). *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* second-order Bernoulli inequality *)
Lemma ber2 : forall n h, 0 <= h ->
  1 + INR n * h + INR n * (INR n - 1) / 2 * h ^ 2 <= (1 + h) ^ n.
Proof.
  induction n as [|n IH]; intros h Hh.
  - simpl; lra.
  - assert (Hn : 0 <= INR n) by apply pos_INR.
    assert (Hq : 0 <= INR n * (INR n - 1)).
    { destruct n; [ simpl; lra | rewrite S_INR;
        assert (0 <= INR n) by apply pos_INR; nra ]. }
    assert (Hle := IH h Hh).
    assert (H3 : (1 + h) * (1 + INR n * h + INR n * (INR n - 1) / 2 * h ^ 2)
                 <= (1 + h) * (1 + h) ^ n)
      by (apply Rmult_le_compat_l; lra).
    assert (Hcube : 0 <= INR n * (INR n - 1) * h ^ 3)
      by (apply Rmult_le_pos; [ exact Hq | apply pow_le; lra ]).
    rewrite S_INR; simpl ((1 + h) ^ S n).
    apply Rle_trans with ((1 + h) * (1 + INR n * h + INR n * (INR n - 1) / 2 * h ^ 2));
      [ nra | exact H3 ].
Qed.

(* a small squeeze theorem *)
Lemma squeeze0 : forall (u w : nat -> R) (N0 : nat),
  (forall n, (N0 <= n)%nat -> 0 <= u n <= w n) -> Un_cv w 0 -> Un_cv u 0.
Proof.
  intros u w N0 Hb Hw eps Heps.
  destruct (Hw eps Heps) as [N1 HN1].
  exists (Nat.max N0 N1); intros n Hn.
  destruct (Hb n ltac:(lia)) as [Hlo Hhi].
  specialize (HN1 n ltac:(lia)).
  unfold R_dist in *; rewrite Rminus_0_r in *.
  rewrite (Rabs_pos_eq (u n)) by exact Hlo.
  apply Rle_lt_trans with (Rabs (w n)); [ | exact HN1 ].
  rewrite (Rabs_pos_eq (w n)) by lra; exact Hhi.
Qed.

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists O; intros n _; unfold R_dist.
  replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

(* THE CRUX: n * x^n -> 0 for 0 <= x < 1 *)
Theorem nxn_zero : forall x, 0 <= x -> x < 1 -> Un_cv (fun n => INR n * x ^ n) 0.
Proof.
  intros x Hx0 Hx1.
  destruct (Req_dec x 0) as [Hx | Hxne].
  - (* x = 0: the sequence is 0 for n >= 1 *)
    intros eps Heps; exists 1%nat; intros n Hn.
    unfold R_dist; replace (INR n * x ^ n) with 0.
    + rewrite Rminus_0_r, Rabs_R0; exact Heps.
    + subst x; destruct n; [ lia | simpl; ring ].
  - assert (Hxpos : 0 < x) by lra.
    set (h := (1 - x) / x).
    assert (Hh : 0 < h) by (unfold h; apply Rdiv_lt_0_compat; lra).
    assert (H1h : 1 + h = / x) by (unfold h; field; lra).
    assert (Hxeq : x = / (1 + h)) by (rewrite H1h, Rinv_inv; reflexivity).
    (* w n = 2/h^2 * /(INR n - 1) -> 0 *)
    assert (Hinf : cv_infty (fun n => INR n - 1)).
    { intros M; destruct (INR_unbounded (M + 1)) as [N HN]; exists N; intros n Hn.
      assert (INR N <= INR n) by (apply le_INR; exact Hn); lra. }
    assert (Hw : Un_cv (fun n => 2 / h ^ 2 * / (INR n - 1)) 0).
    { replace 0 with (2 / h ^ 2 * 0) by ring.
      apply CV_mult; [ apply Un_cv_const | apply cv_infty_cv_0; exact Hinf ]. }
    apply squeeze0 with (w := fun n => 2 / h ^ 2 * / (INR n - 1)) (N0 := 2%nat).
    2: exact Hw.
    intros n Hn.
    assert (Hn2 : 2 <= INR n) by (apply (le_INR 2 n); exact Hn).
    assert (Hxn_pos : 0 <= x ^ n) by (apply pow_le; lra).
    assert (Hnn : 0 <= INR n) by apply pos_INR.
    split; [ apply Rmult_le_pos; assumption | ].
    (* upper bound: INR n * x^n <= 2/h^2 * /(INR n - 1) *)
    assert (Hpow : INR n * (INR n - 1) / 2 * h ^ 2 <= (1 + h) ^ n).
    { pose proof (ber2 n h (Rlt_le _ _ Hh)) as Hb; nra. }
    assert (HQ : 0 < INR n * (INR n - 1) / 2 * h ^ 2) by nra.
    assert (Hxn : x ^ n = / (1 + h) ^ n)
      by (rewrite Hxeq; rewrite Rinv_pow_depr; [ reflexivity | lra ]).
    rewrite Hxn.
    apply Rle_trans with (INR n * / (INR n * (INR n - 1) / 2 * h ^ 2)).
    + apply Rmult_le_compat_l; [ exact Hnn | ].
      apply Rinv_le_contravar; [ exact HQ | exact Hpow ].
    + apply Req_le; field; lra.
Qed.

Print Assumptions nxn_zero.

(* ================================================================= *)
(*  END NxnZero.v                                                     *)
(*  n * x^n -> 0 for 0 <= x < 1, via second-order Bernoulli + squeeze.  *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)
