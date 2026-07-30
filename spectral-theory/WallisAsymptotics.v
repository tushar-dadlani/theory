(* ================================================================= *)
(*  WallisAsymptotics.v  —  Gaussian part-A stack, step 3: the Wallis  *)
(*  limits.                                                            *)
(*                                                                    *)
(*  From the product (n+1)WₙW_{n+1} = π/2 and the ratio bounds         *)
(*  (n+1)/(n+2) ≤ W_{n+1}/Wₙ ≤ 1 (WallisProduct):                     *)
(*                                                                    *)
(*    Wallis_ratio_cv : W_{n+1}/Wₙ → 1        (|ratio−1| ≤ 1/(n+2));   *)
(*    Wallis_sq_asymp : (n+1)·Wₙ² → π/2       (squeeze via the         *)
(*                      cross bound (n+1)Wₙ ≤ (n+2)W_{n+1}):           *)
(*        π/2 ≤ (n+1)Wₙ² ≤ (n+2)/(n+1)·π/2, so the gap ≤ π/(2(n+1)).   *)
(*                                                                    *)
(*  So Wₙ ~ √(π/(2(n+1))) — the value both sides of the Gaussian       *)
(*  squeeze converge to.  No new axioms (classical Reals only).       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import WallisIntegral WallisProduct.
Open Scope R_scope.

(* the cleared (division-free) form of the lower ratio bound *)
Lemma Wallis_cross : forall n, (INR n + 1) * Wallis n <= (INR n + 2) * Wallis (S n).
Proof.
  intro n; pose proof (pos_INR n) as Hn0.
  pose proof (Wallis_monotone (S n)) as Hm2.
  rewrite (Wallis_rec n), !S_INR in Hm2.
  replace (INR n + 1 + 1) with (INR n + 2) in Hm2 by ring.
  apply Rmult_le_reg_l with (/ (INR n + 2)); [ apply Rinv_0_lt_compat; lra | ].
  replace (/ (INR n + 2) * ((INR n + 1) * Wallis n))
    with ((INR n + 1) / (INR n + 2) * Wallis n) by (field; lra).
  replace (/ (INR n + 2) * ((INR n + 2) * Wallis (S n))) with (Wallis (S n)) by (field; lra).
  exact Hm2.
Qed.

(* ----------------------------------------------------------------- *)
(*  The ratio tends to 1.                                             *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_ratio_cv : Un_cv (fun n => Wallis (S n) / Wallis n) 1.
Proof.
  intros eps Heps.
  destruct (INR_unbounded (/ eps)) as [N HN].
  exists N; intros n Hn.
  destruct (Wallis_ratio_bounds n) as [Hlo Hhi].
  pose proof (pos_INR n) as Hn0.
  assert (Heq : 1 - (INR n + 1) / (INR n + 2) = / (INR n + 2)) by (field; lra).
  assert (Hbound : 1 - Wallis (S n) / Wallis n <= / (INR n + 2)) by lra.
  assert (Hlt : / (INR n + 2) < eps).
  { assert (Hn2 : / eps < INR n + 2) by (pose proof (le_INR N n Hn); lra).
    rewrite <- (Rinv_inv eps).
    apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact Heps | lra ] | exact Hn2 ]. }
  unfold R_dist; rewrite Rabs_left1 by lra; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  (n+1)·Wₙ² → π/2.                                                  *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_sq_asymp : Un_cv (fun n => (INR n + 1) * (Wallis n) ^ 2) (PI / 2).
Proof.
  intros eps Heps.
  destruct (INR_unbounded (PI / (2 * eps))) as [N HN].
  exists N; intros n Hn.
  pose proof (pos_INR n) as Hn0.
  pose proof (Wallis_pos n) as HW.
  pose proof (Wallis_pos (S n)) as HW'.
  pose proof (Wallis_product n) as HP.
  pose proof (Wallis_monotone n) as Hm.
  pose proof (Wallis_cross n) as Hc.
  assert (Hpos_nW : 0 <= (INR n + 1) * Wallis n) by (apply Rmult_le_pos; lra).
  assert (Hlow : PI / 2 <= (INR n + 1) * (Wallis n) ^ 2).
  { replace ((Wallis n) ^ 2) with (Wallis n * Wallis n) by ring; nra. }
  pose proof (Rmult_le_compat_r ((INR n + 1) * Wallis n) ((INR n + 1) * Wallis n)
                ((INR n + 2) * Wallis (S n)) Hpos_nW Hc) as Hmm.
  assert (Hrhs : (INR n + 2) * Wallis (S n) * ((INR n + 1) * Wallis n) = (INR n + 2) * (PI / 2))
    by (rewrite <- HP; ring).
  rewrite Hrhs in Hmm.
  assert (Hmul : (INR n + 1) * ((INR n + 1) * (Wallis n) ^ 2 - PI / 2) <= PI / 2).
  { replace ((Wallis n) ^ 2) with (Wallis n * Wallis n) by ring; nra. }
  assert (Hbig : PI / 2 < (INR n + 1) * eps).
  { assert (Hlt' : PI / (2 * eps) < INR n + 1) by (pose proof (le_INR N n Hn); lra).
    pose proof (Rmult_lt_compat_r eps (PI / (2 * eps)) (INR n + 1) Heps Hlt') as Hb.
    replace (PI / (2 * eps) * eps) with (PI / 2) in Hb by (field; lra); exact Hb. }
  unfold R_dist; rewrite Rabs_right by lra.
  apply Rmult_lt_reg_l with (INR n + 1); [ lra | ].
  eapply Rle_lt_trans; [ exact Hmul | exact Hbig ].
Qed.

Print Assumptions Wallis_ratio_cv.
Print Assumptions Wallis_sq_asymp.

(* ================================================================= *)
(*  END WallisAsymptotics.v                                          *)
(*  W_{n+1}/Wₙ → 1 and (n+1)Wₙ² → π/2.  The last purely-Wallis step;    *)
(*  next is the Gaussian squeeze reducing ∫₀^√n(1−x²/n)ⁿ and           *)
(*  ∫₀^∞(1+x²/n)⁻ⁿ to Wallis integrals.                               *)
(* ================================================================= *)
