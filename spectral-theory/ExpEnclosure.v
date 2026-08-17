(* ================================================================= *)
(*  ExpEnclosure.v  —  Stage 3, brick 2: rigorous enclosure of exp.      *)
(*                                                                    *)
(*  A two-sided bound on exp x from the elementary inequality           *)
(*  1 + y <= exp y <= 1/(1-y) (both from exp_ineq1_le) applied to        *)
(*  y = x/n and raised to the n-th power (exp x = (exp(x/n))^n):         *)
(*                                                                    *)
(*    exp_enclose_real : 0 < n -> -1 <= x/n -> x/n < 1 ->               *)
(*      (1 + x/n)^n <= exp x <= (/(1 - x/n))^n.                         *)
(*                                                                    *)
(*  Both endpoints are rational when x is rational and n a nat, so the   *)
(*  Q-packaged Iexp (next) is vm_compute-able.  (This elementary bound   *)
(*  converges as O(x^2/n); a Taylor-remainder version -- faster for      *)
(*  large |x| -- is a later refinement.  For the tail region large |x|   *)
(*  contributions are already killed by ReTC_tail_bound.)               *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* exp(n.y) = (exp y)^n *)
Lemma exp_INR_pow : forall n y, exp (INR n * y) = (exp y) ^ n.
Proof.
  induction n as [| n IH]; intro y.
  - simpl; rewrite Rmult_0_l, exp_0; reflexivity.
  - rewrite S_INR. replace ((INR n + 1) * y) with (INR n * y + y) by ring.
    rewrite exp_plus, IH; simpl; ring.
Qed.

(* exp y <= 1/(1-y) for y < 1 *)
Lemma exp_le_inv1 : forall y, y < 1 -> exp y <= / (1 - y).
Proof.
  intros y Hy. assert (Hpos : 0 < 1 - y) by lra.
  apply Rmult_le_reg_r with (1 - y); [ exact Hpos | ].
  rewrite Rinv_l by lra.
  apply Rle_trans with (exp y * exp (- y)).
  - apply Rmult_le_compat_l; [ left; apply exp_pos | ].
    pose proof (exp_ineq1_le (- y)); lra.
  - rewrite <- exp_plus. replace (y + - y) with 0 by ring. rewrite exp_0; lra.
Qed.

Theorem exp_enclose_real : forall x n, (0 < n)%nat ->
  -1 <= x / INR n -> x / INR n < 1 ->
  (1 + x / INR n) ^ n <= exp x <= (/ (1 - x / INR n)) ^ n.
Proof.
  intros x n Hn Hlo Hhi. set (y := x / INR n) in *.
  assert (HInr : INR n <> 0) by (apply not_0_INR; lia).
  assert (Hx : exp x = (exp y) ^ n)
    by (unfold y; rewrite <- exp_INR_pow; f_equal; field; exact HInr).
  rewrite Hx. split.
  - apply pow_incr. split; [ lra | apply exp_ineq1_le ].
  - apply pow_incr. split; [ left; apply exp_pos | apply exp_le_inv1; exact Hhi ].
Qed.

Print Assumptions exp_enclose_real.
