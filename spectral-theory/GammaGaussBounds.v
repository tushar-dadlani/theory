(* ================================================================= *)
(*  GammaGaussBounds.v   (elementary bounds for the Gauss limit)        *)
(*                                                                    *)
(*  (1 - t/N)^N <= e^{-t}   for  0 <= t <= N.                          *)
(*  The clean dominating bound behind the monotone convergence         *)
(*    int_0^N (1-t/N)^N t^{s-1} dt  ->  int_0^inf e^{-t} t^{s-1} dt      *)
(*  used in the Gauss-limit representation of Gamma.                    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* (exp a)^N = exp (a * N) *)
Lemma exp_pow_nat : forall a N, (exp a) ^ N = exp (a * INR N).
Proof.
  intros a N. induction N as [| N IH].
  - simpl. rewrite Rmult_0_r, exp_0. reflexivity.
  - simpl pow. rewrite IH, <- exp_plus, S_INR. f_equal. ring.
Qed.

(* the dominating bound *)
Lemma one_minus_pow_le_exp : forall t N,
  0 <= t -> t <= INR N -> (1 - t / INR N) ^ N <= exp (- t).
Proof.
  intros t N Ht0 HtN.
  destruct N as [| N].
  - (* N = 0 : then t = 0 *)
    cbn [INR] in HtN. assert (t = 0) by lra. subst t.
    simpl. rewrite Ropp_0, exp_0. lra.
  - (* N >= 1 *)
    set (n := S N).
    assert (HN : 0 < INR n) by (unfold n; apply lt_0_INR; lia).
    assert (Hne : INR n <> 0) by (apply Rgt_not_eq; exact HN).
    set (x := t / INR n).
    assert (Hx0 : 0 <= x) by (unfold x; apply Rle_mult_inv_pos; [ exact Ht0 | exact HN ]).
    assert (Hxt : x * INR n = t) by (unfold x; field; exact Hne).
    assert (Hx1 : x <= 1).
    { apply (Rmult_le_reg_r (INR n)); [ exact HN | ]. rewrite Hxt, Rmult_1_l. exact HtN. }
    assert (Hle : 1 - x <= exp (- x)) by (pose proof (exp_ineq1_le (- x)); lra).
    assert (H0 : 0 <= 1 - x) by lra.
    eapply Rle_trans; [ apply (pow_incr (1 - x) (exp (- x)) n); split; assumption | ].
    rewrite exp_pow_nat. apply Req_le. f_equal.
    rewrite <- Hxt. ring.
Qed.

Print Assumptions one_minus_pow_le_exp.
