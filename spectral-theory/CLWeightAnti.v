(* ================================================================= *)
(*  CLWeightAnti.v  --  ln n * n^{-sigma} decreases from n = 3 on,    *)
(*  uniformly in sigma >= 1.                                          *)
(*                                                                    *)
(*  This is the hypothesis CAbelTail.Cabel_tail needs in order to      *)
(*  bound D(s) = sum chi(n) ln n n^{-s}.  The weight is NOT decreasing *)
(*  from the start -- it rises from n = 1 to n = 2 -- which is why     *)
(*  Cabel_tail was stated with a local monotonicity hypothesis.        *)
(*                                                                    *)
(*  NO CALCULUS IS USED.  The usual proof differentiates ln x / x.     *)
(*  Here it reduces to two elementary steps:                           *)
(*                                                                    *)
(*    sigma = 1 case:  ln y * x <= ln x * y  for  e <= x <= y.        *)
(*      From ln(y/x) <= y/x - 1 (itself just 1 + t < exp t), this      *)
(*      rearranges to (y - x)(ln x - 1) >= 0, which is immediate.      *)
(*                                                                    *)
(*    general sigma:  split x^sigma = x * x^{sigma-1} and use that     *)
(*      x^{sigma-1} <= y^{sigma-1} when sigma >= 1 and x <= y.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import CZetaTerm2.
Open Scope R_scope.

Lemma ln_le_sub1 : forall t, 0 < t -> ln t <= t - 1.
Proof.
  intros t Ht.
  assert (H : t <= exp (t - 1)).
  { destruct (Req_dec (t - 1) 0) as [E | E].
    - rewrite E, exp_0. lra.
    - pose proof (exp_ineq1 (t - 1) E). lra. }
  rewrite <- (ln_exp (t - 1)). apply ln_le'; [ exact Ht | exact H ].
Qed.

Lemma exp_mono_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H. destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq].
  - left. apply exp_increasing. exact Hlt.
  - right. f_equal. exact Heq.
Qed.

Lemma Rpower_base_mono : forall x y a, 0 < x -> x <= y -> 0 <= a ->
  Rpower x a <= Rpower y a.
Proof.
  intros x y a Hx Hxy Ha. unfold Rpower. apply exp_mono_le.
  apply Rmult_le_compat_l; [ exact Ha | apply ln_le'; [ exact Hx | exact Hxy ] ].
Qed.

Lemma Rpower_exp_anti : forall x a b, 1 <= x -> a <= b -> Rpower x a <= Rpower x b.
Proof.
  intros x a b Hx Hab. unfold Rpower. apply exp_mono_le.
  assert (Hl : 0 <= ln x) by (rewrite <- ln_1; apply ln_le'; lra).
  nra.
Qed.

(* the sigma = 1 case *)
Lemma lnx_over_x_antitone : forall x y, exp 1 <= x -> x <= y ->
  ln y * x <= ln x * y.
Proof.
  intros x y Hx Hxy.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (Hx0 : 0 < x) by lra.
  assert (Hy0 : 0 < y) by lra.
  assert (Hlnx : 1 <= ln x)
    by (rewrite <- (ln_exp 1); apply ln_le'; [ exact He | exact Hx ]).
  assert (Hdiv : ln y - ln x = ln (y / x)).
  { unfold Rdiv.
    rewrite (ln_mult y (/ x)) by (first [ lra | apply Rinv_0_lt_compat; lra ]).
    rewrite (ln_Rinv x) by lra. ring. }
  assert (Hkey : ln (y / x) <= y / x - 1)
    by (apply ln_le_sub1; apply Rdiv_lt_0_compat; lra).
  assert (Hmul : (ln y - ln x) * x <= y - x).
  { rewrite Hdiv. apply Rle_trans with ((y / x - 1) * x).
    - apply Rmult_le_compat_r; [ lra | exact Hkey ].
    - apply Req_le. unfold Rdiv.
      replace ((y * / x - 1) * x) with (y * (/ x * x) - x) by ring.
      rewrite Rinv_l by lra. ring. }
  nra.
Qed.

(* the general case, in the cross-multiplied form *)
Lemma ln_rpow_antitone : forall x y sig, 1 <= sig -> exp 1 <= x -> x <= y ->
  ln y * Rpower x sig <= ln x * Rpower y sig.
Proof.
  intros x y sig Hs Hx Hxy.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (He1 : 1 < exp 1) by (rewrite <- exp_0 at 1; apply exp_increasing; lra).
  assert (Hx0 : 0 < x) by lra.
  assert (Hx1 : 1 <= x) by lra.
  assert (Hy1 : 1 <= y) by lra.
  assert (Hlnx0 : 0 <= ln x) by (rewrite <- ln_1; apply ln_le'; lra).
  assert (Hlny0 : 0 <= ln y) by (rewrite <- ln_1; apply ln_le'; lra).
  assert (Hsp : Rpower x sig = x * Rpower x (sig - 1)).
  { replace sig with (1 + (sig - 1)) at 1 by ring.
    rewrite Rpower_plus, Rpower_1 by lra. reflexivity. }
  assert (Hsq : Rpower y sig = y * Rpower y (sig - 1)).
  { replace sig with (1 + (sig - 1)) at 1 by ring.
    rewrite Rpower_plus, Rpower_1 by lra. reflexivity. }
  assert (Hpp : Rpower x (sig - 1) <= Rpower y (sig - 1))
    by (apply Rpower_base_mono; lra).
  assert (Hp0 : 0 < Rpower x (sig - 1)) by (unfold Rpower; apply exp_pos).
  assert (Hstep1 : ln y * x <= ln x * y) by (apply lnx_over_x_antitone; assumption).
  rewrite Hsp, Hsq.
  apply Rle_trans with (ln x * y * Rpower x (sig - 1)).
  - replace (ln y * (x * Rpower x (sig - 1)))
      with ((ln y * x) * Rpower x (sig - 1)) by ring.
    apply Rmult_le_compat_r; [ lra | exact Hstep1 ].
  - replace (ln x * (y * Rpower y (sig - 1)))
      with ((ln x * y) * Rpower y (sig - 1)) by ring.
    apply Rmult_le_compat_l; [ nra | exact Hpp ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the weight itself                                                  *)
(* ----------------------------------------------------------------- *)

Definition wln (sig : R) (n : nat) : R :=
  ln (INR (S n)) * Rpower (INR (S n)) (- sig).

Lemma wln_nonneg : forall sig n, 0 <= wln sig n.
Proof.
  intros sig n. unfold wln. apply Rmult_le_pos.
  - rewrite <- ln_1. apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ].
  - apply Rlt_le. unfold Rpower. apply exp_pos.
Qed.

Lemma wln_le : forall sig n, 1 <= sig -> wln sig n <= ln (INR (S n)) / INR (S n).
Proof.
  intros sig n Hs. unfold wln.
  assert (Hb : 1 <= INR (S n)) by (rewrite <- INR_1; apply le_INR; lia).
  assert (Hl0 : 0 <= ln (INR (S n)))
    by (rewrite <- ln_1; apply ln_le'; lra).
  assert (Hstep : Rpower (INR (S n)) (- sig) <= Rpower (INR (S n)) (-1))
    by (apply Rpower_exp_anti; lra).
  assert (Hone : Rpower (INR (S n)) (-1) = / INR (S n)).
  { replace (-1) with (- (1)) by ring. rewrite Rpower_Ropp, Rpower_1 by lra.
    reflexivity. }
  rewrite Hone in Hstep. unfold Rdiv. nra.
Qed.

Theorem wln_anti : forall sig n, 1 <= sig -> (2 <= n)%nat ->
  0 <= wln sig (S n) /\ wln sig (S n) <= wln sig n.
Proof.
  intros sig n Hs Hn. split; [ apply wln_nonneg | ].
  unfold wln.
  set (x := INR (S n)). set (y := INR (S (S n))).
  assert (Hx3 : 3 <= x)
    by (unfold x; replace 3 with (INR 3) by (simpl; ring); apply le_INR; lia).
  assert (Hxy : x <= y) by (unfold x, y; apply le_INR; lia).
  assert (He : exp 1 <= x) by (pose proof exp_le_3; lra).
  assert (Hx0 : 0 < x) by lra.
  assert (Hy0 : 0 < y) by lra.
  assert (Hkey : ln y * Rpower x sig <= ln x * Rpower y sig)
    by (apply ln_rpow_antitone; assumption).
  assert (Hpx : 0 < Rpower x sig) by (unfold Rpower; apply exp_pos).
  assert (Hpy : 0 < Rpower y sig) by (unfold Rpower; apply exp_pos).
  assert (Hnx : Rpower x (- sig) = / Rpower x sig)
    by (rewrite Rpower_Ropp; reflexivity).
  assert (Hny : Rpower y (- sig) = / Rpower y sig)
    by (rewrite Rpower_Ropp; reflexivity).
  rewrite Hnx, Hny.
  apply (Rmult_le_reg_r (Rpower x sig)); [ exact Hpx | ].
  apply (Rmult_le_reg_r (Rpower y sig)); [ exact Hpy | ].
  replace (ln y * / Rpower y sig * Rpower x sig * Rpower y sig)
    with (ln y * Rpower x sig * (/ Rpower y sig * Rpower y sig)) by ring.
  replace (ln x * / Rpower x sig * Rpower x sig * Rpower y sig)
    with (ln x * Rpower y sig * (/ Rpower x sig * Rpower x sig)) by ring.
  rewrite Rinv_l by lra. rewrite Rinv_l by lra. lra.
Qed.

Print Assumptions wln_anti.

(* ================================================================= *)
(*  END CLWeightAnti.v                                                *)
(* ================================================================= *)
