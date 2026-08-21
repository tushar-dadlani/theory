(* ================================================================= *)
(*  RPowerTail.v  --  the tail of a p-series, at a GENERAL exponent.   *)
(*                                                                    *)
(*    ptail_ub : 1 < p,  1 <= N  ==>                                   *)
(*      Sum_{i=0}^{K} (N+i+1)^{-p}  <=  (1/(p-1)) * N^{-(p-1)}         *)
(*                                                                    *)
(*  THE MISSING BRICK for extending the zeta and zeta' bounds below    *)
(*  the line Re s = 1, which is what Tier B link [4] needs: the mean   *)
(*  value segment for a zero runs from beta < 1 up to a > 1, while     *)
(*  ZetaLogBound / ZetaDerivBound are stated on Re s >= 1.             *)
(*                                                                    *)
(*  Why nothing already in the repo serves.  ZetaStripBound has        *)
(*  pseries_partial_ub, but that bounds a HEAD (from index 0) and only *)
(*  yields the constant 1 + 1/(p-1); the split needs the TAIL, whose   *)
(*  size must DECAY in N.  ZetaLogBound has tail_tele and              *)
(*  ZetaDerivBound has logtail_tele, but both telescope against the    *)
(*  exact identity 1/(n(n+1)) = 1/n - 1/(n+1), which is available only *)
(*  at the integer exponent 2 -- i.e. only when Re s >= 1 exactly.     *)
(*                                                                    *)
(*  At Re s >= 1 - delta the tail exponent becomes -2 + delta and that *)
(*  identity is gone.  A crude majorant does not rescue it: rounding   *)
(*  the exponent down to -3/2 forces the cut N >~ t^2, while the head's *)
(*  G-piece (which contributes ~ N/|t| terms) forces N <~ t.  Those    *)
(*  are incompatible, so the bound stays polynomial.  Checked          *)
(*  numerically: at t = 10^8 the -3/2 route leaves |s| * tail ~ 40000  *)
(*  while the sharp form below leaves ~ 5.7, flat in t.                *)
(*                                                                    *)
(*  The sharp form telescopes against t(n) = n^{-(p-1)} via the mean   *)
(*  value theorem, exactly the argument CZetaTerm.pseries_cv already   *)
(*  runs for its has_ub -- here generalised to start at an arbitrary N *)
(*  and to keep the resulting N^{-(p-1)}, which pseries_cv discards.   *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import CPowBase CZetaTerm.
Open Scope R_scope.

(* one step: the summand is dominated by a telescoping difference *)
Lemma ptail_step : forall p n, 1 < p -> (1 <= n)%nat ->
  Rpower (INR (S n)) (- p)
  <= (Rpower (INR n) (- (p - 1)) - Rpower (INR (S n)) (- (p - 1))) / (p - 1).
Proof.
  intros p n Hp Hn.
  set (q := p - 1). assert (Hq : 0 < q) by (unfold q; lra).
  assert (Hu : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Huv : INR n < INR (S n)) by (apply lt_INR; lia).
  assert (Hvu1 : INR (S n) - INR n = 1) by (rewrite S_INR; ring).
  assert (Hd : forall c, INR n <= c <= INR (S n) ->
               derivable_pt_lim (fun y => Rpower y (- q)) c (- q * Rpower c (- p))).
  { intros c Hc; replace (- p) with (- q - 1) by (unfold q; ring).
    apply Rpow_deriv; apply Rlt_le_trans with (INR n); [ exact Hu | apply (proj1 Hc) ]. }
  destruct (MVT_cor2 (fun y => Rpower y (- q)) (fun y => - q * Rpower y (- p))
             (INR n) (INR (S n)) Huv Hd) as [xi [Hxi [Hxu Hxv]]].
  rewrite Hvu1, Rmult_1_r in Hxi.
  assert (Hxipos : 0 < xi) by lra.
  assert (Htt : Rpower (INR n) (- q) - Rpower (INR (S n)) (- q)
              = q * Rpower xi (- p)) by nra.
  rewrite Htt.
  replace (q * Rpower xi (- p) / q) with (Rpower xi (- p)) by (field; lra).
  apply Rpow_negexp_anti; [ exact Hxipos | lra | lra ].
Qed.

(* THE TAIL BOUND *)
Theorem ptail_ub : forall p N K, 1 < p -> (1 <= N)%nat ->
  sum_f_R0 (fun i => Rpower (INR (S (N + i))) (- p)) K
  <= / (p - 1) * Rpower (INR N) (- (p - 1)).
Proof.
  intros p N K Hp HN.
  assert (Hq : 0 < p - 1) by lra.
  assert (Htel : forall K',
    sum_f_R0 (fun i => (Rpower (INR (N + i)) (- (p - 1))
                        - Rpower (INR (S (N + i))) (- (p - 1))) / (p - 1)) K'
    = (Rpower (INR N) (- (p - 1)) - Rpower (INR (S (N + K'))) (- (p - 1)))
      / (p - 1)).
  { induction K' as [| K' IHK].
    - cbn [sum_f_R0]. rewrite Nat.add_0_r. reflexivity.
    - rewrite tech5, IHK.
      assert (E : (S (N + K') = N + S K')%nat) by lia. rewrite E. field. lra. }
  eapply Rle_trans.
  - apply sum_Rle. intros i _. apply ptail_step; [ exact Hp | lia ].
  - rewrite Htel.
    assert (Hpos : 0 <= Rpower (INR (S (N + K))) (- (p - 1)))
      by (left; unfold Rpower; apply exp_pos).
    assert (E : / (p - 1) * Rpower (INR N) (- (p - 1))
              = Rpower (INR N) (- (p - 1)) / (p - 1)) by (field; lra).
    rewrite E.
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | lra ].
Qed.

(* the shape the below-1 extension consumes: p = 2 - delta *)
Corollary ptail_delta : forall d N K, 0 <= d -> d <= / 2 -> (1 <= N)%nat ->
  sum_f_R0 (fun i => Rpower (INR (S (N + i))) (- (2 - d))) K
  <= 2 * Rpower (INR N) (- (1 - d)).
Proof.
  intros d N K Hd0 Hd2 HN.
  pose proof (ptail_ub (2 - d) N K ltac:(lra) HN) as H.
  replace (2 - d - 1) with (1 - d) in H by ring.
  assert (Hinv : / (1 - d) <= 2).
  { apply (Rmult_le_reg_r (1 - d)); [ lra | ].
    rewrite Rinv_l by lra. lra. }
  assert (Hpos : 0 <= Rpower (INR N) (- (1 - d)))
    by (left; unfold Rpower; apply exp_pos).
  assert (Hi0 : 0 < / (1 - d)) by (apply Rinv_0_lt_compat; lra).
  nra.
Qed.

Print Assumptions ptail_step.
Print Assumptions ptail_ub.
Print Assumptions ptail_delta.
