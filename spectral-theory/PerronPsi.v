(* ================================================================= *)
(*  PerronPsi.v  —  Perron A2: the truncated Perron formula for psi.      *)
(*                                                                    *)
(*  At the half-integer  x = N + 1/2  (so |ln(x/m)| >= 1/(2(N+1))       *)
(*  avoids the diagonal blow-up), for c>1, T>0, and any L with          *)
(*  Cseries_cv PT L (PT = the per-term Perron series, supplied by         *)
(*  perron_identity):                                                    *)
(*                                                                    *)
(*    Cmod (L - psi N)  <=  4(N+1) x^c / (pi T) * D,                     *)
(*      D = Sum_{m>=1} Lam(m) m^{-c}  (convergent).                      *)
(*                                                                    *)
(*  Route: split the K-th partial Perron sum at N, bound the below-       *)
(*  diagonal block by perron_gt1 and the above-diagonal by perron_lt1,    *)
(*  each per-term error <= maj m via the elementary ln y >= 1-1/y         *)
(*  diagonal estimate; then let K -> oo (Rle_cv_lim).  Axiom-clean.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import ComplexField Cmodulus CDeriv CSeries CIntegral2 CSegInt
        CexpFull VonMangoldtGlobal Chebyshev CVonMangoldtSeries
        PerronVertical PerronGt1 PerronLt1 PerronSeriesInt PerronIdentity.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  0.  elementary building blocks (global)                            *)
(* ----------------------------------------------------------------- *)

Lemma ln_le_lin : forall y, 0 < y -> ln y <= y - 1.
Proof.
  intros y Hy; pose proof (exp_ineq1_le (ln y)) as H; rewrite exp_ln in H by exact Hy; lra.
Qed.

Lemma ln_ge_1_minus_inv : forall y, 0 < y -> 1 - / y <= ln y.
Proof.
  intros y Hy; assert (Hiy : 0 < / y) by (apply Rinv_0_lt_compat; exact Hy).
  pose proof (ln_le_lin (/ y) Hiy) as H; rewrite ln_Rinv in H by exact Hy; lra.
Qed.

Lemma one_lt_div : forall a b, 0 < b -> b < a -> 1 < a / b.
Proof.
  intros a b Hb Hba; apply Rmult_lt_reg_r with b; [ exact Hb | rewrite Rmult_1_l ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rgt_not_eq; exact Hb); exact Hba.
Qed.

Lemma div_lt_one : forall a b, 0 < b -> a < b -> a / b < 1.
Proof.
  intros a b Hb Hab; apply Rmult_lt_reg_r with b; [ exact Hb | rewrite Rmult_1_l ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rgt_not_eq; exact Hb); exact Hab.
Qed.

(*  the two diagonal lower bounds *)
Lemma core_lb1 : forall a Nr, 0 <= Nr -> a <= Nr ->
  / (2 * (Nr + 1)) <= 1 - a / (Nr + / 2).
Proof.
  intros a Nr HNr Ha.
  assert (Hxx : 0 < Nr + / 2) by lra.
  apply Rmult_le_reg_r with (Nr + / 2); [ exact Hxx | ].
  replace ((1 - a / (Nr + / 2)) * (Nr + / 2)) with (Nr + / 2 - a) by (field; lra).
  apply Rle_trans with (/ 2).
  - apply Rmult_le_reg_l with (2 * (Nr + 1)); [ lra | ].
    replace (2 * (Nr + 1) * (/ (2 * (Nr + 1)) * (Nr + / 2))) with (Nr + / 2) by (field; lra).
    replace (2 * (Nr + 1) * / 2) with (Nr + 1) by field; lra.
  - lra.
Qed.

Lemma core_lb2 : forall z Nr, 0 <= Nr -> Nr + 1 <= z ->
  / (2 * (Nr + 1)) <= 1 - (Nr + / 2) / z.
Proof.
  intros z Nr HNr Hz; assert (Hz0 : 0 < z) by lra.
  apply Rmult_le_reg_r with z; [ exact Hz0 | ].
  replace ((1 - (Nr + / 2) / z) * z) with (z - (Nr + / 2)) by (field; lra).
  apply Rle_trans with (/ (2 * (Nr + 1)) * z); [ apply Rle_refl | ].
  apply Rmult_le_reg_l with (2 * (Nr + 1)); [ lra | ].
  replace (2 * (Nr + 1) * (/ (2 * (Nr + 1)) * z)) with z by (field; lra).
  nra.
Qed.

Lemma Cpsum_minus : forall (a b : nat -> C) N,
  Cpsum (fun n => Cminus (a n) (b n)) N = Cminus (Cpsum a N) (Cpsum b N).
Proof. induction N as [|N IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma psi_0 : psi 0 = 0.
Proof. reflexivity. Qed.

Lemma psi_S : forall N, psi (S N) = psi N + Lam (S N).
Proof.
  intro N; unfold psi; rewrite seq_S, map_app, Rsum_app; cbn [map fold_right].
  replace (1 + N)%nat with (S N) by lia; ring.
Qed.

Lemma dseries_cv : forall c, 1 < c ->
  { D | Un_cv (sum_f_R0 (fun n => Lam (S n) * Rpower (INR (S n)) (- c))) D }.
Proof.
  intros c Hc1.
  apply (Rseries_abs_cv (fun n => Lam (S n) * Rpower (INR (S n)) (- c)) (blam (mkC c 0))).
  - intro n; rewrite Rabs_pos_eq.
    + unfold blam; cbn [Re]; apply Rmult_le_compat_r;
        [ left; unfold Rpower; apply exp_pos | apply Lam_le_ln; lia ].
    + apply Rmult_le_pos; [ apply Lam_nonneg | left; unfold Rpower; apply exp_pos ].
  - apply blam_sum_cv; exact Hc1.
Qed.

(* ----------------------------------------------------------------- *)
(*  1.  the truncated Perron statement                                 *)
(* ----------------------------------------------------------------- *)

Section PPsi.
Variables (N : nat) (c T : R).
Hypothesis Hc1 : 1 < c.
Hypothesis HT : 0 < T.

Definition xx : R := INR N + / 2.

Lemma xx_pos : 0 < xx.
Proof. unfold xx; pose proof (pos_INR N); lra. Qed.

Let Hcpos : 0 < c := Rlt_trans 0 1 c Rlt_0_1 Hc1.
Let Hcne : c <> 0 := Hc c Hc1.

Definition PT (n : nat) : C := Cmul (RtoC (Lam (S n))) (Vperron (xx / INR (S n)) c T Hcne).
Definition LT (n : nat) : C := if (n <? N)%nat then RtoC (Lam (S n)) else C0.
Definition dser (n : nat) : R := Lam (S n) * Rpower (INR (S n)) (- c).
Definition maj (n : nat) : R := 4 * (INR N + 1) * Rpower xx c / (PI * T) * dser n.

(*  psi N as the truncated indicator Cpsum  *)
Lemma LTsum : forall M, Cpsum LT M = RtoC (psi (Nat.min (S M) N)).
Proof.
  induction M as [|M IH].
  - change (Cpsum LT 0) with (LT 0); unfold LT; destruct (0 <? N)%nat eqn:Hb.
    + apply Nat.ltb_lt in Hb; rewrite (Nat.min_l 1 N ltac:(lia)).
      f_equal; rewrite (psi_S 0), psi_0; ring.
    + apply Nat.ltb_ge in Hb; rewrite (Nat.min_r 1 N ltac:(lia)).
      replace N with 0%nat by lia; rewrite psi_0; reflexivity.
  - simpl (Cpsum LT (S M)); rewrite IH; unfold LT; destruct (S M <? N)%nat eqn:Hb.
    + apply Nat.ltb_lt in Hb.
      rewrite (Nat.min_l (S M) N ltac:(lia)), (Nat.min_l (S (S M)) N ltac:(lia)).
      rewrite (psi_S (S M)), RtoC_add; reflexivity.
    + apply Nat.ltb_ge in Hb.
      rewrite (Nat.min_r (S M) N ltac:(lia)), (Nat.min_r (S (S M)) N ltac:(lia)); ring.
Qed.

Lemma Cpsum_LT_ge : forall M, (N <= M)%nat -> Cpsum LT M = RtoC (psi N).
Proof. intros M HM; rewrite LTsum, (Nat.min_r (S M) N ltac:(lia)); reflexivity. Qed.

(*  the per-term error bound: below-diagonal via perron_gt1, above via lt1  *)
Lemma gterm_bd : forall n, Cmod (Cminus (PT n) (LT n)) <= maj n.
Proof.
  intro n.
  assert (HSn : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (Hxx : 0 < xx) by apply xx_pos.
  assert (Hy0 : 0 < xx / INR (S n)) by (apply Rdiv_lt_0_compat; [ exact Hxx | exact HSn ]).
  pose proof PI_RGT_0 as HPI.
  assert (Hrpq : Rpower (xx / INR (S n)) c = Rpower xx c * Rpower (INR (S n)) (- c))
    by (apply Rpower_div_base; [ exact Hxx | exact HSn ]).
  assert (Hfac : 0 <= Lam (S n) * 2 * Rpower xx c * Rpower (INR (S n)) (- c) / (PI * T)).
  { unfold Rdiv; apply Rmult_le_pos.
    - apply Rmult_le_pos;
        [ apply Rmult_le_pos;
            [ apply Rmult_le_pos; [ apply Lam_nonneg | lra ]
            | left; unfold Rpower; apply exp_pos ]
        | left; unfold Rpower; apply exp_pos ].
    - left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; [ exact HPI | exact HT ]. }
  destruct (n <? N)%nat eqn:Hb.
  - (* below diagonal: xx/INR(S n) > 1, perron_gt1 *)
    apply Nat.ltb_lt in Hb.
    assert (Hsnle : INR (S n) <= INR N) by (apply le_INR; lia).
    assert (Hy1 : 1 < xx / INR (S n))
      by (apply one_lt_div; [ exact HSn | unfold xx; lra ]).
    assert (Hlny : 0 < ln (xx / INR (S n)))
      by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Hcore : / (2 * (INR N + 1)) <= ln (xx / INR (S n))).
    { eapply Rle_trans; [ apply (core_lb1 (INR (S n)) (INR N) (pos_INR N) Hsnle) | ].
      replace (INR (S n) / (INR N + / 2)) with (/ (xx / INR (S n)))
        by (unfold xx; rewrite Rinv_div; reflexivity).
      apply ln_ge_1_minus_inv; exact Hy0. }
    assert (Hinv : / ln (xx / INR (S n)) <= 2 * (INR N + 1)).
    { apply Rle_trans with (/ / (2 * (INR N + 1)));
        [ apply Rinv_le_contravar;
            [ apply Rinv_0_lt_compat; pose proof (pos_INR N); lra | exact Hcore ]
        | rewrite Rinv_inv; apply Rle_refl ]. }
    assert (Hgt : Cminus (PT n) (LT n)
              = Cmul (RtoC (Lam (S n))) (Cminus (Vperron (xx / INR (S n)) c T Hcne) C1)).
    { unfold PT, LT; rewrite (proj2 (Nat.ltb_lt n N) Hb); ring. }
    rewrite Hgt, Cmod_mul, Cmod_RtoC, (Rabs_pos_eq (Lam (S n)) (Lam_nonneg (S n))).
    eapply Rle_trans;
      [ apply Rmult_le_compat_l;
          [ apply Lam_nonneg | apply (perron_gt1 (xx / INR (S n)) c T Hy1 Hcpos HT Hcne) ]
      | ].
    rewrite Hrpq; unfold maj, dser.
    apply Rle_trans with
      (Lam (S n) * 2 * Rpower xx c * Rpower (INR (S n)) (- c) / (PI * T) * (2 * (INR N + 1))).
    + replace (Lam (S n) * (2 * (Rpower xx c * Rpower (INR (S n)) (- c))
                            / (PI * T * ln (xx / INR (S n)))))
        with (Lam (S n) * 2 * Rpower xx c * Rpower (INR (S n)) (- c) / (PI * T)
              * / ln (xx / INR (S n)))
        by (field; repeat split; intro Hz; nra).
      apply Rmult_le_compat_l; [ exact Hfac | exact Hinv ].
    + apply Req_le; field; repeat split; intro Hz; nra.
  - (* below-diagonal branch done; above diagonal: xx/INR(S n) < 1, perron_lt1 *)
    apply Nat.ltb_ge in Hb.
    assert (Hsnge : INR N + 1 <= INR (S n))
      by (replace (INR N + 1) with (INR (S N)) by (rewrite S_INR; ring);
          apply le_INR; lia).
    assert (Hy1 : xx / INR (S n) < 1)
      by (apply div_lt_one; [ exact HSn | unfold xx; lra ]).
    assert (Hlny : ln (xx / INR (S n)) < 0)
      by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Hnln : 0 < - ln (xx / INR (S n))) by lra.
    assert (Hcore : / (2 * (INR N + 1)) <= - ln (xx / INR (S n))).
    { apply Rle_trans with (1 - (INR N + / 2) / INR (S n));
        [ apply (core_lb2 (INR (S n)) (INR N) (pos_INR N) Hsnge) | ].
      assert (H1 : 1 - / / (xx / INR (S n)) <= ln (/ (xx / INR (S n))))
        by (apply ln_ge_1_minus_inv, Rinv_0_lt_compat; exact Hy0).
      rewrite Rinv_inv, ln_Rinv in H1 by exact Hy0.
      unfold xx in *; lra. }
    assert (Hinv : / - ln (xx / INR (S n)) <= 2 * (INR N + 1)).
    { apply Rle_trans with (/ / (2 * (INR N + 1)));
        [ apply Rinv_le_contravar;
            [ apply Rinv_0_lt_compat; pose proof (pos_INR N); lra | exact Hcore ]
        | rewrite Rinv_inv; apply Rle_refl ]. }
    assert (Hgt : Cminus (PT n) (LT n) = Cmul (RtoC (Lam (S n))) (Vperron (xx / INR (S n)) c T Hcne)).
    { unfold PT, LT; rewrite (proj2 (Nat.ltb_ge n N) Hb); ring. }
    rewrite Hgt, Cmod_mul, Cmod_RtoC, (Rabs_pos_eq (Lam (S n)) (Lam_nonneg (S n))).
    eapply Rle_trans;
      [ apply Rmult_le_compat_l;
          [ apply Lam_nonneg | apply (perron_lt1 (xx / INR (S n)) c T Hy0 Hy1 Hcpos HT Hcne) ]
      | ].
    rewrite Hrpq; unfold maj, dser.
    apply Rle_trans with
      (Lam (S n) * 2 * Rpower xx c * Rpower (INR (S n)) (- c) / (PI * T) * (2 * (INR N + 1))).
    + replace (Lam (S n) * (2 * (Rpower xx c * Rpower (INR (S n)) (- c))
                            / (PI * T * - ln (xx / INR (S n)))))
        with (Lam (S n) * 2 * Rpower xx c * Rpower (INR (S n)) (- c) / (PI * T)
              * / - ln (xx / INR (S n)))
        by (field; repeat split; intro Hz; nra).
      apply Rmult_le_compat_l; [ exact Hfac | exact Hinv ].
    + apply Req_le; field; repeat split; intro Hz; nra.
Qed.

(*  the K-th partial Perron sum vs psi N, bounded by the majorant partial sum *)
Lemma decomp : forall M, (N <= M)%nat ->
  Cmod (Cminus (Cpsum PT M) (RtoC (psi N))) <= sum_f_R0 maj M.
Proof.
  intros M HM.
  rewrite <- (Cpsum_LT_ge M HM), <- (Cpsum_minus PT LT M).
  eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
  apply sum_Rle; intros n _; apply gterm_bd.
Qed.

(*  the truncated Perron formula for psi  *)
Theorem perron_psi : forall L, Cseries_cv PT L ->
  exists D, Un_cv (sum_f_R0 (fun n => Lam (S n) * Rpower (INR (S n)) (- c))) D /\
    Cmod (Cminus L (RtoC (psi N))) <= 4 * (INR N + 1) * Rpower xx c / (PI * T) * D.
Proof.
  intros L HL.
  destruct (dseries_cv c Hc1) as [D HD].
  exists D; split; [ exact HD | ].
  set (Kf := 4 * (INR N + 1) * Rpower xx c / (PI * T)).
  assert (Hmajsum : Un_cv (sum_f_R0 maj) (Kf * D)).
  { apply (Un_cv_ext (fun M => Kf * sum_f_R0 dser M)).
    - intro M; induction M as [|M IH].
      + cbn [sum_f_R0]; unfold maj, Kf; ring.
      + rewrite !tech5, Rmult_plus_distr_l, IH; unfold maj, Kf; ring.
    - apply Un_cv_scal; exact HD. }
  apply Rle_cv_lim with
    (Un := fun k => Cmod (Cminus (Cpsum PT (N + k)) (RtoC (psi N))))
    (Vn := fun k => sum_f_R0 maj (N + k)).
  - intro k; apply decomp; lia.
  - intros eps Heps; destruct (HL eps Heps) as [N1 HN1].
    exists N1; intros k Hk; unfold R_dist.
    eapply Rle_lt_trans; [ apply Cmod_diff_le | ].
    replace (Cminus (Cminus (Cpsum PT (N + k)) (RtoC (psi N))) (Cminus L (RtoC (psi N))))
      with (Cminus (Cpsum PT (N + k)) L) by ring.
    apply HN1; lia.
  - apply (Un_cv_shift (sum_f_R0 maj) (Kf * D) N Hmajsum).
Qed.

End PPsi.

(*  wiring perron_identity into perron_psi: the truncated Perron formula      *)
(*  for the genuine Perron integral (1/2pi) int Phi(c+it) x^{c+it}/(c+it) dt   *)
(*  against the Chebyshev psi, at the half-integer x = N + 1/2.                *)
Corollary perron_psi_integral : forall N c T (Hc1 : 1 < c) (HT : 0 < T),
  exists D, Un_cv (sum_f_R0 (fun n => Lam (S n) * Rpower (INR (S n)) (- c))) D /\
    Cmod (Cminus (Cmul (RtoC (/ (2 * PI)))
                    (Cintf (Sfun (xx N) c Hc1) (Sfun_cont (xx N) c (xx_pos N) Hc1) (- T) T))
                 (RtoC (psi N)))
      <= 4 * (INR N + 1) * Rpower (xx N) c / (PI * T) * D.
Proof.
  intros N c T Hc1 HT.
  apply (perron_psi N c T Hc1 HT).
  apply (perron_identity (xx N) c T (xx_pos N) Hc1 HT).
Qed.

Print Assumptions perron_psi.
Print Assumptions perron_psi_integral.

(* ================================================================= *)
(*  END PerronPsi.v — the truncated Perron formula for psi.              *)
(* ================================================================= *)

(* ================================================================= *)
(*  Part 1 complete: elementary bounds + the truncated-indicator sum.    *)
(*  Next: the per-term error bound gterm_bd, then the K->oo assembly.     *)
(* ================================================================= *)
