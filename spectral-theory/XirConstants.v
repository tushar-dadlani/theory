(* ================================================================= *)
(*  XirConstants.v  --  numerals for the two transcendental errors.    *)
(*                                                                    *)
(*  XirSignChange's sign rules take abstract bounds EM (on Mfin t L)   *)
(*  and ET (on the truncation Cc e^{-pi e^L}/pi).  Both are built from *)
(*  exp at irrational arguments -- q = e^{-pi/4} inside Kg1 and Kg2,   *)
(*  e^{L/4} inside EL, and e^{-pi e^L} itself -- so pinning them to    *)
(*  numerals means running the SAME interval machinery that evaluates  *)
(*  the integrand, one level up.  Iexp_pt is used against monotonicity *)
(*  of exp and CertifiedPi's bracket on pi.                            *)
(*                                                                    *)
(*  L is fixed to 13/8 here.  It is a free parameter of the quadrature *)
(*  but the two errors pull in opposite directions -- truncation falls *)
(*  like e^{-pi e^L}, Mfin grows like e^{L/4} -- so it is chosen once. *)
(*  13/8 puts truncation at ~4e-8, three orders below the tightest     *)
(*  budget, at negligible cost in Mfin.  Axiom-clean.                  *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import JacobiTheta IntervalArith IntervalArithFun CertifiedPi
        ThetaDerivMajorant ThetaDeriv PsiXDeriv IntegrandLip
        PsiXSpace RiemannPsi ReTCTailBound IntervalGint.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  exp at a rational, above and below                            *)
(* ----------------------------------------------------------------- *)
Lemma Iexp_ub : forall p m q, inrange m q = true ->
  exp (Q2R q) <= Q2R (ihi (Iexp_pt p m q)).
Proof.
  intros p m q H. destruct (inrange_ok m q H) as [H1 H2].
  destruct (Iexp_pt_sound p m q H1 H2) as [_ Hh]. exact Hh.
Qed.

Lemma Iexp_lb : forall p m q, inrange m q = true ->
  Q2R (ilo (Iexp_pt p m q)) <= exp (Q2R q).
Proof.
  intros p m q H. destruct (inrange_ok m q H) as [H1 H2].
  destruct (Iexp_pt_sound p m q H1 H2) as [Hl _]. exact Hl.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  q = e^{-pi/4}, and the two Lipschitz constants                *)
(* ----------------------------------------------------------------- *)
(* ----------------------------------------------------------------- *)
(*  B.  the sharp constants.  Only TWO interval evaluations are        *)
(*  needed -- e^{-pi} and e^{-4 pi}; everything else follows by         *)
(*  monotonicity of exp, since -9 pi and -9 pi/2 are both below -4 pi. *)
(* ----------------------------------------------------------------- *)
Lemma exp_pi_ub : exp (- PI) <= 4322 / 100000.
Proof.
  assert (Hmono : exp (- PI) <= exp (Q2R (-314159 # 100000))).
  { apply exp_le_compat. pose proof PI_lower. unfold Q2R; simpl; lra. }
  eapply Rle_trans; [ exact Hmono | ].
  eapply Rle_trans; [ apply (Iexp_ub 50 24); vm_compute; reflexivity | ].
  eapply Rle_trans;
    [ apply (Qle_R _ (4322 # 100000)); vm_compute; reflexivity | ].
  unfold Q2R; simpl; lra.
Qed.

Lemma exp_4pi_ub : exp (- (4 * PI)) <= 4 / 1000000.
Proof.
  assert (Hmono : exp (- (4 * PI)) <= exp (Q2R (-1256636 # 100000))).
  { apply exp_le_compat. pose proof PI_lower. unfold Q2R; simpl; lra. }
  eapply Rle_trans; [ exact Hmono | ].
  eapply Rle_trans; [ apply (Iexp_ub 50 24); vm_compute; reflexivity | ].
  eapply Rle_trans;
    [ apply (Qle_R _ (4 # 1000000)); vm_compute; reflexivity | ].
  unfold Q2R; simpl; lra.
Qed.

(* -9 pi and -9 pi/2 are both below -4 pi, so monotonicity suffices *)
Lemma exp_9pi_ub : exp (- (9 * PI)) <= 4 / 1000000.
Proof.
  eapply Rle_trans; [ | apply exp_4pi_ub ].
  apply exp_le_compat. pose proof PI_RGT_0. lra.
Qed.

Lemma exp_45pi_ub : exp (- (9 * PI / 2)) <= 4 / 1000000.
Proof.
  eapply Rle_trans; [ | apply exp_4pi_ub ].
  apply exp_le_compat. pose proof PI_RGT_0. lra.
Qed.

Lemma Ktail_ub : Ktail <= 5 / 1000000.
Proof.
  unfold Ktail, qt.
  pose proof exp_pi_ub as Hq. pose proof exp_45pi_ub as Hn.
  pose proof (exp_pos (- PI)) as Hp. pose proof (exp_pos (- (9 * PI / 2))) as Hp2.
  assert (Hden : 0 < 1 - exp (- PI)) by lra.
  apply (Rmult_le_reg_r (1 - exp (- PI))); [ exact Hden | ].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma Kg1_ub : Kg1 <= 136 / 1000.
Proof.
  unfold Kg1. pose proof PI_upper as HPu. pose proof PI_RGT_0.
  pose proof exp_pi_ub. pose proof exp_4pi_ub. pose proof Ktail_ub.
  pose proof (exp_pos (- PI)). pose proof (exp_pos (- (4 * PI))).
  pose proof Ktail_nonneg.
  assert (W1 : PI * exp (- PI) <= 31416 / 10000 * (4322 / 100000)) by nra.
  assert (W2 : 4 * PI * exp (- (4 * PI))
               <= 4 * (31416 / 10000) * (4 / 1000000)) by nra.
  lra.
Qed.

Lemma Kg2_ub : Kg2 <= 564 / 1000.
Proof.
  unfold Kg2. pose proof PI_upper as HPu. pose proof PI_RGT_0.
  pose proof exp_pi_ub. pose proof exp_4pi_ub. pose proof Ktail_ub.
  pose proof (exp_pos (- PI)). pose proof (exp_pos (- (4 * PI))).
  pose proof Ktail_nonneg.
  assert (HP2 : PI ^ 2 <= 98697 / 10000) by nra.
  assert (V1 : (PI ^ 2 + PI) * exp (- PI)
               <= (98697 / 10000 + 31416 / 10000) * (4322 / 100000)) by nra.
  assert (V2 : (16 * PI ^ 2 + 4 * PI) * exp (- (4 * PI))
               <= (16 * (98697 / 10000) + 4 * (31416 / 10000))
                  * (4 / 1000000)) by nra.
  lra.
Qed.

Lemma MP_ub : MP <= 433 / 10000.
Proof.
  unfold MP. pose proof exp_pi_ub. pose proof exp_4pi_ub. pose proof exp_9pi_ub.
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  L = 13/8 : the growth factor and the truncation               *)
(* ----------------------------------------------------------------- *)
Lemma EL_ub : EL (13 / 8) <= 151 / 100.
Proof.
  unfold EL.
  assert (E : / 4 * (13 / 8) = Q2R (13 # 32)) by (unfold Q2R; simpl; lra).
  rewrite E.
  eapply Rle_trans; [ apply (Iexp_ub 40 20); vm_compute; reflexivity | ].
  eapply Rle_trans;
    [ apply (Qle_R _ (151 # 100)); vm_compute; reflexivity | ].
  unfold Q2R; simpl; lra.
Qed.

Lemma expL_lb : 5077 / 1000 <= exp (13 / 8).
Proof.
  assert (E : (13 : R) / 8 = Q2R (13 # 8)) by (unfold Q2R; simpl; lra).
  rewrite E.
  eapply Rle_trans; [ | apply (Iexp_lb 40 20); vm_compute; reflexivity ].
  eapply Rle_trans;
    [ | apply (Qle_R (5077 # 1000)); vm_compute; reflexivity ].
  unfold Q2R; simpl; lra.
Qed.

Lemma ET_ub : Cc * exp (- (PI * exp (13 / 8))) / PI <= 6 / 100000000.
Proof.
  pose proof PI_lower as HPl. pose proof PI_upper as HPu.
  (* Cc = 1/(1 - e^{-pi}) <= 8/7, since e^{-pi} <= e^{-3} <= 1/8 *)
  assert (Hep : exp (- PI) <= / 8).
  { assert (H1 : exp (- PI) <= exp (-3))
      by (apply exp_le_compat; lra).
    assert (E : exp (-3) * exp 3 = 1)
      by (rewrite <- exp_plus; replace (-3 + 3) with 0 by ring; apply exp_0).
    pose proof exp_3_ge_8. pose proof (exp_pos (-3)). nra. }
  assert (HCc : Cc <= 8 / 7).
  { unfold Cc. apply (Rmult_le_reg_r (1 - exp (- PI))); [ lra | ].
    rewrite Rinv_l by lra. lra. }
  assert (HCc0 : 0 < Cc).
  { unfold Cc. apply Rinv_0_lt_compat. lra. }
  (* pi . e^L >= 3.14159 * 5.077 = 15.950 *)
  assert (Harg : 1594 / 100 <= PI * exp (13 / 8)).
  { pose proof expL_lb as HE.
    assert (H1 : 3.14159 * (5077 / 1000) <= PI * exp (13 / 8))
      by (apply Rmult_le_compat; lra).
    lra. }
  assert (Hexp : exp (- (PI * exp (13 / 8))) <= exp (Q2R (-1594 # 100))).
  { apply exp_le_compat. unfold Q2R; simpl; lra. }
  assert (Hnum : exp (- (PI * exp (13 / 8))) <= 13 / 100000000).
  { eapply Rle_trans; [ exact Hexp | ].
    eapply Rle_trans; [ apply (Iexp_ub 40 24); vm_compute; reflexivity | ].
    eapply Rle_trans;
      [ apply (Qle_R _ (13 # 100000000)); vm_compute; reflexivity | ].
    unfold Q2R; simpl; lra. }
  assert (Hpos : 0 <= exp (- (PI * exp (13 / 8)))) by (left; apply exp_pos).
  assert (Hprod : Cc * exp (- (PI * exp (13 / 8))) <= 8 / 7 * (13 / 100000000))
    by nra.
  unfold Rdiv at 1.
  assert (Hinv : / PI <= / 3) by (apply Rinv_le_contravar; lra).
  assert (HP0 : 0 < / PI) by (apply Rinv_0_lt_compat; lra).
  assert (Hcp : 0 <= Cc * exp (- (PI * exp (13 / 8)))) by nra.
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Mfin at the two bracket endpoints                             *)
(* ----------------------------------------------------------------- *)
Lemma Tt_val : forall t, 0 <= t -> Tt t = t / 2.
Proof. intros t Ht. unfold Tt. rewrite Rabs_pos_eq by exact Ht. reflexivity. Qed.

Lemma Mfin_12 : Mfin 12 (13 / 8) <= 6.
Proof.
  unfold Mfin. rewrite (Tt_val 12) by lra.
  pose proof Kg1_ub. pose proof Kg2_ub. pose proof EL_ub. pose proof MP_ub.
  pose proof Kg1_nonneg. pose proof Kg2_nonneg. pose proof MP_nonneg.
  pose proof (EL_pos (13 / 8)).
  nra.
Qed.

Lemma Mfin_16 : Mfin 16 (13 / 8) <= 87 / 10.
Proof.
  unfold Mfin. rewrite (Tt_val 16) by lra.
  pose proof Kg1_ub. pose proof Kg2_ub. pose proof EL_ub. pose proof MP_ub.
  pose proof Kg1_nonneg. pose proof Kg2_nonneg. pose proof MP_nonneg.
  pose proof (EL_pos (13 / 8)).
  nra.
Qed.

Print Assumptions exp_pi_ub.
Print Assumptions Kg1_ub.
Print Assumptions Kg2_ub.
Print Assumptions EL_ub.
Print Assumptions ET_ub.
Print Assumptions Mfin_12.
Print Assumptions Mfin_16.
