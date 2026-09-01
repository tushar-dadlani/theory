(* ================================================================= *)
(*  FourthZero.v  --  a fourth zero, entirely by the cheap route.     *)
(*                                                                    *)
(*  The first three zeros each needed a bespoke quadrature file        *)
(*  (FirstZeroChk10, SecondZeroChk22, ThirdZeroChk26) with hundreds    *)
(*  of Simpson panels.  This one needs a single vm_compute through     *)
(*  CheapSign.xir_pos_cheap: 70 trapezoid terms for zeta and 400       *)
(*  arctan terms for theta.                                           *)
(*                                                                    *)
(*  t = 63/2 is the second-tightest margin in the sample sequence      *)
(*  (|Z| = 0.90), so it is the honest stress test of the driver.       *)
(*  Measured: Z(31.5) in [-1.3404, -0.4887].                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith.
Require Import ComplexField Cmodulus CoherenceSingularity CritLineZeroCollapse
        EtaZetaStripC
        RiemannXiEntire IntervalArith IntervalAtan XirSignZ ThetaEnclose
        ZetaEM ZetaEnclose ZSign CheapSign
        FirstZeroT10 FirstZeroT16 SecondZeroT22 ThirdZeroT26.
Open Scope R_scope.

Lemma chk315 :
  (match Izeta2 80 28 60 40 60 8 5 8 (63 # 2) 70 (1 # 3) with
   | Some (zr, zi) =>
       match IZ 60 8 5 (Itheta 40 4 4 (63 # 2) 400) zr zi with
       | Some i => Qle_bool (ihi i) (Qopp (1 # 4))
       | None => false
       end
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_315_pos : 0 < xir (63 / 2).
Proof.
  assert (Ht : Q2R (63 # 2) = 63 / 2) by (unfold Q2R; simpl; field).
  assert (Ethr : Q2R (1 # 4) = / 4) by (unfold Q2R; simpl; field).
  assert (Eb : Q2R (1 # 3) = / 3) by (unfold Q2R; simpl; field).
  assert (EI : INR (S 70) = 71) by (simpl; ring).
  rewrite <- Ht.
  apply (xir_pos_cheap 80 28 60 40 60 8 5 8 (63 # 2) 70 (1 # 3)
           40 4 4 400 (1 # 4)).
  - rewrite Ht; lra.
  - rewrite Ethr; lra.
  - lia.
  - rewrite Eb, Ht.
    eapply Rle_trans; [ apply (tail_le (63 / 2) 70 (1 / 8)) | ].
    + lra.
    + lra.
    + rewrite EI; lra.
    + rewrite EI; lra.
  - exact chk315.
Qed.

Theorem fourth_zero_exists :
  exists t, 26 < t < 63 / 2
         /\ XiC (crit t) = C0
         /\ ccollapses (ceta_partial (crit t)).
Proof.
  assert (Hsign : xir 26 * xir (63 / 2) < 0).
  { pose proof xir_26_neg. pose proof xir_315_pos. nra. }
  destruct (crit_sign_change_gives_zero_collapse 26 (63 / 2) ltac:(lra) Hsign)
    as [t [Ht [HX [_ HC]]]].
  exists t. repeat split; try tauto; try apply Ht.
Qed.

Theorem four_distinct_zeros_exist :
  exists t1 t2 t3 t4,
       (10 < t1 < 16) /\ (16 < t2 < 22) /\ (22 < t3 < 26) /\ (26 < t4 < 63 / 2)
    /\ XiC (crit t1) = C0 /\ XiC (crit t2) = C0
    /\ XiC (crit t3) = C0 /\ XiC (crit t4) = C0.
Proof.
  assert (Hs1 : xir 10 * xir 16 < 0).
  { pose proof xir_10_pos. pose proof xir_16_neg. nra. }
  assert (Hs2 : xir 16 * xir 22 < 0).
  { pose proof xir_16_neg. pose proof xir_22_pos. nra. }
  assert (Hs3 : xir 22 * xir 26 < 0).
  { pose proof xir_22_pos. pose proof xir_26_neg. nra. }
  assert (Hs4 : xir 26 * xir (63 / 2) < 0).
  { pose proof xir_26_neg. pose proof xir_315_pos. nra. }
  destruct (crit_sign_change_gives_zero_collapse 10 16 ltac:(lra) Hs1)
    as [t1 [Ht1 [HX1 _]]].
  destruct (crit_sign_change_gives_zero_collapse 16 22 ltac:(lra) Hs2)
    as [t2 [Ht2 [HX2 _]]].
  destruct (crit_sign_change_gives_zero_collapse 22 26 ltac:(lra) Hs3)
    as [t3 [Ht3 [HX3 _]]].
  destruct (crit_sign_change_gives_zero_collapse 26 (63 / 2) ltac:(lra) Hs4)
    as [t4 [Ht4 [HX4 _]]].
  exists t1, t2, t3, t4.
  repeat split; try tauto;
    try apply Ht1; try apply Ht2; try apply Ht3; try apply Ht4.
Qed.
