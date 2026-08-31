(* ================================================================= *)
(*  ThirdZeroT26.v  --  xir 26 < 0.                                    *)
(*                                                                    *)
(*  Budget at t = 26, L = 2, n = 1024:                                 *)
(*    quadrature  M4fin 26 . 2^5 / (720 . 1024^4)  <= 1.36e-10         *)
(*    truncation  Cc e^{-pi e^2} / pi              <= 4.0e-11          *)
(*    ssum >= 0.0007393721, threshold 1/(2(1/4+676)) = 0.00073937153   *)
(*  so ssum - err >= 0.00073937192 > threshold, with 3.9e-10 to spare. *)
(*                                                                    *)
(*  The margin here is 9.6e-10, against 1.6e-8 at t = 22 and 3.0e-6 at *)
(*  t = 16 -- the exponential decay of Xi(1/2+it), measured.           *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import ComplexField IntervalArith IntervalGint CoherenceSingularity
        ThetaTailEntire ReTCTailBound IntegrandLip IntegrandLip4
        SimpsonQuad ReTCSimpson XirSignChange XirConstants
        FirstZeroBridge ThirdZeroChk26.
Local Open Scope R_scope.

Lemma pos1024 : (0 < 1024)%nat.
Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

Lemma h26 : Q2R (1 # 512) = 2 / INR 1024.
Proof.
  rewrite (INR_lit 1024 1024) by (vm_compute; reflexivity).
  unfold Q2R; simpl; lra.
Qed.

Lemma ssum26_b : Q2R (7393721 # 10000000000)
                 <= ssum (gint 26) 0 (2 / INR 1024) 1024.
Proof.
  assert (Hh : 0 <= Q2R (1 # 512)) by (unfold Q2R; simpl; lra).
  assert (Et : Q2R (26 # 1) = 26) by (unfold Q2R; simpl; lra).
  pose proof chk26 as H.
  destruct (Issum 80 36 56 24 56 22 40 5 4 80 26 (1 # 512) 1024)
    as [i |] eqn:E; [ | discriminate ].
  pose proof (Issum_sound 80 36 56 24 56 22 40 5 4 80 26 (1 # 512) 1024
                i Hh E) as HC.
  rewrite Et, h26 in HC. unfold Icontains in HC.
  destruct HC as [Hb _].
  eapply Rle_trans; [ apply Qle_R; exact H | exact Hb ].
Qed.

Theorem xir_26_neg : xir 26 < 0.
Proof.
  pose proof (ReTC_simpson 26 2 1024 pos1024 ltac:(lra)) as HE.
  apply (xir_neg_of_gen 26
           (ssum (gint 26) 0 (2 / INR 1024) 1024)
           (M4fin 26 * 2 ^ 5 / (720 * INR 1024 ^ 4)
            + Cc * exp (- (PI * exp 2)) / PI)).
  - exact HE.
  - assert (E1024 : INR 1024 = IZR 1024)
      by (apply INR_lit; vm_compute; reflexivity).
    rewrite E1024.
    pose proof ssum26_b as HS. rewrite E1024 in HS.
    assert (Ed : Q2R (7393721 # 10000000000) = 7393721 / 10000000000)
      by (unfold Q2R; simpl; lra).
    rewrite Ed in HS.
    pose proof M4fin_26 as HM. pose proof ET_ub2 as HT.
    pose proof (M4fin_nonneg 26) as HM0.
    assert (Hd : (0:R) < 720 * IZR 1024 ^ 4).
    { assert (E : IZR 1024 ^ 4 = 1099511627776) by (simpl; lra).
      rewrite E. lra. }
    assert (Hq : M4fin 26 * 2 ^ 5 / (720 * IZR 1024 ^ 4)
                 <= 3360 * 2 ^ 5 / (720 * IZR 1024 ^ 4)).
    { unfold Rdiv. apply Rmult_le_compat_r.
      - left; apply Rinv_0_lt_compat; exact Hd.
      - apply Rmult_le_compat_r; [ lra | exact HM ]. }
    assert (Enum : 3360 * 2 ^ 5 / (720 * IZR 1024 ^ 4) <= 14 / 100000000000).
    { assert (E : IZR 1024 ^ 4 = 1099511627776) by (simpl; lra).
      rewrite E. lra. }
    assert (Ethr : / (2 * (/ 4 + 26 ^ 2)) = 2 / 2705).
    { replace (2 * (/ 4 + 26 ^ 2)) with (2705 / 2) by (simpl; field).
      field. }
    rewrite Ethr. lra.
  - lra.
Qed.

Print Assumptions xir_26_neg.
