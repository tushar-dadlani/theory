(* ================================================================= *)
(*  SecondZeroT22.v  --  xir 22 > 0.                                   *)
(*                                                                    *)
(*  Cheap: the quadrature is SecondZeroChk22's vm_compute, in its own  *)
(*  .vo.  This file only turns that boolean into a sign.              *)
(*                                                                    *)
(*  Budget at t = 22, L = 2, n = 512:                                  *)
(*    quadrature  M4fin 22 . 2^5 / (720 . 512^4)  <= 1.32e-9           *)
(*    truncation  Cc e^{-pi e^2} / pi             <= 4.0e-11           *)
(*    ssum <= 0.001032517, threshold 1/(2(1/4+484)) = 0.0010325245     *)
(*  so ssum + err <= 0.0010325184 < threshold, with 6.2e-9 to spare.   *)
(*                                                                    *)
(*  L = 2 IS FORCED: at L = 13/8 the truncation alone is 6e-8, which   *)
(*  exceeds the whole 1.6e-8 margin at this t.                        *)
(*                                                                    *)
(*  As in the first-zero files: destruct ... eqn:, never simpl on the  *)
(*  computed option, and never a lemma abstracting it -- both make the *)
(*  kernel re-run the quadrature at Qed.  Axiom-clean.                 *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import ComplexField IntervalArith IntervalGint CoherenceSingularity
        ThetaTailEntire ReTCTailBound IntegrandLip IntegrandLip4
        SimpsonQuad ReTCSimpson XirSignChange XirConstants
        FirstZeroBridge SecondZeroChk22.
Local Open Scope R_scope.

Lemma pos512 : (0 < 512)%nat.
Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

Lemma h22 : Q2R (1 # 256) = 2 / INR 512.
Proof.
  rewrite (INR_lit 512 512) by (vm_compute; reflexivity).
  unfold Q2R; simpl; lra.
Qed.

Lemma ssum22_b : ssum (gint 22) 0 (2 / INR 512) 512
                 <= Q2R (1032517 # 1000000000).
Proof.
  assert (Hh : 0 <= Q2R (1 # 256)) by (unfold Q2R; simpl; lra).
  assert (Et : Q2R (22 # 1) = 22) by (unfold Q2R; simpl; lra).
  pose proof chk22 as H.
  destruct (Issum 60 25 40 14 40 12 40 5 4 60 22 (1 # 256) 512)
    as [i |] eqn:E; [ | discriminate ].
  pose proof (Issum_sound 60 25 40 14 40 12 40 5 4 60 22 (1 # 256) 512
                i Hh E) as HC.
  rewrite Et, h22 in HC. unfold Icontains in HC.
  destruct HC as [_ Hb].
  eapply Rle_trans; [ exact Hb | apply Qle_R; exact H ].
Qed.

Theorem xir_22_pos : 0 < xir 22.
Proof.
  pose proof (ReTC_simpson 22 2 512 pos512 ltac:(lra)) as HE.
  apply (xir_pos_of_gen 22
           (ssum (gint 22) 0 (2 / INR 512) 512)
           (M4fin 22 * 2 ^ 5 / (720 * INR 512 ^ 4)
            + Cc * exp (- (PI * exp 2)) / PI)).
  - exact HE.
  - (* ssum + err < 1 / (2 (1/4 + 22^2)) *)
    assert (E512 : INR 512 = IZR 512)
      by (apply INR_lit; vm_compute; reflexivity).
    rewrite E512.
    pose proof ssum22_b as HS. rewrite E512 in HS.
    assert (Ed : Q2R (1032517 # 1000000000) = 1032517 / 1000000000)
      by (unfold Q2R; simpl; lra).
    rewrite Ed in HS.
    pose proof M4fin_22 as HM. pose proof ET_ub2 as HT.
    pose proof (M4fin_nonneg 22) as HM0.
    assert (Hd : (0:R) < 720 * IZR 512 ^ 4).
    { assert (E : IZR 512 ^ 4 = 68719476736) by (simpl; lra).
      rewrite E. lra. }
    assert (Hq : M4fin 22 * 2 ^ 5 / (720 * IZR 512 ^ 4)
                 <= 2040 * 2 ^ 5 / (720 * IZR 512 ^ 4)).
    { unfold Rdiv. apply Rmult_le_compat_r.
      - left; apply Rinv_0_lt_compat; exact Hd.
      - apply Rmult_le_compat_r; [ lra | exact HM ]. }
    assert (Enum : 2040 * 2 ^ 5 / (720 * IZR 512 ^ 4) <= 14 / 10000000000).
    { assert (E : IZR 512 ^ 4 = 68719476736) by (simpl; lra).
      rewrite E. lra. }
    assert (Ethr : / (2 * (/ 4 + 22 ^ 2)) = 2 / 1937).
    { replace (2 * (/ 4 + 22 ^ 2)) with (1937 / 2) by (simpl; field).
      field. }
    rewrite Ethr. lra.
  - lra.
Qed.

Print Assumptions xir_22_pos.
