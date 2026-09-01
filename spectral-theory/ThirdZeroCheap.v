(* ================================================================= *)
(*  ThirdZeroCheap.v  --  xir 26 < 0 by the POLYNOMIAL route.         *)
(*                                                                    *)
(*  ThirdZeroT26 established this with 1024 Simpson panels and 36      *)
(*  exp halvings, because it computes xir = 1/2 - (1/4+t^2) Re TC, a   *)
(*  difference of two O(1) quantities whose answer is ~1e-9.          *)
(*                                                                    *)
(*  Here the same sign comes from  xir = -c(t) Z(t)  with c(t) > 0     *)
(*  (XirSignZ), Z = cos(theta) Re zeta - sin(theta) Im zeta            *)
(*  (GammaArg), theta from an arctan series (ThetaEnclose) and zeta    *)
(*  from the trapezoid representation (ZetaEnclose).  |Gamma| -- the   *)
(*  factor of size e^{-pi t/4} -- is never computed.                  *)
(*                                                                    *)
(*  40 terms suffice, against 1024 panels.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith.
Require Import ComplexField Cmodulus CZeta ZetaFn CoherenceSingularity
        IntervalArith IntervalAtan XirSignZ GammaArg ThetaEnclose
        ZetaEM ZetaEnclose ZSign.
Open Scope R_scope.

Definition Th26 : Itv := mkI (5048 # 1000) (5084 # 1000).

(*  The application is INLINED, not routed through a Definition: a
    named constant is transparent, so any delta step at Qed re-triggers
    the whole evaluation.  This is the same trap that cost an hour on
    the first attempt here.  *)
Lemma chk26 :
  match Izeta2 80 28 60 40 60 8 5 8 26 40 (1 # 2) with
  | Some (zr, zi) =>
      match IZ 60 8 5 Th26 zr zi with
      | Some i => Qle_bool (1 # 2) (ilo i)
      | None => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_26_neg_cheap : xir 26 < 0.
Proof.
  assert (H26 : Q2R 26 = 26) by (unfold Q2R; simpl; field).
  assert (H0 : 0 < Re (crit (Q2R 26)))
    by (unfold crit; cbn [Re]; lra).
  assert (H1 : Cminus C1 (crit (Q2R 26)) <> C0) by apply crit_ne1.
  assert (EI : INR (S 40) = 41) by (simpl; ring).
  assert (Ehalf : Q2R (1 # 2) = / 2) by (unfold Q2R; simpl; field).
  assert (HB : Kh (crit (Q2R 26))
               * Rpower (INR (S 40)) (- Re (crit (Q2R 26))) / INR (S 40)
               <= Q2R (1 # 2)).
  { rewrite Ehalf, H26.
    eapply Rle_trans; [ apply (tail_le 26 40 (1 / 6)) | ].
    - lra.
    - lra.
    - rewrite EI. lra.
    - rewrite EI. lra. }
  pose proof chk26 as Hc.
  destruct (Izeta2 80 28 60 40 60 8 5 8 26 40 (1 # 2)) as [[zr zi] |] eqn:HZ;
    [ | discriminate ].
  destruct (IZ 60 8 5 Th26 zr zi) as [i |] eqn:HI; [ | discriminate ].
  apply Qle_R' in Hc. rewrite Ehalf in Hc.
  destruct (Izeta2_sound 80 28 60 40 60 8 5 8 26 40 (1 # 2) zr zi H0 H1 HB HZ)
    as [Zr Zi].
  rewrite <- H26.
  apply (xir_neg_of_IZ 60 8 5 Th26 zr zi i (Q2R 26)).
  - rewrite H26; lra.
  - rewrite H26. unfold Th26, Icontains; cbn [ilo ihi].
    pose proof theta_26_bounds as [T1 T2].
    assert (E1 : Q2R (5048 # 1000) = 5048 / 1000)
      by (unfold Q2R; simpl; field).
    assert (E2 : Q2R (5084 # 1000) = 5084 / 1000)
      by (unfold Q2R; simpl; field).
    rewrite E1, E2. lra.
  - rewrite (zF_eq (crit (Q2R 26)) H0 H1). exact Zr.
  - rewrite (zF_eq (crit (Q2R 26)) H0 H1). exact Zi.
  - exact HI.
  - lra.
Qed.
