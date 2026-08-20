(* ================================================================= *)
(*  CCoeffTwo.v  —  Borel-Caratheodory, Step 3:                        *)
(*  the SECOND DERIVATIVE AT THE CENTRE as a circle integral.          *)
(*                                                                    *)
(*    second_deriv_circle :  G entire (derivative Gp) and pointwise     *)
(*      continuous, 0 < Rr  ==>                                        *)
(*                                                                    *)
(*        is_Cderiv Gp C0 ((1/PI) . INT_0^{2PI} G(arc Rr t) . wgt Rr t dt) *)
(*                                                                    *)
(*  i.e.  G''(0) = (1/PI) . A,  A := INT G(arc Rr t) (arc Rr t)^{-2} dt. *)
(*                                                                    *)
(*  This is the object Borel-Caratheodory squeezes: everything after    *)
(*  it (the conjugate half, the positivity trick, the mean value, the   *)
(*  R -> oo limit) is about bounding A.                                *)
(*                                                                    *)
(*  ROUTE.  Straight through the identity-theorem tower, mirroring      *)
(*  CDerivHoloDisk.holo_deriv_fun rather than reusing it (its `fs` is   *)
(*  section-local):                                                    *)
(*    * fseq0_eq + fseq_chain + is_Cderiv_unique give Gp = fseq 1 on    *)
(*      the inner disk, hence is_Cderiv Gp C0 (fseq 2 C0);             *)
(*    * fseq 2 = (2!/2 pi i) . Psi 3 and Psi 3 C0 unfolds to the        *)
(*      Cauchy kernel integral, with clampw Rr C0 C0 = C0;             *)
(*    * CArcWeight.kernel3_wgt collapses that kernel to Ci . G . wgt,   *)
(*      and CIntfLinear.Cintf_scal pulls the Ci out.                   *)
(*  The surviving constant is (2!/2 pi i) . i = 1/PI.                   *)
(*                                                                    *)
(*  The constant was checked numerically before the proof was written:  *)
(*  A/PI reproduces G''(0) for z^2, z^3, 1, z^4, exp z and a general    *)
(*  quadratic, at several radii.  Axiom-clean.                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Factorial.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral RootsOfUnity PerronRemovable CDerivUnique CCircleBound
        CTaylor CCauchyAnalytic CAnalyticTower CAnalyticTowerF
        CIntfLinear CArcWeight.
Open Scope R_scope.

(* the surviving constant:  2 . (1/(2 pi i)) . i  =  1/pi  *)
Lemma coeff2_const : forall X : C,
  Cmul (RtoC 2) (Cmul (Cinv (mkC 0 (2 * PI))) (Cmul (mkC 0 1) X))
  = Cmul (RtoC (/ PI)) X.
Proof.
  intros [xr xi]. pose proof PI_RGT_0 as HPI.
  apply Ceq; unfold Cmul, Cinv, RtoC, Cnorm2; cbn [Re Im]; field; lra.
Qed.

Section CoeffTwo.

Variable G Gp : C -> C.
Variable Rr : R.
Hypothesis HR : 0 < Rr.
Hypothesis HGptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (G z') (G z)) < eps.
Hypothesis HG : forall z, is_Cderiv G z (Gp z).
Variable Hker : Ccont (fun t => Cmul (G (arc Rr t)) (wgt Rr t)).

Definition HGc : CcontC G := ptcont_CcontC G HGptc.

Definition HGgb : exists Mg, 0 <= Mg /\ forall u, Cmod (G (arc Rr u)) <= Mg :=
  Ccont_circle_bounded G Rr HGc.

Lemma HGhol : forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv G z d.
Proof. intros z _. exists (Gp z). apply HG. Qed.

(* the weighted circle integral *)
Definition A2 : C := Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) Hker 0 (2 * PI).

(* ---- the tower represents G and its derivative on the inner disk ---- *)
Lemma G_deriv_fs1 : forall z, Cmod z < Rr / 2 ->
  is_Cderiv G z (fseq G Rr HR HGc 1 z).
Proof.
  intros z Hz.
  apply (is_Cderiv_congr G (fseq G Rr HR HGc 0) z (fseq G Rr HR HGc 1 z)
           (Rr / 2 - Cmod z)).
  - lra.
  - intros w Hw. symmetry.
    apply (fseq0_eq G Rr HR HGc HGptc HGhol w).
    assert (Htri : Cmod w <= Cmod (Cminus w z) + Cmod z)
      by (replace w with (Cadd (Cminus w z) z) at 1 by ring; apply Cmod_triangle).
    lra.
  - exact (fseq_chain G Rr HR HGc HGgb 0 z Hz).
Qed.

Lemma Gp_eq_fs1 : forall z, Cmod z < Rr / 2 -> Gp z = fseq G Rr HR HGc 1 z.
Proof.
  intros z Hz.
  apply (is_Cderiv_unique G z (Gp z) (fseq G Rr HR HGc 1 z));
    [ apply HG | apply G_deriv_fs1; exact Hz ].
Qed.

Lemma Gpp_fs2 : is_Cderiv Gp C0 (fseq G Rr HR HGc 2 C0).
Proof.
  assert (H0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
  apply (is_Cderiv_congr Gp (fseq G Rr HR HGc 1) C0 (fseq G Rr HR HGc 2 C0)
           (Rr / 2)).
  - lra.
  - intros w Hw. apply Gp_eq_fs1.
    replace (Cminus w C0) with w in Hw by ring. exact Hw.
  - apply (fseq_chain G Rr HR HGc HGgb 1 C0). rewrite H0. lra.
Qed.

(* ---- the tower's level-3 Cauchy integral IS Ci . A2 ---- *)
Lemma clamp0 : clampw Rr C0 C0 = C0.
Proof.
  apply clampw_id.
  replace (Cminus C0 C0) with C0 by ring.
  rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

Lemma Psi3_A2 : Psi G Rr HR HGc 3 C0 = Cmul Ci A2.
Proof.
  unfold Psi, PhiN, A2.
  assert (Hscal : Ccont (fun t => Cmul Ci (Cmul (G (arc Rr t)) (wgt Rr t))))
    by (apply Ccont_scal; exact Hker).
  rewrite <- (Cintf_scal Ci (fun t => Cmul (G (arc Rr t)) (wgt Rr t))
                Hker Hscal 0 (2 * PI)).
  apply Cintf_ext. intro t.
  unfold Kwn. rewrite clamp0. apply kernel3_wgt; exact HR.
Qed.

Lemma fs2_const : fseq G Rr HR HGc 2 C0 = Cmul (RtoC (/ PI)) A2.
Proof.
  unfold fseq. rewrite Psi3_A2.
  assert (Hf2 : INR (fact 2) = 2) by (simpl; lra).
  rewrite Hf2. unfold cc, Ci. apply coeff2_const.
Qed.

(* ================================================================= *)
(*  STEP 3                                                             *)
(* ================================================================= *)
Theorem second_deriv_circle : is_Cderiv Gp C0 (Cmul (RtoC (/ PI)) A2).
Proof. rewrite <- fs2_const. exact Gpp_fs2. Qed.

End CoeffTwo.

Print Assumptions second_deriv_circle.
