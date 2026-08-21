(* ================================================================= *)
(*  ZetaStripConfinement.v  —  the strip-confinement REDUCTION.        *)
(*                                                                    *)
(*  MILESTONE 2 (conditional form): the nontrivial zeros of the        *)
(*  operator zeta lie in the closed critical strip 0 <= Re z <= 1.     *)
(*  Equivalently, the entire completed function XiC has no zeros        *)
(*  outside the strip.                                                 *)
(*                                                                    *)
(*  UPDATE.  Both analytic inputs are now DISCHARGED, so the theorem     *)
(*  below is UNCONDITIONAL:                                            *)
(*                                                                    *)
(*    GammaC_half_ne0 : for Re w > 1, GammaC(w/2) <> 0                 *)
(*      -- immediate from GammaCNe0.GammaC_ne0_final, which had        *)
(*         already been made unconditional and was simply not wired    *)
(*         in here;                                                    *)
(*                                                                    *)
(*    LambdaC_completion_complex : the COMPLEX completion identity      *)
(*        LambdaC w = pi^{-w/2} * GammaC(w/2) * zetaC w   (Re w > 1)    *)
(*      -- pure algebra over CZetaXiComplex.XiC_completed_complex,      *)
(*         which had ALREADY lifted the real-ray identity to Re > 1     *)
(*         by a CWalk march.  This file predated it and went stale.     *)
(*                                                                    *)
(*  Given these, the confinement follows from Milestone 1              *)
(*  (zetaC_nonzero, CEulerProductZeta) — zetaC <> 0 for Re > 1 — plus   *)
(*  Cpw <> 0 (Cexpf_ne0) and the functional-equation symmetry          *)
(*  XiC z = XiC(1-z) (RiemannXiEntire.XiC_symmetric), which folds the   *)
(*  left half-plane Re z < 0 onto Re(1-z) > 1.  Axiom-clean.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CexpFull CDeriv CZeta CEulerProductZeta
        GammaC RiemannXiEntire ZetaFunctionalEq ZetaFn CZetaXiComplex GammaCNe0.
Open Scope R_scope.

(* Cpw is never zero (one-line corollary of Cexpf_ne0) *)
Lemma Cpw_ne0 : forall c w, Cpw c w <> C0.
Proof. intros c w; unfold Cpw; apply Cexpf_ne0. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the two former hypotheses, now theorems                        *)
(* ----------------------------------------------------------------- *)

Lemma half_eq : forall w, Cmul w (RtoC (/ 2)) = halfz w.
Proof.
  intro w. unfold halfz. apply Ceq; unfold Cmul, Cadd, RtoC, C0; cbn [Re Im]; ring.
Qed.

Lemma mhalf_eq : forall w, Copp (Cmul w (RtoC (/ 2))) = mhalfz w.
Proof.
  intro w. unfold mhalfz.
  apply Ceq; unfold Cmul, Cadd, Copp, RtoC, C0; cbn [Re Im]; ring.
Qed.

(* complex Gamma nonvanishing on Re > 1/2 *)
Theorem GammaC_half_ne0 : forall w, 1 < Re w -> GammaC (Cmul w (RtoC (/ 2))) <> C0.
Proof. intros w Hw. apply GammaC_ne0_final. unfold Cmul, RtoC; cbn [Re Im]; lra. Qed.

(* the COMPLEX completion identity on Re w > 1 *)
Theorem LambdaC_completion_complex :
  forall w (Hw0 : 0 < Re w) (Hw1 : Cminus C1 w <> C0), 1 < Re w ->
    LambdaC w
    = Cmul (Cpw PI (Copp (Cmul w (RtoC (/ 2)))))
           (Cmul (GammaC (Cmul w (RtoC (/ 2)))) (zetaC w Hw0 Hw1)).
Proof.
  intros w Hw0 Hw1 Hw.
  rewrite mhalf_eq, half_eq, <- (zF_eq w Hw0 Hw1).
  assert (Hw_ne : w <> C0) by
    (intro Hd; apply (f_equal Re) in Hd; unfold C0 in Hd; cbn [Re] in Hd; lra).
  assert (Hw1_ne : Cminus w C1 <> C0) by
    (intro Hd; apply (f_equal Re) in Hd; unfold Cminus, C0, C1 in Hd; cbn [Re] in Hd; lra).
  assert (HP : Cmul (Cinv (Cmul w (Cminus w C1))) (Cmul w (Cminus w C1)) = C1)
    by (apply Cinv_l, Cmul_ne0; assumption).
  assert (H2 : Cmul (RtoC 2) (RtoC (/ 2)) = C1)
    by (rewrite <- RtoC_mul; apply Ceq; unfold RtoC, C1; cbn [Re Im]; lra).
  unfold LambdaC. rewrite (XiC_completed_complex w Hw). unfold RHSz, prefac, archexp.
  symmetry.
  transitivity (Cmul (Cmul (RtoC 2) (RtoC (/ 2)))
    (Cmul (Cmul (Cinv (Cmul w (Cminus w C1))) (Cmul w (Cminus w C1)))
          (Cmul (Cpw PI (mhalfz w)) (Cmul (GammaC (halfz w)) (zF w))))).
  { rewrite H2, HP. ring. }
  ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  XiC has no zeros on Re w > 1                                      *)
(* ----------------------------------------------------------------- *)

Lemma Re_Cminus_C1 : forall w, Re (Cminus C1 w) = 1 - Re w.
Proof. intro w; unfold Cminus, Cadd, Copp, C1; simpl; ring. Qed.

Lemma XiC_nonzero_gt1 : forall w, 1 < Re w -> XiC w <> C0.
Proof.
  intros w Hw.
  assert (Hw0 : 0 < Re w) by lra.
  assert (Hw1 : Cminus C1 w <> C0).
  { intro He; pose proof (Re_Cminus_C1 w) as HRe; rewrite He in HRe; simpl in HRe; lra. }
  (* the completed function is a product of nonzero factors *)
  assert (HL : LambdaC w <> C0).
  { rewrite (LambdaC_completion_complex w Hw0 Hw1 Hw).
    apply Cmul_ne0; [ apply Cpw_ne0 | ].
    apply Cmul_ne0; [ apply GammaC_half_ne0; exact Hw | apply (zetaC_nonzero w Hw Hw0 Hw1) ]. }
  (* XiC w = 0 would make LambdaC w = 0 *)
  intro HX0; apply HL; unfold LambdaC; rewrite HX0; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  CONFINEMENT: every zero of XiC lies in 0 <= Re z <= 1             *)
(* ----------------------------------------------------------------- *)

Theorem XiC_zeros_in_strip : forall z, XiC z = C0 -> 0 <= Re z <= 1.
Proof.
  intros z Hz; split.
  - (* 0 <= Re z : else Re(1-z) > 1 and XiC(1-z) = XiC z <> 0 *)
    destruct (Rle_or_lt 0 (Re z)) as [H | H]; [ exact H | exfalso ].
    assert (Hgt : 1 < Re (Cminus C1 z))
      by (pose proof (Re_Cminus_C1 z); lra).
    apply (XiC_nonzero_gt1 (Cminus C1 z) Hgt).
    rewrite <- (XiC_symmetric z); exact Hz.
  - (* Re z <= 1 : else XiC z <> 0 directly *)
    destruct (Rle_or_lt (Re z) 1) as [H | H]; [ exact H | exfalso ].
    apply (XiC_nonzero_gt1 z H); exact Hz.
Qed.

Print Assumptions GammaC_half_ne0.
Print Assumptions LambdaC_completion_complex.
Print Assumptions XiC_zeros_in_strip.

(* ================================================================= *)
(*  END ZetaStripConfinement.v                                        *)
(*  UNCONDITIONAL: the zeros of the entire completed zeta XiC lie in    *)
(*  the closed critical strip 0 <= Re z <= 1.  Both analytic inputs     *)
(*  are discharged above.  The OPEN strip is ZetaOpenStrip.v.  The      *)
(*  critical line Re z = 1/2 (RH) remains open.                         *)
(* ================================================================= *)
