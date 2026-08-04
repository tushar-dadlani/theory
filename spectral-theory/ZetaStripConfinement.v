(* ================================================================= *)
(*  ZetaStripConfinement.v  —  the strip-confinement REDUCTION.        *)
(*                                                                    *)
(*  MILESTONE 2 (conditional form): the nontrivial zeros of the        *)
(*  operator zeta lie in the closed critical strip 0 <= Re z <= 1.     *)
(*  Equivalently, the entire completed function XiC has no zeros        *)
(*  outside the strip.                                                 *)
(*                                                                    *)
(*  This file machine-checks the classical REDUCTION, isolating the    *)
(*  two remaining analytic inputs as explicit hypotheses:             *)
(*                                                                    *)
(*    H_compl : for Re w > 1, the COMPLEX completion identity          *)
(*        LambdaC w = pi^{-w/2} * GammaC(w/2) * zetaC w                 *)
(*      (currently only the real-argument LambdaC_is_completion_of_    *)
(*       zetaC exists; the all-w version needs a complex theta-Mellin  *)
(*       derivation);                                                  *)
(*                                                                    *)
(*    H_gamma : for Re w > 1, GammaC(w/2) <> 0                         *)
(*      (complex Gamma nonvanishing on Re > 1/2; needs the reflection  *)
(*       formula or Weierstrass product).                             *)
(*                                                                    *)
(*  Given these, the confinement follows from Milestone 1              *)
(*  (zetaC_nonzero, CEulerProductZeta) — zetaC <> 0 for Re > 1 — plus   *)
(*  Cpw <> 0 (Cexpf_ne0) and the functional-equation symmetry          *)
(*  XiC z = XiC(1-z) (RiemannXiEntire.XiC_symmetric), which folds the   *)
(*  left half-plane Re z < 0 onto Re(1-z) > 1.  Axiom-clean.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CexpFull CDeriv CZeta CEulerProductZeta
        GammaC RiemannXiEntire ZetaFunctionalEq.
Open Scope R_scope.

(* Cpw is never zero (one-line corollary of Cexpf_ne0) *)
Lemma Cpw_ne0 : forall c w, Cpw c w <> C0.
Proof. intros c w; unfold Cpw; apply Cexpf_ne0. Qed.

Section Confinement.

(* the complex completion identity, for Re w > 1 (to be discharged later) *)
Hypothesis H_compl :
  forall w (Hw0 : 0 < Re w) (Hw1 : Cminus C1 w <> C0), 1 < Re w ->
    LambdaC w
    = Cmul (Cpw PI (Copp (Cmul w (RtoC (/ 2)))))
           (Cmul (GammaC (Cmul w (RtoC (/ 2)))) (zetaC w Hw0 Hw1)).

(* complex Gamma nonvanishing on Re > 1/2 (to be discharged later) *)
Hypothesis H_gamma : forall w, 1 < Re w -> GammaC (Cmul w (RtoC (/ 2))) <> C0.

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
  { rewrite (H_compl w Hw0 Hw1 Hw).
    apply Cmul_ne0; [ apply Cpw_ne0 | ].
    apply Cmul_ne0; [ apply H_gamma; exact Hw | apply (zetaC_nonzero w Hw Hw0 Hw1) ]. }
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

End Confinement.

Print Assumptions XiC_zeros_in_strip.

(* ================================================================= *)
(*  END ZetaStripConfinement.v                                        *)
(*  Conditional on the complex completion identity (H_compl) and       *)
(*  complex Gamma nonvanishing (H_gamma), the zeros of the entire       *)
(*  completed zeta XiC lie in the closed critical strip 0 <= Re z <= 1  *)
(*  — the classical confinement, with the two analytic inputs cleanly   *)
(*  isolated.  The critical line Re z = 1/2 (RH) remains open.          *)
(* ================================================================= *)
