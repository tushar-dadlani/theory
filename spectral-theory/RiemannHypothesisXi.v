(* ================================================================= *)
(*  RiemannHypothesisXi.v  —  the statement of the Riemann Hypothesis    *)
(*  in this development's machinery.                                   *)
(*                                                                    *)
(*  XiC is the entire completed zeta xi (RiemannXiEntire.v): total,    *)
(*  holomorphic (XiC_entire), symmetric XiC z = XiC(1-z)               *)
(*  (XiC_symmetric), and agreeing with Riemann's real xi on the axis   *)
(*  (XiC_agree).  Its zeros are exactly the NONTRIVIAL zeros of the     *)
(*  zeta function (the 1/2 z(z-1) factor removes the pole at z=1 and    *)
(*  the Gamma(z/2) poles cancel the trivial zeros at -2,-4,...).        *)
(*                                                                    *)
(*  So RH is the statement that every zero of XiC lies on the critical *)
(*  line Re z = 1/2.  This is a well-typed Prop in our machinery — it   *)
(*  is STATED here, not proved; RH is open.                           *)
(*                                                                    *)
(*  What IS proved in the repo, UNCONDITIONALLY, is the confinement of *)
(*  the zeros to the OPEN critical strip 0 < Re z < 1                  *)
(*  (ZetaOpenStrip.XiC_zeros_in_open_strip; the closed form is         *)
(*  ZetaStripConfinement.XiC_zeros_in_strip, whose two former analytic *)
(*  hypotheses are now discharged there).  CriticalDepth.v recoordina- *)
(*  tises that strip by the logit, so that the functional equation      *)
(*  becomes negation and RH becomes depth = 0 (RH_iff_depth_zero).     *)
(*  RH itself — the collapse of the strip onto the line — is untouched.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CZeta.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  THE RIEMANN HYPOTHESIS (statement)                               *)
(* ----------------------------------------------------------------- *)

(* Every zero of the entire completed zeta lies on the critical line. *)
Definition RiemannHypothesis : Prop :=
  forall z : C, XiC z = C0 -> Re z = / 2.

(* The equivalent statement phrased directly about the zeta            *)
(* continuation zetaC (its zeros in the domain Re z > 0 are exactly     *)
(* the nontrivial zeros).                                              *)
Definition RH_zeta : Prop :=
  forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
    zetaC z H0 H1 = C0 -> Re z = / 2.

(* ----------------------------------------------------------------- *)
(*  Sanity check: RH sharpens the strip confinement.                 *)
(*  This direction (line => strip) is trivially TRUE and proved here; *)
(*  it certifies that our RH statement really does entail all zeros    *)
(*  in the closed critical strip 0 <= Re z <= 1.                       *)
(* ----------------------------------------------------------------- *)

Theorem RH_implies_strip :
  RiemannHypothesis -> forall z : C, XiC z = C0 -> 0 <= Re z <= 1.
Proof. intros HRH z Hz; pose proof (HRH z Hz) as He; lra. Qed.

Print Assumptions RH_implies_strip.

(* ================================================================= *)
(*  END RiemannHypothesis.v                                           *)
(*  RH is stated (RiemannHypothesis / RH_zeta) and shown to entail the *)
(*  strip confinement.  The hypothesis itself remains OPEN — nothing    *)
(*  in this development proves or disproves it.                        *)
(* ================================================================= *)
