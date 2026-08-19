(* ================================================================= *)
(*  XiNonzero.v  —  xi is not identically zero: XiC C0 = 1/2 <> 0.      *)
(*                                                                    *)
(*    XiC_C0      : XiC C0 = RtoC (/ 2)                                *)
(*    XiC_ne0_at0 : XiC C0 <> C0                                       *)
(*                                                                    *)
(*  This is the "xi is not identically zero" witness needed by the      *)
(*  discreteness-of-zeros argument (an analytic function with a         *)
(*  non-isolated zero is identically zero, contradicting this).         *)
(*  Trivially from RiemannXiEntire.XiC_agree at s = 0 (the z(z-1)        *)
(*  factor vanishes).  Axiom-clean.                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire.
Open Scope R_scope.

Lemma XiC_C0 : XiC C0 = RtoC (/ 2).
Proof.
  replace C0 with (RtoC 0) by (apply Ceq; simpl; ring).
  rewrite XiC_agree. apply Ceq; simpl; ring.
Qed.

Lemma XiC_ne0_at0 : XiC C0 <> C0.
Proof.
  rewrite XiC_C0. intro Hc.
  apply (f_equal Re) in Hc. unfold RtoC, C0, Re in Hc. simpl in Hc. lra.
Qed.

Print Assumptions XiC_ne0_at0.
