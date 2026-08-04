(* ================================================================= *)
(*  ZetaCriticalLine.v  —  the completed zeta is REAL on the critical  *)
(*  line.                                                              *)
(*                                                                    *)
(*  On the line Re z = 1/2 the two reflections coincide: 1 - z = conj z.*)
(*  Combining the functional equation XiC z = XiC(1-z) (XiC_symmetric)  *)
(*  with reality XiC(conj z) = conj(XiC z) (XiC_conj, ZetaZeroQuadruple)*)
(*  gives XiC z = conj(XiC z), i.e. XiC is REAL-VALUED on the critical  *)
(*  line: Im (XiC (1/2 + it)) = 0.                                     *)
(*                                                                    *)
(*  This is the fact underlying zero-counting on the line (sign changes *)
(*  of the real Riemann-Siegel Z-function) and all numerical           *)
(*  verification of RH.  Unconditional, axiom-clean.                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire ZetaZeroQuadruple.
Open Scope R_scope.

(* on the critical line the point- and axis-reflections coincide *)
Lemma line_one_minus_eq_conj : forall z, Re z = / 2 -> Cminus C1 z = Cconj z.
Proof. intros z Hz; apply Ceq; unfold Cminus, Cconj, C1; simpl; lra. Qed.

(* XiC is real-valued on the critical line *)
Theorem XiC_real_on_line : forall z, Re z = / 2 -> Im (XiC z) = 0.
Proof.
  intros z Hz.
  assert (Hfix : XiC z = Cconj (XiC z)).
  { transitivity (XiC (Cminus C1 z)); [ apply XiC_symmetric | ].
    rewrite (line_one_minus_eq_conj z Hz); apply XiC_conj. }
  assert (HIm : Im (XiC z) = Im (Cconj (XiC z))) by (f_equal; exact Hfix).
  rewrite Im_Cconj in HIm; lra.
Qed.

Print Assumptions XiC_real_on_line.

(* ================================================================= *)
(*  END ZetaCriticalLine.v                                            *)
(*  XiC is real on Re z = 1/2 — the basis of zero-counting on the line. *)
(* ================================================================= *)
