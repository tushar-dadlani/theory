(* ================================================================= *)
(*  ZetaXiLink.v  —  Phase 1: the bridge.  The entire symmetric        *)
(*  complex XiC IS the completed Riemann zeta:                          *)
(*    XiC(s) = ½·s·(s−1)·π^{−s/2}·Γ(s/2)·ζ(s)    for real s > 1.        *)
(*                                                                    *)
(*  Pure assembly of XiC_agree (theta-tail form), the algebraic fact   *)
(*  ½·s(s−1)·J(s) = ½ + ½·s(s−1)(T s + T(1−s))  (since                  *)
(*  s(s−1)(−1/s+1/(s−1)) = 1), and zeta_completed_eq_J                  *)
(*  (π^{−s/2}Γ(s/2)ζ_cont(s) = J(s), s>1).  This fuses the theta tower  *)
(*  (XiC) and the Euler–Maclaurin tower (zeta_cont).  Axiom-clean.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus RiemannXiEntire RiemannThetaFE MellinTail
               GammaReal Ell2ZetaCont ZetaCompleted.
Open Scope R_scope.

Theorem XiC_is_completed_zeta :
  forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  XiC (RtoC s)
  = RtoC (/ 2 * s * ((s - 1)
          * (Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * zeta_cont s Hs0 Hs1))).
Proof.
  intros s Hs0 Hs1 Hs2 Hs.
  assert (Hne0 : s <> 0) by lra.
  assert (Hne1 : s - 1 <> 0) by lra.
  rewrite XiC_agree, (zeta_completed_eq_J s Hs0 Hs1 Hs2 Hs).
  f_equal; unfold J; field; split; assumption.
Qed.

Print Assumptions XiC_is_completed_zeta.

(* ================================================================= *)
(*  END ZetaXiLink.v (Phase 1: XiC = completed zeta on s > 1).        *)
(* ================================================================= *)
