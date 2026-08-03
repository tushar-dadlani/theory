(* ================================================================= *)
(*  ZetaFunctionalEq.v  —  Phase 2: the functional equation of the     *)
(*  completed Riemann zeta.                                            *)
(*                                                                    *)
(*  LambdaC z := 2·XiC(z) / (z(z−1))  is the complex completed zeta,    *)
(*  defined directly from the entire XiC (so no complex Gamma is        *)
(*  needed).  We prove:                                               *)
(*    LambdaC z = LambdaC(1−z)                    (the functional eq),  *)
(*    LambdaC(s) = π^{−s/2}Γ(s/2)ζ(s)   for s>1   (it IS the completion),*)
(*    LambdaC(s) = π^{−s/2}Γ(s/2) · zetaC(s)       (tie to complex ζ).  *)
(*  The symmetry is inherited for free from XiC_symmetric via the       *)
(*  identity (1−z)((1−z)−1) = z(z−1).  Axiom-clean.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus RiemannXiEntire ZetaXiLink
               GammaReal Ell2ZetaCont CZeta.
Open Scope R_scope.

(* the complex completed zeta, built from the entire theta-tail XiC *)
Definition LambdaC (z : C) : C :=
  Cmul (RtoC 2) (Cmul (XiC z) (Cinv (Cmul z (Cminus z C1)))).

(* --- THE FUNCTIONAL EQUATION: LambdaC(z) = LambdaC(1 − z) --- *)
Theorem LambdaC_FE : forall z, LambdaC z = LambdaC (Cminus C1 z).
Proof.
  intro z; unfold LambdaC.
  rewrite <- (XiC_symmetric z).
  replace (Cmul (Cminus C1 z) (Cminus (Cminus C1 z) C1))
    with (Cmul z (Cminus z C1)) by ring.
  reflexivity.
Qed.

(* --- LambdaC restricts to the real completed zeta (s > 1) --- *)
Theorem LambdaC_agree :
  forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  LambdaC (RtoC s)
  = RtoC (Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hs2 Hs.
  assert (Hss : s * (s - 1) <> 0)
    by (apply Rmult_integral_contrapositive_currified; lra).
  unfold LambdaC.
  rewrite (XiC_is_completed_zeta s Hs0 Hs1 Hs2 Hs).
  replace (Cminus (RtoC s) C1) with (RtoC (s - 1)) by (apply Ceq; simpl; lra).
  rewrite <- (RtoC_mul s (s - 1)), (Cinv_RtoC (s * (s - 1)) Hss), <- !RtoC_mul.
  f_equal; field; split; lra.
Qed.

(* --- the completed zeta is (π^{−s/2}Γ(s/2)) times the complex zetaC --- *)
Theorem LambdaC_is_completion_of_zetaC :
  forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2) H0 H1, 1 < s ->
  LambdaC (RtoC s)
  = Cmul (RtoC (Rpower PI (- (s / 2)) * Gam (s / 2) Hs2)) (zetaC (RtoC s) H0 H1).
Proof.
  intros s Hs0 Hs1 Hs2 H0 H1 Hs.
  rewrite (LambdaC_agree s Hs0 Hs1 Hs2 Hs), (zetaC_agree s Hs0 Hs1 H0 H1).
  rewrite <- RtoC_mul; reflexivity.
Qed.

Print Assumptions LambdaC_FE.
Print Assumptions LambdaC_agree.
Print Assumptions LambdaC_is_completion_of_zetaC.

(* ================================================================= *)
(*  END ZetaFunctionalEq.v (Phase 2: completed-zeta functional eq).   *)
(* ================================================================= *)
