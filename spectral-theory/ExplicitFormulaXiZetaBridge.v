(* ================================================================= *)
(*  ExplicitFormulaXiZetaBridge.v  —  Stage C core, brick 1:             *)
(*  the elementary log-derivative terms of the  zeta'/zeta <-> xi'/xi      *)
(*  bridge.                                                              *)
(*                                                                    *)
(*  The completed xi factors (CZetaXiComplex) as                          *)
(*     XiC z = prefac(z) . archexp(z) . GammaC(z/2) . zetaC(z)            *)
(*           = 1/2 z(z-1) . pi^{-z/2} . Gamma(z/2) . zeta(z),             *)
(*  so taking the logarithmic derivative (sum of the four factors' log-    *)
(*  derivatives) and rearranging gives the master identity that carries    *)
(*  the zeros side (xi'/xi, whose poles ARE the nontrivial zeros rho) to   *)
(*  the prime side (zeta'/zeta = sum Lam(n) n^{-s}):                       *)
(*                                                                    *)
(*     zeta'/zeta(z) = xi'/xi(z) - 1/z - 1/(z-1)                          *)
(*                     + 1/2 ln(pi) - 1/2 . (Gamma'/Gamma)(z/2).          *)
(*                                                                    *)
(*  This file proves the two ELEMENTARY, fully explicit terms (no digamma, *)
(*  no Hadamard product, no growth bounds needed):                        *)
(*                                                                    *)
(*    prefac_deriv / prefac_logderiv :                                    *)
(*        d/dz [1/2 z(z-1)] / [1/2 z(z-1)]  =  1/z + 1/(z-1)              *)
(*    archexp_deriv / archexp_logderiv :                                  *)
(*        d/dz [pi^{-z/2}] / [pi^{-z/2}]  =  -1/2 ln(pi).                 *)
(*                                                                    *)
(*  The remaining two terms are the deep Stage-C core: the Gamma-half      *)
(*  digamma  (Gamma'/Gamma)(z/2)  (needs GammaC's derivative + GammaC != 0,*)
(*  both already available) and, crucially, xi'/xi via the HADAMARD        *)
(*  PRODUCT for xi (giving xi'/xi = B + sum_rho [1/(z-rho) + 1/rho]) --    *)
(*  the latter being the genuinely hard, RH-adjacent piece that also       *)
(*  supplies the zeta'/zeta growth bounds vanishing the far contour edges. *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv CHoloCalculus
        CZetaDeriv2 ZetaStripConfinement CZetaXiComplex.
Open Scope R_scope.

Lemma RtoC_half_ne0 : RtoC (/ 2) <> C0.
Proof. intro H. apply (f_equal Re) in H. unfold RtoC, C0 in H; cbn [Re] in H. lra. Qed.

(* ---- prefac z = 1/2 z (z-1) :  derivative and log-derivative ---- *)
Definition dprefac (z : C) : C := Cmul (RtoC (/ 2)) (Cadd (Cminus z C1) z).

Lemma prefac_deriv : forall z, is_Cderiv prefac z (dprefac z).
Proof.
  intro z. unfold prefac, dprefac.
  apply (is_Cderiv_eq _ _ (Cadd (Cmul C0 (Cmul z (Cminus z C1)))
                                (Cmul (RtoC (/ 2)) (Cadd (Cmul C1 (Cminus z C1)) (Cmul z C1))))).
  - apply (Cderiv_mul (fun _ => RtoC (/ 2)) (fun w => Cmul w (Cminus w C1)) z);
      [ apply Cderiv_const | ].
    apply (Cderiv_mul (fun w => w) (fun w => Cminus w C1) z); [ apply Cderiv_id | ].
    apply (is_Cderiv_eq _ _ (Cadd C1 (Copp C0)));
      [ apply Cderiv_minus; [ apply Cderiv_id | apply Cderiv_const ] | ring ].
  - ring.
Qed.

Lemma prefac_logderiv : forall z, z <> C0 -> Cminus z C1 <> C0 ->
  Cmul (dprefac z) (Cinv (prefac z)) = Cadd (Cinv z) (Cinv (Cminus z C1)).
Proof.
  intros z Hz Hz1. unfold dprefac, prefac.
  field. repeat split; [ exact Hz1 | exact Hz | exact RtoC_half_ne0 ].
Qed.

(* ---- archexp z = pi^{-z/2} :  derivative and log-derivative ---- *)
Definition darchexp (z : C) : C := Cmul (RtoC (- / 2 * ln PI)) (archexp z).

Lemma archexp_deriv : forall z, is_Cderiv archexp z (darchexp z).
Proof.
  intro z.
  apply (is_Cderiv_eq _ _ (Cmul (RtoC (- / 2))
                            (Cmul (RtoC (ln PI)) (Cpw PI (Cadd (Cmul (RtoC (- / 2)) z) C0))))).
  - unfold archexp, mhalfz.
    apply (Cderiv_comp_affine (Cpw PI) (RtoC (- / 2)) C0 z
             (Cmul (RtoC (ln PI)) (Cpw PI (Cadd (Cmul (RtoC (- / 2)) z) C0)))).
    apply Cpw_deriv, PI_RGT_0.
  - unfold darchexp, archexp, mhalfz.
    set (P := Cpw PI (Cadd (Cmul (RtoC (- / 2)) z) C0)).
    rewrite (RtoC_mul (- / 2) (ln PI)). ring.
Qed.

Lemma archexp_logderiv : forall z,
  Cmul (darchexp z) (Cinv (archexp z)) = RtoC (- / 2 * ln PI).
Proof.
  intro z. unfold darchexp, archexp.
  field. apply Cpw_ne0.
Qed.

Print Assumptions prefac_deriv.
Print Assumptions prefac_logderiv.
Print Assumptions archexp_deriv.
Print Assumptions archexp_logderiv.
