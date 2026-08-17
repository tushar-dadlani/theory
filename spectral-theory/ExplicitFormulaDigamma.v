(* ================================================================= *)
(*  ExplicitFormulaDigamma.v  —  Stage C core, brick 2:                 *)
(*  the Gamma-half (digamma) term of the  zeta'/zeta <-> xi'/xi  bridge. *)
(*                                                                    *)
(*  Third of the four bridge terms                                        *)
(*    zeta'/zeta = xi'/xi - 1/z - 1/(z-1) + 1/2 ln(pi) - 1/2(Gamma'/Gamma)(z/2). *)
(*  The completed-xi factor  GammaC(z/2) = GammaC(halfz z)  contributes,    *)
(*  by the chain rule, the term  1/2 . (Gamma'/Gamma)(z/2)  =  1/2 digamma. *)
(*                                                                    *)
(*    gammahalf_ne0 : GammaC(z/2) <> 0 on Re z > 0  (from GammaC_ne0_final, *)
(*        the GammaC != 0 result proved earlier this program) -- this is    *)
(*        what makes the log-derivative well-defined.                      *)
(*    gammahalf_deriv : d/dz GammaC(z/2) = (1/2) GammaC'(z/2)  (chain rule, *)
(*        Cderiv_comp_affine), parametrised on the derivative witness dG.   *)
(*    gammahalf_logderiv : the term (Gh'/Gh) = (1/2) digamma(z/2).          *)
(*    gammahalf_deriv_logform : the product-rule-ready form                 *)
(*        d/dz GammaC(z/2) = ((1/2) digamma(z/2)) . GammaC(z/2),            *)
(*        i.e. f' = (log-derivative) . f  (uses gammahalf_ne0).             *)
(*                                                                    *)
(*  With ExplicitFormulaXiZetaBridge (prefac, archexp) this completes 3 of  *)
(*  the 4 bridge terms in  f' = (log-derivative).f  form, ready for the     *)
(*  product-rule assembly of xi'/xi.  The one remaining term -- xi'/xi via  *)
(*  the HADAMARD PRODUCT for xi -- is the deep, RH-adjacent piece.          *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull Holomorphic CDeriv CHoloCalculus
        CZetaDeriv2 GammaC GammaCNe0 CZetaXiComplex.
Open Scope R_scope.

Lemma Rehalf_pos : forall z, 0 < Re z -> 0 < Re (halfz z).
Proof. intros z Hz. unfold halfz, Cadd, Cmul, RtoC, C0; cbn [Re Im]. lra. Qed.

(* the Gamma-half factor  GammaC(z/2)  is nonzero on Re z > 0 (uses GammaC != 0) *)
Lemma gammahalf_ne0 : forall z, 0 < Re z -> GammaC (halfz z) <> C0.
Proof. intros z Hz. apply GammaC_ne0_final, Rehalf_pos; exact Hz. Qed.

(* chain rule:  d/dz GammaC(z/2) = (1/2) * GammaC'(z/2) *)
Lemma gammahalf_deriv : forall z dG,
  is_Cderiv GammaC (halfz z) dG ->
  is_Cderiv (fun w => GammaC (halfz w)) z (Cmul (RtoC (/ 2)) dG).
Proof.
  intros z dG HdG. unfold halfz.
  apply (Cderiv_comp_affine GammaC (RtoC (/ 2)) C0 z dG). exact HdG.
Qed.

(* the digamma  Gamma'/Gamma  at w (given dG = Gamma'(w)) *)
Definition digamma (w dG : C) : C := Cmul dG (Cinv (GammaC w)).

(* the Gamma-half log-derivative term equals  (1/2) * digamma(z/2) *)
Lemma gammahalf_logderiv : forall z dG,
  Cmul (Cmul (RtoC (/ 2)) dG) (Cinv (GammaC (halfz z)))
  = Cmul (RtoC (/ 2)) (digamma (halfz z) dG).
Proof. intros. unfold digamma. ring. Qed.

(* product-rule-ready form:  d/dz GammaC(z/2) = ((1/2) digamma(z/2)) * GammaC(z/2) *)
Lemma gammahalf_deriv_logform : forall z (Hz : 0 < Re z) dG,
  is_Cderiv GammaC (halfz z) dG ->
  is_Cderiv (fun w => GammaC (halfz w)) z
    (Cmul (Cmul (RtoC (/ 2)) (digamma (halfz z) dG)) (GammaC (halfz z))).
Proof.
  intros z Hz dG HdG.
  apply (is_Cderiv_eq _ _ (Cmul (RtoC (/ 2)) dG)).
  - apply gammahalf_deriv; exact HdG.
  - unfold digamma. field. apply gammahalf_ne0; exact Hz.
Qed.

Print Assumptions gammahalf_ne0.
Print Assumptions gammahalf_deriv.
Print Assumptions gammahalf_deriv_logform.
