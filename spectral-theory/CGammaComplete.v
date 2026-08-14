(* ================================================================= *)
(*  CGammaComplete.v  (identity-theorem plan, FE chain — THE FINISH)    *)
(*                                                                    *)
(*  The complex Gamma functional equation, unconditionally:            *)
(*     GammaC (z + 1) = z . GammaC z   for all Re z > 0.               *)
(*  FE_diff = GammaC(z+1) - z GammaC z is holomorphic (FE_diff_holo)    *)
(*  and continuous (FE_diff_ptcont) on {Re>0} and vanishes on the        *)
(*  positive ray (FE_diff_vanishes_real); the identity theorem for the   *)
(*  half-plane (CWalk.reach) propagates that to FE_diff = 0 everywhere   *)
(*  on {Re>0}, and GammaC_FE_from_identity concludes.                   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals.
Require Import ComplexField Cmodulus GammaC GammaCFE CFEChain CWalk.
Open Scope R_scope.

Theorem FE_diff_zero_halfplane : forall z, 0 < Re z -> FE_diff z = C0.
Proof.
  apply (reach FE_diff FE_diff_ptcont FE_diff_holo).
  intros s Hs. exact (FE_diff_vanishes_real s Hs).
Qed.

Theorem GammaC_FE_complete : GammaC_FE.
Proof.
  apply GammaC_FE_from_identity. exact FE_diff_zero_halfplane.
Qed.

(* unfolded headline: the functional equation itself *)
Theorem GammaC_functional_equation :
  forall z, 0 < Re z -> GammaC (Cadd z C1) = Cmul z (GammaC z).
Proof. exact GammaC_FE_complete. Qed.

Print Assumptions GammaC_FE_complete.
