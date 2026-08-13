(* ================================================================= *)
(*  CFEChain.v  (identity-theorem plan, the FE_diff chain — start)     *)
(*                                                                    *)
(*  Building the derivative chain for FE_diff to feed the domain-       *)
(*  restricted identity tower (identity_on_disk_D / identity_propagate  *)
(*  _D) and discharge GammaC_FE_from_identity.                         *)
(*                                                                    *)
(*  Brick 1 (this file): the FE-specific input facts the analyticity    *)
(*  master key needs -- FE_diff is pointwise continuous on Re > 0       *)
(*  (from FE_diff_holo + is_Cderiv_cont).  Together with FE_diff_holo   *)
(*  (differentiable on Re>0) and FE_diff_vanishes_real, these are the    *)
(*  hypotheses cauchy_integral_holo consumes to build the chain.        *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CHoloCalculus GammaCFE.
Open Scope R_scope.

(* FE_diff is (pointwise) continuous everywhere it is holomorphic *)
Lemma FE_diff_ptcont : forall z, 0 < Re z -> forall eps, 0 < eps ->
  exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (FE_diff z') (FE_diff z)) < eps.
Proof.
  intros z Hz eps Heps.
  destruct (FE_diff_holo z Hz) as [d Hd].
  destruct (is_Cderiv_cont FE_diff z d Hd eps Heps) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros z' Hz'.
  pose proof (Hc (Cminus z' z) Hz') as Hcc.
  replace (Cadd z (Cminus z' z)) with z' in Hcc by ring.
  exact Hcc.
Qed.

Print Assumptions FE_diff_ptcont.
