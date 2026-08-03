(* ================================================================= *)
(*  GammaC.v  —  the complex Gamma function GammaC = gnearC + gtailC,   *)
(*  holomorphic on Re z > 0 and agreeing with the real Gam.            *)
(*  The assembly: Cderiv_add of the near-0 and tail holomorphies,       *)
(*  RtoC_add for the agreement (Gam s = gnear s 1 + gtail s 1).         *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic GammaReal
        GammaTailC GammaNearC GammaNearCHolo.
Open Scope R_scope.

Definition GammaC (z : C) : C := Cadd (gnearCt z) (gtailC z).

Theorem GammaC_entire : forall z (Hz : 0 < Re z),
  is_Cderiv GammaC z (Cadd (dgnearC z Hz) (dgtailC z)).
Proof.
  intros z Hz; unfold GammaC.
  apply Cderiv_add; [ apply (gnearC_entire z Hz) | apply (gtailC_entire z) ].
Qed.

Theorem GammaC_agree : forall s (Hs : 0 < s), GammaC (RtoC s) = RtoC (Gam s Hs).
Proof.
  intros s Hs.
  assert (Hz : 0 < Re (RtoC s)) by (simpl; exact Hs).
  unfold GammaC, Gam, mellin.
  rewrite (gnearCt_val (RtoC s) Hz), (gnearC_agree s Hs Hz), gtailC_agree.
  rewrite <- RtoC_add; reflexivity.
Qed.

Print Assumptions GammaC_entire.
Print Assumptions GammaC_agree.

(* ================================================================= *)
(*  END GammaC.v  —  complex Gamma holomorphic on Re z > 0.            *)
(* ================================================================= *)
