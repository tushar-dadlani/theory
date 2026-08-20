(* ================================================================= *)
(*  CWeierFactor.v  —  the Weierstrass factor estimate, for a FREE w.  *)
(*                                                                    *)
(*    weier_dev_le : Cmod ((1 + w) e^{-w} - 1)                         *)
(*                     <= Cmod w ^ 2 * (1 + 3 (1 + Cmod w) e^{Cmod w}) *)
(*                                                                    *)
(*  The repo already proves this for the SPECIFIC w = z / k, inside    *)
(*  GammaCWeierstrass.wcf_dev_le, as the estimate behind the           *)
(*  Weierstrass product  1/Gamma(z) = z e^{gamma z} prod (1+z/k)e^{-z/k}. *)
(*  Hadamard needs the same factor at a FREE point: its factor         *)
(*  (1 - z/rho) e^{z/rho} is literally (1 + w) e^{-w} with w = -z/rho.  *)
(*  So the analytic core does not need building, only freeing from the  *)
(*  1/k parametrisation.                                              *)
(*                                                                    *)
(*  This is wcf_dev_le with its Hmw_eq / HmwZ / HmwSq / Hfac / Hmono   *)
(*  steps removed -- those exist only to re-express Cmod (z/k) in terms *)
(*  of Cmod z, which a free w makes unnecessary.  What survives is the  *)
(*  algebra                                                            *)
(*                                                                    *)
(*    (1+w) e^{-w} - 1  =  -w^2 + (1+w) . Rem,   Rem := e^{-w} - 1 + w  *)
(*                                                                    *)
(*  plus CexpRemainder.Cexpf_remainder and the triangle inequality.    *)
(*                                                                    *)
(*  GammaCWeierstrass is deliberately NOT refactored to use this --     *)
(*  tidier, but it would put the Gamma chain at risk for no gain here.  *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CDeriv CexpFull CexpRemainder.
Open Scope R_scope.

Lemma weier_dev_le : forall w : C,
  Cmod (Cminus (Cmul (Cadd C1 w) (Cexpf (Copp w))) C1)
  <= Cmod w ^ 2 * (1 + 3 * (1 + Cmod w) * exp (Cmod w)).
Proof.
  intro w.
  set (Rem := Cminus (Cminus (Cexpf (Copp w)) C1) (Copp w)).
  assert (Hexp : Cexpf (Copp w) = Cadd (Cadd C1 (Copp w)) Rem)
    by (unfold Rem; ring).
  assert (Hid : Cminus (Cmul (Cadd C1 w) (Cexpf (Copp w))) C1
                = Cadd (Copp (Cmul w w)) (Cmul (Cadd C1 w) Rem))
    by (rewrite Hexp; ring).
  rewrite Hid.
  assert (Hmw0 : 0 <= Cmod w) by apply Cmod_nonneg.
  assert (HRem : Cmod Rem <= 3 * Cmod w ^ 2 * exp (Cmod w)).
  { unfold Rem. pose proof (Cexpf_remainder (Copp w)) as H.
    rewrite Cmod_opp in H. exact H. }
  assert (H1w : Cmod (Cadd C1 w) <= 1 + Cmod w).
  { eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_C1. apply Rle_refl. }
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite Cmod_opp, Cmod_mul, Cmod_mul.
  apply Rle_trans with
    (Cmod w * Cmod w + (1 + Cmod w) * (3 * Cmod w ^ 2 * exp (Cmod w))).
  - apply Rplus_le_compat_l. apply Rmult_le_compat;
      [ apply Cmod_nonneg | apply Cmod_nonneg | exact H1w | exact HRem ].
  - apply Req_le. ring.
Qed.

Print Assumptions weier_dev_le.
