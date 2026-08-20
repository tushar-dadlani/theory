(* ================================================================= *)
(*  CDerivGlobal.v  —  the derivative of an ENTIRE function, as a       *)
(*  function, with no choice axiom.                                    *)
(*                                                                    *)
(*    Fderiv : for F entire (pointwise-continuous, differentiable      *)
(*      everywhere), a function Fderiv F Hc with                        *)
(*        is_Cderiv F z (Fderiv F Hc z)   for every z, and              *)
(*        Fderiv F Hc itself entire.                                   *)
(*                                                                    *)
(*  CDerivHoloDisk.holo_deriv_fun already names the derivative -- level *)
(*  1 of the Cauchy-power tower -- but only on a DISK, and it returns   *)
(*  an existential.  Both limits matter downstream: order_one_step      *)
(*  wants a global Hp, and an existential per radius cannot be          *)
(*  assembled into one.                                                *)
(*                                                                    *)
(*  The fix is the same shape as the Hadamard glue.  The tower's level  *)
(*  1 is a DEFINITION, so run it at a radius read off the point --      *)
(*  radz z = 4 (|z| + 1) -- and take the value there.  Different        *)
(*  radii cannot disagree: both values are derivatives of F at the same *)
(*  point, and is_Cderiv_unique makes derivatives unique.  So near any  *)
(*  z0 the moving-radius function coincides with the fixed-radius one,  *)
(*  which fseq_chain differentiates, and is_Cderiv_ext_local carries    *)
(*  that over.                                                         *)
(*                                                                    *)
(*  No description principle is used: nothing is extracted from the     *)
(*  proposition "a derivative exists".  The value is computed by the    *)
(*  Cauchy integral and only AFTERWARDS shown to be the derivative.     *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral PerronRemovable CDerivUnique CCircleBound CCutoff
        CAnalyticTower CAnalyticTowerF CDerivHoloDisk.
Open Scope R_scope.

Definition radz (z : C) : R := 4 * (Cmod z + 1).

Lemma radz_pos : forall z, 0 < radz z.
Proof. intro z. unfold radz. pose proof (Cmod_nonneg z). lra. Qed.

Section Global.

Variable F : C -> C.
Hypothesis HFptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps.
Hypothesis HFhol : forall z, exists d, is_Cderiv F z d.

Definition Hc : CcontC F := ptcont_CcontC F HFptc.

(* the tower's level 1, at a radius read off the point *)
Definition Fderiv (z : C) : C := fseq F (radz z) (radz_pos z) Hc 1 z.

(* at any admissible radius, level 1 differentiates F *)
Lemma fs1_deriv : forall (Rr : R) (HR : 0 < Rr) (z : C), Cmod z < Rr / 2 ->
  is_Cderiv F z (fseq F Rr HR Hc 1 z).
Proof.
  intros Rr HR z Hz.
  apply (is_Cderiv_congr F (fseq F Rr HR Hc 0) z (fseq F Rr HR Hc 1 z)
           (Rr / 2 - Cmod z)); [ lra | | ].
  - intros w Hw. symmetry.
    apply (fseq0_eq F Rr HR Hc HFptc (fun w' _ => HFhol w') w).
    assert (Htri : Cmod w <= Cmod (Cminus w z) + Cmod z)
      by (replace w with (Cadd (Cminus w z) z) at 1 by ring; apply Cmod_triangle).
    lra.
  - exact (fseq_chain F Rr HR Hc (Ccont_circle_bounded F Rr Hc) 0 z Hz).
Qed.

Theorem Fderiv_spec : forall z, is_Cderiv F z (Fderiv z).
Proof.
  intro z. unfold Fderiv. apply fs1_deriv.
  unfold radz. pose proof (Cmod_nonneg z). lra.
Qed.

(* the radius does not matter: derivatives are unique *)
Lemma Fderiv_fixed : forall (Rr : R) (HR : 0 < Rr) (z : C), Cmod z < Rr / 2 ->
  Fderiv z = fseq F Rr HR Hc 1 z.
Proof.
  intros Rr HR z Hz.
  exact (is_Cderiv_unique F z _ _ (Fderiv_spec z) (fs1_deriv Rr HR z Hz)).
Qed.

Theorem Fderiv_holo : forall z0, exists d, is_Cderiv Fderiv z0 d.
Proof.
  intro z0.
  set (Rr := radz z0).
  assert (HR : 0 < Rr) by apply radz_pos.
  assert (Hin : forall w, Cmod (Cminus w z0) < 1 -> Cmod w < Rr / 2).
  { intros w Hw.
    assert (Htri : Cmod w <= Cmod (Cminus w z0) + Cmod z0)
      by (replace w with (Cadd (Cminus w z0) z0) at 1 by ring; apply Cmod_triangle).
    pose proof (Cmod_nonneg z0). unfold Rr, radz. lra. }
  eexists.
  apply (is_Cderiv_ext_local Fderiv (fseq F Rr HR Hc 1) z0 _ 1 ltac:(lra));
    [ intros w Hw; apply Fderiv_fixed; apply Hin; exact Hw | ].
  apply (fseq_chain F Rr HR Hc (Ccont_circle_bounded F Rr Hc) 1 z0).
  apply Hin. replace (Cminus z0 z0) with C0 by ring.
  rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

End Global.

Print Assumptions Fderiv_spec.
Print Assumptions Fderiv_holo.
