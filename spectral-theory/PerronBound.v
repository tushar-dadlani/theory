(* ================================================================= *)
(*  PerronBound.v  —  Perron milestone A1d (estimate foundations).       *)
(*                                                                    *)
(*  Two reusable analytic tools for the truncated Perron bounds          *)
(*  perron_gt1 / perron_lt1:                                             *)
(*                                                                    *)
(*    Cintf_mod_le2 : Cmod (∫ f) ≤ 2·∫ Cmod f    (the complex-integral    *)
(*        triangle inequality, factor-2 form via Re/Im — sharp enough     *)
(*        for the O(y^c/(T ln y)) horizontal-edge decay; the sup×length   *)
(*        bound Cintf_ML diverges as the closing width U→∞, this does     *)
(*        not).                                                          *)
(*                                                                    *)
(*    Rpower_exp_deriv : d/ds y^s = ln y · y^s   (the EXPONENT derivative  *)
(*        of Rpower, the antiderivative behind ∫ y^σ dσ = (y^b−y^a)/ln y). *)
(*                                                                    *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CSeries CIntegral2.
Open Scope R_scope.

(* the complex-integral triangle inequality, factor-2 form (integrated) *)
Lemma Cintf_mod_le2 : forall f Hf a b
  (Hcm : Riemann_integrable (fun u => Cmod (f u)) a b),
  a <= b -> Cmod (Cintf f Hf a b) <= 2 * RiemannInt Hcm.
Proof.
  intros f Hf a b Hcm Hab.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  rewrite Re_Cintf, Im_Cintf.
  assert (HRe : Rabs (RiemannInt (cont_RI _ (proj1 Hf) a b)) <= RiemannInt Hcm).
  { eapply Rle_trans;
      [ apply (RiemannInt_P17 (cont_RI _ (proj1 Hf) a b)
                 (RiemannInt_P16 (cont_RI _ (proj1 Hf) a b)) Hab) | ].
    apply RiemannInt_P19; [ exact Hab | ].
    intros x Hx; apply Cmod_Re. }
  assert (HIm : Rabs (RiemannInt (cont_RI _ (proj2 Hf) a b)) <= RiemannInt Hcm).
  { eapply Rle_trans;
      [ apply (RiemannInt_P17 (cont_RI _ (proj2 Hf) a b)
                 (RiemannInt_P16 (cont_RI _ (proj2 Hf) a b)) Hab) | ].
    apply RiemannInt_P19; [ exact Hab | ].
    intros x Hx; apply Cmod_Im. }
  lra.
Qed.

(* the exponent derivative of Rpower:  d/ds y^s = ln y · y^s *)
Lemma Rpower_exp_deriv : forall y s0, 0 < y ->
  derivable_pt_lim (fun s => Rpower y s) s0 (ln y * Rpower y s0).
Proof.
  intros y s0 Hy; unfold Rpower.
  replace (ln y * exp (s0 * ln y)) with (exp (s0 * ln y) * ln y) by ring.
  apply (derivable_pt_lim_comp (fun s => s * ln y) exp s0 (ln y) (exp (s0 * ln y))).
  - intros eps Heps; exists (mkposreal 1 Rlt_0_1); intros h Hh0 _.
    replace (((s0 + h) * ln y - s0 * ln y) / h - ln y) with 0 by (field; exact Hh0).
    rewrite Rabs_R0; exact Heps.
  - apply derivable_pt_lim_exp.
Qed.

Print Assumptions Cintf_mod_le2.
Print Assumptions Rpower_exp_deriv.

(* ================================================================= *)
(*  END PerronBound.v — the two estimate foundations.  Next: Vperron,    *)
(*  the right-edge change of variables, the horizontal-edge decay via     *)
(*  ∫ y^σ dσ, the U→∞ limit, giving perron_gt1 / perron_lt1.             *)
(* ================================================================= *)
