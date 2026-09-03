(* ================================================================= *)
(*  CTruncKernel.v  --  Zagier's kernel K_R(z) = 1/z + z/R^2 on the    *)
(*  truncated contour, UNCONDITIONALLY.                               *)
(*                                                                    *)
(*  CTruncCauchyDom.trunc_cauchy_dom evaluates the 1/z half:           *)
(*      int_arc F/z + int_chord F/z = 2*pi*i*F(0).                     *)
(*  The z/R^2 half is holomorphic wherever F is, so its loop integral  *)
(*  vanishes: PrimC (the convex-region primitive) is a primitive for   *)
(*  it on U, and pathint_FTC telescopes arc-then-chord to zero -- the  *)
(*  arc runs Qc -> Pc and the chord runs Pc -> Qc, so the two          *)
(*  differences cancel.  Adding the halves:                            *)
(*                                                                    *)
(*      int_arc F*K_R + int_chord F*K_R = 2*pi*i*F(0).                 *)
(*                                                                    *)
(*  This is the contour identity of brick E5, stated for an arbitrary  *)
(*  F that is pointwise continuous everywhere and holomorphic on the   *)
(*  convex open U carrying the contour -- exactly the interface that   *)
(*  NewmanCutoff.gtrunc_CcontC and NewmanHolo.LTN_holo supply.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CIntegral2 CSegInt CPathIntegral CPathFTC CPrimConv CGoursatLin
        CLeibniz CWinding CPrimitive PerronRemovable CWindingOffCenter
        CTruncWind CTruncCauchy CTruncCauchyDom CNewmanKernel.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Two missing closure lemmas.                                       *)
(* ----------------------------------------------------------------- *)

Lemma Ccont_congr : forall f g, (forall u, f u = g u) -> Ccont f -> Ccont g.
Proof.
  intros f g Heq Hf.
  assert (Hfe : f = g) by (apply functional_extensionality; exact Heq).
  rewrite <- Hfe; exact Hf.
Qed.

Lemma CcontC_mul : forall f g, CcontC f -> CcontC g ->
  CcontC (fun z => Cmul (f z) (g z)).
Proof. intros f g Hf Hg h Hh; apply Ccont_mul; [ apply Hf | apply Hg ]; exact Hh. Qed.

Lemma CcontC_id : CcontC (fun z : C => z).
Proof. intros h Hh; exact Hh. Qed.

(* ================================================================= *)
Section TruncKernel.
Variables (Rr alpha : R).
Hypothesis HR : 0 < Rr.
Hypothesis Halpha : PI / 2 < alpha < PI.
Let Pc : C := mkC (Rr * cos alpha) (Rr * sin alpha).
Let Qc : C := mkC (Rr * cos alpha) (- (Rr * sin alpha)).

Variable U : C -> Prop.
Hypothesis HUc : Convex U.
Hypothesis HUo : Open U.
Hypothesis HU0 : U C0.
Hypothesis HarcU : forall s, - alpha <= s <= alpha -> U (arc Rr s).
Hypothesis HchordU : forall s, 0 <= s <= 1 -> U (seg Pc Qc s).

Variable F : C -> C.
Hypothesis Fptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps.
Hypothesis Fholo : forall z, U z -> exists d, is_Cderiv F z d.

Let HFc : CcontC F := ptcont_CcontC F Fptc.

(* ---- the holomorphic half of the kernel, folded into F ---- *)
Definition Klin (z : C) : C := Cmul (F z) (Cmul z (RtoC (/ (Rr * Rr)))).

Lemma Klin_CcontC : CcontC Klin.
Proof.
  unfold Klin; apply CcontC_mul; [ exact HFc | ].
  apply CcontC_mul; [ exact CcontC_id | apply CcontC_const ].
Qed.

Lemma Klin_holo : forall z, U z -> exists d, is_Cderiv Klin z d.
Proof.
  intros z HUz; destruct (Fholo z HUz) as [d Hd].
  eexists; unfold Klin; apply Cderiv_mul; [ exact Hd | ].
  apply Cderiv_mul; [ apply Cderiv_id | apply Cderiv_const ].
Qed.

(* ---- the contour identity ---- *)
Theorem trunc_kernel_dom :
  forall (HfaK : Ccont (fun u => Cmul (Cmul (F (arc Rr u))
                                            (newman_kernel Rr (arc Rr u)))
                                      (arc' Rr u)))
         (HfcK : Ccont (fun u => Cmul (Cmul (F (seg Pc Qc u))
                                            (newman_kernel Rr (seg Pc Qc u)))
                                      (seg' Pc Qc u))),
  Cadd (pathint (arc Rr) (arc' Rr)
          (fun z => Cmul (F z) (newman_kernel Rr z)) HfaK (- alpha) alpha)
       (pathint (seg Pc Qc) (seg' Pc Qc)
          (fun z => Cmul (F z) (newman_kernel Rr z)) HfcK 0 1)
  = Cmul (F C0) (mkC 0 (2 * PI)).
Proof.
  intros HfaK HfcK. assert (HPI := PI_RGT_0).
  assert (Hcos : cos alpha < 0) by (apply cos_neg_on_quad2; exact Halpha).
  assert (Hchord_ne : forall s, seg Pc Qc s <> C0).
  { intros s Hc. apply (f_equal Re) in Hc. cbn in Hc. nra. }
  (* --- the six continuity witnesses --- *)
  assert (HcC : Ccont (fun u => Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u)))
    by (apply Ccont_mul;
        [ apply Ccont_inv; [ apply Ccont_seg_id | exact Hchord_ne ]
        | apply Ccont_seg'_id ]).
  assert (HfaF : Ccont (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (arc Rr u)))
                                      (arc' Rr u))).
  { apply (Ccont_congr (fun u => Cmul (F (arc Rr u))
                                      (Cmul (Cinv (arc Rr u)) (arc' Rr u))));
      [ intro u; ring
      | apply Ccont_mul; [ apply HFc, Ccont_arc | apply arc_int_cont; exact HR ] ]. }
  assert (HfcF : Ccont (fun u => Cmul (Cmul (F (seg Pc Qc u)) (Cinv (seg Pc Qc u)))
                                      (seg' Pc Qc u))).
  { apply (Ccont_congr (fun u => Cmul (F (seg Pc Qc u))
                                      (Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u))));
      [ intro u; ring
      | apply Ccont_mul; [ apply HFc, Ccont_seg_id | exact HcC ] ]. }
  assert (HfaL : Ccont (fun u => Cmul (Klin (arc Rr u)) (arc' Rr u)))
    by (apply Ccont_mul; [ apply Klin_CcontC, Ccont_arc | apply Ccont_arc' ]).
  assert (HfcL : Ccont (fun u => Cmul (Klin (seg Pc Qc u)) (seg' Pc Qc u)))
    by (apply Ccont_mul; [ apply Klin_CcontC, Ccont_seg_id | apply Ccont_seg'_id ]).
  (* --- split the kernel on each piece --- *)
  assert (Hsuma : Ccont (fun u =>
    Cadd (Cmul (Cmul (F (arc Rr u)) (Cinv (arc Rr u))) (arc' Rr u))
         (Cmul (Klin (arc Rr u)) (arc' Rr u))))
    by (apply Ccont_add; assumption).
  assert (Hsumc : Ccont (fun u =>
    Cadd (Cmul (Cmul (F (seg Pc Qc u)) (Cinv (seg Pc Qc u))) (seg' Pc Qc u))
         (Cmul (Klin (seg Pc Qc u)) (seg' Pc Qc u))))
    by (apply Ccont_add; assumption).
  assert (Harc_split :
    pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (newman_kernel Rr z))
            HfaK (- alpha) alpha
    = Cadd (pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv z))
              HfaF (- alpha) alpha)
           (pathint (arc Rr) (arc' Rr) Klin HfaL (- alpha) alpha)).
  { unfold pathint.
    rewrite (Cintf_ext _ _ HfaK Hsuma (- alpha) alpha);
      [ | intro u; unfold newman_kernel, Klin; ring ].
    apply (Cintf_add _ _ HfaF HfaL Hsuma (- alpha) alpha); lra. }
  assert (Hchord_split :
    pathint (seg Pc Qc) (seg' Pc Qc) (fun z => Cmul (F z) (newman_kernel Rr z))
            HfcK 0 1
    = Cadd (pathint (seg Pc Qc) (seg' Pc Qc) (fun z => Cmul (F z) (Cinv z))
              HfcF 0 1)
           (pathint (seg Pc Qc) (seg' Pc Qc) Klin HfcL 0 1)).
  { unfold pathint.
    rewrite (Cintf_ext _ _ HfcK Hsumc 0 1);
      [ | intro u; unfold newman_kernel, Klin; ring ].
    apply (Cintf_add _ _ HfcF HfcL Hsumc 0 1); lra. }
  (* --- the 1/z half: the truncated Cauchy formula --- *)
  assert (HFz :
    Cadd (pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv z))
            HfaF (- alpha) alpha)
         (pathint (seg Pc Qc) (seg' Pc Qc) (fun z => Cmul (F z) (Cinv z))
            HfcF 0 1)
    = Cmul (F C0) (mkC 0 (2 * PI))).
  { destruct (Fholo C0 HU0) as [dF HdF].
    exact (trunc_cauchy_dom Rr alpha U F dF HR Halpha HUc HUo HU0 HarcU HchordU
             HdF Fptc (fun z HUz _ => Fholo z HUz) HcC HfaF HfcF). }
  (* --- the z/R^2 half: a primitive on U kills the loop --- *)
  assert (HH : forall z, U z -> is_Cderiv (PrimC Klin Klin_CcontC C0) z (Klin z))
    by (intros z HUz;
        exact (PrimC_deriv U HUc HUo Klin Klin_CcontC Klin_holo C0 HU0 z HUz)).
  assert (Iarc : pathint (arc Rr) (arc' Rr) Klin HfaL (- alpha) alpha
               = Cminus (PrimC Klin Klin_CcontC C0 (arc Rr alpha))
                        (PrimC Klin Klin_CcontC C0 (arc Rr (- alpha)))).
  { apply (pathint_FTC (PrimC Klin Klin_CcontC C0) Klin (arc Rr) (arc' Rr)
             HfaL (- alpha) alpha);
      [ lra | intros s Hs; apply HH, HarcU, Hs
      | intros s _; apply arc_Re_deriv | intros s _; apply arc_Im_deriv ]. }
  assert (Ichord : pathint (seg Pc Qc) (seg' Pc Qc) Klin HfcL 0 1
                 = Cminus (PrimC Klin Klin_CcontC C0 (seg Pc Qc 1))
                          (PrimC Klin Klin_CcontC C0 (seg Pc Qc 0))).
  { apply (pathint_FTC (PrimC Klin Klin_CcontC C0) Klin (seg Pc Qc) (seg' Pc Qc)
             HfcL 0 1);
      [ lra | intros s Hs; apply HH, HchordU, Hs
      | intros s _; apply chord_Re_deriv | intros s _; apply chord_Im_deriv ]. }
  assert (HKsum : Cadd (pathint (arc Rr) (arc' Rr) Klin HfaL (- alpha) alpha)
                       (pathint (seg Pc Qc) (seg' Pc Qc) Klin HfcL 0 1) = C0).
  { rewrite Iarc, Ichord, seg_at0, seg_at1.
    assert (Ha1 : arc Rr alpha = Pc) by reflexivity.
    assert (Ha2 : arc Rr (- alpha) = Qc) by (unfold Qc; apply arc_neg).
    rewrite Ha1, Ha2; ring. }
  (* --- assemble --- *)
  rewrite Harc_split, Hchord_split.
  transitivity (Cadd (Cadd (pathint (arc Rr) (arc' Rr)
                              (fun z => Cmul (F z) (Cinv z)) HfaF (- alpha) alpha)
                           (pathint (seg Pc Qc) (seg' Pc Qc)
                              (fun z => Cmul (F z) (Cinv z)) HfcF 0 1))
                     (Cadd (pathint (arc Rr) (arc' Rr) Klin HfaL (- alpha) alpha)
                           (pathint (seg Pc Qc) (seg' Pc Qc) Klin HfcL 0 1))).
  - ring.
  - rewrite HFz, HKsum; ring.
Qed.

End TruncKernel.

Print Assumptions trunc_kernel_dom.

(* ================================================================= *)
(*  END CTruncKernel.v  --  int_C F*(1/z + z/R^2) = 2*pi*i*F(0) on     *)
(*  Zagier's truncated contour, for F holomorphic on the region.       *)
(* ================================================================= *)
