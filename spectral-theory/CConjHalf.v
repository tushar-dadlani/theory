(* ================================================================= *)
(*  CConjHalf.v  —  Borel-Caratheodory, Step 4:                        *)
(*  the CONJUGATE HALF of the weighted circle integral vanishes.       *)
(*                                                                    *)
(*    conj_half_zero :  INT_0^{2PI} conj(G(arc Rr t)) . wgt Rr t dt = 0 *)
(*                                                                    *)
(*  Step 3 wrote G''(0) as A/PI with A = INT G(arc) . wgt.  Writing     *)
(*  2 Re G = G + conj G turns A into an integral of the REAL quantity   *)
(*  Re G -- but only because the conj half contributes nothing.  That   *)
(*  is this file.                                                      *)
(*                                                                    *)
(*  WHY IT VANISHES.  conj (wgt) is (1/Rr^4) . (arc)^2 -- conjugating   *)
(*  the weight turns the n = -2 mode into the n = +2 mode.  So the      *)
(*  conjugate half is the CAUCHY integral of the entire function        *)
(*  z |-> G z . z round a closed loop, which is 0.                     *)
(*                                                                    *)
(*  Concretely: CConjIntegral.Cintf_conj_weighted_zero moves conj       *)
(*  outside the integral, Cconj_involutive puts the weight back, and    *)
(*  CPrimConv.pathint_loop_conv on U := fun _ => True kills the loop.   *)
(*  arc_deriv_i is what identifies the path integral with the weighted  *)
(*  one: (G.arc).(i.arc) = i . G . arc^2.  Axiom-clean.                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Classical.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral RootsOfUnity CTaylor CPrimConv CImproperIntegral
        CIntfLinear CConjIntegral CArcWeight COrderOne CTruncCauchy
        CCauchyAnalytic.
Open Scope R_scope.

Lemma Ci_ne0 : Ci <> C0.
Proof. intro H. apply (f_equal Im) in H. cbn in H. lra. Qed.

Lemma Open_all : Open (fun _ : C => True).
Proof. intros z _. exists 1. split; [ lra | intros; exact I ]. Qed.

Section ConjHalf.

Variable G Gp : C -> C.
Variable Rr : R.
Hypothesis HR : 0 < Rr.
Hypothesis HGc : CcontC G.
Hypothesis HG : forall z, is_Cderiv G z (Gp z).

(* conjugating the weight flips the mode: conj (arc^{-2}) = arc^2 / Rr^4 *)
Lemma conj_wgt : forall t,
  Cconj (wgt Rr t) = Cmul (RtoC (/ Rr ^ 4)) (Cpow (arc Rr t) 2).
Proof.
  intro t.
  assert (HRne : Rr <> 0) by (apply Rgt_not_eq; exact HR).
  apply Ceq.
  - cbn [Re Cconj]. rewrite (Re_wgt Rr t HR), arc_sq.
    cbn [Re Im Cmul RtoC]. field. exact HRne.
  - cbn [Im Cconj]. rewrite (Im_wgt Rr t HR), arc_sq.
    cbn [Re Im Cmul RtoC]. field. exact HRne.
Qed.

(* ---- Cauchy: the loop integral of the entire z |-> G z . z is 0 ---- *)
Lemma Gz_CcontC : CcontC (fun z => Cmul (G z) z).
Proof.
  intros g Hg. apply Ccont_mul; [ exact (HGc g Hg) | exact Hg ].
Qed.

Lemma Gz_holo : forall z, (fun _ : C => True) z -> exists d, is_Cderiv (fun w => Cmul (G w) w) z d.
Proof.
  intros z _. eexists.
  apply (Cderiv_mul G (fun w => w) z (Gp z) C1); [ apply HG | apply Cderiv_id ].
Qed.

Lemma arc_closed : arc Rr 0 = arc Rr (2 * PI).
Proof.
  unfold arc. apply Ceq; cbn [Re Im].
  - rewrite cos_0, cos_2PI. reflexivity.
  - rewrite sin_0, sin_2PI. reflexivity.
Qed.

Theorem Cintf_G_arcsq_zero :
  forall (Hc : Ccont (fun t => Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2))),
  Cintf (fun t => Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2)) Hc 0 (2 * PI) = C0.
Proof.
  intro Hc.
  pose proof PI_RGT_0 as HPI.
  assert (Hscal : Ccont (fun t => Cmul Ci (Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2))))
    by (apply Ccont_scal; exact Hc).
  (* the path integral of G z . z round the circle *)
  assert (Hpath : Ccont (fun u => Cmul ((fun z => Cmul (G z) z) (arc Rr u)) (arc' Rr u))).
  { apply Ccont_mul.
    - apply Ccont_mul; [ exact (HGc (arc Rr) (Ccont_arc Rr)) | apply Ccont_arc ].
    - apply Ccont_arc'. }
  assert (Hloop : pathint (arc Rr) (arc' Rr) (fun z => Cmul (G z) z) Hpath 0 (2 * PI) = C0).
  { apply (pathint_loop_conv (fun _ : C => True) Convex_all Open_all
             (fun z => Cmul (G z) z) Gz_CcontC Gz_holo C0 I).
    - lra.
    - apply arc_closed.
    - intros s _; exact I.
    - intros s _. apply arc_Re_deriv.
    - intros s _. apply arc_Im_deriv. }
  (* and that path integral is Ci times ours *)
  assert (Heq : pathint (arc Rr) (arc' Rr) (fun z => Cmul (G z) z) Hpath 0 (2 * PI)
                = Cmul Ci (Cintf (fun t => Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2)) Hc 0 (2 * PI))).
  { unfold pathint.
    rewrite <- (Cintf_scal Ci _ Hc Hscal 0 (2 * PI)).
    apply Cintf_ext. intro t. rewrite (arc_deriv_i Rr t). cbn [Cpow]. ring. }
  rewrite Heq in Hloop.
  destruct (classic (Cintf (fun t => Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2)) Hc 0 (2 * PI) = C0))
    as [Hz | Hnz]; [ exact Hz | exfalso ].
  exact (Cmul_ne0 Ci _ Ci_ne0 Hnz Hloop).
Qed.

(* ================================================================= *)
(*  STEP 4                                                             *)
(* ================================================================= *)
Theorem conj_half_zero :
  forall (Hcj : Ccont (fun t => Cmul (Cconj (G (arc Rr t))) (wgt Rr t))),
  Cintf (fun t => Cmul (Cconj (G (arc Rr t))) (wgt Rr t)) Hcj 0 (2 * PI) = C0.
Proof.
  intro Hcj.
  assert (HRne : Rr <> 0) by (apply Rgt_not_eq; exact HR).
  assert (Harc2 : Ccont (fun t => Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2))).
  { apply Ccont_mul; [ exact (HGc (arc Rr) (Ccont_arc Rr)) | ].
    apply Cpow_cont. apply Ccont_arc. }
  (* the "v" of Cintf_conj_weighted is conj (wgt) *)
  assert (Hgv : Ccont (fun t => Cmul (G (arc Rr t)) (Cconj (wgt Rr t)))).
  { apply Ccont_mul; [ exact (HGc (arc Rr) (Ccont_arc Rr)) | ].
    apply Ccont_conj. apply Ccont_wgt; exact HR. }
  assert (Hcgv : Ccont (fun t => Cmul (Cconj (G (arc Rr t))) (Cconj (Cconj (wgt Rr t))))).
  { apply Ccont_mul.
    - apply Ccont_conj. exact (HGc (arc Rr) (Ccont_arc Rr)).
    - apply Ccont_conj. apply Ccont_conj. apply Ccont_wgt; exact HR. }
  (* the un-conjugated half is Cauchy's, hence zero *)
  assert (Hzero : Cintf (fun t => Cmul (G (arc Rr t)) (Cconj (wgt Rr t))) Hgv 0 (2 * PI) = C0).
  { assert (Hscal : Ccont (fun t => Cmul (RtoC (/ Rr ^ 4))
                             (Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2))))
      by (apply Ccont_scal; exact Harc2).
    assert (Hpt : forall t, Cmul (G (arc Rr t)) (Cconj (wgt Rr t))
                          = Cmul (RtoC (/ Rr ^ 4))
                                 (Cmul (G (arc Rr t)) (Cpow (arc Rr t) 2)))
      by (intro t; rewrite (conj_wgt t); ring).
    rewrite (Cintf_ext _ _ Hgv Hscal 0 (2 * PI) Hpt).
    rewrite (Cintf_scal (RtoC (/ Rr ^ 4)) _ Harc2 Hscal 0 (2 * PI)).
    rewrite (Cintf_G_arcsq_zero Harc2). apply Ceq; simpl; ring. }
  pose proof (Cintf_conj_weighted_zero (fun t => G (arc Rr t)) (fun t => Cconj (wgt Rr t))
                Hgv Hcgv 0 (2 * PI) Hzero) as Hconj.
  rewrite <- Hconj. apply Cintf_ext. intro t.
  rewrite (Cconj_involutive (wgt Rr t)). reflexivity.
Qed.

End ConjHalf.

Print Assumptions conj_half_zero.
