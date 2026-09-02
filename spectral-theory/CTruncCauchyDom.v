(* ================================================================= *)
(*  CTruncCauchyDom.v  --  the truncated Cauchy formula, UNCONDITIONAL.*)
(*                                                                    *)
(*  CTruncCauchy.trunc_cauchy takes the removable quotient phi as a    *)
(*  parameter together with its whole exceptional-point interface.     *)
(*  This file discharges that interface once and for all by taking     *)
(*  phi := CRemovableExt.rphi F C0 dF, exactly as CRemovableExtDom.    *)
(*  cauchy_interior_dom does for the circle:                           *)
(*                                                                    *)
(*    F pointwise continuous everywhere + holomorphic on U off 0       *)
(*    + differentiable AT 0                                            *)
(*      ==>  int_arc F/z + int_chord F/z  =  F(0) * 2*pi*i             *)
(*                                                                    *)
(*  This is brick E5 of docs/pnt_endgame_plan.md, and the input shape  *)
(*  matches NewmanCutoff.gtrunc_CcontC exactly.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CIntegral2 CSegInt CPathIntegral CPrimConv CGoursatExcept
        CRemovableExt CRemovableExtDom PerronRemovable CTruncWind CTruncCauchy.
Open Scope R_scope.

(* rphi is holomorphic off w on ANY set where F is -- the disk in
   rphi_holo_off_dom is incidental, the proof uses it at one point only *)
Lemma rphi_holo_off_gen : forall (F : C -> C) (w dw : C) (U : C -> Prop),
  (forall z, U z -> z <> w -> exists d, is_Cderiv F z d) ->
  forall z, U z -> z <> w -> exists d, is_Cderiv (rphi F w dw) z d.
Proof.
  intros F w dw U Fholo z HUz Hz.
  destruct (Fholo z HUz Hz) as [dF HdF].
  assert (Hne : Cminus z w <> C0) by (apply minus_ne; exact Hz).
  eexists.
  apply (is_Cderiv_congr (rphi F w dw)
           (fun z' => Cmul (Cminus (F z') (F w)) (Cinv (Cminus z' w)))
           z _ (Cmod (Cminus z w))).
  - apply Cmod_pos_of_ne; exact Hne.
  - intros z' Hz'. apply rphi_off. intro E; subst z'.
    assert (Cmod (Cminus w z) = Cmod (Cminus z w))
      by (rewrite <- Cmod_opp; f_equal; ring). lra.
  - apply (Cderiv_div (fun z' => Cminus (F z') (F w)) (fun z' => Cminus z' w) z
             (Cminus dF C0) (Cminus C1 C0)).
    + apply (Cderiv_minus F (fun _ => F w) z dF C0); [ exact HdF | apply Cderiv_const ].
    + apply (Cderiv_minus (fun z' => z') (fun _ => w) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ].
    + exact Hne.
Qed.

Lemma Cminus_C0_r : forall z : C, Cminus z C0 = z.
Proof. intro z; apply Ceq; cbn; ring. Qed.

Theorem trunc_cauchy_dom :
  forall (Rr alpha : R) (U : C -> Prop) (F : C -> C) (dF : C),
  0 < Rr -> PI / 2 < alpha < PI ->
  Convex U -> Open U -> U C0 ->
  (forall s, - alpha <= s <= alpha -> U (arc Rr s)) ->
  (forall s, 0 <= s <= 1 ->
     U (seg (mkC (Rr * cos alpha) (Rr * sin alpha))
            (mkC (Rr * cos alpha) (- (Rr * sin alpha))) s)) ->
  is_Cderiv F C0 dF ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps) ->
  (forall z, U z -> z <> C0 -> exists d, is_Cderiv F z d) ->
  forall (HcC : Ccont (fun u =>
           Cmul (Cinv (seg (mkC (Rr * cos alpha) (Rr * sin alpha))
                           (mkC (Rr * cos alpha) (- (Rr * sin alpha))) u))
                (seg' (mkC (Rr * cos alpha) (Rr * sin alpha))
                      (mkC (Rr * cos alpha) (- (Rr * sin alpha))) u)))
         (HfaF : Ccont (fun u =>
           Cmul (Cmul (F (arc Rr u)) (Cinv (arc Rr u))) (arc' Rr u)))
         (HfcF : Ccont (fun u =>
           Cmul (Cmul (F (seg (mkC (Rr * cos alpha) (Rr * sin alpha))
                              (mkC (Rr * cos alpha) (- (Rr * sin alpha))) u))
                      (Cinv (seg (mkC (Rr * cos alpha) (Rr * sin alpha))
                                 (mkC (Rr * cos alpha) (- (Rr * sin alpha))) u)))
                (seg' (mkC (Rr * cos alpha) (Rr * sin alpha))
                      (mkC (Rr * cos alpha) (- (Rr * sin alpha))) u))),
  Cadd (pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv z)) HfaF (- alpha) alpha)
       (pathint (seg (mkC (Rr * cos alpha) (Rr * sin alpha))
                     (mkC (Rr * cos alpha) (- (Rr * sin alpha))))
                (seg' (mkC (Rr * cos alpha) (Rr * sin alpha))
                      (mkC (Rr * cos alpha) (- (Rr * sin alpha))))
                (fun z => Cmul (F z) (Cinv z)) HfcF 0 1)
  = Cmul (F C0) (mkC 0 (2 * PI)).
Proof.
  intros Rr alpha U F dF HR Halpha HUc HUo HU0 HarcU HchordU HdF Fptc Fholo
         HcC HfaF HfcF.
  assert (Hcos : cos alpha < 0) by (apply cos_neg_on_quad2; exact Halpha).
  assert (Harc_ne : forall s, arc Rr s <> C0).
  { intros s Hc. assert (HM : Cmod (arc Rr s) = Rr) by (apply Cmod_arc; lra).
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra. }
  assert (Hchord_ne : forall s,
    seg (mkC (Rr * cos alpha) (Rr * sin alpha))
        (mkC (Rr * cos alpha) (- (Rr * sin alpha))) s <> C0).
  { intros s Hc. apply (f_equal Re) in Hc. cbn in Hc. nra. }
  apply (trunc_cauchy Rr alpha HR Halpha U HUc HUo HU0 HarcU HchordU
           C0 HU0 F (rphi F C0 dF)).
  - exact (rphi_cc_dom F C0 dF HdF Fptc).
  - intro s. rewrite (rphi_off F C0 dF (arc Rr s) (Harc_ne s)), Cminus_C0_r.
    reflexivity.
  - intro s. rewrite (rphi_off F C0 dF _ (Hchord_ne s)), Cminus_C0_r. reflexivity.
  - exact (rphi_holo_off_gen F C0 dF U Fholo).
  - exact (rphi_bd F C0 dF HdF).
  - intros z Hz eps He. exact (rphi_ptcont_dom F C0 dF HdF Fptc z eps He).
  - exact HcC.
Qed.

Print Assumptions trunc_cauchy_dom.
