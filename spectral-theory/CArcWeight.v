(* ================================================================= *)
(*  CArcWeight.v  —  the circle weight  wgt Rr t = (arc Rr t)^{-2}.     *)
(*                                                                    *)
(*  Borel-Caratheodory needs the n = 2 Cauchy coefficient, which on     *)
(*  the circle |z| = Rr is an integral against e^{-2it}.  Rather than   *)
(*  introduce Cexpf on the circle, everything here is phrased with      *)
(*      wgt Rr t := Cinv (Cpow (arc Rr t) 2),                          *)
(*  which IS that weight up to the factor R^{-2} and stays inside the   *)
(*  existing arc / Cpow / Cinv / Cconj algebra.                        *)
(*                                                                    *)
(*    arc_deriv_i  : arc' Rr t = Ci . arc Rr t   (the circle's         *)
(*                   tangent is i times its position)                  *)
(*    kernel3_wgt  : the n = 3 Cauchy kernel at the centre collapses,   *)
(*                   G(arc)/(arc-0)^3 . arc'  =  Ci . G(arc) . wgt,     *)
(*                   which is what turns the tower's Psi 3 C0 into a    *)
(*                   plain weighted integral.                          *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CDeriv CIntegral2 CSegInt CPathIntegral
        RootsOfUnity CTaylor CWindingOffCenter CCauchyAnalytic
        CImproperIntegral CIntfLinear JensenOrthogonality.
Open Scope R_scope.

Definition wgt (Rr : R) (t : R) : C := Cinv (Cpow (arc Rr t) 2).

Lemma arc_ne0 : forall Rr t, 0 < Rr -> arc Rr t <> C0.
Proof.
  intros Rr t HR Hc.
  assert (Hm : Cmod (arc Rr t) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hm. lra.
Qed.

(* the tangent to the circle is i times the position *)
Lemma arc_deriv_i : forall Rr t, arc' Rr t = Cmul Ci (arc Rr t).
Proof.
  intros Rr t. unfold arc, arc', Ci. apply Ceq; cbn [Re Im Cmul]; ring.
Qed.

Lemma Cmod_wgt : forall Rr t, 0 < Rr -> Cmod (wgt Rr t) = / Rr ^ 2.
Proof.
  intros Rr t HR. unfold wgt.
  assert (HA : arc Rr t <> C0) by (apply arc_ne0; exact HR).
  assert (Hp : Cpow (arc Rr t) 2 <> C0)
    by (cbn [Cpow]; apply Cmul_ne0; [ exact HA | apply Cmul_ne0;
        [ exact HA | apply C1_neq_C0 ] ]).
  rewrite (Cmod_inv _ Hp).
  f_equal. cbn [Cpow]. rewrite !Cmod_mul, Cmod_C1, (Cmod_arc Rr t ltac:(lra)).
  ring.
Qed.

(* THE KERNEL COLLAPSE: the n = 3 Cauchy kernel at the centre *)
Lemma kernel3_wgt : forall (G : C -> C) (Rr t : R), 0 < Rr ->
  Cmul (Cmul (G (arc Rr t)) (Cinv (Cpow (Cminus (arc Rr t) C0) 3))) (arc' Rr t)
  = Cmul Ci (Cmul (G (arc Rr t)) (wgt Rr t)).
Proof.
  intros G Rr t HR.
  assert (HA : arc Rr t <> C0) by (apply arc_ne0; exact HR).
  unfold wgt.
  replace (Cminus (arc Rr t) C0) with (arc Rr t) by ring.
  rewrite (arc_deriv_i Rr t).
  cbn [Cpow]. field. exact HA.
Qed.

(* the continuity side-condition the weighted circle integral needs,
   so callers of the coefficient identity do not have to build it *)
Lemma Ccont_wgt : forall Rr, 0 < Rr -> Ccont (wgt Rr).
Proof.
  intros Rr HR. unfold wgt.
  apply Ccont_inv.
  - apply Cpow_cont. apply Ccont_arc.
  - intro u. apply Cpow_ne0. apply arc_ne0; exact HR.
Qed.

Lemma Ccont_G_wgt : forall (G : C -> C) (Rr : R), 0 < Rr -> CcontC G ->
  Ccont (fun t => Cmul (G (arc Rr t)) (wgt Rr t)).
Proof.
  intros G Rr HR HGc. apply Ccont_mul.
  - exact (HGc (arc Rr) (Ccont_arc Rr)).
  - apply Ccont_wgt; exact HR.
Qed.

(* ----------------------------------------------------------------- *)
(*  the weight integrates to zero over a full turn                    *)
(*                                                                    *)
(*  wgt is the n = 2 Fourier mode in disguise: (arc Rr t)^2 has        *)
(*  argument 2t, so Re wgt = cos 2t / Rr^2 and Im wgt = - sin 2t/Rr^2. *)
(*  Both integrate to 0 over [0, 2PI] -- JensenOrthogonality, no       *)
(*  Cauchy theorem needed.  This is what lets an arbitrary REAL        *)
(*  constant be subtracted from the integrand later (Step 5): the      *)
(*  subtraction changes nothing.                                       *)
(* ----------------------------------------------------------------- *)
Lemma arc_sq : forall Rr t,
  Cpow (arc Rr t) 2 = mkC (Rr ^ 2 * cos (2 * t)) (Rr ^ 2 * sin (2 * t)).
Proof.
  intros Rr t. apply Ceq;
    cbn [Re Im Cmul Cpow C1 arc]; rewrite ?cos_2a, ?sin_2a; ring.
Qed.

Lemma Cnorm2_arc_sq : forall Rr t,
  Cnorm2 (mkC (Rr ^ 2 * cos (2 * t)) (Rr ^ 2 * sin (2 * t))) = Rr ^ 4.
Proof.
  intros Rr t. unfold Cnorm2; cbn [Re Im].
  pose proof (sin2_cos2 (2 * t)) as Hpy. unfold Rsqr in Hpy. nra.
Qed.

Lemma Re_wgt : forall Rr t, 0 < Rr -> Re (wgt Rr t) = / Rr ^ 2 * cos (2 * t).
Proof.
  intros Rr t HR.
  assert (HRne : Rr <> 0) by (apply Rgt_not_eq; exact HR).
  unfold wgt. rewrite arc_sq. unfold Cinv. cbn [Re Im].
  rewrite Cnorm2_arc_sq. field. exact HRne.
Qed.

Lemma Im_wgt : forall Rr t, 0 < Rr -> Im (wgt Rr t) = - / Rr ^ 2 * sin (2 * t).
Proof.
  intros Rr t HR.
  assert (HRne : Rr <> 0) by (apply Rgt_not_eq; exact HR).
  unfold wgt. rewrite arc_sq. unfold Cinv. cbn [Re Im].
  rewrite Cnorm2_arc_sq. field. exact HRne.
Qed.

Theorem Cintf_wgt_zero : forall Rr (Hw : Ccont (wgt Rr)), 0 < Rr ->
  Cintf (wgt Rr) Hw 0 (2 * PI) = C0.
Proof.
  intros Rr Hw HR.
  assert (HI2 : INR 2 = 2) by (simpl; lra).
  apply Ceq; rewrite ?Re_Cintf, ?Im_Cintf; cbn [Re Im C0].
  - assert (Heq : (fun t => Re (wgt Rr t))
                = (fun t => / Rr ^ 2 * (fun u => cos (INR 2 * u)) t))
      by (apply functional_extensionality; intro t;
          rewrite (Re_wgt Rr t HR), HI2; reflexivity).
    assert (prx : Riemann_integrable
                    (fun t => / Rr ^ 2 * (fun u => cos (INR 2 * u)) t) 0 (2 * PI))
      by (rewrite <- Heq; exact (cont_RI _ (proj1 Hw) 0 (2 * PI))).
    rewrite (RiemannInt_ext_fun _ _ 0 (2 * PI) (cont_RI _ (proj1 Hw) 0 (2 * PI)) prx Heq).
    rewrite (RInt_scal (/ Rr ^ 2) _ 0 (2 * PI) (cos_scaled_int (INR 2) 0 (2 * PI)) prx).
    rewrite (cos_int_2PI 2 ltac:(lia)). ring.
  - assert (Heq : (fun t => Im (wgt Rr t))
                = (fun t => - / Rr ^ 2 * (fun u => sin (INR 2 * u)) t))
      by (apply functional_extensionality; intro t;
          rewrite (Im_wgt Rr t HR), HI2; reflexivity).
    assert (prx : Riemann_integrable
                    (fun t => - / Rr ^ 2 * (fun u => sin (INR 2 * u)) t) 0 (2 * PI))
      by (rewrite <- Heq; exact (cont_RI _ (proj2 Hw) 0 (2 * PI))).
    rewrite (RiemannInt_ext_fun _ _ 0 (2 * PI) (cont_RI _ (proj2 Hw) 0 (2 * PI)) prx Heq).
    rewrite (RInt_scal (- / Rr ^ 2) _ 0 (2 * PI) (sin_scaled_int (INR 2) 0 (2 * PI)) prx).
    rewrite (sin_int_2PI 2 ltac:(lia)). ring.
Qed.

Print Assumptions kernel3_wgt.
Print Assumptions Ccont_G_wgt.
Print Assumptions Cintf_wgt_zero.
