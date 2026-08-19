(* ================================================================= *)
(*  ZeroFreeMVP.v  —  Hadamard keystone, brick 3 (zero-free half):      *)
(*  the MEAN VALUE PROPERTY for ln|F| of an entire zero-free function.  *)
(*                                                                    *)
(*    zero_free_MVP : F entire, F' entire, F zero-free everywhere,      *)
(*    F'/F path-continuous, 0 < Rr ==>                                 *)
(*      RiemannInt (fun t => ln (Cmod (F (arc Rr t)))) 0 (2*PI)         *)
(*      = 2*PI * ln (Cmod (F C0)).                                     *)
(*                                                                    *)
(*  i.e. (1/2PI) INT_0^{2PI} ln|F(Rr e^{it})| dt = ln|F(0)|.  This is    *)
(*  the zeros-FREE half of Jensen's formula -- the other half          *)
(*  (JensenZeroFactor.jensen_zero_factor) handles the zero at radius a. *)
(*                                                                    *)
(*  Assembly (all pieces now proved):                                  *)
(*   * F = Cc.e^{G} with G entire = Log F   (brick 3 (a),               *)
(*     CLogFExpEntire.logF_exp_entire);                                *)
(*   * G path-continuous   (brick 3 (b1), CHoloCcontC.holo_CcontC);     *)
(*   * mean value of G:  M G Rr = M G 0 = 2PI.G(0)                      *)
(*     (CCauchyFormula.M_const + meanval0), whose arc-uniform-          *)
(*     continuity hypothesis is discharged by CUnifCont.arc_Fp_unif     *)
(*     from pointwise continuity of G' = F'/F;                         *)
(*   * take real parts (Re commutes with the contour integral,         *)
(*     CIntegral2.Re_Cintf) and use |F| = |Cc|.e^{Re G}                 *)
(*     (Cmod_mul + Cmod_Cexpf), so ln|F| = ln|Cc| + Re G; the constant  *)
(*     ln|Cc| cancels in ln|F(0)| = mean of ln|F|.                     *)
(*                                                                    *)
(*  Axiom-clean.  This closes the zero-free half of brick 3.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CexpfDeriv CSine EulerFormula CSegInt CIntegral2
        CPathIntegral CCauchyFormula CUnifCont CPrimitiveDisk
        CImproperIntegral CLogFExpEntire CHoloCcontC.
Open Scope R_scope.

Theorem zero_free_MVP : forall (F Fp : C -> C) (Rr : R),
  (forall z, is_Cderiv F z (Fp z)) ->
  (forall z, exists d, is_Cderiv Fp z d) ->
  (forall z, F z <> C0) ->
  CcontC (fun w => Cmul (Fp w) (Cinv (F w))) ->
  0 < Rr ->
  forall (pr : Riemann_integrable (fun t => ln (Cmod (F (arc Rr t)))) 0 (2 * PI)),
  RiemannInt pr = 2 * PI * ln (Cmod (F C0)).
Proof.
  intros F Fp Rr HFhol HFphol HFne0 HcontG HRr pr.
  set (g := fun w : C => Cmul (Fp w) (Cinv (F w))).
  destruct (logF_exp_entire F Fp HFhol HFphol HFne0 HcontG) as [G [Cc [HGderiv HFexp]]].
  (* G and g are (pointwise) holomorphic *)
  assert (HGex : forall z, exists d, is_Cderiv G z d)
    by (intro z; exists (g z); apply HGderiv).
  assert (HGc : CcontC G) by (apply holo_CcontC; exact HGex).
  assert (Hghol : forall z, exists d, is_Cderiv g z d).
  { intro z. destruct (HFphol z) as [dFp HdFp]. unfold g. eexists.
    apply Cderiv_div; [ exact HdFp | apply HFhol | apply HFne0 ]. }
  assert (Hpcont : forall w eps, 0 < eps -> exists del, 0 < del /\
             forall w', Cmod (Cminus w' w) < del -> Cmod (Cminus (g w') (g w)) < eps).
  { intros w eps Heps. destruct (Hghol w) as [dg Hdg].
    exact (Cderiv_cont_w g w dg Hdg eps Heps). }
  (* mean value of G:  M G Rr = M G 0 = 2 PI . G(0) *)
  assert (HMconst : M G HGc Rr = M G HGc 0)
    by (apply (M_const G g HGc HcontG HGderiv
                 (fun r0 eps Heps => arc_Fp_unif g Hpcont r0 eps Heps)); exact HRr).
  assert (HMval : M G HGc Rr = Cmul (RtoC (2 * PI)) (G C0))
    by (rewrite HMconst; apply meanval0).
  (* Re of a real-scalar times a complex *)
  assert (HRescal : forall a w, Re (Cmul (RtoC a) w) = a * Re w)
    by (intros a [wr wi]; unfold Cmul, RtoC, Re; simpl; ring).
  (* RiemannInt of Re(G o arc Rr) = 2 PI . Re(G 0) *)
  pose (prReG := cont_RI _ (proj1 (HGc (arc Rr) (Ccont_arc Rr))) 0 (2 * PI)).
  assert (HI : RiemannInt prReG = 2 * PI * Re (G C0)).
  { assert (Hre : Re (M G HGc Rr) = RiemannInt prReG).
    { change (M G HGc Rr)
        with (Cintf (fun t => G (arc Rr t)) (HGc (arc Rr) (Ccont_arc Rr)) 0 (2 * PI)).
      apply Re_Cintf. }
    rewrite <- Hre, HMval, HRescal. ring. }
  (* Cc <> 0, so ln (Cmod Cc) is legitimate *)
  assert (HCcne : Cc <> C0).
  { intro Hcc. apply (HFne0 C0). rewrite (HFexp C0), Hcc. ring. }
  assert (HCcpos : 0 < Cmod Cc).
  { destruct (Cmod_nonneg Cc) as [Hlt | Heq0]; [ exact Hlt | ].
    exfalso. apply HCcne. apply (proj1 (Cmod0 Cc)). symmetry. exact Heq0. }
  set (K := ln (Cmod Cc)).
  (* pointwise:  ln|F(arc Rr t)| = K + Re(G(arc Rr t)) *)
  assert (Hpt : forall t, ln (Cmod (F (arc Rr t))) = K + Re (G (arc Rr t))).
  { intro t. rewrite (HFexp (arc Rr t)), Cmod_mul, Cmod_Cexpf.
    rewrite (ln_mult (Cmod Cc) (exp (Re (G (arc Rr t)))) HCcpos (exp_pos _)).
    unfold K. rewrite ln_exp. reflexivity. }
  assert (Hpt0 : ln (Cmod (F C0)) = K + Re (G C0)).
  { rewrite (HFexp C0), Cmod_mul, Cmod_Cexpf.
    rewrite (ln_mult (Cmod Cc) (exp (Re (G C0))) HCcpos (exp_pos _)).
    unfold K. rewrite ln_exp. reflexivity. }
  (* integrability of the split *)
  assert (prK : Riemann_integrable (fct_cte K) 0 (2 * PI)) by apply RiemannInt_P14.
  assert (prsum : Riemann_integrable
             (fun t => fct_cte K t + 1 * Re (G (arc Rr t))) 0 (2 * PI))
    by (apply RiemannInt_P10; [ exact prK | exact prReG ]).
  assert (Hab : (0:R) <= 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hext : forall x, 0 < x < 2 * PI ->
             ln (Cmod (F (arc Rr x))) = fct_cte K x + 1 * Re (G (arc Rr x)))
    by (intros x _; rewrite Hpt; unfold fct_cte; ring).
  assert (Hsplit : RiemannInt pr = RiemannInt prsum)
    by (apply RiemannInt_P18; [ exact Hab | exact Hext ]).
  assert (H13 : RiemannInt prsum = RiemannInt prK + 1 * RiemannInt prReG)
    by apply RiemannInt_P13.
  assert (H15 : RiemannInt prK = K * (2 * PI - 0)) by apply RiemannInt_P15.
  rewrite Hsplit, H13, H15, HI, Hpt0. ring.
Qed.

Print Assumptions zero_free_MVP.
