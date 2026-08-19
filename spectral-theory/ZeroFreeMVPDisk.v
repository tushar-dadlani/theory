(* ================================================================= *)
(*  ZeroFreeMVPDisk.v  —  disk-cofactor bridge, THE CLOSE:              *)
(*  the zero-free mean value property on a DISK.                        *)
(*                                                                    *)
(*    zero_free_MVP_disk : F holomorphic and zero-free on a disk        *)
(*    Cmod z < R2 (F' also holomorphic there), 0 < r < R2 ==>           *)
(*      RiemannInt (fun t => ln (Cmod (F (arc r t)))) 0 (2 PI)          *)
(*      = 2 PI . ln (Cmod (F C0)).                                     *)
(*                                                                    *)
(*  This is exactly the cofactor bridge needed for n(r)=O(r): the       *)
(*  cofactor G_R = xi/P_R is zero-free only on the disk, not entire.    *)
(*  Assembled from every piece of the bridge:                          *)
(*   * gcut (CGcutCont): a globally-continuous stand-in for g = F'/F;   *)
(*   * disk log G = seg_int(gcut) C0, holomorphic on the inner disk     *)
(*     (PrimE_deriv) and CcontC (seg_int_endpoint_cont, the LINCHPIN);  *)
(*   * F = Cc.e^G on the inner disk (Cderiv0_const, as in logF_exp);    *)
(*   * disk mean value (CMeanValueDisk.M_const_disk / meanval0_disk),   *)
(*     Re-part + ln bookkeeping (as in ZeroFreeMVP).                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CexpfDeriv CSine EulerFormula CSegInt CIntegral2 CImproperIntegral
        CPathIntegral CGoursatExcept CPrimConv CPrimitiveDisk CDerivConst
        CUnifCont CMeanValueDisk CCutoff CGcutCont CSegIntCont ChebyshevPrime.
Open Scope R_scope.

Theorem zero_free_MVP_disk : forall (F Fp : C -> C) (R2 r : R),
  0 < r -> r < R2 ->
  (forall z, Cmod z < R2 -> is_Cderiv F z (Fp z)) ->
  (forall z, Cmod z < R2 -> exists d, is_Cderiv Fp z d) ->
  (forall z, Cmod z < R2 -> F z <> C0) ->
  forall (pr : Riemann_integrable (fun t => ln (Cmod (F (arc r t)))) 0 (2 * PI)),
  RiemannInt pr = 2 * PI * ln (Cmod (F C0)).
Proof.
  intros F Fp R2 r Hr HrR2 HFhol HFphol HFne0 pr.
  set (g := fun w : C => Cmul (Fp w) (Cinv (F w))).
  set (r1 := (r + R2) / 2). set (rc := (r1 + R2) / 2).
  assert (Hr1 : 0 < r1) by (unfold r1; lra).
  assert (Hrr1 : r < r1) by (unfold r1; lra).
  assert (Hr1c : r1 < rc) by (unfold rc, r1; lra).
  assert (HcR2 : rc < R2) by (unfold rc, r1; lra).
  (* g holomorphic on disk R2 *)
  assert (Hghol : forall z, Cmod z < R2 -> exists d, is_Cderiv g z d).
  { intros z Hz. destruct (HFphol z Hz) as [dFp HdFp]. unfold g. eexists.
    apply Cderiv_div; [ exact HdFp | apply HFhol; exact Hz | apply HFne0; exact Hz ]. }
  (* the globally-continuous cutoff *)
  set (gc := gcut g r1 rc).
  assert (Hgcpc : forall z eps, 0 < eps -> exists del, 0 < del /\
             forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (gc w) (gc z)) < eps)
    by (intros z eps He; apply (gcut_cmod_cont g r1 rc R2 Hr1c HcR2 Hghol z eps He)).
  assert (Hgcc : CcontC gc) by (apply Cmodcont_CcontC; exact Hgcpc).
  (* the disk logarithm G = seg_int gc C0 = PrimE gc Hgcc C0 *)
  set (G := PrimE gc Hgcc C0).
  assert (HdiskC0 : disk r1 C0)
    by (unfold disk; assert (Cmod C0 = 0) as H0 by (apply (proj2 (Cmod0 C0)); reflexivity);
        rewrite H0; lra).
  assert (HGder : forall z, disk r1 z -> is_Cderiv G z (gc z)).
  { apply (PrimE_deriv (disk r1) (disk_convex r1) (disk_open r1) gc Hgcc C0 HdiskC0).
    - intros z' Hz' _. apply (gcut_holo g r1 rc R2 Hr1c HcR2 Hghol); exact Hz'.
    - destruct (gcut_holo g r1 rc R2 Hr1c HcR2 Hghol C0 HdiskC0) as [d0 Hd0].
      destruct (Cderiv_cont_w gc C0 d0 Hd0 1 Rlt_0_1) as [eta [Heta Hb0]].
      exists (Cmod (gc C0) + 1), eta. split; [ exact Heta | ]. intros w Hw.
      apply Rle_trans with (Cmod (gc C0) + Cmod (Cminus (gc w) (gc C0))).
      + pose proof (Cmod_triangle (gc C0) (Cminus (gc w) (gc C0))) as HT.
        replace (Cadd (gc C0) (Cminus (gc w) (gc C0))) with (gc w) in HT by ring. exact HT.
      + specialize (Hb0 w Hw). lra.
    - intros z' _ eps Heps. apply (Hgcpc z' eps Heps).
    - exact HdiskC0. }
  (* on the inner disk, gc = g *)
  assert (Hgcg : forall z, disk r1 z -> gc z = g z)
    by (intros z Hz; apply (gcut_one g r1 rc Hr1c z); exact Hz).
  (* G is path-continuous (the LINCHPIN) *)
  assert (HGcc : CcontC G) by (apply (seg_int_endpoint_cont gc Hgcc C0); exact Hgcpc).
  (* F = Cc . e^G on the inner disk (as in logF_exp) *)
  set (Hexp := fun w : C => Cmul (F w) (Cexpf (Copp (G w)))).
  assert (Hexp_deriv : forall z, disk r1 z -> is_Cderiv Hexp z C0).
  { intros z Hz.
    assert (HzR2 : Cmod z < R2) by (unfold disk in Hz; lra).
    assert (HGz : is_Cderiv G z (g z)) by (rewrite <- (Hgcg z Hz); apply HGder; exact Hz).
    assert (Hexpder : is_Cderiv (fun w => Cexpf (Copp (G w))) z
                        (Cmul (Cexpf (Copp (G z))) (Copp (g z))))
      by (apply (Cexpf_comp_deriv (fun w => Copp (G w)) z (Copp (g z)));
          apply Cderiv_opp; exact HGz).
    pose proof (Cderiv_mul F (fun w => Cexpf (Copp (G w))) z (Fp z)
                  (Cmul (Cexpf (Copp (G z))) (Copp (g z)))
                  (HFhol z HzR2) Hexpder) as Hprod.
    cbv beta in Hprod.
    assert (HFg : Cmul (F z) (g z) = Fp z).
    { unfold g.
      assert (HinvF : Cmul (F z) (Cinv (F z)) = C1)
        by (rewrite <- (Cinv_l (F z) (HFne0 z HzR2)); ring).
      transitivity (Cmul (Fp z) (Cmul (F z) (Cinv (F z)))); [ ring | ].
      rewrite HinvF; ring. }
    assert (Hgcontrib : Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Copp (g z)))
                        = Copp (Cmul (Fp z) (Cexpf (Copp (G z))))).
    { transitivity (Cmul (Cexpf (Copp (G z))) (Copp (Cmul (F z) (g z)))); [ ring | ].
      rewrite HFg. ring. }
    replace (Cadd (Cmul (Fp z) (Cexpf (Copp (G z))))
                  (Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Copp (g z)))))
       with C0 in Hprod by (rewrite Hgcontrib; ring).
    exact Hprod. }
  set (Cc := Cmul (F C0) (Cexpf (Copp (G C0)))).
  assert (HFexp : forall z, disk r1 z -> F z = Cmul Cc (Cexpf (G z))).
  { intros z Hz.
    assert (Hc : Cmul (F z) (Cexpf (Copp (G z))) = Cmul (F C0) (Cexpf (Copp (G C0))))
      by exact (Cderiv0_const (disk r1) (disk_convex r1) Hexp Hexp_deriv z C0 Hz HdiskC0).
    unfold Cc. rewrite <- Hc.
    replace (Cmul (Cmul (F z) (Cexpf (Copp (G z)))) (Cexpf (G z)))
       with (Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Cexpf (G z)))) by ring.
    rewrite <- Cexpf_add. replace (Cadd (Copp (G z)) (G z)) with C0 by ring.
    rewrite Cexpf_C0. ring. }
  (* mean value of G on the inner disk *)
  assert (Hpcont' : forall w eps, 0 < eps -> exists del, 0 < del /\
             forall w', Cmod (Cminus w' w) < del -> Cmod (Cminus (gc w') (gc w)) < eps)
    by (intros w eps He; apply (Hgcpc w eps He)).
  assert (HMconst : M G HGcc r = M G HGcc 0).
  { apply (M_const_disk r1 G gc HGcc Hgcc HGder
             (fun r0 eps He => arc_Fp_unif gc Hpcont' r0 eps He) r Hr Hrr1). }
  assert (HMval : M G HGcc r = Cmul (RtoC (2 * PI)) (G C0))
    by (rewrite HMconst; apply meanval0_disk).
  assert (HRescal : forall a w, Re (Cmul (RtoC a) w) = a * Re w)
    by (intros a [wr wi]; unfold Cmul, RtoC, Re; simpl; ring).
  pose (prReG := cont_RI _ (proj1 (HGcc (arc r) (Ccont_arc r))) 0 (2 * PI)).
  assert (HI : RiemannInt prReG = 2 * PI * Re (G C0)).
  { assert (Hre : Re (M G HGcc r) = RiemannInt prReG).
    { change (M G HGcc r)
        with (Cintf (fun t => G (arc r t)) (HGcc (arc r) (Ccont_arc r)) 0 (2 * PI)).
      apply Re_Cintf. }
    rewrite <- Hre, HMval, HRescal. ring. }
  (* Cc <> 0 *)
  assert (HFne0d : F C0 <> C0) by (apply HFne0; unfold disk in HdiskC0; lra).
  assert (HCcne : Cc <> C0) by (unfold Cc; intro Hcc; apply HFne0d;
    apply (proj1 (Cmod0 (F C0))); rewrite (HFexp C0 HdiskC0); unfold Cc;
    rewrite Hcc; rewrite Cmod_mul; rewrite (proj2 (Cmod0 C0) eq_refl); ring).
  assert (HCcpos : 0 < Cmod Cc).
  { destruct (Cmod_nonneg Cc) as [Hlt | Heq0]; [ exact Hlt | ].
    exfalso. apply HCcne. apply (proj1 (Cmod0 Cc)). symmetry. exact Heq0. }
  set (K := ln (Cmod Cc)).
  assert (Harc : forall t, disk r1 (arc r t))
    by (intro t; unfold disk; rewrite Cmod_arc; lra).
  assert (Hpt : forall t, ln (Cmod (F (arc r t))) = K + Re (G (arc r t))).
  { intro t. rewrite (HFexp (arc r t) (Harc t)), Cmod_mul, Cmod_Cexpf.
    rewrite (ln_mult (Cmod Cc) (exp (Re (G (arc r t)))) HCcpos (exp_pos _)).
    unfold K. rewrite ln_exp. reflexivity. }
  assert (Hpt0 : ln (Cmod (F C0)) = K + Re (G C0)).
  { rewrite (HFexp C0 HdiskC0), Cmod_mul, Cmod_Cexpf.
    rewrite (ln_mult (Cmod Cc) (exp (Re (G C0))) HCcpos (exp_pos _)).
    unfold K. rewrite ln_exp. reflexivity. }
  assert (prK : Riemann_integrable (fct_cte K) 0 (2 * PI)) by apply RiemannInt_P14.
  assert (prsum : Riemann_integrable
             (fun t => fct_cte K t + 1 * Re (G (arc r t))) 0 (2 * PI))
    by (apply RiemannInt_P10; [ exact prK | exact prReG ]).
  assert (Hab : (0:R) <= 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hext : forall x, 0 < x < 2 * PI ->
             ln (Cmod (F (arc r x))) = fct_cte K x + 1 * Re (G (arc r x)))
    by (intros x _; rewrite Hpt; unfold fct_cte; ring).
  assert (Hsplit : RiemannInt pr = RiemannInt prsum)
    by (apply RiemannInt_P18; [ exact Hab | exact Hext ]).
  assert (H13 : RiemannInt prsum = RiemannInt prK + 1 * RiemannInt prReG)
    by apply RiemannInt_P13.
  assert (H15 : RiemannInt prK = K * (2 * PI - 0)) by apply RiemannInt_P15.
  rewrite Hsplit, H13, H15, HI, Hpt0. ring.
Qed.

Print Assumptions zero_free_MVP_disk.
