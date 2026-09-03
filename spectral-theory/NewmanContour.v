(* ================================================================= *)
(*  NewmanContour.v  --  brick E5 closed: Newman's contour identity    *)
(*  for the HONEST (discontinuous-integrand) transform.                *)
(*                                                                    *)
(*  Newman applies Cauchy's formula to                                 *)
(*        F(z) = (g(z) - g_T(z)) * e^{zT}                              *)
(*  on Zagier's truncated contour, against the kernel K_R = 1/z+z/R^2. *)
(*  Here g := gext (NewmanGExt) and g_T := LTN _ 0 T (NewmanTransform),*)
(*  the transform of Newman's step function f(t) = psiR(e^t)/e^t - 1.  *)
(*                                                                    *)
(*  Two inputs make this work:                                         *)
(*    * NewmanHolo.LTN_holo -- g_T is ENTIRE in z (the truncated       *)
(*      integral is holomorphic everywhere), so it contributes no      *)
(*      constraint on the region;                                     *)
(*    * NewmanCutoff.gtrunc_ptcont -- gext cut off to the truncated    *)
(*      disk is globally pointwise continuous and unchanged there,     *)
(*      which is what the path-integral infrastructure demands.        *)
(*                                                                    *)
(*  The contour is the circle |z| = Rc truncated at Re z = -dl, i.e.   *)
(*  alpha = acos(-dl/Rc); the ambient region is the slightly larger    *)
(*  truncated disk U = {|z| < Rc+1} cap {Re z > -2dl}, on which        *)
(*  BfnUniform.gext_holo_strip gives holomorphy.  Conclusion:          *)
(*                                                                    *)
(*      int_arc F*K_R + int_chord F*K_R = 2*pi*i*(g(0) - g_T(0)).      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CHoloCcontC CexpFull CExpEntire CexpfDeriv CExpKernel
        CIntegral2 CSegInt CPathIntegral CPathFTC CPrimConv
        CGoursatLin PerronRemovable CWindingOffCenter
        CTruncWind CTruncCauchy CTruncCauchyDom
        CTruncDisk CNewmanKernel CTruncKernel
        Chebyshev NewmanGExt BfnUniform NewmanCutoff
        CIntegralD NewmanTransform NewmanHolo.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Pointwise continuity is closed under products and differences.     *)
(* ----------------------------------------------------------------- *)

Lemma PtcontC_sub : forall f g, PtcontC f -> PtcontC g ->
  PtcontC (fun z => Cminus (f z) (g z)).
Proof.
  intros f g Hf Hg z0 eps Heps.
  destruct (Hf z0 (eps / 2) ltac:(lra)) as [d1 [Hd1 H1]].
  destruct (Hg z0 (eps / 2) ltac:(lra)) as [d2 [Hd2 H2]].
  exists (Rmin d1 d2); split; [ apply Rmin_pos; assumption | ].
  intros w Hw.
  assert (Hw1 : Cmod (Cminus w z0) < d1)
    by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ]).
  assert (Hw2 : Cmod (Cminus w z0) < d2)
    by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
  replace (Cminus (Cminus (f w) (g w)) (Cminus (f z0) (g z0)))
    with (Cadd (Cminus (f w) (f z0)) (Copp (Cminus (g w) (g z0)))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ]; rewrite Cmod_opp.
  assert (H1' := H1 w Hw1); assert (H2' := H2 w Hw2); lra.
Qed.

Lemma PtcontC_mul : forall f g, PtcontC f -> PtcontC g ->
  PtcontC (fun z => Cmul (f z) (g z)).
Proof.
  intros f g Hf Hg z0 eps Heps.
  set (Mf := Cmod (f z0)). set (Mg := Cmod (g z0)).
  assert (HMf : 0 <= Mf) by apply Cmod_nonneg.
  assert (HMg : 0 <= Mg) by apply Cmod_nonneg.
  destruct (Hf z0 (eps / 2 / (Mg + 1)) ltac:(apply Rdiv_lt_0_compat; lra))
    as [d1 [Hd1 H1]].
  destruct (Hg z0 (eps / 2 / (Mf + 1)) ltac:(apply Rdiv_lt_0_compat; lra))
    as [d2 [Hd2 H2]].
  destruct (Hg z0 1 ltac:(lra)) as [d3 [Hd3 H3]].
  exists (Rmin d1 (Rmin d2 d3)); split;
    [ apply Rmin_pos; [ assumption | apply Rmin_pos; assumption ] | ].
  intros w Hw.
  assert (Hw1 : Cmod (Cminus w z0) < d1)
    by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ]).
  assert (Hw23 : Cmod (Cminus w z0) < Rmin d2 d3)
    by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
  assert (Hw2 : Cmod (Cminus w z0) < d2)
    by (eapply Rlt_le_trans; [ exact Hw23 | apply Rmin_l ]).
  assert (Hw3 : Cmod (Cminus w z0) < d3)
    by (eapply Rlt_le_trans; [ exact Hw23 | apply Rmin_r ]).
  (* |g w| <= Mg + 1 *)
  assert (Hgb : Cmod (g w) <= Mg + 1).
  { assert (Hd : Cmod (Cminus (g w) (g z0)) < 1) by (apply H3; exact Hw3).
    replace (g w) with (Cadd (g z0) (Cminus (g w) (g z0))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | unfold Mg; lra ]. }
  replace (Cminus (Cmul (f w) (g w)) (Cmul (f z0) (g z0)))
    with (Cadd (Cmul (Cminus (f w) (f z0)) (g w))
               (Cmul (f z0) (Cminus (g w) (g z0)))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ]; rewrite !Cmod_mul.
  assert (Ht1 : Cmod (Cminus (f w) (f z0)) * Cmod (g w) < eps / 2).
  { apply Rle_lt_trans with (Cmod (Cminus (f w) (f z0)) * (Mg + 1));
      [ apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hgb ] | ].
    apply Rlt_le_trans with (eps / 2 / (Mg + 1) * (Mg + 1));
      [ apply Rmult_lt_compat_r; [ lra | apply H1; exact Hw1 ]
      | apply Req_le; field; lra ]. }
  assert (Ht2 : Mf * Cmod (Cminus (g w) (g z0)) <= eps / 2).
  { apply Rle_trans with (Mf * (eps / 2 / (Mf + 1)));
      [ apply Rmult_le_compat_l; [ exact HMf | left; apply H2; exact Hw2 ] | ].
    apply Rle_trans with ((Mf + 1) * (eps / 2 / (Mf + 1)));
      [ apply Rmult_le_compat_r; [ | lra ] | apply Req_le; field; lra ].
    left; apply Rdiv_lt_0_compat; lra. }
  unfold Mf in Ht2; lra.
Qed.

Lemma holo_PtcontC : forall F : C -> C,
  (forall z, exists d, is_Cderiv F z d) -> PtcontC F.
Proof.
  intros F H; unfold PtcontC; intros z eps Heps; apply (holo_ptcont F H z eps Heps).
Qed.

(* ----------------------------------------------------------------- *)
(*  The two entire factors:  e^{zT}  and  g_T.                         *)
(* ----------------------------------------------------------------- *)

Definition Etf (T : R) (z : C) : C := Cexpf (Cmul z (RtoC T)).

Lemma Etf_holo : forall T z, exists d, is_Cderiv (Etf T) z d.
Proof.
  intros T z; unfold Etf; eexists; apply Cexpf_comp_deriv.
  apply Cderiv_mul; [ apply Cderiv_id | apply Cderiv_const ].
Qed.

Lemma Etf_at0 : forall T, Etf T C0 = C1.
Proof.
  intro T; unfold Etf.
  replace (Cmul C0 (RtoC T)) with C0 by ring; apply Cexpf_at0.
Qed.

Definition gTr (T : R) (HT : 0 <= T) (z : C) : C := LTN z 0 T (Rle_refl 0) HT.

Lemma gTr_holo : forall T (HT : 0 <= T) z, exists d, is_Cderiv (gTr T HT) z d.
Proof. intros T HT z; eexists; unfold gTr; apply LTN_holo. Qed.

(* ----------------------------------------------------------------- *)
(*  Newman's integrand, honest and truncated.                          *)
(* ----------------------------------------------------------------- *)

Definition Gd (T : R) (HT : 0 <= T) (z : C) : C :=
  Cmul (Cminus (gext z) (gTr T HT z)) (Etf T z).

Definition Gdt (Rr del T : R) (HT : 0 <= T) (z : C) : C :=
  Cmul (Cminus (gtrunc Rr del z) (gTr T HT z)) (Etf T z).

Lemma Gdt_eq : forall Rr del T (HT : 0 <= T) z,
  gtrunc Rr del z = gext z -> Gdt Rr del T HT z = Gd T HT z.
Proof. intros Rr del T HT z H; unfold Gdt, Gd; rewrite H; reflexivity. Qed.

Lemma Gdt_ptcont : forall Rr del T (HT : 0 <= T),
  PtcontC (gtrunc Rr del) -> PtcontC (Gdt Rr del T HT).
Proof.
  intros Rr del T HT Hg; unfold Gdt.
  apply PtcontC_mul;
    [ apply PtcontC_sub;
      [ exact Hg | apply holo_PtcontC; apply gTr_holo ]
    | apply holo_PtcontC; apply Etf_holo ].
Qed.

(* ================================================================= *)
(*  The contour identity.                                             *)
(* ================================================================= *)
Section NC.

Variables (Rc dl del T alpha : R).
Hypothesis HRc : 0 < Rc.
Hypothesis Hdl : 0 < dl.
Hypothesis Hdel : 0 < del.
Hypothesis Hsmall : 4 * dl <= del.
Hypothesis HT : 0 <= T.
Hypothesis Halpha : PI / 2 < alpha < PI.
Hypothesis Hchord : Rc * cos alpha = - dl.
Hypothesis Hstrip : forall z, Rabs (Re z) < 2 * dl -> Rabs (Im z) <= Rc + 1 ->
  exists d, is_Cderiv gext z d.
Hypothesis Hagree : forall z, Cmod z <= Rc + 1 -> - (del / 2) <= Re z ->
  gtrunc (Rc + 1) del z = gext z.
Hypothesis Hptc : PtcontC (gtrunc (Rc + 1) del).

Let U : C -> Prop := TruncDisk (Rc + 1) (2 * dl).
Let Pc : C := mkC (Rc * cos alpha) (Rc * sin alpha).
Let Qc : C := mkC (Rc * cos alpha) (- (Rc * sin alpha)).

Lemma U_agree : forall z, U z -> gtrunc (Rc + 1) del z = gext z.
Proof.
  intros z [Hm Hr]; apply Hagree; lra.
Qed.

Lemma U_gext_holo : forall z, U z -> exists d, is_Cderiv gext z d.
Proof.
  intros z [Hm Hr].
  destruct (Rle_lt_dec 0 (Re z)) as [Hge | Hlt];
    [ apply gext_holo_re_ge0; exact Hge | ].
  apply Hstrip.
  - unfold Rabs; destruct (Rcase_abs (Re z)); lra.
  - eapply Rle_trans; [ apply Rabs_Im_le3 | lra ].
Qed.

Lemma U_gtrunc_holo : forall z, U z -> exists d, is_Cderiv (gtrunc (Rc + 1) del) z d.
Proof.
  intros z HUz.
  destruct (TruncDisk_open (Rc + 1) (2 * dl) z HUz) as [r [Hr Hball]].
  destruct (U_gext_holo z HUz) as [d Hd].
  exists d.
  apply (is_Cderiv_congr (gtrunc (Rc + 1) del) gext z d r);
    [ exact Hr | intros w Hw; apply U_agree, Hball, Hw | exact Hd ].
Qed.

Lemma U_Gdt_holo : forall z, U z -> exists d, is_Cderiv (Gdt (Rc + 1) del T HT) z d.
Proof.
  intros z HUz.
  destruct (U_gtrunc_holo z HUz) as [d1 Hd1].
  destruct (gTr_holo T HT z) as [d2 Hd2].
  destruct (Etf_holo T z) as [d3 Hd3].
  eexists; unfold Gdt; apply Cderiv_mul;
    [ apply Cderiv_minus; [ exact Hd1 | exact Hd2 ] | exact Hd3 ].
Qed.

Lemma U_C0 : U C0.
Proof.
  assert (HR0 : Re C0 = 0) by reflexivity.
  unfold U, TruncDisk; split.
  - rewrite (proj2 (Cmod0 C0) eq_refl); lra.
  - rewrite HR0; lra.
Qed.

Lemma U_arc : forall s, - alpha <= s <= alpha -> U (arc Rc s).
Proof.
  intros s Hs; unfold U, TruncDisk; split.
  - rewrite Cmod_arc by lra; lra.
  - cbn [Re arc].
    assert (Hcabs : cos s = cos (Rabs s))
      by (unfold Rabs; destruct (Rcase_abs s);
          [ rewrite cos_neg; reflexivity | reflexivity ]).
    assert (Habs : 0 <= Rabs s <= alpha)
      by (unfold Rabs; destruct (Rcase_abs s); lra).
    assert (Hcs : cos alpha <= cos s).
    { rewrite Hcabs.
      destruct (Rle_lt_or_eq_dec (Rabs s) alpha (proj2 Habs)) as [Hlt | Heq].
      - left; apply cos_decreasing_1; try lra; apply Habs.
      - rewrite Heq; apply Rle_refl. }
    assert (Hmul : Rc * cos alpha <= Rc * cos s)
      by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

Lemma U_chord : forall s, 0 <= s <= 1 -> U (seg Pc Qc s).
Proof.
  intros s [Hs0 Hs1]; unfold U, TruncDisk, Pc, Qc.
  rewrite seg_chord.
  assert (Hsc := sin2_cos2 alpha); unfold Rsqr in Hsc.
  split; cbn [Re Im].
  - assert (HRR : sqrt ((Rc + 1) * (Rc + 1)) = Rc + 1) by (apply sqrt_square; lra).
    assert (Hsp : 0 <= s * (1 - s)) by (apply Rmult_le_pos; lra).
    assert (Hb : (1 - 2 * s) * (1 - 2 * s) <= 1) by lra.
    pose proof (Rle_0_sqr (Rc * cos alpha)) as Hq1.
    pose proof (Rle_0_sqr (Rc * sin alpha)) as Hq2.
    pose proof (Rle_0_sqr (Rc * sin alpha * (1 - 2 * s))) as Hq3.
    unfold Rsqr in Hq1, Hq2, Hq3.
    assert (Hkey : Rc * cos alpha * (Rc * cos alpha)
                 + Rc * sin alpha * (1 - 2 * s) * (Rc * sin alpha * (1 - 2 * s))
                 <= Rc * Rc).
    { replace (Rc * sin alpha * (1 - 2 * s) * (Rc * sin alpha * (1 - 2 * s)))
        with (Rc * sin alpha * (Rc * sin alpha) * ((1 - 2 * s) * (1 - 2 * s)))
        by ring.
      assert (Hmm : Rc * sin alpha * (Rc * sin alpha) * ((1 - 2 * s) * (1 - 2 * s))
                  <= Rc * sin alpha * (Rc * sin alpha) * 1)
        by (apply Rmult_le_compat_l; assumption).
      nra. }
    unfold Cmod, Cnorm2; cbn [Re Im].
    rewrite <- HRR; apply sqrt_lt_1_alt; split; [ lra | lra ].
  - lra.
Qed.

(* ---- the contour lies where gtrunc is gext, so the truncation is
       invisible to every estimate downstream ---- *)
Lemma Gdt_arc : forall s, - alpha <= s <= alpha ->
  Gdt (Rc + 1) del T HT (arc Rc s) = Gd T HT (arc Rc s).
Proof. intros s Hs; apply Gdt_eq, U_agree, U_arc, Hs. Qed.

Lemma Gdt_chord : forall s, 0 <= s <= 1 ->
  Gdt (Rc + 1) del T HT (seg Pc Qc s) = Gd T HT (seg Pc Qc s).
Proof. intros s Hs; apply Gdt_eq, U_agree, U_chord, Hs. Qed.

(* ---- and the two continuity witnesses the path integrals need,
       so the identity below is not vacuous ---- *)
Let HGc : CcontC (Gdt (Rc + 1) del T HT) :=
  ptcont_CcontC _ (Gdt_ptcont (Rc + 1) del T HT Hptc).

Lemma arc_ne0 : forall s, arc Rc s <> C0.
Proof.
  intros s Hc; assert (HM : Cmod (arc Rc s) = Rc) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM; lra.
Qed.

Lemma chord_ne0 : forall s, seg Pc Qc s <> C0.
Proof.
  intros s Hc; apply (f_equal Re) in Hc; cbn in Hc; lra.
Qed.

Lemma Kcont_arc : Ccont (fun u => newman_kernel Rc (arc Rc u)).
Proof.
  unfold newman_kernel; apply Ccont_add;
    [ apply Ccont_inv; [ apply Ccont_arc | apply arc_ne0 ]
    | apply Ccont_mul; [ apply Ccont_arc | apply Ccont_const ] ].
Qed.

Lemma Kcont_chord : Ccont (fun u => newman_kernel Rc (seg Pc Qc u)).
Proof.
  unfold newman_kernel; apply Ccont_add;
    [ apply Ccont_inv; [ apply Ccont_seg_id | apply chord_ne0 ]
    | apply Ccont_mul; [ apply Ccont_seg_id | apply Ccont_const ] ].
Qed.

Lemma HfaK_wit : Ccont (fun u => Cmul (Cmul (Gdt (Rc + 1) del T HT (arc Rc u))
                                            (newman_kernel Rc (arc Rc u)))
                                      (arc' Rc u)).
Proof.
  apply Ccont_mul; [ apply Ccont_mul; [ apply HGc, Ccont_arc | apply Kcont_arc ]
                   | apply Ccont_arc' ].
Qed.

Lemma HfcK_wit : Ccont (fun u => Cmul (Cmul (Gdt (Rc + 1) del T HT (seg Pc Qc u))
                                            (newman_kernel Rc (seg Pc Qc u)))
                                      (seg' Pc Qc u)).
Proof.
  apply Ccont_mul; [ apply Ccont_mul; [ apply HGc, Ccont_seg_id | apply Kcont_chord ]
                   | apply Ccont_seg'_id ].
Qed.

(* ---- the identity ---- *)
Theorem newman_contour :
  forall (HfaK : Ccont (fun u => Cmul (Cmul (Gdt (Rc + 1) del T HT (arc Rc u))
                                            (newman_kernel Rc (arc Rc u)))
                                      (arc' Rc u)))
         (HfcK : Ccont (fun u => Cmul (Cmul (Gdt (Rc + 1) del T HT (seg Pc Qc u))
                                            (newman_kernel Rc (seg Pc Qc u)))
                                      (seg' Pc Qc u))),
  Cadd (pathint (arc Rc) (arc' Rc)
          (fun z => Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z))
          HfaK (- alpha) alpha)
       (pathint (seg Pc Qc) (seg' Pc Qc)
          (fun z => Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z))
          HfcK 0 1)
  = Cmul (Cminus (gext C0) (LTN C0 0 T (Rle_refl 0) HT)) (mkC 0 (2 * PI)).
Proof.
  intros HfaK HfcK.
  assert (HG0 : Gdt (Rc + 1) del T HT C0
              = Cminus (gext C0) (LTN C0 0 T (Rle_refl 0) HT)).
  { unfold Gdt, gTr; rewrite (U_agree C0 U_C0), (Etf_at0 T); ring. }
  rewrite <- HG0.
  exact (trunc_kernel_dom Rc alpha HRc Halpha U
           (TruncDisk_convex (Rc + 1) (2 * dl))
           (TruncDisk_open (Rc + 1) (2 * dl))
           U_C0 U_arc U_chord
           (Gdt (Rc + 1) del T HT)
           (Gdt_ptcont (Rc + 1) del T HT Hptc)
           U_Gdt_holo HfaK HfcK).
Qed.

End NC.

Print Assumptions newman_contour.
Print Assumptions HfaK_wit.
Print Assumptions HfcK_wit.

(* ================================================================= *)
(*  The parameters exist: for every contour radius Rc there is a       *)
(*  truncation depth dl (and a cutoff width del) meeting every         *)
(*  hypothesis above, and an angle alpha realising it.                 *)
(* ================================================================= *)

Lemma alpha_of_delta : forall Rc d, 0 < d -> d < Rc ->
  exists alpha, PI / 2 < alpha < PI /\ Rc * cos alpha = - d.
Proof.
  intros Rc d Hd Hdr.
  assert (HRc : 0 < Rc) by lra.
  assert (Hq : - d / Rc * Rc = - d) by (field; lra).
  assert (Hx : -1 <= - d / Rc <= 1).
  { split; apply Rmult_le_reg_r with Rc; try lra; rewrite Hq; lra. }
  assert (Hcc : cos (acos (- d / Rc)) = - d / Rc) by (apply cos_acos; exact Hx).
  assert (Hb := acos_bound (- d / Rc)).
  assert (Hneg : - d / Rc < 0).
  { apply Rmult_lt_reg_r with Rc; [ lra | ].
    replace (- d / Rc * Rc) with (- d) by (field; lra); lra. }
  assert (Hgt1 : - 1 < - d / Rc).
  { apply Rmult_lt_reg_r with Rc; [ lra | ].
    replace (- d / Rc * Rc) with (- d) by (field; lra); lra. }
  exists (acos (- d / Rc)); split; [ split | ].
  - apply (cos_decreasing_0 (acos (- d / Rc)) (PI / 2));
      [ lra | lra | | | rewrite Hcc, cos_PI2; exact Hneg ];
      assert (HPI := PI_RGT_0); lra.
  - apply (cos_decreasing_0 PI (acos (- d / Rc)));
      [ assert (HPI := PI_RGT_0); lra | apply Rle_refl | lra | lra | ];
      rewrite cos_PI, Hcc; exact Hgt1.
  - rewrite Hcc; field; lra.
Qed.

Theorem newman_contour_params : forall Rc, 0 < Rc ->
  exists dl del : R,
    0 < dl /\ dl < Rc /\ 0 < del /\ 4 * dl <= del /\
    (forall z, Rabs (Re z) < 2 * dl -> Rabs (Im z) <= Rc + 1 ->
       exists d, is_Cderiv gext z d) /\
    (forall z, Cmod z <= Rc + 1 -> - (del / 2) <= Re z ->
       gtrunc (Rc + 1) del z = gext z) /\
    PtcontC (gtrunc (Rc + 1) del).
Proof.
  intros Rc HRc.
  destruct (gtrunc_ptcont (Rc + 1) ltac:(lra)) as [del [Hdel [Hptc Hag]]].
  destruct (gext_holo_strip (Rc + 1) ltac:(lra)) as [d1 [Hd1 Hstr]].
  set (dl := Rmin (Rmin (del / 4) (d1 / 4)) (Rc / 2)).
  assert (Hm1 : dl <= del / 4) by (unfold dl; eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
  assert (Hm2 : dl <= d1 / 4) by (unfold dl; eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
  assert (Hm3 : dl <= Rc / 2) by (unfold dl; apply Rmin_r).
  assert (Hdl : 0 < dl)
    by (unfold dl; repeat apply Rmin_glb_lt; lra).
  exists dl, del.
  repeat split; try lra; try assumption.
  intros z Hre Him; apply Hstr; [ lra | exact Him ].
Qed.

Print Assumptions newman_contour_params.

(* ================================================================= *)
(*  END NewmanContour.v -- E5 closed:  the truncated-contour integral  *)
(*  of (g - g_T)e^{zT} against Zagier's kernel is 2*pi*i*(g(0)-g_T(0)).*)
(* ================================================================= *)
