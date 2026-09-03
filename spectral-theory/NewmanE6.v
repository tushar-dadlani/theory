(* ================================================================= *)
(*  NewmanE6.v  --  brick E6: the contour estimate.                    *)
(*                                                                    *)
(*  From the contour identity (NewmanContour.newman_contour) to a      *)
(*  quantitative bound on  g(0) - g_T(0):                              *)
(*                                                                    *)
(*    |g(0) - g_T(0)| * 2pi                                            *)
(*        <= (24 pi B + 4 pi M d) / R  +  4 M R (1/d + 1/R) e^{-dT}    *)
(*                                                                    *)
(*  with B = Kup + 1 the bound on Newman's f and M a bound on g near   *)
(*  the imaginary axis.  The five pieces:                              *)
(*                                                                    *)
(*    arc, Re z >= 0    : |(g - g_T) e^{zT} K_R| <= 4B/R^2   -- the     *)
(*        cancellation, with g - g_T bounded by the tail (kern_bound); *)
(*    arc, Re z <= 0 (two pieces, |Re z| <= d): the SAME 4B/R^2 for    *)
(*        the g_T half (its tail bound flips sign), plus 2Md/R^2 for   *)
(*        the g half, because there the kernel itself is small;        *)
(*    chord, g_T half   : deformed to the far-left arc                 *)
(*        (NewmanDeform.chord_to_arc), where 4B/R^2 applies again;     *)
(*    chord, g half     : |g| <= M, |e^{zT}| = e^{-dT}, |K_R| bounded  *)
(*        crudely -- the only piece that needs T -> oo.                *)
(*                                                                    *)
(*  Note the arc is split at Re z = 0 and NOT at |Re z| = d: on the    *)
(*  truncated contour the whole left arc already has |Re z| <= d.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CIntegral2 CSegInt CPathIntegral CLeibniz CGoursatLin
        CExpKernel CNewmanKernel CTruncKernel CTruncWind CTruncCauchy
        Chebyshev ChebyshevBound ChebyshevPsiR CIntegralD
        PerronRemovable NewmanArcML NewmanGLeft NewmanNearAxis
        NewmanTransform NewmanTail NewmanGExt NewmanCutoff
        NewmanContour NewmanKernelCut NewmanDeform NewmanML.
Open Scope R_scope.

Section E6.

Variables (Rc dl del T alpha M : R).
Hypothesis HRc : 0 < Rc.
Hypothesis Hdl : 0 < dl.
Hypothesis Hsmall : 4 * dl <= del.
Hypothesis HT : 0 <= T.
Hypothesis Halpha : PI / 2 < alpha < PI.
Hypothesis Hchord : Rc * cos alpha = - dl.
Hypothesis Hstrip : forall z, Rabs (Re z) < 2 * dl -> Rabs (Im z) <= Rc + 1 ->
  exists d, is_Cderiv gext z d.
Hypothesis Hagree : forall z, Cmod z <= Rc + 1 -> - (del / 2) <= Re z ->
  gtrunc (Rc + 1) del z = gext z.
Hypothesis Hptc : PtcontC (gtrunc (Rc + 1) del).
Hypothesis HM : forall z, Rabs (Re z) <= dl -> Rabs (Im z) <= Rc ->
  Cmod (gtrunc (Rc + 1) del z) <= M.

Let Pc : C := mkC (Rc * cos alpha) (Rc * sin alpha).
Let Qc : C := mkC (Rc * cos alpha) (- (Rc * sin alpha)).

Lemma HPI : 0 < PI. Proof. exact PI_RGT_0. Qed.
Lemma HB : 0 <= Kup + 1. Proof. pose proof Kup_pos; lra. Qed.
Lemma HRR : 0 < Rc * Rc. Proof. nra. Qed.

Lemma dl_le_Rc : dl <= Rc.
Proof.
  pose proof (COS_bound alpha) as [Hlo Hhi].
  assert (Hm2 : Rc * cos alpha >= Rc * (-1)) by (apply Rmult_ge_compat_l; lra).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Pointwise bounds on the arc.                                       *)
(* ----------------------------------------------------------------- *)

Lemma Re_arc : forall u, Re (arc Rc u) = Rc * cos u.
Proof. intro u; reflexivity. Qed.

Lemma Cmod_arcRc : forall u, Cmod (arc Rc u) = Rc.
Proof. intro u; apply Cmod_arc; lra. Qed.

Lemma Gdt_split : forall z,
  Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z)
  = Cmul (Cmul (Cminus (gtrunc (Rc + 1) del z) (LTN z 0 T (Rle_refl 0) HT))
               (cexpzt z T))
         (newman_kernel Rc z).
Proof. intro z; unfold Gdt, Etf, gTr, cexpzt; reflexivity. Qed.

Lemma mid_bound : forall u, - (PI / 2) <= u <= PI / 2 ->
  Cmod (Cmul (Gdt (Rc + 1) del T HT (arc Rc u)) (newman_kernel Rc (arc Rc u)))
  <= 4 * (Kup + 1) / (Rc * Rc).
Proof.
  intros u Hu; rewrite Gdt_split.
  assert (Hcos : 0 <= cos u) by (apply cos_ge_0; lra).
  assert (Hre : 0 <= Re (arc Rc u)) by (rewrite Re_arc; nra).
  apply kern_bound; [ apply HB | exact HRc | apply Cnorm2_arc | ].
  intro Hne.
  assert (Hpos : 0 < Re (arc Rc u)) by lra.
  assert (Hgt : gtrunc (Rc + 1) del (arc Rc u) = gext (arc Rc u))
    by (apply Hagree; [ rewrite Cmod_arcRc; lra | lra ]).
  rewrite Hgt; apply gext_LTN_bound; exact Hpos.
Qed.

Lemma left_cos : forall u, PI / 2 <= Rabs u <= alpha ->
  cos alpha <= cos u <= 0.
Proof.
  intros u Hu; pose proof HPI as HP.
  assert (Hcabs : cos u = cos (Rabs u))
    by (unfold Rabs; destruct (Rcase_abs u);
        [ rewrite cos_neg; reflexivity | reflexivity ]).
  rewrite Hcabs; split.
  - destruct (Rle_lt_or_eq_dec (Rabs u) alpha (proj2 Hu)) as [Hlt | Heq];
      [ left; apply cos_decreasing_1; lra | rewrite Heq; apply Rle_refl ].
  - rewrite <- cos_PI2.
    destruct (Rle_lt_or_eq_dec (PI / 2) (Rabs u) (proj1 Hu)) as [Hlt | Heq];
      [ left; apply cos_decreasing_1; lra | rewrite <- Heq; apply Rle_refl ].
Qed.

Lemma left_bound : forall u, PI / 2 <= Rabs u <= alpha ->
  Cmod (Cmul (Gdt (Rc + 1) del T HT (arc Rc u)) (newman_kernel Rc (arc Rc u)))
  <= 4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc).
Proof.
  intros u Hu; rewrite Gdt_split.
  destruct (left_cos u Hu) as [Hlo Hhi].
  assert (Hre : Re (arc Rc u) = Rc * cos u) by apply Re_arc.
  assert (Hrele : Re (arc Rc u) <= 0) by (rewrite Hre; nra).
  assert (Hrege : - dl <= Re (arc Rc u))
    by (rewrite Hre; rewrite <- Hchord; apply Rmult_le_compat_l; lra).
  assert (Habs : Rabs (Re (arc Rc u)) <= dl)
    by (unfold Rabs; destruct (Rcase_abs (Re (arc Rc u))); lra).
  (* split the integrand and use the triangle inequality *)
  replace (Cmul (Cmul (Cminus (gtrunc (Rc + 1) del (arc Rc u))
                              (LTN (arc Rc u) 0 T (Rle_refl 0) HT))
                      (cexpzt (arc Rc u) T))
                (newman_kernel Rc (arc Rc u)))
    with (Cadd (Cmul (Cmul (gtrunc (Rc + 1) del (arc Rc u)) (cexpzt (arc Rc u) T))
                     (newman_kernel Rc (arc Rc u)))
               (Copp (Cmul (Cmul (LTN (arc Rc u) 0 T (Rle_refl 0) HT)
                                 (cexpzt (arc Rc u) T))
                           (newman_kernel Rc (arc Rc u))))) by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ]; rewrite Cmod_opp.
  assert (Hg : Cmod (Cmul (Cmul (gtrunc (Rc + 1) del (arc Rc u))
                                (cexpzt (arc Rc u) T))
                          (newman_kernel Rc (arc Rc u)))
               <= 2 * M * dl / (Rc * Rc)).
  { apply (kern_nearaxis (gtrunc (Rc + 1) del (arc Rc u)) (arc Rc u) dl M T Rc);
      [ lra | exact HT | exact Hrele | exact Habs
      | apply HM;
          [ exact Habs
          | eapply Rle_trans;
              [ apply Rabs_Im_le3 | rewrite Cmod_arcRc; apply Rle_refl ] ]
      | exact HRc | apply Cnorm2_arc ]. }
  assert (Ht : Cmod (Cmul (Cmul (LTN (arc Rc u) 0 T (Rle_refl 0) HT)
                                (cexpzt (arc Rc u) T))
                          (newman_kernel Rc (arc Rc u)))
               <= 4 * (Kup + 1) / (Rc * Rc)).
  { apply kern_bound; [ apply HB | exact HRc | apply Cnorm2_arc | ].
    intro Hne; apply LTN_tail_left; lra. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The two halves of the integrand, separately.                       *)
(* ----------------------------------------------------------------- *)

Definition Wg (z : C) : C := Cmul (gtrunc (Rc + 1) del z) (Etf T z).
Definition Wt (z : C) : C := Cmul (gTr T HT z) (Etf T z).

Lemma Wg_CcontC : CcontC Wg.
Proof.
  unfold Wg; apply CcontC_mul;
    [ apply ptcont_CcontC; exact Hptc
    | apply ptcont_CcontC; apply holo_PtcontC; apply Etf_holo ].
Qed.

Lemma Wt_holo : forall z, exists e, is_Cderiv Wt z e.
Proof.
  intro z; destruct (gTr_holo T HT z) as [e1 He1].
  destruct (Etf_holo T z) as [e2 He2].
  eexists; unfold Wt; apply Cderiv_mul; [ exact He1 | exact He2 ].
Qed.

Lemma Wt_CcontC : CcontC Wt.
Proof. apply ptcont_CcontC, holo_PtcontC, Wt_holo. Qed.

(* ----------------------------------------------------------------- *)
(*  The far-left arc (the deformed chord).                             *)
(* ----------------------------------------------------------------- *)

Lemma far_bound : forall u, alpha <= u <= 2 * PI - alpha ->
  Cmod (Cmul (Wt (arc Rc u)) (newman_kernel Rc (arc Rc u)))
  <= 4 * (Kup + 1) / (Rc * Rc).
Proof.
  intros u Hu.
  assert (Hcu := cos_le_far alpha u Halpha Hu).
  assert (Hre : Re (arc Rc u) = Rc * cos u) by apply Re_arc.
  assert (Hneg : Re (arc Rc u) <= - dl)
    by (rewrite Hre, <- Hchord; apply Rmult_le_compat_l; lra).
  replace (Cmul (Wt (arc Rc u)) (newman_kernel Rc (arc Rc u)))
    with (Cmul (Cmul (LTN (arc Rc u) 0 T (Rle_refl 0) HT) (cexpzt (arc Rc u) T))
               (newman_kernel Rc (arc Rc u)))
    by (unfold Wt, Etf, gTr, cexpzt; reflexivity).
  apply kern_bound; [ apply HB | exact HRc | apply Cnorm2_arc | ].
  intro Hne; apply LTN_tail_left; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The chord geometry and its bound.                                  *)
(* ----------------------------------------------------------------- *)

Lemma Re_chord : forall u, Re (seg Pc Qc u) = - dl.
Proof.
  intro u; unfold Pc, Qc; rewrite seg_chord; cbn [Re]; exact Hchord.
Qed.

Lemma Cmod_chord_le : forall u, 0 <= u <= 1 -> Cmod (seg Pc Qc u) <= Rc.
Proof.
  intros u [Hu0 Hu1]; unfold Pc, Qc; rewrite seg_chord.
  assert (Hsc := sin2_cos2 alpha); unfold Rsqr in Hsc.
  assert (HRR2 : sqrt (Rc * Rc) = Rc) by (apply sqrt_square; lra).
  assert (Hsp : 0 <= u * (1 - u)) by (apply Rmult_le_pos; lra).
  assert (Hb : (1 - 2 * u) * (1 - 2 * u) <= 1) by lra.
  pose proof (Rle_0_sqr (Rc * sin alpha)) as Hq2; unfold Rsqr in Hq2.
  unfold Cmod, Cnorm2; cbn [Re Im]; rewrite <- HRR2; apply sqrt_le_1_alt.
  replace (Rc * sin alpha * (1 - 2 * u) * (Rc * sin alpha * (1 - 2 * u)))
    with (Rc * sin alpha * (Rc * sin alpha) * ((1 - 2 * u) * (1 - 2 * u))) by ring.
  assert (Hmm : Rc * sin alpha * (Rc * sin alpha) * ((1 - 2 * u) * (1 - 2 * u))
              <= Rc * sin alpha * (Rc * sin alpha) * 1)
    by (apply Rmult_le_compat_l; assumption).
  nra.
Qed.

Lemma Cmod_chord_ge : forall u, dl <= Cmod (seg Pc Qc u).
Proof.
  intro u.
  assert (HA : Rabs (Re (seg Pc Qc u)) <= Cmod (seg Pc Qc u))
    by apply CTruncDisk.Rabs_Re_le_Cmod.
  rewrite Re_chord, Rabs_Ropp, (Rabs_pos_eq dl) in HA by lra; exact HA.
Qed.

Lemma Cmod_QP : Cmod (Cminus Qc Pc) <= 2 * Rc.
Proof.
  assert (Hsc := sin2_cos2 alpha); unfold Rsqr in Hsc.
  assert (H4 : sqrt (2 * Rc * (2 * Rc)) = 2 * Rc) by (apply sqrt_square; lra).
  unfold Pc, Qc, Cminus, Cmod, Cnorm2; cbn [Re Im].
  rewrite <- H4; apply sqrt_le_1_alt.
  pose proof (Rle_0_sqr (cos alpha)) as Hq; unfold Rsqr in Hq; nra.
Qed.

Lemma chord_g_bound : forall u, 0 <= u <= 1 ->
  Cmod (Cmul (Wg (seg Pc Qc u)) (newman_kernel Rc (seg Pc Qc u)))
  <= M * exp (- (dl * T)) * (/ dl + / Rc).
Proof.
  intros u Hu; unfold Wg; rewrite !Cmod_mul.
  assert (HE : Cmod (Etf T (seg Pc Qc u)) = exp (- (dl * T))).
  { change (Etf T (seg Pc Qc u)) with (cexpzt (seg Pc Qc u) T).
    rewrite Cmod_cexpzt, Re_chord; f_equal; ring. }
  rewrite HE.
  assert (HGm : Cmod (gtrunc (Rc + 1) del (seg Pc Qc u)) <= M).
  { apply HM.
    - rewrite Re_chord, Rabs_Ropp, (Rabs_pos_eq dl) by lra; apply Rle_refl.
    - eapply Rle_trans; [ apply Rabs_Im_le3 | apply Cmod_chord_le; exact Hu ]. }
  assert (Hzne : seg Pc Qc u <> C0).
  { intro Hc; pose proof (Cmod_chord_ge u) as Hm.
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hm; lra. }
  assert (HK0 := Cmod_newman_kernel_le Rc (seg Pc Qc u) Hzne HRc).
  assert (Hge := Cmod_chord_ge u); assert (Hle := Cmod_chord_le u Hu).
  assert (H1 : / Cmod (seg Pc Qc u) <= / dl)
    by (apply Rinv_le_contravar; lra).
  assert (H2 : Cmod (seg Pc Qc u) / (Rc * Rc) <= / Rc).
  { unfold Rdiv; replace (/ Rc) with (Rc * / (Rc * Rc)) by (field; lra).
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; nra | exact Hle ]. }
  assert (HK : Cmod (newman_kernel Rc (seg Pc Qc u)) <= / dl + / Rc) by lra.
  apply Rmult_le_compat.
  - apply Rmult_le_pos; [ apply Cmod_nonneg | left; apply exp_pos ].
  - apply Cmod_nonneg.
  - apply Rmult_le_compat_r; [ left; apply exp_pos | exact HGm ].
  - exact HK.
Qed.

(* ----------------------------------------------------------------- *)
(*  The five path-integral pieces.                                     *)
(* ----------------------------------------------------------------- *)

Lemma Ccont_sub : forall f g, Ccont f -> Ccont g ->
  Ccont (fun u => Cminus (f u) (g u)).
Proof.
  intros f g Hf Hg.
  apply (Ccont_congr (fun u => Cadd (f u) (Copp (g u))));
    [ intro u; ring
    | apply Ccont_add; [ exact Hf | apply Ccont_opp; exact Hg ] ].
Qed.

Lemma Hcg_wit : Ccont (fun u => Cmul (Cmul (Wg (seg Pc Qc u))
                                           (newman_kernel Rc (seg Pc Qc u)))
                                     (seg' Pc Qc u)).
Proof.
  apply Ccont_mul;
    [ apply Ccont_mul;
      [ apply Wg_CcontC, Ccont_seg_id
      | exact (Kcont_chord Rc dl alpha Hdl Hchord) ]
    | apply Ccont_seg'_id ].
Qed.

Lemma Hct_wit : Ccont (fun u => Cmul (Cmul (Wt (seg Pc Qc u))
                                           (newman_kernel Rc (seg Pc Qc u)))
                                     (seg' Pc Qc u)).
Proof.
  apply Ccont_mul;
    [ apply Ccont_mul;
      [ apply Wt_CcontC, Ccont_seg_id
      | exact (Kcont_chord Rc dl alpha Hdl Hchord) ]
    | apply Ccont_seg'_id ].
Qed.

Lemma Hfa_wit : Ccont (fun u => Cmul (Cmul (Wt (arc Rc u))
                                           (newman_kernel Rc (arc Rc u)))
                                     (arc' Rc u)).
Proof.
  apply Ccont_mul;
    [ apply Ccont_mul;
      [ apply Wt_CcontC, Ccont_arc | exact (Kcont_arc Rc HRc) ]
    | apply Ccont_arc' ].
Qed.

Lemma chord_split : forall Hc,
  pathint (seg Pc Qc) (seg' Pc Qc)
     (fun z => Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z)) Hc 0 1
  = Cminus (pathint (seg Pc Qc) (seg' Pc Qc)
              (fun z => Cmul (Wg z) (newman_kernel Rc z)) Hcg_wit 0 1)
           (pathint (seg Pc Qc) (seg' Pc Qc)
              (fun z => Cmul (Wt z) (newman_kernel Rc z)) Hct_wit 0 1).
Proof.
  intro Hc; unfold pathint.
  assert (Hsub : Ccont (fun u =>
    Cminus (Cmul (Cmul (Wg (seg Pc Qc u)) (newman_kernel Rc (seg Pc Qc u)))
                 (seg' Pc Qc u))
           (Cmul (Cmul (Wt (seg Pc Qc u)) (newman_kernel Rc (seg Pc Qc u)))
                 (seg' Pc Qc u))))
    by (apply Ccont_sub; [ exact Hcg_wit | exact Hct_wit ]).
  rewrite (Cintf_ext _ _ Hc Hsub 0 1);
    [ | intro u; unfold Wg, Wt, Gdt; ring ].
  apply Cintf_sub; lra.
Qed.

Lemma chord_gT_deform :
  pathint (seg Pc Qc) (seg' Pc Qc)
     (fun z => Cmul (Wt z) (newman_kernel Rc z)) Hct_wit 0 1
  = pathint (arc Rc) (arc' Rc)
     (fun z => Cmul (Wt z) (newman_kernel Rc z)) Hfa_wit alpha (2 * PI - alpha).
Proof.
  exact (chord_to_arc Rc dl alpha HRc Hdl Halpha Hchord Wt Wt_CcontC Wt_holo
           Hct_wit Hfa_wit).
Qed.

(* ----------------------------------------------------------------- *)
(*  ML for each of the five pieces.                                    *)
(* ----------------------------------------------------------------- *)

Lemma piece_mid : forall Hf,
  Cmod (pathint (arc Rc) (arc' Rc)
          (fun z => Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z)) Hf
          (- (PI / 2)) (PI / 2))
  <= 2 * (4 * (Kup + 1) / (Rc * Rc) * Rc) * (PI / 2 - - (PI / 2)).
Proof.
  intro Hf; pose proof HPI; apply arc_ML; [ lra | lra | apply mid_bound ].
Qed.

Lemma piece_left1 : forall Hf,
  Cmod (pathint (arc Rc) (arc' Rc)
          (fun z => Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z)) Hf
          (PI / 2) alpha)
  <= 2 * ((4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc)) * Rc)
     * (alpha - PI / 2).
Proof.
  intro Hf; pose proof HPI; apply arc_ML; [ lra | lra | ].
  intros u Hu; apply left_bound; rewrite (Rabs_pos_eq u) by lra; lra.
Qed.

Lemma piece_left2 : forall Hf,
  Cmod (pathint (arc Rc) (arc' Rc)
          (fun z => Cmul (Gdt (Rc + 1) del T HT z) (newman_kernel Rc z)) Hf
          (- alpha) (- (PI / 2)))
  <= 2 * ((4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc)) * Rc)
     * (- (PI / 2) - - alpha).
Proof.
  intro Hf; pose proof HPI; apply arc_ML; [ lra | lra | ].
  intros u Hu; apply left_bound; rewrite (Rabs_left u) by lra; lra.
Qed.

Lemma piece_far :
  Cmod (pathint (arc Rc) (arc' Rc)
          (fun z => Cmul (Wt z) (newman_kernel Rc z)) Hfa_wit alpha (2 * PI - alpha))
  <= 2 * (4 * (Kup + 1) / (Rc * Rc) * Rc) * (2 * PI - alpha - alpha).
Proof.
  pose proof HPI.
  assert (Heq : 2 * PI - alpha - alpha = 2 * PI - alpha - alpha) by reflexivity.
  apply (arc_ML (fun z => Cmul (Wt z) (newman_kernel Rc z)) Rc alpha (2 * PI - alpha)
           (4 * (Kup + 1) / (Rc * Rc)) Hfa_wit); [ lra | lra | apply far_bound ].
Qed.

Lemma piece_chord :
  Cmod (pathint (seg Pc Qc) (seg' Pc Qc)
          (fun z => Cmul (Wg z) (newman_kernel Rc z)) Hcg_wit 0 1)
  <= 2 * (M * exp (- (dl * T)) * (/ dl + / Rc) * Cmod (Cminus Qc Pc)).
Proof.
  apply seg_ML; intros u Hu; apply chord_g_bound; exact Hu.
Qed.

(* ----------------------------------------------------------------- *)
(*  The contour estimate.                                              *)
(* ----------------------------------------------------------------- *)

Theorem newman_bound :
  Cmod (Cminus (gext C0) (LTN C0 0 T (Rle_refl 0) HT)) * (2 * PI)
  <= (24 * PI * (Kup + 1) + 4 * PI * M * dl) / Rc
     + 4 * M * Rc * (/ dl + / Rc) * exp (- (dl * T)).
Proof.
  pose proof HPI as HP; pose proof HB as HBn.
  assert (HMnn : 0 <= M).
  { assert (HR0 : Re C0 = 0) by reflexivity.
    assert (HI0 : Im C0 = 0) by reflexivity.
    eapply Rle_trans; [ apply Cmod_nonneg | apply HM ];
      [ rewrite HR0 | rewrite HI0 ]; rewrite Rabs_R0; lra. }
  assert (Hinvd : 0 < / dl) by (apply Rinv_0_lt_compat; lra).
  assert (HinvR : 0 < / Rc) by (apply Rinv_0_lt_compat; lra).
  assert (HE : 0 < exp (- (dl * T))) by apply exp_pos.
  set (Ha := HfaK_wit Rc del T HRc HT Hptc).
  set (Hc := HfcK_wit Rc dl del T alpha Hdl HT Hchord Hptc).
  pose proof (newman_contour Rc dl del T alpha HRc Hdl Hsmall HT Halpha Hchord
                Hstrip Hagree Hptc Ha Hc) as HID.
  assert (Hmod2 : Cmod (mkC 0 (2 * PI)) = 2 * PI).
  { unfold Cmod, Cnorm2; cbn [Re Im].
    replace (0 * 0 + 2 * PI * (2 * PI)) with (2 * PI * (2 * PI)) by ring.
    apply sqrt_square; lra. }
  rewrite <- Hmod2, <- Cmod_mul, <- HID.
  rewrite (pathint_split (arc Rc) (arc' Rc) _ Ha (- alpha) (- (PI / 2)) alpha).
  rewrite (pathint_split (arc Rc) (arc' Rc) _ Ha (- (PI / 2)) (PI / 2) alpha).
  rewrite chord_split, chord_gT_deform.
  (* five moduli *)
  eapply Rle_trans.
  { eapply Rle_trans; [ apply Cmod_triangle | ]; apply Rplus_le_compat.
    - eapply Rle_trans; [ apply Cmod_triangle | ]; apply Rplus_le_compat.
      + apply piece_left2.
      + eapply Rle_trans; [ apply Cmod_triangle | ]; apply Rplus_le_compat;
          [ apply piece_mid | apply piece_left1 ].
    - replace (Cminus (pathint (seg Pc Qc) (seg' Pc Qc)
                         (fun z => Cmul (Wg z) (newman_kernel Rc z)) Hcg_wit 0 1)
                      (pathint (arc Rc) (arc' Rc)
                         (fun z => Cmul (Wt z) (newman_kernel Rc z)) Hfa_wit
                         alpha (2 * PI - alpha)))
        with (Cadd (pathint (seg Pc Qc) (seg' Pc Qc)
                      (fun z => Cmul (Wg z) (newman_kernel Rc z)) Hcg_wit 0 1)
                   (Copp (pathint (arc Rc) (arc' Rc)
                            (fun z => Cmul (Wt z) (newman_kernel Rc z)) Hfa_wit
                            alpha (2 * PI - alpha)))) by ring.
      eapply Rle_trans; [ apply Cmod_triangle | ]; rewrite Cmod_opp.
      apply Rplus_le_compat; [ apply piece_chord | apply piece_far ]. }
  (* pure arithmetic from here *)
  assert (Hkey : 4 * (4 * (Kup + 1) + 2 * M * dl) * (alpha - PI / 2)
                 + 8 * (Kup + 1) * PI + 8 * (Kup + 1) * (2 * PI - alpha - alpha)
                 <= 24 * PI * (Kup + 1) + 4 * PI * M * dl).
  { assert (HMd : 0 <= M * dl) by (apply Rmult_le_pos; lra).
    assert (Hp : M * dl * (alpha - PI / 2) <= M * dl * (PI / 2))
      by (apply Rmult_le_compat_l; lra).
    nra. }
  assert (Hdiv : forall X Y : R, X <= Y -> X / Rc <= Y / Rc)
    by (intros X Y H; unfold Rdiv; apply Rmult_le_compat_r; [ lra | exact H ]).
  assert (HAeq :
    2 * ((4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc)) * Rc)
      * (- (PI / 2) - - alpha)
    + (2 * (4 * (Kup + 1) / (Rc * Rc) * Rc) * (PI / 2 - - (PI / 2))
       + 2 * ((4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc)) * Rc)
         * (alpha - PI / 2))
    + 2 * (4 * (Kup + 1) / (Rc * Rc) * Rc) * (2 * PI - alpha - alpha)
    = (4 * (4 * (Kup + 1) + 2 * M * dl) * (alpha - PI / 2)
       + 8 * (Kup + 1) * PI + 8 * (Kup + 1) * (2 * PI - alpha - alpha)) / Rc)
    by (field; lra).
  assert (HA :
    2 * ((4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc)) * Rc)
      * (- (PI / 2) - - alpha)
    + (2 * (4 * (Kup + 1) / (Rc * Rc) * Rc) * (PI / 2 - - (PI / 2))
       + 2 * ((4 * (Kup + 1) / (Rc * Rc) + 2 * M * dl / (Rc * Rc)) * Rc)
         * (alpha - PI / 2))
    + 2 * (4 * (Kup + 1) / (Rc * Rc) * Rc) * (2 * PI - alpha - alpha)
    <= (24 * PI * (Kup + 1) + 4 * PI * M * dl) / Rc)
    by (rewrite HAeq; apply Hdiv; exact Hkey).
  assert (HS := Cmod_QP).
  assert (Hii : 2 * (M * exp (- (dl * T)) * (/ dl + / Rc) * Cmod (Cminus Qc Pc))
              <= 4 * M * Rc * (/ dl + / Rc) * exp (- (dl * T))).
  { assert (HMEK : 0 <= M * exp (- (dl * T)) * (/ dl + / Rc))
      by (repeat apply Rmult_le_pos; lra).
    replace (4 * M * Rc * (/ dl + / Rc) * exp (- (dl * T)))
      with (2 * (M * exp (- (dl * T)) * (/ dl + / Rc) * (2 * Rc))) by ring.
    apply Rmult_le_compat_l; [ lra | ].
    apply Rmult_le_compat_l; [ exact HMEK | exact HS ]. }
  lra.
Qed.

End E6.

Print Assumptions newman_bound.

(* ================================================================= *)
(*  END NewmanE6.v -- the contour estimate.  The only T-dependence     *)
(*  left is the chord's e^{-dT}; everything else is O(B/R) + O(Md/R).  *)
(* ================================================================= *)
