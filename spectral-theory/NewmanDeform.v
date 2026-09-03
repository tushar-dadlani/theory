(* ================================================================= *)
(*  NewmanDeform.v  --  the chord slides round to the far-left arc.    *)
(*                                                                    *)
(*  Zagier's estimate of the g_T half of the left contour replaces the *)
(*  chord {Re z = -d} by the far-left arc {|z| = R, Re z <= -d}: both  *)
(*  run from Pc to Qc, and g_T e^{zT} K_R is holomorphic on the region *)
(*  between them, which is {|z| <= R, Re z <= -d} -- convex, and       *)
(*  crucially NOT containing the kernel's pole at 0.                   *)
(*                                                                    *)
(*  This matters because the chord bound for g_T is O(B R / d^2): no   *)
(*  cancellation is available there, whereas on the circle             *)
(*  |K_R| = 2|Re z|/R^2 cancels the 1/|Re z| in the g_T tail bound and *)
(*  gives the uniform 4B/R^2.                                         *)
(*                                                                    *)
(*  As in CTruncKernel, the deformation is NOT pathint_loop_conv (two  *)
(*  parametrised pieces, not one closed gam): PrimC is a primitive on  *)
(*  the region and pathint_FTC evaluates both paths at the same two    *)
(*  endpoints.  NewmanKernelCut.Kcut supplies the global continuity    *)
(*  PrimC insists on.                                                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CIntegral2 CSegInt CPathIntegral CPathFTC CPrimConv CGoursat
        CTruncWind CTruncCauchy CNewmanKernel CTruncKernel
        NewmanCutoff NewmanContour NewmanKernelCut.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The deformation region: a disc cut by a half-plane on the LEFT.    *)
(* ----------------------------------------------------------------- *)

Definition LeftDisk (Rr h : R) (z : C) : Prop := Cmod z < Rr /\ Re z < - h.

Lemma LeftDisk_convex : forall Rr h, Convex (LeftDisk Rr h).
Proof.
  intros Rr h a b [Ham Har] [Hbm Hbr] s Hs; split.
  - pose proof (seg_convex_bound a b C0 s Hs) as HB.
    rewrite !CTruncDisk.Cminus_C0_r in HB.
    eapply Rle_lt_trans; [ exact HB | apply Rmax_lub_lt; assumption ].
  - rewrite CTruncDisk.Re_seg; destruct Hs as [Hs0 Hs1].
    destruct (Req_dec s 0) as [Hs_eq | Hs_ne].
    + subst s; lra.
    + assert (0 < s * (- h - Re b)) by (apply Rmult_lt_0_compat; lra).
      assert (0 <= (1 - s) * (- h - Re a)) by (apply Rmult_le_pos; lra).
      nra.
Qed.

Lemma LeftDisk_open : forall Rr h, Open (LeftDisk Rr h).
Proof.
  intros Rr h z [Hmod Hre].
  exists (Rmin (Rr - Cmod z) (- h - Re z)); split.
  - apply Rmin_pos; lra.
  - intros w Hw; split.
    + rewrite <- (CTruncDisk.Cadd_diff z w).
      eapply Rle_lt_trans; [ apply Cmod_triangle | ].
      apply Rlt_le_trans with (Cmod z + (Rr - Cmod z)); [ | lra ].
      apply Rplus_lt_compat_l.
      eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ].
    + assert (HR : Rabs (Re (Cminus w z)) <= Cmod (Cminus w z))
        by apply CTruncDisk.Rabs_Re_le_Cmod.
      assert (Hlt : Cmod (Cminus w z) < - h - Re z)
        by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
      rewrite CTruncDisk.Re_Cminus in HR.
      assert (HR2 : Rabs (Re w - Re z) < - h - Re z)
        by (eapply Rle_lt_trans; [ exact HR | exact Hlt ]).
      apply Rabs_def2 in HR2; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Trigonometric bookkeeping for the far end of the arc.              *)
(* ----------------------------------------------------------------- *)

Lemma cos_2PI_minus : forall u, cos (2 * PI - u) = cos u.
Proof.
  intro u; rewrite cos_minus, cos_2PI, sin_2PI; ring.
Qed.

Lemma sin_2PI_minus : forall u, sin (2 * PI - u) = - sin u.
Proof.
  intro u; rewrite sin_minus, cos_2PI, sin_2PI; ring.
Qed.

Lemma cos_le_far : forall alpha u, PI / 2 < alpha < PI ->
  alpha <= u <= 2 * PI - alpha -> cos u <= cos alpha.
Proof.
  intros alpha u Halpha Hu; assert (HPI := PI_RGT_0).
  assert (Hmono : forall v, alpha <= v <= PI -> cos v <= cos alpha).
  { intros v Hv; destruct (Rle_lt_or_eq_dec alpha v (proj1 Hv)) as [Hlt | Heq];
      [ left; apply cos_decreasing_1; lra | rewrite <- Heq; apply Rle_refl ]. }
  destruct (Rle_dec u PI) as [Hle | Hgt].
  - apply Hmono; lra.
  - rewrite <- (cos_2PI_minus u); apply Hmono; lra.
Qed.

(* ================================================================= *)
Section Deform.

Variables (Rr d alpha : R).
Hypothesis HR : 0 < Rr.
Hypothesis Hd : 0 < d.
Hypothesis Halpha : PI / 2 < alpha < PI.
Hypothesis Hchord : Rr * cos alpha = - d.

Let Pc : C := mkC (Rr * cos alpha) (Rr * sin alpha).
Let Qc : C := mkC (Rr * cos alpha) (- (Rr * sin alpha)).
Let V : C -> Prop := LeftDisk (Rr + 1) (d / 2).

Variable W : C -> C.
Hypothesis HWc : CcontC W.
Hypothesis HWholo : forall z, exists e, is_Cderiv W z e.

Lemma d_le_Rr : d <= Rr.
Proof.
  pose proof (COS_bound alpha) as [Hlo Hhi].
  assert (Hm : Rr * cos alpha >= Rr * (-1)) by (apply Rmult_ge_compat_l; lra).
  lra.
Qed.

Let G (z : C) : C := Cmul (W z) (Kcut Rr d z).

Lemma G_CcontC : CcontC G.
Proof. unfold G; apply CcontC_mul; [ exact HWc | apply Kcut_CcontC; exact Hd ]. Qed.

Lemma G_holo : forall z, V z -> exists e, is_Cderiv G z e.
Proof.
  intros z [Hm Hr].
  assert (Hbig : d / 2 < Cmod z).
  { assert (HA : Rabs (Re z) <= Cmod z) by apply CTruncDisk.Rabs_Re_le_Cmod.
    unfold Rabs in HA; destruct (Rcase_abs (Re z)); lra. }
  destruct (HWholo z) as [e1 He1].
  destruct (Kcut_holo Rr d z Hd Hbig) as [e2 He2].
  eexists; unfold G; apply Cderiv_mul; [ exact He1 | exact He2 ].
Qed.

Lemma V_base : V (mkC (- Rr) 0).
Proof.
  pose proof d_le_Rr; unfold V, LeftDisk; split; cbn [Re].
  - assert (HM : Cmod (mkC (- Rr) 0) = Rr).
    { unfold Cmod, Cnorm2; cbn [Re Im].
      replace (- Rr * - Rr + 0 * 0) with (Rr * Rr) by ring.
      apply sqrt_square; lra. }
    rewrite HM; lra.
  - lra.
Qed.

Lemma V_arc : forall u, alpha <= u <= 2 * PI - alpha -> V (arc Rr u).
Proof.
  intros u Hu; unfold V, LeftDisk; split.
  - rewrite Cmod_arc by lra; lra.
  - cbn [Re arc].
    assert (Hcu := cos_le_far alpha u Halpha Hu).
    assert (Hmul : Rr * cos u <= Rr * cos alpha)
      by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

Lemma V_chord : forall s, 0 <= s <= 1 -> V (seg Pc Qc s).
Proof.
  intros s [Hs0 Hs1]; unfold V, LeftDisk, Pc, Qc; rewrite seg_chord.
  assert (Hsc := sin2_cos2 alpha); unfold Rsqr in Hsc.
  split; cbn [Re Im]; [ | lra ].
  assert (HRR : sqrt ((Rr + 1) * (Rr + 1)) = Rr + 1) by (apply sqrt_square; lra).
  assert (Hsp : 0 <= s * (1 - s)) by (apply Rmult_le_pos; lra).
  assert (Hb : (1 - 2 * s) * (1 - 2 * s) <= 1) by lra.
  pose proof (Rle_0_sqr (Rr * cos alpha)) as Hq1.
  pose proof (Rle_0_sqr (Rr * sin alpha)) as Hq2.
  pose proof (Rle_0_sqr (Rr * sin alpha * (1 - 2 * s))) as Hq3.
  unfold Rsqr in Hq1, Hq2, Hq3.
  assert (Hkey : Rr * cos alpha * (Rr * cos alpha)
               + Rr * sin alpha * (1 - 2 * s) * (Rr * sin alpha * (1 - 2 * s))
               <= Rr * Rr).
  { replace (Rr * sin alpha * (1 - 2 * s) * (Rr * sin alpha * (1 - 2 * s)))
      with (Rr * sin alpha * (Rr * sin alpha) * ((1 - 2 * s) * (1 - 2 * s))) by ring.
    assert (Hmm : Rr * sin alpha * (Rr * sin alpha) * ((1 - 2 * s) * (1 - 2 * s))
                <= Rr * sin alpha * (Rr * sin alpha) * 1)
      by (apply Rmult_le_compat_l; assumption).
    nra. }
  unfold Cmod, Cnorm2; cbn [Re Im].
  rewrite <- HRR; apply sqrt_lt_1_alt; split; lra.
Qed.

(* ---- endpoints ---- *)
Lemma arc_far_end : arc Rr (2 * PI - alpha) = Qc.
Proof.
  unfold Qc, arc; rewrite cos_2PI_minus, sin_2PI_minus.
  apply Ceq; cbn; ring.
Qed.

(* ---- both paths avoid the cut disc, so Kcut = newman_kernel there ---- *)
Lemma Kcut_on_arc : forall u, alpha <= u <= 2 * PI - alpha ->
  Kcut Rr d (arc Rr u) = newman_kernel Rr (arc Rr u).
Proof.
  intros u Hu; pose proof d_le_Rr; apply Kcut_eq; [ exact Hd | ].
  rewrite Cmod_arc by lra; lra.
Qed.

Lemma Kcut_on_chord : forall s,
  Kcut Rr d (seg Pc Qc s) = newman_kernel Rr (seg Pc Qc s).
Proof.
  intro s; apply Kcut_eq; [ exact Hd | ].
  assert (HA : Rabs (Re (seg Pc Qc s)) <= Cmod (seg Pc Qc s))
    by apply CTruncDisk.Rabs_Re_le_Cmod.
  assert (HRe : Re (seg Pc Qc s) = Rr * cos alpha)
    by (unfold Pc, Qc; rewrite seg_chord; reflexivity).
  rewrite HRe, Hchord in HA.
  unfold Rabs in HA; destruct (Rcase_abs (- d)); lra.
Qed.

(* ---- the deformation ---- *)
Theorem chord_to_arc :
  forall (Hfc : Ccont (fun u => Cmul (Cmul (W (seg Pc Qc u))
                                           (newman_kernel Rr (seg Pc Qc u)))
                                     (seg' Pc Qc u)))
         (Hfa : Ccont (fun u => Cmul (Cmul (W (arc Rr u))
                                           (newman_kernel Rr (arc Rr u)))
                                     (arc' Rr u))),
  pathint (seg Pc Qc) (seg' Pc Qc) (fun z => Cmul (W z) (newman_kernel Rr z))
          Hfc 0 1
  = pathint (arc Rr) (arc' Rr) (fun z => Cmul (W z) (newman_kernel Rr z))
            Hfa alpha (2 * PI - alpha).
Proof.
  intros Hfc Hfa; assert (HPI := PI_RGT_0).
  assert (HGc := G_CcontC).
  assert (Hgc : Ccont (fun u => Cmul (G (seg Pc Qc u)) (seg' Pc Qc u)))
    by (apply Ccont_mul; [ apply HGc, Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hga : Ccont (fun u => Cmul (G (arc Rr u)) (arc' Rr u)))
    by (apply Ccont_mul; [ apply HGc, Ccont_arc | apply Ccont_arc' ]).
  assert (HH : forall z, V z -> is_Cderiv (PrimC G HGc (mkC (- Rr) 0)) z (G z))
    by (intros z HVz;
        exact (PrimC_deriv V (LeftDisk_convex (Rr + 1) (d / 2))
                 (LeftDisk_open (Rr + 1) (d / 2)) G HGc G_holo
                 (mkC (- Rr) 0) V_base z HVz)).
  (* each path is evaluated by the primitive at its endpoints *)
  assert (Ichord : pathint (seg Pc Qc) (seg' Pc Qc) G Hgc 0 1
                 = Cminus (PrimC G HGc (mkC (- Rr) 0) Qc)
                          (PrimC G HGc (mkC (- Rr) 0) Pc)).
  { rewrite (pathint_FTC (PrimC G HGc (mkC (- Rr) 0)) G (seg Pc Qc) (seg' Pc Qc)
               Hgc 0 1 ltac:(lra)
               (fun s Hs => HH _ (V_chord s Hs))
               (fun s _ => chord_Re_deriv Pc Qc s)
               (fun s _ => chord_Im_deriv Pc Qc s)).
    rewrite seg_at0, seg_at1; reflexivity. }
  assert (Iarc : pathint (arc Rr) (arc' Rr) G Hga alpha (2 * PI - alpha)
               = Cminus (PrimC G HGc (mkC (- Rr) 0) Qc)
                        (PrimC G HGc (mkC (- Rr) 0) Pc)).
  { rewrite (pathint_FTC (PrimC G HGc (mkC (- Rr) 0)) G (arc Rr) (arc' Rr)
               Hga alpha (2 * PI - alpha) ltac:(lra)
               (fun s Hs => HH _ (V_arc s Hs))
               (fun s _ => arc_Re_deriv Rr s)
               (fun s _ => arc_Im_deriv Rr s)).
    rewrite arc_far_end.
    assert (Hpa : arc Rr alpha = Pc) by reflexivity.
    rewrite Hpa; reflexivity. }
  (* and G is the honest integrand on both paths *)
  unfold pathint.
  rewrite (Cintf_ext
             (fun u => Cmul (Cmul (W (seg Pc Qc u)) (newman_kernel Rr (seg Pc Qc u)))
                            (seg' Pc Qc u))
             (fun u => Cmul (G (seg Pc Qc u)) (seg' Pc Qc u)) Hfc Hgc 0 1);
    [ | intro u; unfold G; rewrite Kcut_on_chord; ring ].
  rewrite (Cintf_ext
             (fun u => Cmul (Cmul (W (arc Rr u)) (newman_kernel Rr (arc Rr u)))
                            (arc' Rr u))
             (fun u => Cmul (G (arc Rr u)) (arc' Rr u)) Hfa Hga
             alpha (2 * PI - alpha));
    [ | intro u; unfold G; rewrite Kcut_eq;
        [ ring | exact Hd | rewrite Cmod_arc by lra; pose proof d_le_Rr; lra ] ].
  change (pathint (seg Pc Qc) (seg' Pc Qc) G Hgc 0 1
          = pathint (arc Rr) (arc' Rr) G Hga alpha (2 * PI - alpha)).
  rewrite Ichord, Iarc; reflexivity.
Qed.

End Deform.

Print Assumptions chord_to_arc.

(* ================================================================= *)
(*  END NewmanDeform.v -- the chord and the far-left arc give the same *)
(*  integral for any entire W against Zagier's kernel.                 *)
(* ================================================================= *)
