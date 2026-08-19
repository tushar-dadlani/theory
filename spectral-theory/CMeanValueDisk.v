(* ================================================================= *)
(*  CMeanValueDisk.v  —  disk-cofactor bridge, Stage 2:                  *)
(*  the mean value property for a DISK-holomorphic function.            *)
(*                                                                    *)
(*    M_const_disk : 0 < R -> R < R2 -> M R = M 0                       *)
(*    meanval0_disk : M 0 = 2 PI . F(0)                                 *)
(*                                                                    *)
(*  where M r = INT_0^{2PI} F(arc r t) dt and F is holomorphic only on  *)
(*  the disk `Cmod z < R2` (hypothesis HFhol_disk).  Near-verbatim copy *)
(*  of CCauchyFormula's Section Cauchy chain, with the ONLY two uses of *)
(*  global holomorphy localized:                                       *)
(*   * seg_FTC -> CSegFTCDisk.seg_FTC_disk (radial segment in the disk);*)
(*   * circint_Fp_zero -> pathint_primitive_loop with disk membership   *)
(*     (circle |z|=r in the disk).                                      *)
(*  Domain bookkeeping shrinks the Leibniz neighbourhood to stay in the *)
(*  disk (Cmod_arc_abs).  Axiom-clean.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CPathFTC CSegInt CGoursatFTC CGoursatML CGoursatLin
        Holomorphic CHoloCalculus CWinding CMeanValue CLeibniz CPrimitive CGoursat
        CCauchyFormula CPrimitiveDisk CSegFTCDisk.
Open Scope R_scope.

Lemma Cmod_arc_abs : forall r t, Cmod (arc r t) = Rabs r.
Proof.
  intros r t. unfold Cmod.
  replace (Cnorm2 (arc r t)) with (Rsqr r).
  - apply sqrt_Rsqr_abs.
  - unfold Cnorm2, arc, Re, Im, Rsqr. pose proof (sin2_cos2 t); unfold Rsqr in *. nra.
Qed.

Section MeanValueDisk.
Variable R2 : R.
Hypothesis HR2 : 0 < R2.
Variable F Fp : C -> C.
Variable HF : CcontC F.
Variable HFp : CcontC Fp.
Hypothesis HFhol_disk : forall z, disk R2 z -> is_Cderiv F z (Fp z).
Hypothesis Harc_uc : forall r0 eps, 0 < eps -> exists del, 0 < del /\
  forall rho t, 0 <= t <= 2 * PI -> Rabs (rho - r0) < del ->
    Cmod (Cminus (Fp (arc rho t)) (Fp (arc r0 t))) < eps.

Definition Fphi (r t : R) : C := F (arc r t).
Definition Fdphi (r t : R) : C := Cmul (Fp (arc r t)) (mkC (cos t) (sin t)).

Lemma Hdphi_cont : forall r, Ccont (fun t => Fdphi r t).
Proof.
  intro r; apply Ccont_mul; [ apply (HFp (arc r) (Ccont_arc r)) | apply Ccont_cossin ].
Qed.

Definition M (r : R) : C := Cintf (fun t => Fphi r t) (HF (arc r) (Ccont_arc r)) 0 (2 * PI).
Definition Mder (r : R) : C := Cintf (fun t => Fdphi r t) (Hdphi_cont r) 0 (2 * PI).

Lemma Fdphi_unif_disk : forall r0, 0 <= r0 < R2 -> forall eps, 0 < eps ->
  exists del, 0 < del /\
  forall r t, 0 <= t <= 2 * PI -> Rabs (r - r0) < del ->
    Cmod (Cminus (Cminus (Fphi r t) (Fphi r0 t)) (Cmul (Fdphi r0 t) (RtoC (r - r0))))
    <= eps * Rabs (r - r0).
Proof.
  intros r0 Hr0 eps Heps.
  destruct (Harc_uc r0 (eps / 2) ltac:(lra)) as [del [Hdel Huc]].
  exists (Rmin del (R2 - r0)); split; [ apply Rmin_pos; [ exact Hdel | lra ] | ].
  intros r t Ht Hr.
  assert (Hrdel : Rabs (r - r0) < del) by (eapply Rlt_le_trans; [ exact Hr | apply Rmin_l ]).
  assert (HrR2 : Rabs r < R2).
  { assert (Hr2 : Rabs (r - r0) < R2 - r0) by (eapply Rlt_le_trans; [ exact Hr | apply Rmin_r ]).
    pose proof (Rabs_triang (r - r0) r0) as Ht3.
    replace (r - r0 + r0) with r in Ht3 by ring.
    rewrite (Rabs_pos_eq r0) in Ht3 by lra. lra. }
  assert (Harc0 : disk R2 (arc r0 t))
    by (unfold disk; rewrite Cmod_arc_abs, (Rabs_pos_eq r0) by lra; lra).
  assert (Harcr : disk R2 (arc r t)) by (unfold disk; rewrite Cmod_arc_abs; exact HrR2).
  unfold Fphi, Fdphi.
  rewrite <- (seg_FTC_disk (disk R2) (disk_convex R2) F Fp HFp (arc r0 t) (arc r t)
               Harc0 Harcr HFhol_disk).
  replace (Cmul (Cmul (Fp (arc r0 t)) (mkC (cos t) (sin t))) (RtoC (r - r0)))
     with (Cmul (Fp (arc r0 t)) (Cminus (arc r t) (arc r0 t)))
     by (rewrite arc_diff; ring).
  rewrite <- (seg_int_const (Fp (arc r0 t)) (CcontC_const _) (arc r0 t) (arc r t)).
  rewrite <- (seg_int_sub Fp (fun _ => Fp (arc r0 t)) HFp (CcontC_const _)
               (CcontC_add Fp (fun _ => Copp (Fp (arc r0 t))) HFp
                 (CcontC_opp _ (CcontC_const _))) (arc r0 t) (arc r t)).
  eapply Rle_trans.
  { apply (seg_int_ML (fun z => Cminus (Fp z) (Fp (arc r0 t))) _
             (arc r0 t) (arc r t) (eps / 2)).
    intros s Hs. rewrite seg_arc.
    apply Rlt_le, Huc; [ exact Ht | ].
    replace (r0 + s * (r - r0) - r0) with (s * (r - r0)) by ring.
    rewrite Rabs_mult.
    apply Rle_lt_trans with (1 * Rabs (r - r0));
      [ apply Rmult_le_compat_r;
        [ apply Rabs_pos | rewrite Rabs_pos_eq by lra; lra ]
      | rewrite Rmult_1_l; exact Hrdel ]. }
  rewrite arc_diff, Cmod_mul, Cmod_RtoC, Cmod_cossin.
  apply Req_le; field.
Qed.

Lemma M_deriv_disk : forall r0, 0 <= r0 < R2 ->
  derivable_pt_lim (fun r => Re (M r)) r0 (Re (Mder r0))
  /\ derivable_pt_lim (fun r => Im (M r)) r0 (Im (Mder r0)).
Proof.
  intros r0 Hr0.
  apply (leibniz_deriv Fphi Fdphi 0 (2 * PI) r0 ltac:(generalize PI_RGT_0; lra)
           (fun r => HF (arc r) (Ccont_arc r)) (Hdphi_cont r0) (Fdphi_unif_disk r0 Hr0)).
Qed.

Lemma Mder_zero_disk : forall r, 0 < r -> r < R2 -> Mder r = C0.
Proof.
  intros r Hr HrR2.
  assert (Hcz : pathint (arc r) (arc' r) Fp
                  (Ccont_mul _ _ (HFp (arc r) (Ccont_arc r)) (Ccont_arc' r)) 0 (2 * PI) = C0).
  { apply (pathint_primitive_loop F Fp (arc r) (arc' r) _ 0 (2 * PI)).
    - generalize PI_RGT_0; lra.
    - unfold arc; apply Ceq; cbn; rewrite ?cos_0, ?sin_0, ?cos_2PI, ?sin_2PI; ring.
    - intros s _. apply HFhol_disk. unfold disk.
      rewrite Cmod_arc_abs, (Rabs_pos_eq r) by lra. exact HrR2.
    - intros s _; apply dRe_arc_theta.
    - intros s _; apply dIm_arc_theta. }
  assert (Hcirc : Cmul (RtoC r) (Cmul Ci (Mder r)) = C0).
  { unfold Mder.
    rewrite <- (Cintf_cmul_l Ci (fun t => Fdphi r t) (Hdphi_cont r)
                 (Ccont_scal _ _ (Hdphi_cont r)) 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
    rewrite <- (Cintf_cmul_l (RtoC r) (fun t => Cmul Ci (Fdphi r t))
                 (Ccont_scal _ _ (Hdphi_cont r))
                 (Ccont_scal _ _ (Ccont_scal _ _ (Hdphi_cont r)))
                 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
    rewrite <- Hcz.
    unfold pathint. apply Cintf_ext; intro u.
    unfold Fdphi, arc'; apply Ceq; cbn; ring. }
  apply (Cmul_eq0_l Ci); [ apply Ci_neq0 | ].
  apply (Cmul_eq0_l (RtoC r)); [ apply RtoC_neq0; lra | exact Hcirc ].
Qed.

Lemma M_const_disk : forall R, 0 < R -> R < R2 -> M R = M 0.
Proof.
  intros R HR HRR2; apply Ceq.
  - destruct (MVT_cor2 (fun r => Re (M r)) (fun r => Re (Mder r)) 0 R HR
               (fun c Hc => proj1 (M_deriv_disk c ltac:(lra)))) as [c [Hc [Hc0 HcR]]].
    assert (Hz : Re (Mder c) = 0) by (rewrite (Mder_zero_disk c Hc0 ltac:(lra)); reflexivity).
    rewrite Hz in Hc; lra.
  - destruct (MVT_cor2 (fun r => Im (M r)) (fun r => Im (Mder r)) 0 R HR
               (fun c Hc => proj2 (M_deriv_disk c ltac:(lra)))) as [c [Hc [Hc0 HcR]]].
    assert (Hz : Im (Mder c) = 0) by (rewrite (Mder_zero_disk c Hc0 ltac:(lra)); reflexivity).
    rewrite Hz in Hc; lra.
Qed.

Lemma meanval0_disk : M 0 = Cmul (RtoC (2 * PI)) (F C0).
Proof.
  unfold M.
  transitivity (Cintf (fun _ => F C0) (Ccont_const (F C0)) 0 (2 * PI)).
  - apply Cintf_ext; intro u; unfold Fphi.
    replace (arc 0 u) with C0 by (unfold arc, C0; apply Ceq; cbn; ring); reflexivity.
  - rewrite Cintf_const_ab; replace (2 * PI - 0) with (2 * PI) by ring; reflexivity.
Qed.

End MeanValueDisk.

Print Assumptions M_const_disk.
