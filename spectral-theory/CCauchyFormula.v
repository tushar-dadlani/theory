(* ================================================================= *)
(*  CCauchyFormula.v  —  Milestone C, brick C2d: Cauchy's integral      *)
(*  formula on a circle,  ∮_{|z|=R} F(z)/z dz = 2πi·F(0).                *)
(*                                                                    *)
(*  Mean-value route: M(r) := ∫₀^{2π} F(arc r θ)dθ is constant because   *)
(*  M'(r) = (1/ir)∮_{|z|=r}F' = 0 (Block 2), so M(R)=M(0)=2πF(0).        *)
(*  Blocks 1 (reduction) + 4 (Leibniz, CLeibniz) + 5 (MVT) assembled.    *)
(*                                                                    *)
(*  The 2D uniform continuity of F'∘arc (Harc_uc) is a section          *)
(*  hypothesis, discharged axiom-clean in CUnifCont.v.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CPathFTC CSegInt CGoursatFTC CGoursatML CGoursatLin
        Holomorphic CHoloCalculus CWinding CMeanValue CLeibniz CPrimitive CGoursat.
Open Scope R_scope.

(* ---- small field / geometry helpers ---- *)
Lemma Cmul_eq0_l : forall a b, a <> C0 -> Cmul a b = C0 -> b = C0.
Proof.
  intros a b Ha H.
  assert (K : Cmul (Cinv a) a = C1) by (apply Cinv_l; exact Ha).
  assert (Hb : b = Cmul (Cmul (Cinv a) a) b) by (rewrite K; ring).
  rewrite Hb.
  replace (Cmul (Cmul (Cinv a) a) b) with (Cmul (Cinv a) (Cmul a b)) by ring.
  rewrite H; ring.
Qed.

Lemma RtoC_neq0 : forall r, r <> 0 -> RtoC r <> C0.
Proof.
  intros r Hr Hc; apply Hr; change 0 with (Re C0); rewrite <- Hc; reflexivity.
Qed.

Lemma Ci_neq0 : Ci <> C0.
Proof. intro Hc; assert (H := f_equal Im Hc); cbn in H; lra. Qed.

Lemma Ccont_cossin : Ccont (fun t => mkC (cos t) (sin t)).
Proof. split; [ apply continuity_cos | apply continuity_sin ]. Qed.

Lemma Cmod_cossin : forall t, Cmod (mkC (cos t) (sin t)) = 1.
Proof.
  intro t; unfold Cmod, Cnorm2; cbn.
  rewrite <- (sqrt_1); f_equal; pose proof (sin2_cos2 t); unfold Rsqr in *; nra.
Qed.

Lemma arc_diff : forall r r0 t,
  Cminus (arc r t) (arc r0 t) = Cmul (RtoC (r - r0)) (mkC (cos t) (sin t)).
Proof. intros; unfold arc, Cminus, Cmul, RtoC; apply Ceq; cbn; ring. Qed.

Lemma seg_arc : forall r r0 t s,
  seg (arc r0 t) (arc r t) s = arc (r0 + s * (r - r0)) t.
Proof. intros; unfold seg, arc, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

Section Cauchy.
Variable F Fp : C -> C.
Variable HF : CcontC F.
Variable HFp : CcontC Fp.
Hypothesis HFhol : forall z, is_Cderiv F z (Fp z).
(* 2D uniform continuity of Fp∘arc, uniform in θ over [0,2π] (CUnifCont) *)
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

(* ---- Block 4 input: the uniform first-order estimate via seg-FTC ---- *)
Lemma Fdphi_unif : forall r0 eps, 0 < eps -> exists del, 0 < del /\
  forall r t, 0 <= t <= 2 * PI -> Rabs (r - r0) < del ->
    Cmod (Cminus (Cminus (Fphi r t) (Fphi r0 t)) (Cmul (Fdphi r0 t) (RtoC (r - r0))))
    <= eps * Rabs (r - r0).
Proof.
  intros r0 eps Heps.
  destruct (Harc_uc r0 (eps / 2) ltac:(lra)) as [del [Hdel Huc]].
  exists del; split; [ exact Hdel | ]; intros r t Ht Hr.
  unfold Fphi, Fdphi.
  rewrite <- (seg_FTC F Fp HFp (arc r0 t) (arc r t) HFhol).
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
      | rewrite Rmult_1_l; exact Hr ]. }
  rewrite arc_diff, Cmod_mul, Cmod_RtoC, Cmod_cossin.
  apply Req_le; field.
Qed.

(* ---- Block 4: M is (componentwise) differentiable, M' = Mder ---- *)
Lemma M_deriv : forall r0,
  derivable_pt_lim (fun r => Re (M r)) r0 (Re (Mder r0))
  /\ derivable_pt_lim (fun r => Im (M r)) r0 (Im (Mder r0)).
Proof.
  intro r0.
  apply (leibniz_deriv Fphi Fdphi 0 (2 * PI) r0 ltac:(generalize PI_RGT_0; lra)
           (fun r => HF (arc r) (Ccont_arc r)) (Hdphi_cont r0) (Fdphi_unif r0)).
Qed.

(* ---- Block 2 ⇒ M'(r) = 0 for r > 0 ---- *)
Lemma Mder_zero : forall r, 0 < r -> Mder r = C0.
Proof.
  intros r Hr.
  assert (Hcirc : Cmul (RtoC r) (Cmul Ci (Mder r)) = C0).
  { unfold Mder.
    rewrite <- (Cintf_cmul_l Ci (fun t => Fdphi r t) (Hdphi_cont r)
                 (Ccont_scal _ _ (Hdphi_cont r)) 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
    rewrite <- (Cintf_cmul_l (RtoC r) (fun t => Cmul Ci (Fdphi r t))
                 (Ccont_scal _ _ (Hdphi_cont r))
                 (Ccont_scal _ _ (Ccont_scal _ _ (Hdphi_cont r)))
                 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
    rewrite <- (circint_Fp_zero F Fp HFhol r
                 (Ccont_mul _ _ (HFp (arc r) (Ccont_arc r)) (Ccont_arc' r))).
    unfold pathint. apply Cintf_ext; intro u.
    unfold Fdphi, arc'; apply Ceq; cbn; ring. }
  apply (Cmul_eq0_l Ci); [ apply Ci_neq0 | ].
  apply (Cmul_eq0_l (RtoC r)); [ apply RtoC_neq0; lra | exact Hcirc ].
Qed.

(* ---- Block 5: M is constant on [0,R] (MVT) ---- *)
Lemma M_const : forall R, 0 < R -> M R = M 0.
Proof.
  intros R HR; apply Ceq.
  - destruct (MVT_cor2 (fun r => Re (M r)) (fun r => Re (Mder r)) 0 R HR
               (fun c _ => proj1 (M_deriv c))) as [c [Hc [Hc0 HcR]]].
    assert (Re (Mder c) = 0)
      by (rewrite (Mder_zero c Hc0); reflexivity).
    rewrite H in Hc; lra.
  - destruct (MVT_cor2 (fun r => Im (M r)) (fun r => Im (Mder r)) 0 R HR
               (fun c _ => proj2 (M_deriv c))) as [c [Hc [Hc0 HcR]]].
    assert (Im (Mder c) = 0)
      by (rewrite (Mder_zero c Hc0); reflexivity).
    rewrite H in Hc; lra.
Qed.

(* ---- Block 1: reduction + endpoints ---- *)
Lemma meanval0 : M 0 = Cmul (RtoC (2 * PI)) (F C0).
Proof.
  unfold M.
  transitivity (Cintf (fun _ => F C0) (Ccont_const (F C0)) 0 (2 * PI)).
  - apply Cintf_ext; intro u; unfold Fphi.
    replace (arc 0 u) with C0 by (unfold arc, C0; apply Ceq; cbn; ring); reflexivity.
  - rewrite Cintf_const_ab; replace (2 * PI - 0) with (2 * PI) by ring; reflexivity.
Qed.

Lemma winding_F_over_z : forall (R : R) (Hr : 0 < R)
  (Hpf : Ccont (fun u => Cmul (Cmul (F (arc R u)) (Cinv (arc R u))) (arc' R u))),
  pathint (arc R) (arc' R) (fun z => Cmul (F z) (Cinv z)) Hpf 0 (2 * PI)
  = Cmul Ci (M R).
Proof.
  intros R Hr Hpf; unfold pathint, M.
  transitivity (Cintf (fun u => Cmul Ci (Fphi R u))
                  (Ccont_scal Ci (fun u => Fphi R u) (HF (arc R) (Ccont_arc R))) 0 (2 * PI)).
  - apply Cintf_ext; intro u; unfold Fphi.
    rewrite <- (arc_over_id R u Hr); ring.
  - apply (Cintf_cmul_l Ci (fun u => Fphi R u) (HF (arc R) (Ccont_arc R))
             (Ccont_scal Ci (fun u => Fphi R u) (HF (arc R) (Ccont_arc R)))
             0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
Qed.

Theorem cauchy_integral_formula : forall (R : R) (Hr : 0 < R)
  (Hpf : Ccont (fun u => Cmul (Cmul (F (arc R u)) (Cinv (arc R u))) (arc' R u))),
  pathint (arc R) (arc' R) (fun z => Cmul (F z) (Cinv z)) Hpf 0 (2 * PI)
  = Cmul (mkC 0 (2 * PI)) (F C0).
Proof.
  intros R Hr Hpf.
  rewrite (winding_F_over_z R Hr Hpf), (M_const R Hr), meanval0.
  replace (Cmul Ci (Cmul (RtoC (2 * PI)) (F C0)))
     with (Cmul (Cmul Ci (RtoC (2 * PI))) (F C0)) by ring.
  replace (Cmul Ci (RtoC (2 * PI))) with (mkC 0 (2 * PI))
     by (unfold Ci, RtoC, Cmul; apply Ceq; cbn; ring).
  reflexivity.
Qed.

End Cauchy.

Print Assumptions cauchy_integral_formula.

(* ================================================================= *)
(*  END CCauchyFormula.v  —  Cauchy's integral formula on a circle.     *)
(* ================================================================= *)
