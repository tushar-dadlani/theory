(* ================================================================= *)
(*  CAnalyticTowerF.v  (identity-theorem plan, FE chain brick 3/4)      *)
(*                                                                    *)
(*  The derivative tower, specialised to a holomorphic F on the         *)
(*  |z| < Rr+1 disk.  The defining property: fseq 0 = F, i.e. the        *)
(*  Cauchy representation  (1/2 pi i) oint F(z)/(z-w) dz = F(w)          *)
(*  (cauchy_interior_dom), packaged through the origin clamp.  With      *)
(*  fseq_chain (fseq (S k) = (fseq k)') this exhibits F's all-orders     *)
(*  holomorphic derivative tower -- the holomorphic => analytic step.    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Factorial FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral CLeibniz RootsOfUnity CWindingOffCenter CCauchyAnalytic
        CRemovableExtDom CFEChainCont CTaylor CAnalyticTower.
Open Scope R_scope.

Lemma Cpow1 : forall x : C, Cpow x 1 = x.
Proof. intro x; cbn; ring. Qed.

Theorem fseq0_eq :
  forall (F : C -> C) (Rr : R) (HR : 0 < Rr) (HFc : CcontC F)
    (HFptc : forall z eps, 0 < eps -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps)
    (HFhol : forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv F z d),
  forall w, Cmod w < Rr / 2 -> fseq F Rr HR HFc 0 w = F w.
Proof.
  intros F Rr HR HFc HFptc HFhol w Hw.
  pose proof (Cmod_nonneg w) as Hcw.
  assert (HwR : Cmod w < Rr) by lra.
  assert (Harc : forall u, Cminus (arc Rr u) w <> C0)
    by (apply arc_ne_pt; [ exact HR | exact HwR ]).
  assert (Hcl : clampw Rr C0 w = w).
  { apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
    replace (Cminus w C0) with w by ring. lra. }
  assert (Hpc : Ccont (fun u => Cmul (Cmul (F (arc Rr u))
                        (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))).
  { assert (Hfe : (fun u => Cmul (Cmul (F (arc Rr u))
                        (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))
                  = Kwn F Rr 1 w).
    { apply functional_extensionality; intro u; unfold Kwn; rewrite Cpow1; reflexivity. }
    rewrite Hfe. apply (Kwn_cont F Rr 1 HFc w Harc). }
  assert (HPsi : Psi F Rr HR HFc 1 w = Cmul (mkC 0 (2 * PI)) (F w)).
  { unfold Psi, PhiN.
    transitivity (Cintf (fun u => Cmul (Cmul (F (arc Rr u))
                    (Cinv (Cminus (arc Rr u) w))) (arc' Rr u)) Hpc 0 (2 * PI)).
    - apply Cintf_ext. intro u. unfold Kwn. rewrite Hcl, Cpow1. reflexivity.
    - change (Cintf (fun u => Cmul (Cmul (F (arc Rr u))
                (Cinv (Cminus (arc Rr u) w))) (arc' Rr u)) Hpc 0 (2 * PI))
        with (pathint (arc Rr) (arc' Rr)
                (fun z => Cmul (F z) (Cinv (Cminus z w))) Hpc 0 (2 * PI)).
      destruct (HFhol w ltac:(lra)) as [dw Hdw].
      apply (cauchy_interior_dom F Rr w dw HR HwR Hdw HFptc
               (fun z Hz (_ : z <> w) => HFhol z Hz)). }
  unfold fseq.
  assert (H1 : RtoC (INR (fact 0)) = C1)
    by (change (fact 0) with 1%nat; rewrite INR_1; apply Ceq; reflexivity).
  rewrite H1, Cmul_1_l.
  change (Psi F Rr HR HFc (S 0)) with (Psi F Rr HR HFc 1).
  rewrite HPsi.
  assert (HXne : mkC 0 (2 * PI) <> C0)
    by (intro Hc; apply (f_equal Im) in Hc; cbn in Hc; generalize PI_RGT_0; lra).
  unfold cc. field. exact HXne.
Qed.

Print Assumptions fseq0_eq.

(* ================================================================= *)
(*  Per-level continuity (Fptc): each fseq k is pointwise continuous   *)
(*  everywhere, since Psi (S k) is (PhiN_ptcont_uncond) and fseq k is   *)
(*  a fixed scalar multiple of it.                                     *)
(* ================================================================= *)

Lemma scal_eps : forall B X eps, 0 <= B -> 0 <= X -> 0 < eps ->
  X < eps / (B + 1) -> B * X < eps.
Proof.
  intros B X eps HB HX He HX'.
  assert (HB1 : 0 < B + 1) by lra.
  apply Rle_lt_trans with (B * (eps / (B + 1))).
  - apply Rmult_le_compat_l; [ exact HB | lra ].
  - apply (Rmult_lt_reg_r (B + 1)); [ exact HB1 | ].
    replace (B * (eps / (B + 1)) * (B + 1)) with (B * eps) by (field; lra).
    nra.
Qed.

Theorem fseq_cont : forall (g : C -> C) (Rr : R) (HR : 0 < Rr) (Hg : CcontC g)
  (Mg : R), (forall u, Cmod (g (arc Rr u)) <= Mg) ->
  forall k w2 eps, 0 < eps -> exists del, 0 < del /\
    forall w, Cmod (Cminus w w2) < del ->
      Cmod (Cminus (fseq g Rr HR Hg k w) (fseq g Rr HR Hg k w2)) < eps.
Proof.
  intros g Rr HR Hg Mg Hgb k w2 eps Heps.
  assert (H0R' : Cmod C0 < Rr)
    by (rewrite (proj2 (Cmod0 C0) eq_refl); exact HR).
  destruct (PhiN_ptcont_uncond g Rr C0 k HR H0R' Hg Mg Hgb w2
              (eps / (Cmod (Cmul (RtoC (INR (fact k))) cc) + 1))
              ltac:(apply Rdiv_lt_0_compat;
                    [ exact Heps | pose proof (Cmod_nonneg (Cmul (RtoC (INR (fact k))) cc)); lra ]))
    as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros w Hw.
  assert (HPsiP : forall x, Psi g Rr HR Hg (S k) x = PhiN g Rr C0 (S k) HR H0R' Hg x)
    by (intro x; unfold Psi, PhiN; apply Cintf_irrel).
  assert (Heq : Cminus (fseq g Rr HR Hg k w) (fseq g Rr HR Hg k w2)
    = Cmul (Cmul (RtoC (INR (fact k))) cc)
           (Cminus (PhiN g Rr C0 (S k) HR H0R' Hg w)
                   (PhiN g Rr C0 (S k) HR H0R' Hg w2))).
  { unfold fseq. rewrite !HPsiP. ring. }
  rewrite Heq, Cmod_mul.
  apply scal_eps;
    [ apply Cmod_nonneg | apply Cmod_nonneg | exact Heps | apply (Hc w Hw) ].
Qed.

Print Assumptions fseq_cont.

(* ================================================================= *)
(*  Circle bounds (Hbd): on a circle of radius Re < Rr/2, every level  *)
(*  fseq k is bounded, via the Cauchy ML estimate on Psi (S k)         *)
(*  (|Psi(S k)(z)| <= 2 . (Mg . Rr / (Rr-Re)^(S k)) . 2 pi).           *)
(* ================================================================= *)

Theorem fseq_bd : forall (g : C -> C) (Rr Re : R) (HR : 0 < Rr) (Hg : CcontC g)
  (Mg : R), 0 <= Mg -> (forall u, Cmod (g (arc Rr u)) <= Mg) ->
  0 <= Re -> Re < Rr / 2 ->
  forall k, exists Mf, 0 <= Mf /\
    forall u, Cmod (fseq g Rr HR Hg k (arc Re u)) <= Mf.
Proof.
  intros g Rr Re HR Hg Mg HMg Hgb HRe0 HRe k.
  assert (Hdpos : 0 < Rr - Re) by lra.
  set (P := Mg * / (Rr - Re) ^ (S k) * Rr).
  assert (HP0 : 0 <= P).
  { unfold P. apply Rmult_le_pos; [ | lra ].
    apply Rmult_le_pos; [ exact HMg | ].
    left; apply Rinv_0_lt_compat; apply pow_lt; exact Hdpos. }
  assert (Hpi : 0 <= 2 * PI) by (generalize PI_RGT_0; lra).
  exists (INR (fact k) * Cmod cc * (2 * P * (2 * PI))).
  split.
  { apply Rmult_le_pos; [ apply Rmult_le_pos; [ apply pos_INR | apply Cmod_nonneg ] | ].
    apply Rmult_le_pos; [ lra | exact Hpi ]. }
  intros u. set (z := arc Re u).
  assert (Hzmod : Cmod z = Re) by (unfold z; apply Cmod_arc; lra).
  assert (HzR : Cmod z < Rr) by lra.
  assert (Hclz : clampw Rr C0 z = z).
  { apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
    replace (Cminus z C0) with z by ring. lra. }
  assert (HPsibd : Cmod (Psi g Rr HR Hg (S k) z) <= 2 * P * (2 * PI)).
  { replace (2 * P * (2 * PI)) with (2 * P * (2 * PI - 0)) by ring.
    unfold Psi, PhiN. apply Cintf_ML; [ exact Hpi | ].
    intros u' _. rewrite Hclz. unfold Kwn.
    rewrite Cmod_mul, Cmod_mul, (Cmod_arc' Rr u' ltac:(lra)).
    assert (Hane : Cminus (arc Rr u') z <> C0)
      by (apply arc_ne_pt; [ exact HR | exact HzR ]).
    assert (Hpne : Cpow (Cminus (arc Rr u') z) (S k) <> C0)
      by (apply Cpow_ne0; exact Hane).
    rewrite (Cmod_inv _ Hpne), Cmod_Cpow.
    assert (Hlb : Rr - Re <= Cmod (Cminus (arc Rr u') z)).
    { eapply Rle_trans; [ | apply Cmod_rev_triangle ].
      rewrite (Cmod_arc Rr u' ltac:(lra)), Hzmod. lra. }
    assert (Hcmpos : 0 < Cmod (Cminus (arc Rr u') z)) by lra.
    unfold P. apply Rmult_le_compat_r; [ lra | ].
    apply Rmult_le_compat.
    - apply Cmod_nonneg.
    - left; apply Rinv_0_lt_compat; apply pow_lt; exact Hcmpos.
    - apply Hgb.
    - apply Rinv_le_contravar; [ apply pow_lt; exact Hdpos | ].
      apply pow_incr; split; [ lra | exact Hlb ]. }
  unfold fseq.
  rewrite Cmod_mul, Cmod_mul, Cmod_RtoC, (Rabs_right (INR (fact k)))
    by (apply Rle_ge, pos_INR).
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l; [ apply pos_INR | ].
  apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
  exact HPsibd.
Qed.

Print Assumptions fseq_bd.
