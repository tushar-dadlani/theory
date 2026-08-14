(* ================================================================= *)
(*  CScaledDisk.v  (identity-theorem plan, FE chain brick 5 — core)     *)
(*                                                                    *)
(*  The scaled/shifted local zero lemma.  For F holomorphic on {Re>0}   *)
(*  and continuous, if F vanishes on a small disk about z0 (Re z0 > 0)  *)
(*  then F vanishes on the whole disk |z - z0| < eps for any eps with   *)
(*  5 eps < Re z0.  Built by running the derivative tower of            *)
(*  G(w) = F(z0 + eps w) and feeding identity_at_zero_D; the Hvanish     *)
(*  input (all levels vanish at 0) comes from tower_vanish_from_local.   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt CPathIntegral
        PerronRemovable CIdentityZeroDom CDerivUnique CContBounded CCircleBound
        CAnalyticTower CAnalyticTowerF.
Open Scope R_scope.

(* if the base level vanishes near 0, every level vanishes at 0 *)
Lemma tower_vanish_from_local :
  forall (g : C -> C) (Rr : R) (HR : 0 < Rr) (Hg : CcontC g)
    (Hgb : exists Mg, 0 <= Mg /\ forall u, Cmod (g (arc Rr u)) <= Mg)
    (delta : R), 0 < delta ->
    (forall w, Cmod w < delta -> fseq g Rr HR Hg 0 w = C0) ->
    forall k, fseq g Rr HR Hg k C0 = C0.
Proof.
  intros g Rr HR Hg Hgb delta Hd Hbase.
  assert (Hind : forall k, exists dk, 0 < dk /\ dk <= Rr / 2 /\
                   forall w, Cmod w < dk -> fseq g Rr HR Hg k w = C0).
  { induction k as [| k [dk [Hdk [HdkR Hk]]]].
    - exists (Rmin delta (Rr / 2)). split; [ | split ].
      + apply Rmin_glb_lt; [ exact Hd | lra ].
      + apply Rmin_r.
      + intros w Hw. apply Hbase.
        eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ].
    - exists (dk / 2). split; [ lra | split; [ lra | ] ].
      intros w Hw.
      assert (HwR : Cmod w < Rr / 2) by lra.
      pose proof (fseq_chain g Rr HR Hg Hgb k w HwR) as Hchain.
      assert (Hc0 : is_Cderiv (fseq g Rr HR Hg k) w C0).
      { apply (is_Cderiv_congr (fseq g Rr HR Hg k) (fun _ => C0) w C0 (dk / 2)).
        - lra.
        - intros w' Hw'. apply Hk.
          assert (Cmod w' <= Cmod (Cminus w' w) + Cmod w).
          { replace w' with (Cadd (Cminus w' w) w) at 1 by ring.
            apply Cmod_triangle. }
          lra.
        - apply Cderiv_const. }
      exact (is_Cderiv_unique (fseq g Rr HR Hg k) w
               (fseq g Rr HR Hg (S k) w) C0 Hchain Hc0). }
  intro k. destruct (Hind k) as [dk [Hdk [_ Hk]]].
  apply Hk. rewrite (proj2 (Cmod0 C0) eq_refl). exact Hdk.
Qed.

Print Assumptions tower_vanish_from_local.

Lemma Rabs_Re_le_Cmod : forall w, Rabs (Re w) <= Cmod w.
Proof.
  intro w. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Re w)).
  apply sqrt_le_1_alt. unfold Rsqr.
  pose proof (Rle_0_sqr (Im w)) as H. unfold Rsqr in H. nra.
Qed.

(* ================================================================= *)
(*  The scaled/shifted local zero lemma.                              *)
(* ================================================================= *)
Theorem scaled_disk_zero :
  forall (F : C -> C),
    (forall z e, 0 < e -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < e) ->
    CcontC F ->
    (forall z, 0 < Re z -> exists d, is_Cderiv F z d) ->
  forall z0 eps r0, 0 < eps -> 5 * eps < Re z0 -> 0 < r0 ->
    (forall z, Cmod (Cminus z z0) < r0 -> F z = C0) ->
    forall z, Cmod (Cminus z z0) < eps -> F z = C0.
Proof.
  intros F HFptc HFc HFhol z0 eps r0 Heps H5 Hr0 Hzero z Hz.
  assert (HR4 : 0 < 4) by lra.
  set (G := fun w => F (Cadd (Cmul (RtoC eps) w) z0)).
  assert (Hpt : forall w, Cmod w < 5 -> 0 < Re (Cadd (Cmul (RtoC eps) w) z0)).
  { intros w Hw.
    replace (Re (Cadd (Cmul (RtoC eps) w) z0)) with (eps * Re w + Re z0)
      by (unfold Cadd, Cmul, RtoC; cbn [Re Im]; ring).
    pose proof (Rabs_Re_le_Cmod w) as HRe.
    pose proof (Rle_abs (Re w)) as Hra.
    pose proof (Rle_abs (- Re w)) as Hra2. rewrite Rabs_Ropp in Hra2.
    pose proof (Rabs_pos (Re w)). nra. }
  assert (HGc : CcontC G).
  { intros gam Hgam. apply HFc.
    apply Ccont_add; [ apply Ccont_scal; exact Hgam | apply Ccont_const ]. }
  assert (HGhol : forall w, Cmod w < 4 + 1 -> exists d, is_Cderiv G w d).
  { intros w Hw.
    destruct (HFhol (Cadd (Cmul (RtoC eps) w) z0) (Hpt w ltac:(lra))) as [dF HdF].
    exists (Cmul (RtoC eps) dF).
    exact (Cderiv_comp_affine F (RtoC eps) z0 w dF HdF). }
  assert (HGptc : forall zz e, 0 < e -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' zz) < del -> Cmod (Cminus (G z') (G zz)) < e).
  { intros zz e He.
    destruct (HFptc (Cadd (Cmul (RtoC eps) zz) z0) e He) as [del [Hdel Hb]].
    exists (del / eps). split; [ apply Rdiv_lt_0_compat; lra | ].
    intros z' Hz'. unfold G. apply Hb.
    replace (Cminus (Cadd (Cmul (RtoC eps) z') z0) (Cadd (Cmul (RtoC eps) zz) z0))
      with (Cmul (RtoC eps) (Cminus z' zz)) by ring.
    rewrite Cmod_mul, Cmod_RtoC, (Rabs_right eps) by lra.
    apply Rlt_le_trans with (eps * (del / eps));
      [ apply Rmult_lt_compat_l; lra | apply Req_le; field; lra ]. }
  destruct (Ccont_circle_bounded G 4 HGc) as [Mg [HMg HGbd]].
  assert (HGb : exists Mg', 0 <= Mg' /\ forall u, Cmod (G (arc 4 u)) <= Mg')
    by (exists Mg; split; assumption).
  (* base: fseq 0 vanishes near 0 *)
  set (delta := Rmin (r0 / eps) 2).
  assert (Hdelta : 0 < delta)
    by (apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; lra | lra ]).
  assert (Hbase : forall w, Cmod w < delta -> fseq G 4 HR4 HGc 0 w = C0).
  { intros w Hw.
    assert (Hw2 : Cmod w < 4 / 2)
      by (eapply Rlt_le_trans; [ exact Hw | unfold delta; eapply Rle_trans;
          [ apply Rmin_r | lra ] ]).
    rewrite (fseq0_eq G 4 HR4 HGc HGptc HGhol w Hw2). unfold G. apply Hzero.
    replace (Cminus (Cadd (Cmul (RtoC eps) w) z0) z0) with (Cmul (RtoC eps) w) by ring.
    rewrite Cmod_mul, Cmod_RtoC, (Rabs_right eps) by lra.
    apply Rlt_le_trans with (eps * (r0 / eps)).
    - apply Rmult_lt_compat_l; [ lra | ].
      eapply Rlt_le_trans; [ exact Hw | unfold delta; apply Rmin_l ].
    - apply Req_le; field; lra. }
  pose proof (tower_vanish_from_local G 4 HR4 HGc HGb delta Hdelta Hbase) as Hvanish.
  (* identity_at_zero_D at radius 1 *)
  assert (Hhbd : forall k, exists Mf, 0 <= Mf /\ forall u,
            Cmod (fseq G 4 HR4 HGc k (arc 1 u)) <= Mf)
    by (apply (fseq_bd G 4 1 HR4 HGc Mg HMg HGbd); lra).
  pose proof (identity_at_zero_D 1 (fseq G 4 HR4 HGc) ltac:(lra)
                (fun k zz Hzz => fseq_chain G 4 HR4 HGc HGb k zz
                   ltac:(replace (4 / 2) with (1 + 1) by lra; exact Hzz))
                (fseq_cont G 4 HR4 HGc Mg HGbd)
                Hhbd Hvanish) as Hid.
  (* transfer back to F z *)
  set (w := Cmul (RtoC (/ eps)) (Cminus z z0)).
  assert (Hwmod : Cmod w < 1).
  { unfold w. rewrite Cmod_mul, Cmod_RtoC, (Rabs_right (/ eps))
      by (left; apply Rinv_0_lt_compat; lra).
    apply Rlt_le_trans with (/ eps * eps).
    - apply Rmult_lt_compat_l; [ apply Rinv_0_lt_compat; lra | exact Hz ].
    - apply Req_le; field; lra. }
  assert (Hzw : Cadd (Cmul (RtoC eps) w) z0 = z).
  { unfold w.
    replace (Cmul (RtoC eps) (Cmul (RtoC (/ eps)) (Cminus z z0)))
      with (Cminus z z0) by
      (apply Ceq; unfold Cadd, Cmul, RtoC, Cminus, Copp; cbn [Re Im]; field; lra).
    ring. }
  pose proof (Hid w Hwmod) as Hfw.
  assert (Hw2 : Cmod w < 4 / 2) by lra.
  rewrite (fseq0_eq G 4 HR4 HGc HGptc HGhol w Hw2) in Hfw.
  unfold G in Hfw. rewrite Hzw in Hfw. exact Hfw.
Qed.

Print Assumptions scaled_disk_zero.
