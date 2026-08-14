(* ================================================================= *)
(*  CRealDisk.v  (identity-theorem plan, FE chain brick 5 — base case)  *)
(*                                                                    *)
(*  The scaled/shifted REAL-vanishing disk lemma: for F holomorphic on   *)
(*  {Re>0} and continuous, if F vanishes on the real interval            *)
(*  |s - a| < a/2 (a > 0) then F vanishes on the 2D disk |z - a| < a/6.  *)
(*  This turns 1D vanishing (on the positive ray) into a first 2D zero   *)
(*  disk -- the seed the walk propagates.  Same G(w)=F(a+eps w) tower    *)
(*  as scaled_disk_zero, but fed to identity_on_disk_D (real vanishing)  *)
(*  instead of identity_at_zero_D.                                       *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt CPathIntegral
        PerronRemovable CIdentityRealDom CContBounded CCircleBound
        CAnalyticTower CAnalyticTowerF CScaledDisk.
Open Scope R_scope.

Theorem real_disk_zero :
  forall (F : C -> C),
    (forall z e, 0 < e -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < e) ->
    CcontC F ->
    (forall z, 0 < Re z -> exists d, is_Cderiv F z d) ->
  forall a, 0 < a ->
    (forall s, Rabs (s - a) < a / 2 -> F (mkC s 0) = C0) ->
    forall z, Cmod (Cminus z (mkC a 0)) < a / 6 -> F z = C0.
Proof.
  intros F HFptc HFc HFhol a Ha Hreal z Hz.
  assert (HR4 : 0 < 4) by lra.
  set (eps := a / 6).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  set (G := fun w => F (Cadd (Cmul (RtoC eps) w) (mkC a 0))).
  assert (Hpt : forall w, Cmod w < 5 -> 0 < Re (Cadd (Cmul (RtoC eps) w) (mkC a 0))).
  { intros w Hw.
    replace (Re (Cadd (Cmul (RtoC eps) w) (mkC a 0))) with (eps * Re w + a)
      by (unfold Cadd, Cmul, RtoC; cbn [Re Im]; ring).
    pose proof (Rabs_Re_le_Cmod w) as HRe.
    pose proof (Rle_abs (- Re w)) as Hra2. rewrite Rabs_Ropp in Hra2.
    pose proof (Rabs_pos (Re w)). unfold eps in *. nra. }
  assert (HGc : CcontC G).
  { intros gam Hgam. apply HFc.
    apply Ccont_add; [ apply Ccont_scal; exact Hgam | apply Ccont_const ]. }
  assert (HGhol : forall w, Cmod w < 4 + 1 -> exists d, is_Cderiv G w d).
  { intros w Hw.
    destruct (HFhol (Cadd (Cmul (RtoC eps) w) (mkC a 0)) (Hpt w ltac:(lra))) as [dF HdF].
    exists (Cmul (RtoC eps) dF).
    exact (Cderiv_comp_affine F (RtoC eps) (mkC a 0) w dF HdF). }
  assert (HGptc : forall zz e, 0 < e -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' zz) < del -> Cmod (Cminus (G z') (G zz)) < e).
  { intros zz e He.
    destruct (HFptc (Cadd (Cmul (RtoC eps) zz) (mkC a 0)) e He) as [del [Hdel Hb]].
    exists (del / eps). split; [ apply Rdiv_lt_0_compat; lra | ].
    intros z' Hz'. unfold G. apply Hb.
    replace (Cminus (Cadd (Cmul (RtoC eps) z') (mkC a 0))
                    (Cadd (Cmul (RtoC eps) zz) (mkC a 0)))
      with (Cmul (RtoC eps) (Cminus z' zz)) by ring.
    rewrite Cmod_mul, Cmod_RtoC, (Rabs_right eps) by lra.
    apply Rlt_le_trans with (eps * (del / eps));
      [ apply Rmult_lt_compat_l; lra | apply Req_le; field; lra ]. }
  destruct (Ccont_circle_bounded G 4 HGc) as [Mg [HMg HGbd]].
  (* real vanishing of G on |x| < 1 *)
  assert (Hvan0 : forall x, Rabs (x - 0) < 1 ->
            fseq G 4 HR4 HGc 0%nat (mkC x 0) = C0).
  { intros x Hx. rewrite Rminus_0_r in Hx. pose proof (Rabs_pos x).
    assert (Hx2 : Cmod (mkC x 0) < 4 / 2).
    { unfold Cmod, Cnorm2; cbn [Re Im].
      replace (x * x + 0 * 0) with (Rsqr x) by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr_abs. lra. }
    rewrite (fseq0_eq G 4 HR4 HGc HGptc HGhol (mkC x 0) Hx2). unfold G.
    replace (Cadd (Cmul (RtoC eps) (mkC x 0)) (mkC a 0)) with (mkC (a + eps * x) 0)
      by (apply Ceq; unfold Cadd, Cmul, RtoC; cbn [Re Im]; ring).
    apply Hreal.
    replace (a + eps * x - a) with (eps * x) by ring.
    rewrite Rabs_mult, (Rabs_right eps) by lra. unfold eps. nra. }
  assert (Hhbd : forall k, exists Mf, 0 <= Mf /\ forall u,
            Cmod (fseq G 4 HR4 HGc k (Cadd (arc 1 u) (mkC 0 0))) <= Mf).
  { intro k. destruct (fseq_bd G 4 1 HR4 HGc Mg HMg HGbd ltac:(lra) ltac:(lra) k)
      as [Mf [HMf0 HMf]]. exists Mf; split; [ exact HMf0 | ].
    intro u. replace (Cadd (arc 1 u) (mkC 0 0)) with (arc 1 u)
      by (apply Ceq; simpl; ring). apply HMf. }
  pose proof (identity_on_disk_D (fseq G 4 HR4 HGc) 1 0 1
                (Cmul (RtoC (/ eps)) (Cminus z (mkC a 0)))
                ltac:(lra) ltac:(lra) ltac:(lra)
                (fun k zz Hzz => fseq_chain G 4 HR4 HGc
                   (ex_intro _ Mg (conj HMg HGbd)) k zz
                   ltac:(replace (Cminus zz (mkC 0 0)) with zz in Hzz
                           by (apply Ceq; simpl; ring);
                         replace (4 / 2) with (1 + 1) by lra; exact Hzz))
                (fseq_cont G 4 HR4 HGc Mg HGbd)
                Hhbd Hvan0) as Hid.
  set (w := Cmul (RtoC (/ eps)) (Cminus z (mkC a 0))) in *.
  assert (Hwmod : Cmod w < 1).
  { unfold w. rewrite Cmod_mul, Cmod_RtoC, (Rabs_right (/ eps))
      by (left; apply Rinv_0_lt_compat; lra).
    apply Rlt_le_trans with (/ eps * eps).
    - apply Rmult_lt_compat_l; [ apply Rinv_0_lt_compat; lra | unfold eps; exact Hz ].
    - apply Req_le; field; lra. }
  specialize (Hid Hwmod).
  replace (Cadd w (mkC 0 0)) with w in Hid by (apply Ceq; simpl; ring).
  assert (Hw2 : Cmod w < 4 / 2) by lra.
  rewrite (fseq0_eq G 4 HR4 HGc HGptc HGhol w Hw2) in Hid.
  unfold G in Hid.
  assert (Hzw : Cadd (Cmul (RtoC eps) w) (mkC a 0) = z).
  { unfold w.
    replace (Cmul (RtoC eps) (Cmul (RtoC (/ eps)) (Cminus z (mkC a 0))))
      with (Cminus z (mkC a 0)) by
      (apply Ceq; unfold Cmul, RtoC, Cminus, Cadd, Copp; cbn [Re Im]; field; lra).
    ring. }
  rewrite Hzw in Hid. exact Hid.
Qed.

Print Assumptions real_disk_zero.
