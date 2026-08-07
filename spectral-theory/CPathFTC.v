(* ================================================================= *)
(*  CPathFTC.v  —  Milestone C, brick C1c: the complex-derivative-along- *)
(*  a-path chain rule, and the path fundamental theorem of calculus.     *)
(*                                                                    *)
(*  Generalizes CDerivLine.is_Cderiv_line (straight line z+t*h) to an    *)
(*  arbitrary C^1 path gam: if F is complex-differentiable at gam u with *)
(*  derivative d and gam has real derivative gam' u (componentwise),     *)
(*  then s |-> Re/Im (F (gam s)) is differentiable at u with derivative  *)
(*  Re/Im (d * gam' u).  Hence for a primitive H (H' = f along gam),     *)
(*  pathint gam gam' f = H(gam b) - H(gam a)  (path FTC), and in         *)
(*  particular the loop integral of a function-with-primitive is 0 --    *)
(*  the engine of Cauchy's theorem on convex sets (C2).                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CImproperIntegral CDerivLine
        Holomorphic ContinuousCoV CIntegral2 CPathIntegral.
Open Scope R_scope.

Lemma Re_Cadd : forall a b, Re (Cadd a b) = Re a + Re b.
Proof. intros a b; unfold Cadd; reflexivity. Qed.
Lemma Im_Cadd : forall a b, Im (Cadd a b) = Im a + Im b.
Proof. intros a b; unfold Cadd; reflexivity. Qed.

Section Chain.
Variables (F : C -> C) (gam gam' : R -> C).

Lemma Cderiv_path_Re : forall u d,
  is_Cderiv F (gam u) d ->
  derivable_pt_lim (fun s => Re (gam s)) u (Re (gam' u)) ->
  derivable_pt_lim (fun s => Im (gam s)) u (Im (gam' u)) ->
  derivable_pt_lim (fun s => Re (F (gam s))) u (Re (Cmul d (gam' u))).
Proof.
  intros u d HF HgR HgI eps Heps.
  set (g' := gam' u).
  set (Md := Cmod d); set (Mg := Rabs (Re g') + Rabs (Im g')).
  assert (HMd : 0 <= Md) by apply Cmod_nonneg.
  assert (HMg : 0 <= Mg) by (unfold Mg; apply Rplus_le_le_0_compat; apply Rabs_pos).
  set (ep := eps / (2 * (Mg + 2))).
  assert (Hep : 0 < ep) by (unfold ep; apply Rdiv_lt_0_compat; lra).
  set (eg := Rmin (eps / (4 * (Md + 1))) (/ 4)).
  assert (Heg : 0 < eg)
    by (unfold eg; apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; lra | lra ]).
  assert (Heg1 : eg <= eps / (4 * (Md + 1))) by (unfold eg; apply Rmin_l).
  assert (Heg2 : eg <= / 4) by (unfold eg; apply Rmin_r).
  destruct (HF ep Hep) as [delF [HdelF HFb]].
  destruct (HgR eg Heg) as [dR HgRb].
  destruct (HgI eg Heg) as [dI HgIb].
  assert (HdF1 : 0 < delF / (Mg + 1)) by (apply Rdiv_lt_0_compat; lra).
  set (delta := Rmin dR (Rmin dI (delF / (Mg + 1)))).
  assert (Hd0 : 0 < delta).
  { unfold delta; apply Rmin_glb_lt;
      [ apply cond_pos | apply Rmin_glb_lt; [ apply cond_pos | exact HdF1 ] ]. }
  exists (mkposreal _ Hd0).
  intros dh Hdh0 Hdhlt; cbn in Hdhlt.
  assert (HdhR : Rabs dh < dR) by (eapply Rlt_le_trans; [ exact Hdhlt | apply Rmin_l ]).
  assert (HdhI : Rabs dh < dI)
    by (eapply Rlt_le_trans; [ exact Hdhlt | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (HdhF : Rabs dh < delF / (Mg + 1))
    by (eapply Rlt_le_trans; [ exact Hdhlt | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
  assert (Hdhpos : 0 < Rabs dh) by (apply Rabs_pos_lt; exact Hdh0).
  set (k := Cminus (gam (u + dh)) (gam u)).
  set (kk := Cminus k (Cmul (RtoC dh) g')).
  set (Rem := Cminus (Cminus (F (Cadd (gam u) k)) (F (gam u))) (Cmul d k)).
  (* component bounds on kk *)
  assert (HRek : Re k = Re (gam (u + dh)) - Re (gam u)) by (unfold k; apply Re_Cminus).
  assert (HImk : Im k = Im (gam (u + dh)) - Im (gam u)) by (unfold k; apply Im_Cminus).
  assert (HReKK : Re kk = Re k - dh * Re g')
    by (unfold kk; rewrite Re_Cminus, Re_RtoC_mul; reflexivity).
  assert (HImKK : Im kk = Im k - dh * Im g')
    by (unfold kk; rewrite Im_Cminus, Im_RtoC_mul; reflexivity).
  assert (HkkRe : Rabs (Re kk) <= eg * Rabs dh).
  { replace (Re kk) with (((Re (gam (u + dh)) - Re (gam u)) / dh - Re g') * dh)
      by (rewrite HReKK, HRek; field; exact Hdh0).
    rewrite Rabs_mult; apply Rmult_le_compat_r; [ apply Rabs_pos | apply Rlt_le, HgRb; assumption ]. }
  assert (HkkIm : Rabs (Im kk) <= eg * Rabs dh).
  { replace (Im kk) with (((Im (gam (u + dh)) - Im (gam u)) / dh - Im g') * dh)
      by (rewrite HImKK, HImk; field; exact Hdh0).
    rewrite Rabs_mult; apply Rmult_le_compat_r; [ apply Rabs_pos | apply Rlt_le, HgIb; assumption ]. }
  assert (Hkkmod : Cmod kk <= 2 * eg * Rabs dh).
  { eapply Rle_trans; [ apply Cmod_le_sum | ]; lra. }
  assert (Hgmod : Cmod g' <= Mg) by apply Cmod_le_sum.
  assert (Hkmod : Cmod k <= (Mg + 1) * Rabs dh).
  { assert (Hsplit : k = Cadd kk (Cmul (RtoC dh) g')) by (unfold kk; ring).
    rewrite Hsplit; eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_mul, Cmod_RtoC.
    apply Rle_trans with (2 * eg * Rabs dh + Rabs dh * Mg).
    - apply Rplus_le_compat; [ exact Hkkmod
      | apply Rmult_le_compat_l; [ apply Rabs_pos | exact Hgmod ] ].
    - assert (2 * eg <= 1) by lra; nra. }
  assert (HkdelF : Cmod k < delF).
  { eapply Rle_lt_trans; [ exact Hkmod | ].
    apply Rmult_lt_reg_r with (/ (Mg + 1)); [ apply Rinv_0_lt_compat; lra | ].
    replace ((Mg + 1) * Rabs dh * / (Mg + 1)) with (Rabs dh) by (field; lra).
    replace (delF * / (Mg + 1)) with (delF / (Mg + 1)) by (unfold Rdiv; ring); exact HdhF. }
  assert (HRemmod : Cmod Rem <= ep * Cmod k).
  { unfold Rem; apply HFb; exact HkdelF. }
  (* the algebraic decomposition *)
  assert (Hgam : gam (u + dh) = Cadd (gam u) k) by (unfold k; ring).
  assert (HFdec : F (gam (u + dh)) = Cadd (Cadd (F (gam u)) (Cmul d k)) Rem)
    by (rewrite Hgam; unfold Rem; ring).
  assert (HRkk : Re (Cmul d kk) = Re (Cmul d k) - dh * Re (Cmul d g')).
  { assert (Cmul d kk = Cminus (Cmul d k) (Cmul (RtoC dh) (Cmul d g')))
      by (unfold kk; ring).
    rewrite H, Re_Cminus, Re_RtoC_mul; reflexivity. }
  replace ((Re (F (gam (u + dh))) - Re (F (gam u))) / dh - Re (Cmul d g'))
    with ((Re (Cmul d kk) + Re Rem) / dh).
  2:{ rewrite HFdec, !Re_Cadd, HRkk; field; exact Hdh0. }
  (* the estimate *)
  unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv by exact Hdh0.
  apply Rle_lt_trans with ((Md * (2 * eg * Rabs dh) + ep * ((Mg + 1) * Rabs dh)) * / Rabs dh).
  - apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; exact Hdhpos | ].
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    + eapply Rle_trans; [ apply Cmod_Re_le | ].
      rewrite Cmod_mul; apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hkkmod ].
    + eapply Rle_trans; [ apply Cmod_Re_le | ].
      eapply Rle_trans; [ exact HRemmod | ].
      apply Rmult_le_compat_l; [ apply Rlt_le; exact Hep | exact Hkmod ].
  - replace ((Md * (2 * eg * Rabs dh) + ep * ((Mg + 1) * Rabs dh)) * / Rabs dh)
      with (2 * Md * eg + ep * (Mg + 1)) by (field; lra).
    assert (Hb1 : 2 * Md * eg <= eps / 2).
    { assert (Hge : eg * (4 * (Md + 1)) <= eps).
      { replace eps with (eps / (4 * (Md + 1)) * (4 * (Md + 1))) by (field; lra).
        apply Rmult_le_compat_r; [ lra | exact Heg1 ]. }
      nra. }
    assert (Hb2 : ep * (Mg + 1) < eps / 2).
    { assert (Hepv : ep * (Mg + 2) = eps / 2) by (unfold ep; field; lra).
      apply Rlt_le_trans with (ep * (Mg + 2)); [ apply Rmult_lt_compat_l; lra | lra ]. }
    lra.
Qed.

Lemma Cderiv_path_Im : forall u d,
  is_Cderiv F (gam u) d ->
  derivable_pt_lim (fun s => Re (gam s)) u (Re (gam' u)) ->
  derivable_pt_lim (fun s => Im (gam s)) u (Im (gam' u)) ->
  derivable_pt_lim (fun s => Im (F (gam s))) u (Im (Cmul d (gam' u))).
Proof.
  intros u d HF HgR HgI eps Heps.
  set (g' := gam' u).
  set (Md := Cmod d); set (Mg := Rabs (Re g') + Rabs (Im g')).
  assert (HMd : 0 <= Md) by apply Cmod_nonneg.
  assert (HMg : 0 <= Mg) by (unfold Mg; apply Rplus_le_le_0_compat; apply Rabs_pos).
  set (ep := eps / (2 * (Mg + 2))).
  assert (Hep : 0 < ep) by (unfold ep; apply Rdiv_lt_0_compat; lra).
  set (eg := Rmin (eps / (4 * (Md + 1))) (/ 4)).
  assert (Heg : 0 < eg)
    by (unfold eg; apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; lra | lra ]).
  assert (Heg1 : eg <= eps / (4 * (Md + 1))) by (unfold eg; apply Rmin_l).
  assert (Heg2 : eg <= / 4) by (unfold eg; apply Rmin_r).
  destruct (HF ep Hep) as [delF [HdelF HFb]].
  destruct (HgR eg Heg) as [dR HgRb].
  destruct (HgI eg Heg) as [dI HgIb].
  assert (HdF1 : 0 < delF / (Mg + 1)) by (apply Rdiv_lt_0_compat; lra).
  set (delta := Rmin dR (Rmin dI (delF / (Mg + 1)))).
  assert (Hd0 : 0 < delta).
  { unfold delta; apply Rmin_glb_lt;
      [ apply cond_pos | apply Rmin_glb_lt; [ apply cond_pos | exact HdF1 ] ]. }
  exists (mkposreal _ Hd0).
  intros dh Hdh0 Hdhlt; cbn in Hdhlt.
  assert (HdhR : Rabs dh < dR) by (eapply Rlt_le_trans; [ exact Hdhlt | apply Rmin_l ]).
  assert (HdhI : Rabs dh < dI)
    by (eapply Rlt_le_trans; [ exact Hdhlt | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (HdhF : Rabs dh < delF / (Mg + 1))
    by (eapply Rlt_le_trans; [ exact Hdhlt | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
  assert (Hdhpos : 0 < Rabs dh) by (apply Rabs_pos_lt; exact Hdh0).
  set (k := Cminus (gam (u + dh)) (gam u)).
  set (kk := Cminus k (Cmul (RtoC dh) g')).
  set (Rem := Cminus (Cminus (F (Cadd (gam u) k)) (F (gam u))) (Cmul d k)).
  assert (HRek : Re k = Re (gam (u + dh)) - Re (gam u)) by (unfold k; apply Re_Cminus).
  assert (HImk : Im k = Im (gam (u + dh)) - Im (gam u)) by (unfold k; apply Im_Cminus).
  assert (HReKK : Re kk = Re k - dh * Re g')
    by (unfold kk; rewrite Re_Cminus, Re_RtoC_mul; reflexivity).
  assert (HImKK : Im kk = Im k - dh * Im g')
    by (unfold kk; rewrite Im_Cminus, Im_RtoC_mul; reflexivity).
  assert (HkkRe : Rabs (Re kk) <= eg * Rabs dh).
  { replace (Re kk) with (((Re (gam (u + dh)) - Re (gam u)) / dh - Re g') * dh)
      by (rewrite HReKK, HRek; field; exact Hdh0).
    rewrite Rabs_mult; apply Rmult_le_compat_r; [ apply Rabs_pos | apply Rlt_le, HgRb; assumption ]. }
  assert (HkkIm : Rabs (Im kk) <= eg * Rabs dh).
  { replace (Im kk) with (((Im (gam (u + dh)) - Im (gam u)) / dh - Im g') * dh)
      by (rewrite HImKK, HImk; field; exact Hdh0).
    rewrite Rabs_mult; apply Rmult_le_compat_r; [ apply Rabs_pos | apply Rlt_le, HgIb; assumption ]. }
  assert (Hkkmod : Cmod kk <= 2 * eg * Rabs dh).
  { eapply Rle_trans; [ apply Cmod_le_sum | ]; lra. }
  assert (Hgmod : Cmod g' <= Mg) by apply Cmod_le_sum.
  assert (Hkmod : Cmod k <= (Mg + 1) * Rabs dh).
  { assert (Hsplit : k = Cadd kk (Cmul (RtoC dh) g')) by (unfold kk; ring).
    rewrite Hsplit; eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_mul, Cmod_RtoC.
    apply Rle_trans with (2 * eg * Rabs dh + Rabs dh * Mg).
    - apply Rplus_le_compat; [ exact Hkkmod
      | apply Rmult_le_compat_l; [ apply Rabs_pos | exact Hgmod ] ].
    - assert (2 * eg <= 1) by lra; nra. }
  assert (HkdelF : Cmod k < delF).
  { eapply Rle_lt_trans; [ exact Hkmod | ].
    apply Rmult_lt_reg_r with (/ (Mg + 1)); [ apply Rinv_0_lt_compat; lra | ].
    replace ((Mg + 1) * Rabs dh * / (Mg + 1)) with (Rabs dh) by (field; lra).
    replace (delF * / (Mg + 1)) with (delF / (Mg + 1)) by (unfold Rdiv; ring); exact HdhF. }
  assert (HRemmod : Cmod Rem <= ep * Cmod k) by (unfold Rem; apply HFb; exact HkdelF).
  assert (Hgam : gam (u + dh) = Cadd (gam u) k) by (unfold k; ring).
  assert (HFdec : F (gam (u + dh)) = Cadd (Cadd (F (gam u)) (Cmul d k)) Rem)
    by (rewrite Hgam; unfold Rem; ring).
  assert (HRkk : Im (Cmul d kk) = Im (Cmul d k) - dh * Im (Cmul d g')).
  { assert (Cmul d kk = Cminus (Cmul d k) (Cmul (RtoC dh) (Cmul d g')))
      by (unfold kk; ring).
    rewrite H, Im_Cminus, Im_RtoC_mul; reflexivity. }
  replace ((Im (F (gam (u + dh))) - Im (F (gam u))) / dh - Im (Cmul d g'))
    with ((Im (Cmul d kk) + Im Rem) / dh).
  2:{ rewrite HFdec, !Im_Cadd, HRkk; field; exact Hdh0. }
  unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv by exact Hdh0.
  apply Rle_lt_trans with ((Md * (2 * eg * Rabs dh) + ep * ((Mg + 1) * Rabs dh)) * / Rabs dh).
  - apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; exact Hdhpos | ].
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    + eapply Rle_trans; [ apply Cmod_Im_le | ].
      rewrite Cmod_mul; apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hkkmod ].
    + eapply Rle_trans; [ apply Cmod_Im_le | ].
      eapply Rle_trans; [ exact HRemmod | ].
      apply Rmult_le_compat_l; [ apply Rlt_le; exact Hep | exact Hkmod ].
  - replace ((Md * (2 * eg * Rabs dh) + ep * ((Mg + 1) * Rabs dh)) * / Rabs dh)
      with (2 * Md * eg + ep * (Mg + 1)) by (field; lra).
    assert (Hb1 : 2 * Md * eg <= eps / 2).
    { assert (Hge : eg * (4 * (Md + 1)) <= eps).
      { replace eps with (eps / (4 * (Md + 1)) * (4 * (Md + 1))) by (field; lra).
        apply Rmult_le_compat_r; [ lra | exact Heg1 ]. }
      nra. }
    assert (Hb2 : ep * (Mg + 1) < eps / 2).
    { assert (Hepv : ep * (Mg + 2) = eps / 2) by (unfold ep; field; lra).
      apply Rlt_le_trans with (ep * (Mg + 2)); [ apply Rmult_lt_compat_l; lra | lra ]. }
    lra.
Qed.

End Chain.

(* ================================================================= *)
(*  The path fundamental theorem of calculus.                          *)
(* ================================================================= *)

Theorem pathint_FTC : forall (H f : C -> C) (gam gam' : R -> C)
  (Hf : Ccont (fun u => Cmul (f (gam u)) (gam' u))) a b,
  a <= b ->
  (forall s, a <= s <= b -> is_Cderiv H (gam s) (f (gam s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Re (gam r)) s (Re (gam' s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Im (gam r)) s (Im (gam' s))) ->
  pathint gam gam' f Hf a b = Cminus (H (gam b)) (H (gam a)).
Proof.
  intros H f gam gam' Hf a b Hab HH HgR HgI.
  unfold pathint, Cintf; apply Ceq; unfold Cminus; cbn [Re Im].
  - apply (FTC_antideriv (fun u => Re (Cmul (f (gam u)) (gam' u)))
             (fun u => Re (H (gam u))) a b Hab).
    + intros x Hx; apply (proj1 Hf).
    + split; [ | exact Hab ]; intros x Hx.
      exists (exist (fun l => derivable_pt_lim (fun u => Re (H (gam u))) x l)
                (Re (Cmul (f (gam x)) (gam' x)))
                (Cderiv_path_Re H gam gam' x (f (gam x)) (HH x Hx) (HgR x Hx) (HgI x Hx))).
      reflexivity.
  - apply (FTC_antideriv (fun u => Im (Cmul (f (gam u)) (gam' u)))
             (fun u => Im (H (gam u))) a b Hab).
    + intros x Hx; apply (proj2 Hf).
    + split; [ | exact Hab ]; intros x Hx.
      exists (exist (fun l => derivable_pt_lim (fun u => Im (H (gam u))) x l)
                (Im (Cmul (f (gam x)) (gam' x)))
                (Cderiv_path_Im H gam gam' x (f (gam x)) (HH x Hx) (HgR x Hx) (HgI x Hx))).
      reflexivity.
Qed.

(* a closed path whose integrand has a primitive integrates to 0 *)
Corollary pathint_primitive_loop : forall (H f : C -> C) (gam gam' : R -> C)
  (Hf : Ccont (fun u => Cmul (f (gam u)) (gam' u))) a b,
  a <= b -> gam a = gam b ->
  (forall s, a <= s <= b -> is_Cderiv H (gam s) (f (gam s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Re (gam r)) s (Re (gam' s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Im (gam r)) s (Im (gam' s))) ->
  pathint gam gam' f Hf a b = C0.
Proof.
  intros H f gam gam' Hf a b Hab Hloop HH HgR HgI.
  rewrite (pathint_FTC H f gam gam' Hf a b Hab HH HgR HgI), Hloop; ring.
Qed.

Print Assumptions Cderiv_path_Re.
Print Assumptions pathint_FTC.

(* ================================================================= *)
(*  END CPathFTC.v  —  the path chain rule + path FTC.                  *)
(* ================================================================= *)
