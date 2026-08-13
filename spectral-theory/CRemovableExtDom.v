(* ================================================================= *)
(*  CRemovableExtDom.v  (identity-theorem plan, domain-restricted B1)   *)
(*                                                                    *)
(*  First brick of the domain-restricted removable extension: the      *)
(*  quotient  (F(z)-F(w))/(z-w)  is CONTINUOUS at any z <> w whenever   *)
(*  F is merely CONTINUOUS at z -- no differentiability needed.         *)
(*                                                                    *)
(*  This is what lets rphi's continuity (rphi_cc) be discharged from a  *)
(*  globally-continuous F rather than a globally-DIFFERENTIABLE (entire)*)
(*  one -- the key to feeding a function holomorphic only on a disk     *)
(*  (like FE_diff on Re>0) into cauchy_interior_cond.                   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        CDeriv CHoloCalculus CWindingOffCenter CRemovableExt CCauchyInterior
        PerronRemovable.
Open Scope R_scope.

Lemma minus_ne : forall a b, a <> b -> Cminus a b <> C0.
Proof.
  intros a b Hab Hc. apply Hab. apply Ceq;
    [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
    unfold Cminus, C0 in Hc; cbn in Hc; lra.
Qed.

Lemma Cmod_pos_of_ne : forall c, c <> C0 -> 0 < Cmod c.
Proof.
  intros c Hc. pose proof (Cmod_nonneg c) as Hnn. destruct (Cmod0 c) as [H0 _].
  assert (Cmod c <> 0) by (intro Hz; apply Hc, H0; exact Hz). lra.
Qed.

(* the inverse difference, as pure C-field algebra *)
Lemma Cinv_diff : forall a b, a <> C0 -> b <> C0 ->
  Cminus (Cinv a) (Cinv b) = Cmul (Cminus b a) (Cinv (Cmul a b)).
Proof. intros a b Ha Hb. field. split; assumption. Qed.

(* pointwise continuity of the removable quotient off the pole *)
Lemma quotient_ptcont : forall (F : C -> C) (w z : C),
  z <> w ->
  (forall eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps) ->
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del ->
      Cmod (Cminus (Cmul (Cminus (F z') (F w)) (Cinv (Cminus z' w)))
                   (Cmul (Cminus (F z) (F w)) (Cinv (Cminus z w)))) < eps.
Proof.
  intros F w z Hzw Fptc eps Heps.
  set (m := Cmod (Cminus z w)).
  assert (Hzwne : Cminus z w <> C0).
  { intro Hc. apply Hzw. apply Ceq;
      [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
      unfold Cminus, C0 in Hc; cbn in Hc; lra. }
  assert (Hm : 0 < m).
  { unfold m. pose proof (Cmod_nonneg (Cminus z w)).
    destruct (Cmod0 (Cminus z w)) as [Hc _].
    assert (Cmod (Cminus z w) <> 0) by (intro H0; apply Hzwne, Hc; exact H0). lra. }
  set (Cb := Cmod (Cminus (F z) (F w))).
  assert (HCb : 0 <= Cb) by apply Cmod_nonneg.
  (* F ptcont at z, tolerance eps*m/4 *)
  destruct (Fptc (eps * m / 4) ltac:(apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; lra | ]; lra))
    as [del1 [Hdel1 HF1]].
  exists (Rmin (m / 2) (Rmin del1 (eps * m * m / (4 * (Cb + 1))))).
  split.
  { repeat apply Rmin_pos; try lra.
    apply Rdiv_lt_0_compat; [ apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; lra | exact Hm ] | lra ]. }
  intros z' Hz'.
  assert (Hz'2 : Cmod (Cminus z' z) < m / 2)
    by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_l ]).
  assert (Hz'del1 : Cmod (Cminus z' z) < del1)
    by (eapply Rlt_le_trans; [ exact Hz' | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (Hz'b : Cmod (Cminus z' z) < eps * m * m / (4 * (Cb + 1)))
    by (eapply Rlt_le_trans; [ exact Hz' | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
  (* z' - w is bounded away from 0 *)
  assert (Hzz' : Cmod (Cminus z z') = Cmod (Cminus z' z))
    by (rewrite <- Cmod_opp; f_equal; ring).
  assert (Hz'w_lb : m / 2 <= Cmod (Cminus z' w)).
  { assert (Hrt : Cmod (Cminus z w) - Cmod (Cminus z' w)
                  <= Cmod (Cminus (Cminus z w) (Cminus z' w)))
      by apply Cmod_rev_triangle.
    replace (Cminus (Cminus z w) (Cminus z' w)) with (Cminus z z') in Hrt by ring.
    fold m in Hrt. rewrite Hzz' in Hrt. lra. }
  assert (Hz'wne : Cminus z' w <> C0)
    by (intro Hc; rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hz'w_lb; lra).
  assert (Hz'wpos : 0 < Cmod (Cminus z' w)) by lra.
  (* split: a.u - b.v = (a-b).u + b.(u-v),  a-b = F z' - F z *)
  set (u := Cinv (Cminus z' w)). set (v := Cinv (Cminus z w)).
  assert (Hdecomp :
    Cminus (Cmul (Cminus (F z') (F w)) u) (Cmul (Cminus (F z) (F w)) v)
    = Cadd (Cmul (Cminus (F z') (F z)) u)
           (Cmul (Cminus (F z) (F w)) (Cminus u v))).
  { unfold u, v. ring. }
  rewrite Hdecomp.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  (* bound term 1: |F z' - F z| * |u| <= (eps m/4) * (2/m) = eps/2 *)
  assert (H2m : 0 < 2 / m) by (apply Rdiv_lt_0_compat; lra).
  assert (HT1 : Cmod (Cmul (Cminus (F z') (F z)) u) < eps / 2).
  { rewrite Cmod_mul. unfold u. rewrite (Cmod_inv _ Hz'wne).
    apply Rle_lt_trans with (Cmod (Cminus (F z') (F z)) * (2 / m)).
    - apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
      apply Rle_trans with (/ (m / 2));
        [ apply Rinv_le_contravar; [ lra | exact Hz'w_lb ] | apply Req_le; field; lra ].
    - apply Rlt_le_trans with (eps * m / 4 * (2 / m));
        [ apply Rmult_lt_compat_r; [ exact H2m | apply HF1; exact Hz'del1 ]
        | apply Req_le; field; lra ]. }
  (* bound term 2: |b| * |u - v| <= Cb * (2|z'-z|/m^2) < eps/2 *)
  assert (HT2 : Cmod (Cmul (Cminus (F z) (F w)) (Cminus u v)) < eps / 2).
  { rewrite Cmod_mul. fold Cb.
    unfold u, v. rewrite (Cinv_diff (Cminus z' w) (Cminus z w) Hz'wne Hzwne).
    rewrite Cmod_mul, (Cmod_inv _ (Cmul_ne0 _ _ Hz'wne Hzwne)), Cmod_mul.
    (* Cb * (|(z-w)-(z'-w)| * / (|z'-w| |z-w|)) *)
    replace (Cminus (Cminus z w) (Cminus z' w)) with (Cminus z z') by ring.
    apply Rle_lt_trans with (Cb * (Cmod (Cminus z z') * / (m / 2 * m))).
    - apply Rmult_le_compat_l; [ exact HCb | ].
      apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
      apply Rinv_le_contravar;
        [ apply Rmult_lt_0_compat; [ lra | exact Hm ]
        | apply Rmult_le_compat; [ lra | left; exact Hm | exact Hz'w_lb | unfold m; lra ] ].
    - rewrite Hzz'.
      apply Rle_lt_trans with (Cb * (eps * m * m / (4 * (Cb + 1)) * / (m / 2 * m))).
      + apply Rmult_le_compat_l; [ exact HCb | ].
        apply Rmult_le_compat_r;
          [ left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; [ lra | exact Hm ]
          | left; exact Hz'b ].
      + assert (Hden2 : 0 < m / 2 * m) by (apply Rmult_lt_0_compat; lra).
        assert (Hval : Cb * (eps * m * m / (4 * (Cb + 1)) * / (m / 2 * m))
                       = eps / 2 * (Cb / (Cb + 1))) by (field; lra).
        rewrite Hval.
        assert (Hfrac : Cb / (Cb + 1) < 1).
        { apply Rmult_lt_reg_r with (Cb + 1); [ lra | ].
          unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r. lra. }
        assert (Hfrac0 : 0 <= Cb / (Cb + 1)) by (apply Rle_mult_inv_pos; lra).
        nra. }
  lra.
Qed.

Print Assumptions quotient_ptcont.

(* ================================================================= *)
(*  rphi continuity from a globally-CONTINUOUS F (not entire)          *)
(* ================================================================= *)

Section RemovableDom.
Variable F : C -> C.
Variable w dw : C.
Hypothesis Hdw : is_Cderiv F w dw.
Hypothesis Fptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps.

Lemma rphi_ptcont_dom : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del ->
    Cmod (Cminus (rphi F w dw z') (rphi F w dw z)) < eps.
Proof.
  intros z eps Heps. destruct (Ceq_dec z w) as [Hzw | Hzw].
  - (* z = w: removability, from Hdw *)
    subst z. rewrite rphi_w.
    destruct (Hdw (eps / 2) ltac:(lra)) as [del [Hdel Hb]].
    exists del; split; [ exact Hdel | ].
    intros z' Hz'. destruct (Ceq_dec z' w) as [Hz'w | Hz'w].
    + subst z'. rewrite rphi_w.
      replace (Cminus dw dw) with C0 by (apply Ceq; simpl; ring).
      rewrite (proj2 (Cmod0 C0) eq_refl); exact Heps.
    + assert (Hne : Cminus z' w <> C0) by (apply minus_ne; exact Hz'w).
      assert (Hpos : 0 < Cmod (Cminus z' w)) by (apply Cmod_pos_of_ne; exact Hne).
      pose proof (Hb (Cminus z' w) Hz') as Hrem.
      replace (Cadd w (Cminus z' w)) with z' in Hrem by (apply Ceq; simpl; ring).
      rewrite (rphi_minus_dw F w dw z' Hz'w), Cmod_mul, (Cmod_inv _ Hne).
      apply (Rmult_lt_reg_r (Cmod (Cminus z' w))); [ exact Hpos | ].
      rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      eapply Rle_lt_trans; [ exact Hrem | nra ].
  - (* z <> w: quotient continuity from F continuous at z *)
    destruct (quotient_ptcont F w z Hzw (Fptc z) eps Heps) as [del0 [Hdel0 Hq]].
    exists (Rmin del0 (Cmod (Cminus z w))); split.
    { apply Rmin_pos; [ exact Hdel0 | apply Cmod_pos_of_ne, minus_ne; exact Hzw ]. }
    intros z' Hz'.
    assert (Hz'w : z' <> w).
    { intro E; subst z'.
      assert (Cmod (Cminus w z) = Cmod (Cminus z w))
        by (rewrite <- Cmod_opp; f_equal; ring).
      assert (Cmod (Cminus w z) < Cmod (Cminus z w))
        by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_r ]). lra. }
    rewrite (rphi_off F w dw z' Hz'w), (rphi_off F w dw z Hzw).
    apply Hq. eapply Rlt_le_trans; [ exact Hz' | apply Rmin_l ].
Qed.

Lemma rphi_cc_dom : CcontC (rphi F w dw).
Proof. apply ptcont_CcontC, rphi_ptcont_dom. Qed.

(* disk-restricted holomorphy off w: needs F differentiable only on the disk *)
Variable R2 : R.
Hypothesis Fholo_disk : forall z, Cmod z < R2 -> z <> w -> exists d, is_Cderiv F z d.

Lemma rphi_holo_off_dom : forall z, Cmod z < R2 -> z <> w ->
  exists d, is_Cderiv (rphi F w dw) z d.
Proof.
  intros z Hzd Hz. destruct (Fholo_disk z Hzd Hz) as [dF HdF].
  assert (Hne : Cminus z w <> C0) by (apply minus_ne; exact Hz).
  eexists.
  apply (is_Cderiv_congr (rphi F w dw)
           (fun z' => Cmul (Cminus (F z') (F w)) (Cinv (Cminus z' w)))
           z _ (Cmod (Cminus z w))).
  - apply Cmod_pos_of_ne; exact Hne.
  - intros z' Hz'. apply rphi_off. intro E; subst z'.
    assert (Cmod (Cminus w z) = Cmod (Cminus z w))
      by (rewrite <- Cmod_opp; f_equal; ring). lra.
  - apply (Cderiv_div (fun z' => Cminus (F z') (F w)) (fun z' => Cminus z' w) z
             (Cminus dF C0) (Cminus C1 C0)).
    + apply (Cderiv_minus F (fun _ => F w) z dF C0); [ exact HdF | apply Cderiv_const ].
    + apply (Cderiv_minus (fun z' => z') (fun _ => w) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ].
    + exact Hne.
Qed.

End RemovableDom.

(* ================================================================= *)
(*  DOMAIN-RESTRICTED B1: Cauchy formula for F holomorphic on the disk *)
(* ================================================================= *)
Theorem cauchy_interior_dom : forall (F : C -> C) (Rr : R) (w dw : C),
  0 < Rr -> Cmod w < Rr ->
  is_Cderiv F w dw ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps) ->
  (forall z, Cmod z < Rr + 1 -> z <> w -> exists d, is_Cderiv F z d) ->
  forall (Hf : Ccont (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (Cminus (arc Rr u) w)))
                                    (arc' Rr u))),
  pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv (Cminus z w))) Hf 0 (2 * PI)
  = Cmul (mkC 0 (2 * PI)) (F w).
Proof.
  intros F Rr w dw HR HwR Hdw Fptc Fholo Hf.
  assert (Harc_ne : forall u, arc Rr u <> w).
  { intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
    rewrite Hc in HM. lra. }
  apply (cauchy_interior_cond (Rr + 1) Rr w F (rphi F w dw)).
  - exact HR.
  - lra.
  - exact HwR.
  - exact (rphi_cc_dom F w dw Hdw Fptc).
  - intro u. exact (rphi_off F w dw (arc Rr u) (Harc_ne u)).
  - intros z Hzd Hz. exact (rphi_holo_off_dom F w dw (Rr + 1) Fholo z Hzd Hz).
  - exact (rphi_bd F w dw Hdw).
  - intros z Hzd eps He. exact (rphi_ptcont_dom F w dw Hdw Fptc z eps He).
Qed.

Print Assumptions rphi_cc_dom.
Print Assumptions cauchy_interior_dom.
