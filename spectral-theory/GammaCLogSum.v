(* ================================================================= *)
(*  GammaCLogSum.v   (the complex log-sum  L = sum_k t_k  is holomorphic) *)
(*                                                                    *)
(*  Route B, file 2/3 of the GammaC != 0 brick.  Builds the log-sum       *)
(*     L z = sum_{k>=1} ( log(1+z/k) - z/k )                              *)
(*  as the pointwise limit of  sum tterm_k  (GammaCLogTerm), and proves   *)
(*  it holomorphic on {Re z > 0} via the sum_deriv difference-quotient    *)
(*  argument (order-1 template of CZetaHolo.v) with the summable weight   *)
(*  1/k^2 (no ln-weighted p-series needed, since t_k = O(|z|^2/k^2)).      *)
(*                                                                    *)
(*     Cmod_gterm_le / Cmod_tterm_le : the  |z|/k^2 , |z|^2/k^2  bounds;   *)
(*     Lf, Sderiv           : the base- and derivative-series limits;      *)
(*     L_holo / Lf_holo     : is_Cderiv Lf z (Sderiv z)  for Re z > 0;     *)
(*     Lf_agree             : Lf (RtoC s) = RtoC (Winf s)  (real axis),    *)
(*                            via 1-D ODE uniqueness + telescoping to LW.  *)
(*                                                                    *)
(*  These three exports (Lf, Lf_holo, Lf_agree) are exactly the interface  *)
(*  that GammaCNe0.v's Section requires: instantiating it with them makes  *)
(*  GammaC_ne0 and the strip equivalence UNCONDITIONAL.                    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CSeriesLin CDeriv CDerivLine CGoursatML
        CexpFull CexpRemainder Holomorphic CZetaHolo GammaCLogTerm GammaCWeierstrass
        GammaWeierstrass CSegInt CPathIntegral CPrimConv CIntegral2.
Open Scope R_scope.

Lemma kk_ne0 : forall n, RtoC (INR (S n)) <> C0.
Proof.
  intro n. intro Hc. apply (f_equal Re) in Hc.
  unfold RtoC, C0 in Hc; cbn [Re] in Hc. pose proof (Snpos n). lra.
Qed.

Lemma kk_pos : forall n, 0 < INR (S n).
Proof. intro n. pose proof (Snpos n). lra. Qed.

(* ---------- Group A: closed form + Cmod bounds ---------- *)

Lemma gterm_closed : forall n z, RG z ->
  gterm n z = Cmul (Copp z)
    (Cinv (Cmul (RtoC (INR (S n))) (Cadd (RtoC (INR (S n))) z))).
Proof.
  intros n z Hz. unfold gterm.
  assert (Hk : RtoC (INR (S n)) <> C0) by apply kk_ne0.
  assert (Hkz : Cadd (RtoC (INR (S n))) z <> C0) by (apply kz_ne0; exact Hz).
  rewrite <- (cinvRtoC (INR (S n)) (Rgt_not_eq _ _ (kk_pos n))).
  field. split; assumption.
Qed.

Lemma kk_le_Cmod : forall n z, 0 <= Re z ->
  INR (S n) <= Cmod (Cadd (RtoC (INR (S n))) z).
Proof.
  intros n z Hz.
  apply Rle_trans with (Re (Cadd (RtoC (INR (S n))) z)).
  - unfold Cadd, RtoC; cbn [Re]. lra.
  - eapply Rle_trans; [ apply Rle_abs | apply Cmod_Re_le ].
Qed.

Lemma prod_ne0 : forall n z, RG z ->
  Cmul (RtoC (INR (S n))) (Cadd (RtoC (INR (S n))) z) <> C0.
Proof.
  intros n z Hz Hc.
  assert (H0 : Cmod (Cmul (RtoC (INR (S n))) (Cadd (RtoC (INR (S n))) z)) = 0)
    by (rewrite Hc; apply (proj2 (Cmod0 C0)); reflexivity).
  rewrite Cmod_mul, Cmod_RtoC, (Rabs_right (INR (S n))) in H0 by (pose proof (Snpos n); lra).
  pose proof (Snpos n) as HS.
  assert (Hkz : Cadd (RtoC (INR (S n))) z <> C0) by (apply kz_ne0; exact Hz).
  pose proof (Cmod_pos_ne0 _ Hkz). nra.
Qed.

Lemma Cmod_gterm_le : forall n z, 0 <= Re z ->
  Cmod (gterm n z) <= Cmod z * / (INR (S n)) ^ 2.
Proof.
  intros n z Hz.
  assert (HRG : RG z) by (unfold RG; lra).
  rewrite (gterm_closed n z HRG), Cmod_mul, Cmod_opp.
  assert (Hprod : Cmul (RtoC (INR (S n))) (Cadd (RtoC (INR (S n))) z) <> C0)
    by (apply prod_ne0; exact HRG).
  rewrite (Cmod_inv _ Hprod), Cmod_mul, Cmod_RtoC, (Rabs_right (INR (S n)))
    by (pose proof (Snpos n); lra).
  apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
  replace (/ (INR (S n)) ^ 2) with (/ (INR (S n) * INR (S n))) by (f_equal; simpl; ring).
  apply Rinv_le_contravar.
  - apply Rmult_lt_0_compat; pose proof (Snpos n); lra.
  - apply Rmult_le_compat_l; [ pose proof (Snpos n); lra | apply kk_le_Cmod; exact Hz ].
Qed.

Lemma Cmod_tterm_le : forall n z, 0 <= Re z ->
  Cmod (tterm n z) <= 2 * (Cmod z * Cmod z) * / (INR (S n)) ^ 2.
Proof.
  intros n z Hz. unfold tterm, PrimC.
  eapply Rle_trans.
  { apply (seg_int_ML (ghat n) (ghat_cc n) C0 z (Cmod z * / (INR (S n)) ^ 2)).
    intros u Hu. unfold seg.
    set (w := Cadd C0 (Cmul (RtoC u) (Cminus z C0))).
    assert (HwRe : Re w = u * Re z).
    { unfold w, Cadd, Cmul, Cminus, RtoC, C0; cbn [Re Im]. ring. }
    assert (HwRe0 : 0 <= Re w)
      by (rewrite HwRe; apply Rmult_le_pos; lra).
    assert (HwRG : RG w) by (unfold RG; lra).
    rewrite (ghat_eq_gterm n w HwRG).
    eapply Rle_trans; [ apply Cmod_gterm_le; exact HwRe0 | ].
    apply Rmult_le_compat_r.
    - left; apply Rinv_0_lt_compat, pow_lt, kk_pos.
    - unfold w.
      replace (Cadd C0 (Cmul (RtoC u) (Cminus z C0)))
        with (Cmul (RtoC u) (Cminus z C0))
        by (apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring).
      rewrite Cmod_mul, Cmod_RtoC, (Rabs_right u) by lra.
      assert (Hcz : Cmod (Cminus z C0) = Cmod z)
        by (f_equal; unfold Cminus, C0; apply Ceq; cbn [Re Im]; ring).
      rewrite Hcz. rewrite <- (Rmult_1_l (Cmod z)) at 2.
      apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ]. }
  assert (Hcz : Cmod (Cminus z C0) = Cmod z)
    by (f_equal; unfold Cminus, C0; apply Ceq; cbn [Re Im]; ring).
  rewrite Hcz. apply Req_le. ring.
Qed.

(* ---------- majorant convergence ---------- *)

Lemma invsq_zero0 : / (INR 0) ^ 2 = 0.
Proof.
  replace (INR 0) with 0 by reflexivity.
  replace ((0:R) ^ 2) with (0:R) by ring. apply Rinv_0.
Qed.

Lemma sum_invsq_shift : forall N,
  sum_f_R0 (fun k => / (INR (S k)) ^ 2) N = sum_f_R0 (fun k => / (INR k) ^ 2) (S N).
Proof.
  intro N. rewrite (decomp_sum (fun k => / (INR k) ^ 2) (S N) (Nat.lt_0_succ N)).
  rewrite Nat.pred_succ. cbv beta. rewrite invsq_zero0. ring.
Qed.

Lemma invsq_cv : { T | Un_cv (sum_f_R0 (fun k => / (INR (S k)) ^ 2)) T }.
Proof.
  set (Un := sum_f_R0 (fun k => / (INR (S k)) ^ 2)).
  assert (Hgrow : Un_growing Un).
  { intro N. unfold Un. rewrite tech5.
    assert (0 <= / (INR (S (S N))) ^ 2) by (left; apply Rinv_0_lt_compat, pow_lt, kk_pos). lra. }
  assert (Hub : has_ub Un).
  { exists 2. intros v [N ->]. unfold Un.
    rewrite sum_invsq_shift. apply invsq_bound. }
  destruct (growing_cv Un Hgrow Hub) as [l Hl]. exists l; exact Hl.
Defined.

(* ---------- Group B: the two series converge ---------- *)

Definition gterm_cv (z : C) (H : 0 < Re z) : { S | Cseries_cv (fun k => gterm k z) S }.
Proof.
  apply (Cseries_abs_cv (fun k => gterm k z) (fun k => Cmod z * / (INR (S k)) ^ 2)).
  - intro k. apply Cmod_gterm_le. lra.
  - destruct invsq_cv as [T HT]. exists (Cmod z * T).
    replace (sum_f_R0 (fun k => Cmod z * / (INR (S k)) ^ 2))
       with (fun N => Cmod z * sum_f_R0 (fun k => / (INR (S k)) ^ 2) N).
    + apply (CV_mult (fun _ => Cmod z) (sum_f_R0 (fun k => / (INR (S k)) ^ 2)) (Cmod z) T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun k => / (INR (S k)) ^ 2) N (Cmod z)). apply sum_eq; intros; ring.
Defined.

Definition tterm_cv (z : C) (H : 0 < Re z) : { V | Cseries_cv (fun k => tterm k z) V }.
Proof.
  apply (Cseries_abs_cv (fun k => tterm k z)
           (fun k => 2 * (Cmod z * Cmod z) * / (INR (S k)) ^ 2)).
  - intro k. apply Cmod_tterm_le. lra.
  - destruct invsq_cv as [T HT]. exists (2 * (Cmod z * Cmod z) * T).
    replace (sum_f_R0 (fun k => 2 * (Cmod z * Cmod z) * / (INR (S k)) ^ 2))
       with (fun N => 2 * (Cmod z * Cmod z) * sum_f_R0 (fun k => / (INR (S k)) ^ 2) N).
    + apply (CV_mult (fun _ => 2 * (Cmod z * Cmod z))
               (sum_f_R0 (fun k => / (INR (S k)) ^ 2)) (2 * (Cmod z * Cmod z)) T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun k => / (INR (S k)) ^ 2) N (2 * (Cmod z * Cmod z))).
      apply sum_eq; intros; ring.
Defined.

Definition Lf (z : C) : C :=
  match Rlt_dec 0 (Re z) with
  | left H => proj1_sig (tterm_cv z H)
  | right _ => C0
  end.
Definition Sderiv (z : C) : C :=
  match Rlt_dec 0 (Re z) with
  | left H => proj1_sig (gterm_cv z H)
  | right _ => C0
  end.

Lemma Lf_series : forall z (H : 0 < Re z), Cseries_cv (fun k => tterm k z) (Lf z).
Proof.
  intros z H. unfold Lf. destruct (Rlt_dec 0 (Re z)) as [H' | H'];
    [ exact (proj2_sig (tterm_cv z H')) | lra ].
Qed.
Lemma Sderiv_series : forall z (H : 0 < Re z), Cseries_cv (fun k => gterm k z) (Sderiv z).
Proof.
  intros z H. unfold Sderiv. destruct (Rlt_dec 0 (Re z)) as [H' | H'];
    [ exact (proj2_sig (gterm_cv z H')) | lra ].
Qed.

(* ---------- Group C: the segment remainder machinery ---------- *)

Section Rem.
Variables (z h : C) (n : nat).
Hypothesis Hseg : forall t, 0 <= t <= 1 -> RG (Cadd z (Cmul (RtoC t) h)).

Lemma line_t'_Re : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (tterm n (Cadd z (Cmul (RtoC u) h)))) t
    (Re (Cmul (gterm n (Cadd z (Cmul (RtoC t) h))) h)).
Proof.
  intros t Ht. apply (is_Cderiv_line_Re (fun w => tterm n w) z h).
  apply tterm_deriv; apply Hseg; exact Ht.
Qed.
Lemma line_t''_Re : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (Cmul (gterm n (Cadd z (Cmul (RtoC u) h))) h)) t
    (Re (Cmul (Cmul (dgterm n (Cadd z (Cmul (RtoC t) h))) h) h)).
Proof.
  intros t Ht. apply (is_Cderiv_line_Re (fun w => Cmul (gterm n w) h) z h).
  apply Cderiv_mul_const_r; apply gterm_deriv; apply Hseg; exact Ht.
Qed.
Lemma line_t'_Im : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (tterm n (Cadd z (Cmul (RtoC u) h)))) t
    (Im (Cmul (gterm n (Cadd z (Cmul (RtoC t) h))) h)).
Proof.
  intros t Ht. apply (is_Cderiv_line_Im (fun w => tterm n w) z h).
  apply tterm_deriv; apply Hseg; exact Ht.
Qed.
Lemma line_t''_Im : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (Cmul (gterm n (Cadd z (Cmul (RtoC u) h))) h)) t
    (Im (Cmul (Cmul (dgterm n (Cadd z (Cmul (RtoC t) h))) h) h)).
Proof.
  intros t Ht. apply (is_Cderiv_line_Im (fun w => Cmul (gterm n w) h) z h).
  apply Cderiv_mul_const_r; apply gterm_deriv; apply Hseg; exact Ht.
Qed.

Lemma rem_Re : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (dgterm n (Cadd z (Cmul (RtoC t) h))) <= Bn) ->
  Rabs (Re (tterm n (Cadd z (Cmul (RtoC 1) h)))
        - Re (tterm n (Cadd z (Cmul (RtoC 0) h)))
        - Re (Cmul (gterm n (Cadd z (Cmul (RtoC 0) h))) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Re (tterm n (Cadd z (Cmul (RtoC u) h))))
    (fun t => Re (Cmul (gterm n (Cadd z (Cmul (RtoC t) h))) h))
    (fun t => Re (Cmul (Cmul (dgterm n (Cadd z (Cmul (RtoC t) h))) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_t'_Re.
  - apply line_t''_Re.
  - intros t Ht. eapply Rle_trans; [ apply Cmod_Re_le | ]. rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ]. apply Hbd; exact Ht.
Qed.
Lemma rem_Im : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (dgterm n (Cadd z (Cmul (RtoC t) h))) <= Bn) ->
  Rabs (Im (tterm n (Cadd z (Cmul (RtoC 1) h)))
        - Im (tterm n (Cadd z (Cmul (RtoC 0) h)))
        - Im (Cmul (gterm n (Cadd z (Cmul (RtoC 0) h))) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Im (tterm n (Cadd z (Cmul (RtoC u) h))))
    (fun t => Im (Cmul (gterm n (Cadd z (Cmul (RtoC t) h))) h))
    (fun t => Im (Cmul (Cmul (dgterm n (Cadd z (Cmul (RtoC t) h))) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_t'_Im.
  - apply line_t''_Im.
  - intros t Ht. eapply Rle_trans; [ apply Cmod_Im_le | ]. rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ]. apply Hbd; exact Ht.
Qed.
End Rem.

Lemma Rn_bound : forall z h n, 0 < Re z -> Cmod h < Re z / 2 ->
  Cmod (Cminus (Cminus (tterm n (Cadd z h)) (tterm n z)) (Cmul (gterm n z) h))
    <= 2 * (/ (INR (S n)) ^ 2) * (Cmod h * Cmod h).
Proof.
  intros z h n Hz Hh.
  assert (Hseg : forall t, 0 <= t <= 1 -> RG (Cadd z (Cmul (RtoC t) h))).
  { intros t Ht. unfold RG. pose proof (seg_Re z h t Ht Hh). lra. }
  assert (Hbd : forall t, 0 <= t <= 1 ->
    Cmod (dgterm n (Cadd z (Cmul (RtoC t) h))) <= / (INR (S n)) ^ 2).
  { intros t Ht. apply Cmod_dgterm_le. pose proof (seg_Re z h t Ht Hh). lra. }
  assert (HW0 : 0 <= / (INR (S n)) ^ 2)
    by (left; apply Rinv_0_lt_compat, pow_lt, kk_pos).
  pose proof (rem_Re z h n Hseg (/ (INR (S n)) ^ 2) HW0 Hbd) as HRe.
  pose proof (rem_Im z h n Hseg (/ (INR (S n)) ^ 2) HW0 Hbd) as HIm.
  rewrite seg_pt_1, seg_pt_0 in HRe, HIm.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  rewrite !Re_Cminus, !Im_Cminus.
  replace (2 * (/ (INR (S n)) ^ 2) * (Cmod h * Cmod h))
    with ((/ (INR (S n)) ^ 2) * (Cmod h * Cmod h)
          + (/ (INR (S n)) ^ 2) * (Cmod h * Cmod h)) by ring.
  apply Rplus_le_compat; assumption.
Qed.

(* ---------- Group D: assemble sum_deriv + is_Cderiv ---------- *)

Lemma sum_deriv : forall z (H0 : 0 < Re z),
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall h Vzh Vz, Cmod h < del ->
      Cseries_cv (fun k => tterm k (Cadd z h)) Vzh ->
      Cseries_cv (fun k => tterm k z) Vz ->
      Cmod (Cminus (Cminus Vzh Vz) (Cmul (Sderiv z) h)) <= eps * Cmod h.
Proof.
  intros z H0 eps Heps.
  destruct invsq_cv as [T HT].
  assert (Hpos : forall N, 0 <= sum_f_R0 (fun k => / (INR (S k)) ^ 2) N).
  { intro N; induction N as [| N IHN].
    - change (sum_f_R0 (fun k => / (INR (S k)) ^ 2) 0) with (/ (INR (S 0)) ^ 2).
      left; apply Rinv_0_lt_compat, pow_lt, kk_pos.
    - rewrite tech5;
        assert (0 <= / (INR (S (S N))) ^ 2)
          by (left; apply Rinv_0_lt_compat, pow_lt, kk_pos); lra. }
  assert (HT0 : 0 <= T) by (apply (Un_cv_nonneg _ _ HT Hpos)).
  set (del := Rmin (Re z / 2) (Rmin 1 (eps / (2 * T + 1)))).
  assert (Hdiv : 0 < eps / (2 * T + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists del; split.
  { unfold del; repeat apply Rmin_glb_lt; lra. }
  intros h Vzh Vz Hh HVzh HVz.
  assert (Hh1 : Cmod h < Re z / 2)
    by (apply Rlt_le_trans with del; [ exact Hh | apply Rmin_l ]).
  assert (Hcs : Cseries_cv (fun k => Cmul (gterm k z) h) (Cmul (Sderiv z) h)).
  { replace (fun k => Cmul (gterm k z) h) with (fun k => Cmul h (gterm k z))
      by (apply functional_extensionality; intro k; ring).
    replace (Cmul (Sderiv z) h) with (Cmul h (Sderiv z)) by ring.
    apply Cseries_cv_cscal; apply Sderiv_series; exact H0. }
  assert (HR : Cseries_cv
    (fun k => Cminus (Cminus (tterm k (Cadd z h)) (tterm k z)) (Cmul (gterm k z) h))
    (Cminus (Cminus Vzh Vz) (Cmul (Sderiv z) h))).
  { apply Cseries_cv_minus; [ apply Cseries_cv_minus; assumption | exact Hcs ]. }
  assert (Hb_cv : Un_cv (sum_f_R0 (fun k => 2 * (/ (INR (S k)) ^ 2) * (Cmod h * Cmod h)))
                        (2 * (Cmod h * Cmod h) * T)).
  { replace (fun k => 2 * (/ (INR (S k)) ^ 2) * (Cmod h * Cmod h))
      with (fun k => 2 * (Cmod h * Cmod h) * (/ (INR (S k)) ^ 2))
      by (apply functional_extensionality; intro k; ring).
    replace (sum_f_R0 (fun k => 2 * (Cmod h * Cmod h) * (/ (INR (S k)) ^ 2)))
      with (fun N => 2 * (Cmod h * Cmod h) * sum_f_R0 (fun k => / (INR (S k)) ^ 2) N)
      by (apply functional_extensionality; intro N;
          rewrite (scal_sum (fun k => / (INR (S k)) ^ 2) N (2 * (Cmod h * Cmod h)));
          apply sum_eq; intros; ring).
    apply (CV_mult (fun _ => 2 * (Cmod h * Cmod h))
             (sum_f_R0 (fun k => / (INR (S k)) ^ 2)) _ T);
      [ apply Un_cv_const | exact HT ]. }
  destruct (Rseries_le_cv
    (fun k => Cmod (Cminus (Cminus (tterm k (Cadd z h)) (tterm k z)) (Cmul (gterm k z) h)))
    (fun k => 2 * (/ (INR (S k)) ^ 2) * (Cmod h * Cmod h))
    (2 * (Cmod h * Cmod h) * T)
    (fun k => Cmod_nonneg _)
    (fun k => Rn_bound z h k H0 Hh1)
    Hb_cv) as [Sa [HSa HSale]].
  eapply Rle_trans; [ apply (Cseries_triangle _ _ Sa HR HSa) | ].
  eapply Rle_trans; [ exact HSale | ].
  assert (Hh4 : Cmod h < eps / (2 * T + 1))
    by (apply Rlt_le_trans with del; [ exact Hh
        | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
  assert (Hkey : (2 * T + 1) * Cmod h < eps).
  { apply Rlt_le_trans with ((2 * T + 1) * (eps / (2 * T + 1)));
      [ apply Rmult_lt_compat_l; lra | apply Req_le; field; lra ]. }
  pose proof (Cmod_nonneg h); nra.
Qed.

Lemma L_holo : forall z, 0 < Re z -> is_Cderiv Lf z (Sderiv z).
Proof.
  intros z H0 eps Heps.
  destruct (sum_deriv z H0 eps Heps) as [del [Hdel Hsum]].
  set (del' := Rmin del (Re z / 2)).
  exists del'; split; [ unfold del'; apply Rmin_glb_lt; [ exact Hdel | lra ] | ].
  intros h Hh.
  assert (Hhd : Cmod h < del)
    by (apply Rlt_le_trans with del'; [ exact Hh | apply Rmin_l ]).
  assert (Hh2 : Cmod h < Re z / 2)
    by (apply Rlt_le_trans with del'; [ exact Hh | apply Rmin_r ]).
  assert (Hzh : 0 < Re (Cadd z h)).
  { assert (HRa : Re (Cadd z h) = Re z + Re h) by (unfold Cadd; cbn [Re]; ring).
    pose proof (Cmod_Re_le h) as HR.
    assert (Hlt : Rabs (Re h) < Re z / 2) by lra.
    apply Rabs_def2 in Hlt. rewrite HRa. lra. }
  exact (Hsum h (Lf (Cadd z h)) (Lf z) Hhd
           (Lf_series (Cadd z h) Hzh) (Lf_series z H0)).
Qed.

Lemma Lf_holo : forall z, 0 < Re z -> exists d, is_Cderiv Lf z d.
Proof. intros z H0. exists (Sderiv z). apply L_holo; exact H0. Qed.

(* ================================================================= *)
(*  Lf_agree: on the real axis  L(RtoC s) = RtoC (Winf s).             *)
(*  Bridge via 1-D ODE uniqueness: tterm k (RtoC .) and the real       *)
(*  antiderivative  A(x) = ln(1+x/K) - x/K  share derivative and value *)
(*  at 0, hence agree; then the sum telescopes to LW -> Winf.          *)
(* ================================================================= *)

(* --- real derivative helpers --- *)
Lemma linmul_deriv : forall c t, derivable_pt_lim (fun x => x * c) t c.
Proof.
  intros c t.
  assert (H := derivable_pt_lim_mult id (fct_cte c) t 1 0
                 (derivable_pt_lim_id t) (derivable_pt_lim_const c t)).
  unfold mult_fct, id, fct_cte in H.
  replace (1 * c + t * 0) with c in H by ring. exact H.
Qed.
Lemma xK_deriv : forall K t, derivable_pt_lim (fun x => x / K) t (/ K).
Proof. intros K t. exact (linmul_deriv (/ K) t). Qed.
Lemma f1_deriv : forall K t, derivable_pt_lim (fun x => 1 + x / K) t (/ K).
Proof.
  intros K t.
  assert (H := derivable_pt_lim_plus (fct_cte 1) (fun x => x / K) t 0 (/ K)
                 (derivable_pt_lim_const 1 t) (xK_deriv K t)).
  unfold plus_fct, fct_cte in H.
  replace (0 + / K) with (/ K) in H by ring. exact H.
Qed.
Lemma A_deriv : forall K t, 0 < K -> 0 <= t ->
  derivable_pt_lim (fun x => ln (1 + x / K) - x / K) t (/ (K + t) - / K).
Proof.
  intros K t HK Ht.
  assert (Hg : 0 < 1 + t / K)
    by (assert (0 <= t / K) by (apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; exact HK ]); lra).
  assert (Hln : derivable_pt_lim (fun x => ln (1 + x / K)) t (/ (K + t))).
  { assert (Hc := derivable_pt_lim_comp (fun x => 1 + x / K) ln t (/ K) (/ (1 + t / K))
                    (f1_deriv K t) (derivable_pt_lim_ln (1 + t / K) Hg)).
    unfold comp in Hc.
    replace (/ (1 + t / K) * / K) with (/ (K + t)) in Hc
      by (field; split; apply Rgt_not_eq; lra).
    exact Hc. }
  assert (H := derivable_pt_lim_minus (fun x => ln (1 + x / K)) (fun x => x / K) t
                 (/ (K + t)) (/ K) Hln (xK_deriv K t)).
  unfold minus_fct in H. exact H.
Qed.

Lemma zero_deriv_eq : forall (f : R -> R) (a b : R),
  a <= b -> (forall t, a <= t <= b -> derivable_pt_lim f t 0) -> f b = f a.
Proof.
  intros f a b Hab Hd. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq].
  - destruct (MVT_cor2 f (fun _ => 0) a b Hlt (fun c Hc => Hd c Hc)) as [c [Hc _]].
    rewrite Rmult_0_l in Hc. lra.
  - rewrite Heq. reflexivity.
Qed.

(* --- gterm on the real axis is RtoC of the real derivative --- *)
Lemma seg_RtoC : forall u, Cadd C0 (Cmul (RtoC u) C1) = RtoC u.
Proof. intro u. apply Ceq; unfold Cadd, Cmul, RtoC, C0, C1; cbn [Re Im]; ring. Qed.

Lemma gterm_RtoC : forall k t, 0 <= t ->
  gterm k (RtoC t) = RtoC (/ (INR (S k) + t) - / INR (S k)).
Proof.
  intros k t Ht. unfold gterm.
  assert (HKt : INR (S k) + t <> 0) by (pose proof (kk_pos k); lra).
  rewrite <- (RtoC_add (INR (S k)) t), (cinvRtoC (INR (S k) + t) HKt).
  apply Ceq; unfold Cminus, RtoC; cbn [Re Im]; ring.
Qed.

Lemma tterm_line_Re : forall k t, 0 <= t ->
  derivable_pt_lim (fun x => Re (tterm k (RtoC x))) t (/ (INR (S k) + t) - / INR (S k)).
Proof.
  intros k t Ht.
  assert (Hd : is_Cderiv (tterm k) (Cadd C0 (Cmul (RtoC t) C1)) (gterm k (RtoC t))).
  { rewrite seg_RtoC. apply tterm_deriv. unfold RG, RtoC; cbn [Re]. lra. }
  pose proof (is_Cderiv_line_Re (tterm k) C0 C1 (gterm k (RtoC t)) t Hd) as HL.
  assert (Hfun : (fun u => Re (tterm k (Cadd C0 (Cmul (RtoC u) C1))))
               = (fun x => Re (tterm k (RtoC x))))
    by (apply functional_extensionality; intro u; rewrite seg_RtoC; reflexivity).
  rewrite Hfun in HL.
  assert (Hval : Re (Cmul (gterm k (RtoC t)) C1) = / (INR (S k) + t) - / INR (S k))
    by (rewrite (gterm_RtoC k t Ht); unfold Cmul, RtoC, C1; cbn [Re Im]; ring).
  rewrite Hval in HL. exact HL.
Qed.
Lemma tterm_line_Im : forall k t, 0 <= t ->
  derivable_pt_lim (fun x => Im (tterm k (RtoC x))) t 0.
Proof.
  intros k t Ht.
  assert (Hd : is_Cderiv (tterm k) (Cadd C0 (Cmul (RtoC t) C1)) (gterm k (RtoC t))).
  { rewrite seg_RtoC. apply tterm_deriv. unfold RG, RtoC; cbn [Re]. lra. }
  pose proof (is_Cderiv_line_Im (tterm k) C0 C1 (gterm k (RtoC t)) t Hd) as HL.
  assert (Hfun : (fun u => Im (tterm k (Cadd C0 (Cmul (RtoC u) C1))))
               = (fun x => Im (tterm k (RtoC x))))
    by (apply functional_extensionality; intro u; rewrite seg_RtoC; reflexivity).
  rewrite Hfun in HL.
  assert (Hval : Im (Cmul (gterm k (RtoC t)) C1) = 0)
    by (rewrite (gterm_RtoC k t Ht); unfold Cmul, RtoC, C1; cbn [Re Im]; ring).
  rewrite Hval in HL. exact HL.
Qed.

Lemma tterm_RtoC_val : forall k s, 0 < s ->
  tterm k (RtoC s) = RtoC (ln (1 + s / INR (S k)) - s / INR (S k)).
Proof.
  intros k s Hs.
  assert (HRe : Re (tterm k (RtoC s)) = ln (1 + s / INR (S k)) - s / INR (S k)).
  { pose (f := fun x => Re (tterm k (RtoC x)) - (ln (1 + x / INR (S k)) - x / INR (S k))).
    assert (Hf0 : f 0 = 0).
    { unfold f. replace (RtoC 0) with C0 by (unfold RtoC, C0; reflexivity).
      rewrite (tterm_0 k). unfold C0; cbn [Re].
      replace (0 / INR (S k)) with 0 by (unfold Rdiv; rewrite Rmult_0_l; reflexivity).
      rewrite Rplus_0_r, ln_1. ring. }
    assert (Hfd : forall t, 0 <= t <= s -> derivable_pt_lim f t 0).
    { intros t Ht.
      assert (Hd := derivable_pt_lim_minus (fun x => Re (tterm k (RtoC x)))
                      (fun x => ln (1 + x / INR (S k)) - x / INR (S k)) t
                      (/ (INR (S k) + t) - / INR (S k)) (/ (INR (S k) + t) - / INR (S k))
                      (tterm_line_Re k t (proj1 Ht))
                      (A_deriv (INR (S k)) t (kk_pos k) (proj1 Ht))).
      unfold minus_fct in Hd. unfold f.
      replace 0 with ((/ (INR (S k) + t) - / INR (S k)) - (/ (INR (S k) + t) - / INR (S k)))
        by ring. exact Hd. }
    pose proof (zero_deriv_eq f 0 s (Rlt_le 0 s Hs) Hfd) as Hcst.
    rewrite Hf0 in Hcst. unfold f in Hcst. lra. }
  assert (HIm : Im (tterm k (RtoC s)) = 0).
  { pose (g := fun x => Im (tterm k (RtoC x))).
    assert (Hg0 : g 0 = 0).
    { unfold g. replace (RtoC 0) with C0 by (unfold RtoC, C0; reflexivity).
      rewrite (tterm_0 k). unfold C0; cbn [Im]. reflexivity. }
    assert (Hgd : forall t, 0 <= t <= s -> derivable_pt_lim g t 0)
      by (intros t Ht; exact (tterm_line_Im k t (proj1 Ht))).
    pose proof (zero_deriv_eq g 0 s (Rlt_le 0 s Hs) Hgd) as Hcst.
    rewrite Hg0 in Hcst. unfold g in Hcst. exact Hcst. }
  apply Ceq; [ rewrite HRe | rewrite HIm ]; unfold RtoC; cbn [Re Im]; reflexivity.
Qed.

(* --- telescoping to LW, hence to Winf --- *)
Lemma RtoC_Cpsum_loc : forall (f : nat -> R) N,
  Cpsum (fun k => RtoC (f k)) N = RtoC (sum_f_R0 f N).
Proof.
  intros f N. induction N as [| N IH].
  - reflexivity.
  - simpl Cpsum. rewrite IH, tech5. apply Ceq; unfold Cadd, RtoC; cbn [Re Im]; ring.
Qed.

Lemma LW_sum : forall s N, LW s (S N) = sum_f_R0 (fun k => Lg s (S k)) N.
Proof.
  intros s N. induction N as [| N IH].
  - change (LW s 1) with (LW s 0 + Lg s 1). change (LW s 0) with 0.
    change (sum_f_R0 (fun k => Lg s (S k)) 0) with (Lg s 1). ring.
  - change (LW s (S (S N))) with (LW s (S N) + Lg s (S (S N))).
    rewrite (tech5 (fun k => Lg s (S k)) N), IH. reflexivity.
Qed.

Lemma Lf_agree : forall s (Hs : 0 < s), Lf (RtoC s) = RtoC (Winf s Hs).
Proof.
  intros s Hs.
  assert (HRe : 0 < Re (RtoC s)) by (unfold RtoC; cbn [Re]; exact Hs).
  assert (Hcpsum : forall N, Cpsum (fun k => tterm k (RtoC s)) N = RtoC (LW s (S N))).
  { intro N.
    replace (fun k => tterm k (RtoC s)) with (fun k => RtoC (Lg s (S k))).
    2:{ apply functional_extensionality; intro k.
        rewrite (tterm_RtoC_val k s Hs). unfold Lg. reflexivity. }
    rewrite (RtoC_Cpsum_loc (fun k => Lg s (S k)) N), (LW_sum s N). reflexivity. }
  assert (HLW : Un_cv (LW s) (Winf s Hs))
    by (unfold Winf; exact (proj2_sig (LW_cv s Hs))).
  pose proof (Un_cv_shiftS (LW s) (Winf s Hs) HLW) as Hshift.
  assert (Hccv : CUn_cv (fun N => RtoC (LW s (S N))) (RtoC (Winf s Hs))).
  { intros eps Heps. destruct (Hshift eps Heps) as [M HM]. exists M. intros n Hn.
    pose proof (HM n Hn) as HMn. unfold R_dist in HMn.
    replace (Cminus (RtoC (LW s (S n))) (RtoC (Winf s Hs)))
      with (RtoC (LW s (S n) - Winf s Hs))
      by (apply Ceq; unfold Cminus, RtoC; cbn [Re Im]; ring).
    rewrite Cmod_RtoC. exact HMn. }
  assert (Hfinal : CUn_cv (Cpsum (fun k => tterm k (RtoC s))) (RtoC (Winf s Hs))).
  { intros eps Heps. destruct (Hccv eps Heps) as [M HM]. exists M. intros n Hn.
    rewrite (Hcpsum n). exact (HM n Hn). }
  pose proof (Lf_series (RtoC s) HRe) as HLf. unfold Cseries_cv in HLf.
  exact (CUn_cv_unique _ _ _ HLf Hfinal).
Qed.
Print Assumptions Lf_holo.
Print Assumptions Lf_agree.
