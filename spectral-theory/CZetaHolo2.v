(* ================================================================= *)
(*  CZetaHolo2.v  —  Milestone B, brick B7: differentiation under the   *)
(*  sum for the zeta' series.  One order up from CZetaHolo's sum_deriv:  *)
(*  the analytic derivative series G'(w) = Sum dgtermC(w,n) is itself    *)
(*  differentiable at z with derivative Sum d2gtermC(z,n), via the       *)
(*  (ln)^3-weighted segment-uniform second-order remainder.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull Holomorphic CexpRemainder
        CSeries CSeriesLin CDeriv CDerivLine CBaseDeriv CBaseDeriv2 CBaseDeriv3
        CZetaTerm CZetaTerm2 CZetaTerm3 CZetaDeriv CZetaDeriv2 CZetaDeriv3
        CZetaDeriv4 CZetaDeriv5 CD3sGCKnot CZeta CZetaHolo.
Open Scope R_scope.

(* the (ln)^3-weighted segment weight *)
Definition W2summand (z : C) (n : nat) : R :=
  (3 * (ln (INR (S (S n))) * ln (INR (S (S n))))
   + ln (INR (S (S n))) * ln (INR (S (S n))) * ln (INR (S (S n))) * (Cmod z + 1))
  * Rpower (INR (S n)) (- (Re z / 2) - 1).

Lemma W2summand_nonneg : forall z n, 0 <= W2summand z n.
Proof.
  intros z n; unfold W2summand.
  assert (0 <= ln (INR (S (S n))))
    by (rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]).
  apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
  apply Rplus_le_le_0_compat; [ apply Rmult_le_pos; [ lra | apply Rmult_le_pos; assumption ]
    | apply Rmult_le_pos; [ apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ]
      | pose proof (Cmod_nonneg z); lra ] ].
Qed.

(* the (ln)^3-weighted p-series with free parameters q>0, M>=0 *)
Lemma weighted_pseries_cv2 : forall q M, 0 < q -> 0 <= M ->
  { T | Un_cv (sum_f_R0 (fun n =>
    (3 * (ln (INR (S (S n))) * ln (INR (S (S n))))
     + ln (INR (S (S n))) * ln (INR (S (S n))) * ln (INR (S (S n))) * M)
    * Rpower (INR (S n)) (- q - 1))) T }.
Proof.
  intros q M Hq HM.
  set (c := q / 2).
  assert (Hc : 0 <= c) by (unfold c; lra).
  destruct (lnpow_pseries_cv c (q + 1) Hc ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- (q + 1))).
  set (K := 3 * ((4 / q) * (4 / q)) + M * ((6 / q) * ((6 / q) * (6 / q)))).
  assert (HK : 0 <= K).
  { unfold K; apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; [ lra | apply Rmult_le_pos; apply Rlt_le; apply Rdiv_lt_0_compat; lra ].
    - apply Rmult_le_pos; [ assumption | apply Rmult_le_pos;
        [ apply Rlt_le; apply Rdiv_lt_0_compat; lra
        | apply Rmult_le_pos; apply Rlt_le; apply Rdiv_lt_0_compat; lra ] ]. }
  set (d3 := fun n =>
    (3 * (ln (INR (S (S n))) * ln (INR (S (S n))))
     + ln (INR (S (S n))) * ln (INR (S (S n))) * ln (INR (S (S n))) * M)
    * Rpower (INR (S n)) (- q - 1)).
  assert (Hd0 : forall n, 0 <= d3 n).
  { intro n; unfold d3.
    assert (Hb1 : 1 <= INR (S (S n))) by (rewrite <- INR_1; apply le_INR; lia).
    assert (0 <= ln (INR (S (S n)))) by (rewrite <- ln_1; apply ln_le'; lra).
    apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
    apply Rplus_le_le_0_compat; [ apply Rmult_le_pos; [ lra | apply Rmult_le_pos; assumption ]
      | apply Rmult_le_pos; [ apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ]
        | assumption ] ]. }
  assert (Hbound : forall n, d3 n <= K * term n).
  { intro n; unfold d3, term.
    set (b := INR (S (S n))).
    assert (Hb1 : 1 <= b) by (unfold b; rewrite <- INR_1; apply le_INR; lia).
    assert (Hlnb0 : 0 <= ln b) by (rewrite <- ln_1; apply ln_le'; lra).
    assert (Hsq : ln b * ln b <= (4 / q) * (4 / q) * Rpower b c).
    { assert (Hqq : ln b <= 4 / q * Rpower b (q / 4)).
      { replace (4 / q) with (/ (q / 4)) by (field; lra).
        apply ln_le_rpow; [ lra | exact Hb1 ]. }
      apply Rle_trans with ((4 / q * Rpower b (q / 4)) * (4 / q * Rpower b (q / 4))).
      - apply Rmult_le_compat; assumption.
      - replace ((4 / q * Rpower b (q / 4)) * (4 / q * Rpower b (q / 4)))
          with ((4 / q) * (4 / q) * (Rpower b (q / 4) * Rpower b (q / 4))) by ring.
        rewrite <- Rpower_plus; replace (q / 4 + q / 4) with c by (unfold c; field).
        apply Rle_refl. }
    assert (Hcube : ln b * ln b * ln b
                    <= (6 / q) * ((6 / q) * (6 / q)) * Rpower b c).
    { assert (Hqq : ln b <= 6 / q * Rpower b (q / 6)).
      { replace (6 / q) with (/ (q / 6)) by (field; lra).
        apply ln_le_rpow; [ lra | exact Hb1 ]. }
      apply Rle_trans with
        (((6 / q * Rpower b (q / 6)) * (6 / q * Rpower b (q / 6))) * (6 / q * Rpower b (q / 6))).
      - apply Rmult_le_compat;
          [ apply Rmult_le_pos; exact Hlnb0 | exact Hlnb0
          | apply Rmult_le_compat; assumption | exact Hqq ].
      - replace (((6 / q * Rpower b (q / 6)) * (6 / q * Rpower b (q / 6))) * (6 / q * Rpower b (q / 6)))
          with ((6 / q) * ((6 / q) * (6 / q))
                * (Rpower b (q / 6) * (Rpower b (q / 6) * Rpower b (q / 6)))) by ring.
        rewrite <- !Rpower_plus; replace (q / 6 + (q / 6 + q / 6)) with c by (unfold c; field).
        apply Rle_refl. }
    replace (- q - 1) with (- (q + 1)) by ring.
    rewrite <- (Rmult_assoc K (Rpower b c) (Rpower (INR (S n)) (- (q + 1)))).
    apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
    unfold K.
    replace ((3 * ((4 / q) * (4 / q)) + M * ((6 / q) * ((6 / q) * (6 / q)))) * Rpower b c)
      with (3 * ((4 / q) * (4 / q) * Rpower b c) + M * ((6 / q) * ((6 / q) * (6 / q)) * Rpower b c))
      by ring.
    apply Rplus_le_compat.
    - apply Rmult_le_compat_l; [ lra | exact Hsq ].
    - rewrite (Rmult_comm (ln b * ln b * ln b) M).
      apply Rmult_le_compat_l; [ exact HM | exact Hcube ]. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hd0 (S N)); unfold d3 in *; lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (K * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun m => K * term m) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun m => K * term m) with (fun m => term m * K)
        by (apply functional_extensionality; intro m; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact HK | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M0; rewrite tech5.
      assert (0 <= term (S M0)) by (unfold term; apply Rmult_le_pos; apply Rlt_le;
        unfold Rpower; apply exp_pos); lra.
Qed.

Section Remainder2.
Variables (z h : C) (n : nat).
Hypothesis Hseg : forall t, 0 <= t <= 1 -> Cminus C1 (Cadd z (Cmul (RtoC t) h)) <> C0.

Lemma line_phi'_Re2 : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (dgtermC (Cadd z (Cmul (RtoC u) h)) n)) t
    (Re (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Re (fun w => dgtermC w n) z h).
  apply dgtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi''_Re2 : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (Cmul (d2gtermC (Cadd z (Cmul (RtoC u) h)) n) h)) t
    (Re (Cmul (Cmul (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Re (fun w => Cmul (d2gtermC w n) h) z h).
  apply Cderiv_mul_const_r; apply d2gtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi'_Im2 : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (dgtermC (Cadd z (Cmul (RtoC u) h)) n)) t
    (Im (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Im (fun w => dgtermC w n) z h).
  apply dgtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi''_Im2 : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (Cmul (d2gtermC (Cadd z (Cmul (RtoC u) h)) n) h)) t
    (Im (Cmul (Cmul (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Im (fun w => Cmul (d2gtermC w n) h) z h).
  apply Cderiv_mul_const_r; apply d2gtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma remainder_Re2 : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) <= Bn) ->
  Rabs (Re (dgtermC (Cadd z (Cmul (RtoC 1) h)) n)
        - Re (dgtermC (Cadd z (Cmul (RtoC 0) h)) n)
        - Re (Cmul (d2gtermC (Cadd z (Cmul (RtoC 0) h)) n) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Re (dgtermC (Cadd z (Cmul (RtoC u) h)) n))
    (fun t => Re (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h))
    (fun t => Re (Cmul (Cmul (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_phi'_Re2.
  - apply line_phi''_Re2.
  - intros t Ht.
    eapply Rle_trans; [ apply Cmod_Re_le | ].
    rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Hbd; exact Ht.
Qed.

Lemma remainder_Im2 : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) <= Bn) ->
  Rabs (Im (dgtermC (Cadd z (Cmul (RtoC 1) h)) n)
        - Im (dgtermC (Cadd z (Cmul (RtoC 0) h)) n)
        - Im (Cmul (d2gtermC (Cadd z (Cmul (RtoC 0) h)) n) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Im (dgtermC (Cadd z (Cmul (RtoC u) h)) n))
    (fun t => Im (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h))
    (fun t => Im (Cmul (Cmul (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_phi'_Im2.
  - apply line_phi''_Im2.
  - intros t Ht.
    eapply Rle_trans; [ apply Cmod_Im_le | ].
    rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Hbd; exact Ht.
Qed.

End Remainder2.

Lemma seg_d3_bound : forall z h n t, 0 <= t <= 1 -> 0 < Re z ->
  Cmod h < Re z / 2 -> Cmod h < Cmod (Cminus z C1) / 2 -> Cmod h < 1 ->
  Cmod (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) <= 2 * W2summand z n.
Proof.
  intros z h n t Ht Hz Hh1 Hh2 Hh3.
  set (s' := Cadd z (Cmul (RtoC t) h)).
  assert (HRe : Re z / 2 <= Re s') by (apply seg_Re; assumption).
  assert (Hne : Cminus C1 s' <> C0) by (apply seg_ne1; assumption).
  assert (Hlnb : 0 <= ln (INR (S (S n))))
    by (rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]).
  assert (HsM : Cmod s' <= Cmod z + 1).
  { unfold s'. eapply Rle_trans; [ apply Cmod_triangle | ].
    assert (Cmod (Cmul (RtoC t) h) <= Cmod h).
    { rewrite Cmod_mul, Cmod_RtoC, (Rabs_right t) by lra.
      apply Rle_trans with (1 * Cmod h); [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ] | lra ]. }
    lra. }
  eapply Rle_trans; [ apply Cmod_d3gtermC_bound; [ lra | exact Hne ] | ].
  apply Rmult_le_compat_l; [ lra | ].
  unfold d3bound, W2summand.
  apply Rmult_le_compat.
  - apply Rplus_le_le_0_compat; [ apply Rmult_le_pos; [ lra | apply Rmult_le_pos; assumption ]
      | apply Rmult_le_pos; [ apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ]
        | apply Cmod_nonneg ] ].
  - apply Rlt_le; unfold Rpower; apply exp_pos.
  - apply Rplus_le_compat_l; apply Rmult_le_compat_l;
      [ apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ] | exact HsM ].
  - apply Rle_Rpower; [ rewrite <- INR_1; apply le_INR; lia | lra ].
Qed.

Lemma Rn_bound2 : forall z h n, 0 < Re z ->
  Cmod h < Re z / 2 -> Cmod h < Cmod (Cminus z C1) / 2 -> Cmod h < 1 ->
  Cmod (Cminus (Cminus (dgtermC (Cadd z h) n) (dgtermC z n)) (Cmul (d2gtermC z n) h))
    <= 4 * W2summand z n * (Cmod h * Cmod h).
Proof.
  intros z h n Hz Hh1 Hh2 Hh3.
  assert (Hseg : forall t, 0 <= t <= 1 -> Cminus C1 (Cadd z (Cmul (RtoC t) h)) <> C0)
    by (intros t Ht; apply seg_ne1; assumption).
  assert (HW0 : 0 <= 2 * W2summand z n).
  { pose proof (W2summand_nonneg z n); lra. }
  assert (Hbd : forall t, 0 <= t <= 1 -> Cmod (d3gtermC (Cadd z (Cmul (RtoC t) h)) n) <= 2 * W2summand z n)
    by (intros t Ht; apply seg_d3_bound; assumption).
  pose proof (remainder_Re2 z h n Hseg (2 * W2summand z n) HW0 Hbd) as HRe.
  pose proof (remainder_Im2 z h n Hseg (2 * W2summand z n) HW0 Hbd) as HIm.
  rewrite seg_pt_1, seg_pt_0 in HRe, HIm.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  rewrite !Re_Cminus, !Im_Cminus.
  replace (4 * W2summand z n * (Cmod h * Cmod h))
    with (2 * W2summand z n * (Cmod h * Cmod h) + 2 * W2summand z n * (Cmod h * Cmod h)) by ring.
  apply Rplus_le_compat; assumption.
Qed.

(* the sum G'(w) = sum dgtermC(w,.) is differentiable at z with
   derivative D2 = sum d2gtermC(z,.). *)
Lemma sum_deriv2 : forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall h Vzh Vz, Cmod h < del ->
      Cseries_cv (dgtermC (Cadd z h)) Vzh -> Cseries_cv (dgtermC z) Vz ->
      Cmod (Cminus (Cminus Vzh Vz) (Cmul (proj1_sig (d2gtermC_cv z H0 H1)) h)) <= eps * Cmod h.
Proof.
  intros z H0 H1 eps Heps.
  destruct (d2gtermC_cv z H0 H1) as [D HD]; cbn [proj1_sig].
  destruct (weighted_pseries_cv2 (Re z / 2) (Cmod z + 1) ltac:(lra)
             ltac:(pose proof (Cmod_nonneg z); lra)) as [T HT].
  assert (HTsum : Un_cv (sum_f_R0 (W2summand z)) T)
    by (unfold W2summand;
        replace (fun n => (3 * (ln (INR (S (S n))) * ln (INR (S (S n)))) +
          ln (INR (S (S n))) * ln (INR (S (S n))) * ln (INR (S (S n))) * (Cmod z + 1)) *
          Rpower (INR (S n)) (- (Re z / 2) - 1))
        with (W2summand z) in HT by (apply functional_extensionality; intro; unfold W2summand;
          f_equal); exact HT).
  assert (HT0 : 0 <= T).
  { apply (Un_cv_nonneg (sum_f_R0 (W2summand z))); [ exact HTsum | ].
    intro N; induction N; [ simpl; apply W2summand_nonneg
      | rewrite tech5; pose proof (W2summand_nonneg z (S N)); lra ]. }
  assert (Hz1 : 0 < Cmod (Cminus z C1))
    by (apply Cmod_pos_ne0; intro Hc;
        apply H1; replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  set (del := Rmin (Re z / 2) (Rmin (Cmod (Cminus z C1) / 2) (Rmin 1 (eps / (4 * T + 1))))).
  assert (Hdiv : 0 < eps / (4 * T + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists del; split.
  { unfold del; repeat apply Rmin_glb_lt; lra. }
  intros h Vzh Vz Hh HVzh HVz.
  assert (Hh1 : Cmod h < Re z / 2) by (apply Rlt_le_trans with del; [ exact Hh | apply Rmin_l ]).
  assert (Hh2 : Cmod h < Cmod (Cminus z C1) / 2)
    by (apply Rlt_le_trans with del; [ exact Hh | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (Hh3 : Cmod h < 1)
    by (apply Rlt_le_trans with del; [ exact Hh
        | eapply Rle_trans; [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ] ]).
  assert (Hh4 : Cmod h < eps / (4 * T + 1))
    by (apply Rlt_le_trans with del; [ exact Hh
        | eapply Rle_trans; [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ] ]).
  assert (Hcs : Cseries_cv (fun n => Cmul (d2gtermC z n) h) (Cmul D h)).
  { replace (fun n => Cmul (d2gtermC z n) h) with (fun n => Cmul h (d2gtermC z n))
      by (apply functional_extensionality; intro n; ring).
    replace (Cmul D h) with (Cmul h D) by ring.
    apply Cseries_cv_cscal; exact HD. }
  assert (HR : Cseries_cv
    (fun n => Cminus (Cminus (dgtermC (Cadd z h) n) (dgtermC z n)) (Cmul (d2gtermC z n) h))
    (Cminus (Cminus Vzh Vz) (Cmul D h))).
  { apply Cseries_cv_minus; [ apply Cseries_cv_minus; assumption | exact Hcs ]. }
  assert (Hb_cv : Un_cv (sum_f_R0 (fun n => 4 * W2summand z n * (Cmod h * Cmod h)))
                        (4 * (Cmod h * Cmod h) * T)).
  { replace (fun n => 4 * W2summand z n * (Cmod h * Cmod h))
      with (fun n => 4 * (Cmod h * Cmod h) * W2summand z n)
      by (apply functional_extensionality; intro n; ring).
    replace (sum_f_R0 (fun n => 4 * (Cmod h * Cmod h) * W2summand z n))
      with (fun N => 4 * (Cmod h * Cmod h) * sum_f_R0 (W2summand z) N)
      by (apply functional_extensionality; intro N;
          rewrite (scal_sum (W2summand z) N (4 * (Cmod h * Cmod h))); apply sum_eq; intros; ring).
    apply (CV_mult (fun _ => 4 * (Cmod h * Cmod h)) (sum_f_R0 (W2summand z)) _ T);
      [ apply Un_cv_const | exact HTsum ]. }
  destruct (Rseries_le_cv
    (fun n => Cmod (Cminus (Cminus (dgtermC (Cadd z h) n) (dgtermC z n)) (Cmul (d2gtermC z n) h)))
    (fun n => 4 * W2summand z n * (Cmod h * Cmod h))
    (4 * (Cmod h * Cmod h) * T)
    (fun n => Cmod_nonneg _)
    (fun n => Rn_bound2 z h n H0 Hh1 Hh2 Hh3)
    Hb_cv) as [Sa [HSa HSale]].
  eapply Rle_trans; [ apply (Cseries_triangle _ _ Sa HR HSa) | ].
  eapply Rle_trans; [ exact HSale | ].
  assert (Hkey : (4 * T + 1) * Cmod h < eps).
  { apply Rlt_le_trans with ((4 * T + 1) * (eps / (4 * T + 1)));
      [ apply Rmult_lt_compat_l; lra | apply Req_le; field; lra ]. }
  pose proof (Cmod_nonneg h); nra.
Qed.

Print Assumptions sum_deriv2.

(* ================================================================= *)
(*  END CZetaHolo2.v  —  the zeta' series is differentiable (-> zeta''). *)
(* ================================================================= *)
