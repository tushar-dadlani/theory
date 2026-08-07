(* ================================================================= *)
(*  CZetaTerm3.v  —  Milestone B, brick B6c: the (ln)^3-weighted bound   *)
(*  on the third s-derivative term d3gtermC, and its summability.        *)
(*  One order up from CZetaTerm2's d2bound / Cmod_d2gtermC_bound /       *)
(*  d2bound_sum_cv, via the double MVT (base_deriv_d3sGC knot +          *)
(*  Re/Im_d3k_deriv) and the tail bound Cmod_dd3kb.                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CexpFull CPowBase CBaseDeriv
        CBaseDeriv3 CZetaTerm CZetaTerm2 CZetaDeriv2 CZetaDeriv5 CD3sGCKnot.
Open Scope R_scope.

Definition d3bound (s : C) (n : nat) : R :=
  (3 * (ln (INR (S (S n))) * ln (INR (S (S n))))
   + ln (INR (S (S n))) * ln (INR (S (S n))) * ln (INR (S (S n))) * Cmod s)
  * Rpower (INR (S n)) (- Re s - 1).

(* d3k s u = d3kb (Copp s) u, so the t-derivative of Re/Im (d3k s .) is
   Re/Im (dd3kb (Copp s) .). *)
Lemma d3k_eq : forall s u, d3k s u = d3kb (Copp s) u.
Proof.
  intros s u; unfold d3k, d3kb, dsk.
  replace (RtoC (- (ln u * ln u * ln u)))
    with (Cmul (RtoC (ln u * ln u)) (Cmul (Copp C1) (RtoC (ln u))))
    by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
  ring.
Qed.

Lemma Re_d3k_deriv : forall s c, 0 < c ->
  derivable_pt_lim (fun t => Re (d3k s t)) c (Re (dd3kb (Copp s) c)).
Proof.
  intros s c Hc.
  assert (Hf : (fun t => Re (d3k s t)) = (fun t => Re (d3kb (Copp s) t)))
    by (apply functional_extensionality; intro u; rewrite d3k_eq; reflexivity).
  rewrite Hf; apply Re_d3kb_deriv; exact Hc.
Qed.

Lemma Im_d3k_deriv : forall s c, 0 < c ->
  derivable_pt_lim (fun t => Im (d3k s t)) c (Im (dd3kb (Copp s) c)).
Proof.
  intros s c Hc.
  assert (Hf : (fun t => Im (d3k s t)) = (fun t => Im (d3kb (Copp s) t)))
    by (apply functional_extensionality; intro u; rewrite d3k_eq; reflexivity).
  rewrite Hf; apply Im_d3kb_deriv; exact Hc.
Qed.

Section Bound.
Variables (s : C) (n : nat).
Hypotheses (Hs0 : 0 <= Re s) (Hs1 : Cminus C1 s <> C0).

Let a := INR (S n).
Let b := INR (S (S n)).

Lemma d3_Ha : 0 < a. Proof. unfold a; apply lt_0_INR; lia. Qed.
Lemma d3_Ha1 : 1 <= a. Proof. unfold a; rewrite <- INR_1; apply le_INR; lia. Qed.
Lemma d3_Hab : a < b. Proof. unfold a, b; apply lt_INR; lia. Qed.
Lemma d3_Hba1 : b - a = 1. Proof. unfold a, b; rewrite (S_INR (S n)); ring. Qed.

Lemma dd3kb_tail_bound : forall zeta, a < zeta -> zeta < b ->
  Cmod (dd3kb (Copp s) zeta) <= d3bound s n.
Proof.
  intros zeta Hza Hzb.
  pose proof d3_Ha as Ha. pose proof d3_Ha1 as Ha1.
  assert (Hzpos : 0 < zeta) by lra.
  assert (Hz1 : 1 <= zeta) by lra.
  assert (Hlz0 : 0 <= ln zeta) by (rewrite <- ln_1; apply ln_le'; lra).
  assert (Hlzb : ln zeta <= ln b) by (apply ln_le'; lra).
  assert (Hlb0 : 0 <= ln b)
    by (rewrite <- ln_1; apply ln_le'; [ lra | unfold b; rewrite <- INR_1; apply le_INR; lia ]).
  eapply Rle_trans; [ apply Cmod_dd3kb; exact Hz1 | ].
  rewrite Cmod_opp.
  replace (Re (Copp s) - 1) with (- Re s - 1) by (unfold Copp; cbn [Re]; ring).
  unfold d3bound; fold b.
  apply Rmult_le_compat.
  - apply Rplus_le_le_0_compat.
    + apply Rmult_le_pos; [ lra | apply Rmult_le_pos; assumption ].
    + apply Rmult_le_pos; [ apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ]
        | apply Cmod_nonneg ].
  - apply Rlt_le; unfold Rpower; apply exp_pos.
  - apply Rplus_le_compat.
    + apply Rmult_le_compat_l; [ lra | apply Rmult_le_compat; assumption ].
    + apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
      apply Rmult_le_compat;
        [ apply Rmult_le_pos; assumption | assumption
        | apply Rmult_le_compat; assumption | assumption ].
  - replace (- Re s - 1) with (- (Re s + 1)) by ring.
    apply Rpow_negexp_anti; [ exact Ha | apply Rlt_le; exact Hza | lra ].
Qed.

Lemma Re_d3gtermC_bound : Rabs (Re (d3gtermC s n)) <= d3bound s n.
Proof.
  pose proof d3_Ha as Ha. pose proof d3_Hab as Hab. pose proof d3_Hba1 as Hba1.
  destruct (MVT_cor2 (fun t => Re (d3sGC s t)) (fun t => Re (d3k s t)) a b Hab
             (fun c Hc => base_deriv_d3sGC_Re s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Re (d3k s t)) (fun t => Re (dd3kb (Copp s) t)) a xi Hxia
             (fun c Hc => Re_d3k_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hval : Re (d3gtermC s n) = - (Re (dd3kb (Copp s) zeta) * (xi - a))).
  { unfold d3gtermC; fold a b; rewrite !Re_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (dd3kb (Copp s) zeta) * 1).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Cmod_Re_le.
    + rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r; apply dd3kb_tail_bound; lra.
Qed.

Lemma Im_d3gtermC_bound : Rabs (Im (d3gtermC s n)) <= d3bound s n.
Proof.
  pose proof d3_Ha as Ha. pose proof d3_Hab as Hab. pose proof d3_Hba1 as Hba1.
  destruct (MVT_cor2 (fun t => Im (d3sGC s t)) (fun t => Im (d3k s t)) a b Hab
             (fun c Hc => base_deriv_d3sGC_Im s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Im (d3k s t)) (fun t => Im (dd3kb (Copp s) t)) a xi Hxia
             (fun c Hc => Im_d3k_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hval : Im (d3gtermC s n) = - (Im (dd3kb (Copp s) zeta) * (xi - a))).
  { unfold d3gtermC; fold a b; rewrite !Im_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (dd3kb (Copp s) zeta) * 1).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Cmod_Im_le.
    + rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r; apply dd3kb_tail_bound; lra.
Qed.

End Bound.

Lemma Cmod_d3gtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (d3gtermC s n) <= 2 * d3bound s n.
Proof.
  intros s n Hs0 Hs1.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  pose proof (Re_d3gtermC_bound s n Hs0 Hs1) as HR.
  pose proof (Im_d3gtermC_bound s n Hs0 Hs1) as HI.
  lra.
Qed.

(* summability of d3bound: the (ln)^3-weighted p-series *)
Lemma d3bound_sum_cv : forall s, 0 < Re s -> { T | Un_cv (sum_f_R0 (d3bound s)) T }.
Proof.
  intros s Hs.
  set (c := Re s / 2).
  assert (Hc : 0 <= c) by (unfold c; lra).
  destruct (lnpow_pseries_cv c (Re s + 1) Hc ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- (Re s + 1))).
  set (K := 3 * ((4 / Re s) * (4 / Re s)) + Cmod s * ((6 / Re s) * ((6 / Re s) * (6 / Re s)))).
  assert (HK : 0 <= K).
  { unfold K; pose proof (Cmod_nonneg s).
    apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; [ lra | apply Rmult_le_pos; apply Rlt_le; apply Rdiv_lt_0_compat; lra ].
    - apply Rmult_le_pos; [ assumption | apply Rmult_le_pos;
        [ apply Rlt_le; apply Rdiv_lt_0_compat; lra
        | apply Rmult_le_pos; apply Rlt_le; apply Rdiv_lt_0_compat; lra ] ]. }
  assert (Hd0 : forall n, 0 <= d3bound s n).
  { intro n; unfold d3bound.
    assert (Hb1 : 1 <= INR (S (S n))) by (rewrite <- INR_1; apply le_INR; lia).
    assert (0 <= ln (INR (S (S n)))) by (rewrite <- ln_1; apply ln_le'; lra).
    apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
    apply Rplus_le_le_0_compat; [ apply Rmult_le_pos; [ lra | apply Rmult_le_pos; assumption ]
      | apply Rmult_le_pos; [ apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ]
        | apply Cmod_nonneg ] ]. }
  assert (Hbound : forall n, d3bound s n <= K * term n).
  { intro n; unfold d3bound, term.
    set (b := INR (S (S n))).
    assert (Hb1 : 1 <= b) by (unfold b; rewrite <- INR_1; apply le_INR; lia).
    assert (Hlnb0 : 0 <= ln b) by (rewrite <- ln_1; apply ln_le'; lra).
    assert (Hsq : ln b * ln b <= (4 / Re s) * (4 / Re s) * Rpower b c).
    { assert (Hq : ln b <= 4 / Re s * Rpower b (Re s / 4)).
      { replace (4 / Re s) with (/ (Re s / 4)) by (field; lra).
        apply ln_le_rpow; [ lra | exact Hb1 ]. }
      apply Rle_trans with ((4 / Re s * Rpower b (Re s / 4)) * (4 / Re s * Rpower b (Re s / 4))).
      - apply Rmult_le_compat; assumption.
      - replace ((4 / Re s * Rpower b (Re s / 4)) * (4 / Re s * Rpower b (Re s / 4)))
          with ((4 / Re s) * (4 / Re s) * (Rpower b (Re s / 4) * Rpower b (Re s / 4))) by ring.
        rewrite <- Rpower_plus; replace (Re s / 4 + Re s / 4) with c by (unfold c; field).
        apply Rle_refl. }
    assert (Hcube : ln b * ln b * ln b
                    <= (6 / Re s) * ((6 / Re s) * (6 / Re s)) * Rpower b c).
    { assert (Hq : ln b <= 6 / Re s * Rpower b (Re s / 6)).
      { replace (6 / Re s) with (/ (Re s / 6)) by (field; lra).
        apply ln_le_rpow; [ lra | exact Hb1 ]. }
      apply Rle_trans with
        (((6 / Re s * Rpower b (Re s / 6)) * (6 / Re s * Rpower b (Re s / 6)))
          * (6 / Re s * Rpower b (Re s / 6))).
      - apply Rmult_le_compat;
          [ apply Rmult_le_pos; exact Hlnb0 | exact Hlnb0
          | apply Rmult_le_compat; assumption | exact Hq ].
      - replace (((6 / Re s * Rpower b (Re s / 6)) * (6 / Re s * Rpower b (Re s / 6)))
          * (6 / Re s * Rpower b (Re s / 6)))
          with ((6 / Re s) * ((6 / Re s) * (6 / Re s))
                * (Rpower b (Re s / 6) * (Rpower b (Re s / 6) * Rpower b (Re s / 6)))) by ring.
        rewrite <- !Rpower_plus; replace (Re s / 6 + (Re s / 6 + Re s / 6)) with c by (unfold c; field).
        apply Rle_refl. }
    replace (- Re s - 1) with (- (Re s + 1)) by ring.
    rewrite <- (Rmult_assoc K (Rpower b c) (Rpower (INR (S n)) (- (Re s + 1)))).
    apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
    unfold K.
    replace ((3 * ((4 / Re s) * (4 / Re s)) + Cmod s * ((6 / Re s) * ((6 / Re s) * (6 / Re s))))
             * Rpower b c)
      with (3 * ((4 / Re s) * (4 / Re s) * Rpower b c)
            + Cmod s * ((6 / Re s) * ((6 / Re s) * (6 / Re s)) * Rpower b c)) by ring.
    apply Rplus_le_compat.
    - apply Rmult_le_compat_l; [ lra | exact Hsq ].
    - rewrite (Rmult_comm (ln b * ln b * ln b) (Cmod s)).
      apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hcube ]. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hd0 (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (K * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun m => K * term m) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun m => K * term m) with (fun m => term m * K)
        by (apply functional_extensionality; intro m; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact HK | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M; rewrite tech5.
      assert (0 <= term (S M)) by (unfold term; apply Rmult_le_pos; apply Rlt_le;
        unfold Rpower; apply exp_pos); lra.
Qed.

Print Assumptions Cmod_d3gtermC_bound.
Print Assumptions d3bound_sum_cv.

(* ================================================================= *)
(*  END CZetaTerm3.v  —  (ln)^3 bound on d3gtermC and its summability.   *)
(* ================================================================= *)
