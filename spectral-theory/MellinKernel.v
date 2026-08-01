(* ================================================================= *)
(*  MellinKernel.v  —  Riemann FE milestone R2b, capstone:          *)
(*  the Mellin kernel scaling  ∫₀^∞ t^{a-1}e^{-ct}dt = c^{-a}·Γ(a).   *)
(*                                                                    *)
(*  The substitution x=ct is done on the FINITE [ε,A] (cov_local),    *)
(*  and the image [cε,cA] is split at the fixed point 1 with the      *)
(*  FINITE Chasles RiemannInt_P26 — never an "improper Chasles".      *)
(*  Choosing ε_k = δ/(k+1), A_k = μ(k+1) with δ=1/max(1,c),           *)
(*  μ=max(1,1/c) keeps ε_k, cε_k ∈ (0,1] and A_k, cA_k ≥ 1 for every  *)
(*  k, so both sides straddle 1 throughout and the two improper       *)
(*  limits assemble cleanly.  Then UL_sequence pins                    *)
(*     mellin a c = Rpower c (-a) · Gam a.                            *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal ImproperCv0 ImproperCv1 MellinElem MellinTail
        RpowerZero JacobiTheta LocalCoV.
Open Scope R_scope.

(* --- Rpower of a product of positive bases --- *)

Lemma Rpower_mult_base : forall x y z, 0 < x -> 0 < y ->
  Rpower (x * y) z = Rpower x z * Rpower y z.
Proof.
  intros x y z Hx Hy; unfold Rpower.
  rewrite ln_mult by assumption; rewrite Rmult_plus_distr_l, exp_plus; reflexivity.
Qed.

(* --- scaling a Riemann integral by a constant --- *)

Lemma RInt_scal_val : forall f k a b (Hf : Riemann_integrable f a b)
  (Hkf : Riemann_integrable (fun x => k * f x) a b),
  a <= b -> RiemannInt Hkf = k * RiemannInt Hf.
Proof.
  intros f k a b Hf Hkf Hab.
  pose (H0 := RiemannInt_P14 a b 0).
  pose (H3 := RiemannInt_P10 k H0 Hf).
  assert (Heq : RiemannInt Hkf = RiemannInt H3)
    by (apply RiemannInt_P18; [ exact Hab | intros x _; unfold fct_cte; ring ]).
  rewrite Heq, (RiemannInt_P13 H0 Hf H3), (RiemannInt_P15 H0); ring.
Qed.

(* --- the pointwise substituted integrand --- *)

Lemma gnk_scale_pt : forall a c t, 0 < c -> 0 < t ->
  gnk a 1 (c * t) * c = Rpower c a * gnk a c t.
Proof.
  intros a c t Hc Ht; unfold gnk.
  rewrite (Rpower_mult_base c t (a - 1) Hc Ht).
  replace (- (1 * (c * t))) with (- (c * t)) by ring.
  assert (Hca : Rpower c (a - 1) * c = Rpower c a).
  { rewrite <- (Rpower_1 c Hc) at 2; rewrite <- Rpower_plus;
      apply (f_equal (Rpower c)); ring. }
  rewrite <- Hca; ring.
Qed.

(* --- sequence helpers --- *)

Lemma cv_infty_scale : forall d, 0 < d -> forall u, cv_infty u -> cv_infty (fun k => d * u k).
Proof.
  intros d Hd u Hu M; destruct (Hu (M / d)) as [N HN]; exists N; intros k Hk.
  specialize (HN k Hk); apply Rmult_lt_reg_l with (/ d); [ apply Rinv_0_lt_compat; exact Hd | ].
  rewrite <- Rmult_assoc; rewrite Rinv_l by (apply Rgt_not_eq; exact Hd); rewrite Rmult_1_l.
  replace (/ d * M) with (M / d) by (unfold Rdiv; ring); exact HN.
Qed.

Lemma Un_cv_scale0 : forall d u, Un_cv u 0 -> Un_cv (fun k => d * u k) 0.
Proof.
  intros d u Hu.
  replace 0 with (d * 0) by ring.
  apply (CV_mult (fun _ => d) u d 0); [ apply Un_cv_const | exact Hu ].
Qed.

(* ================================================================= *)
(*  The kernel scaling identity.                                    *)
(* ================================================================= *)

Theorem mellin_scale : forall a c (Ha : 0 < a) (Hc : 0 < c),
  mellin a c Ha Hc = Rpower c (- a) * Gam a Ha.
Proof.
  intros a c Ha Hc.
  (* range-controlling constants *)
  set (dm := / Rmax 1 c).
  set (mu := Rmax 1 (/ c)).
  assert (Hmc : 1 <= Rmax 1 c) by apply Rmax_l.
  assert (Hmc0 : 0 < Rmax 1 c) by lra.
  assert (Hdm0 : 0 < dm) by (unfold dm; apply Rinv_0_lt_compat; exact Hmc0).
  assert (Hdm1 : dm <= 1) by (unfold dm; apply inv_le_1; exact Hmc).
  assert (Hcdm1 : c * dm <= 1).
  { unfold dm; apply Rle_trans with (Rmax 1 c * / Rmax 1 c).
    - apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hmc0 | apply Rmax_r ].
    - rewrite Rinv_r by (apply Rgt_not_eq; exact Hmc0); apply Rle_refl. }
  assert (Hmu1 : 1 <= mu) by apply Rmax_l.
  assert (Hcinv : 0 < / c) by (apply Rinv_0_lt_compat; exact Hc).
  assert (Hcmu : 1 <= c * mu).
  { unfold mu; apply Rle_trans with (c * / c).
    - rewrite Rinv_r by (apply Rgt_not_eq; exact Hc); apply Rle_refl.
    - apply Rmult_le_compat_l; [ left; exact Hc | apply Rmax_r ]. }
  (* the sequences *)
  set (ek := fun k => dm / (1 + INR k)).
  set (Ak := fun k => mu * (1 + INR k)).
  assert (Hp : forall k, 0 < 1 + INR k) by (intro k; pose proof (pos_INR k); lra).
  assert (Hek0 : forall k, 0 < ek k)
    by (intro k; unfold ek; apply Rdiv_lt_0_compat; [ exact Hdm0 | apply Hp ]).
  assert (Hek1 : forall k, ek k <= 1).
  { intro k; unfold ek; apply Rle_trans with dm; [ | exact Hdm1 ].
    rewrite <- (Rmult_1_r dm) at 2; unfold Rdiv; apply Rmult_le_compat_l;
      [ left; exact Hdm0 | rewrite <- Rinv_1; apply Rinv_le_contravar; [ lra | pose proof (pos_INR k); lra ] ]. }
  assert (Hcek0 : forall k, 0 < c * ek k) by (intro k; apply Rmult_lt_0_compat; [ exact Hc | apply Hek0 ]).
  assert (Hcek1 : forall k, c * ek k <= 1).
  { intro k; unfold ek, Rdiv; rewrite <- Rmult_assoc.
    apply Rle_trans with (c * dm); [ | exact Hcdm1 ].
    rewrite <- (Rmult_1_r (c * dm)) at 2; apply Rmult_le_compat_l;
      [ left; apply Rmult_lt_0_compat; [ exact Hc | exact Hdm0 ] |
        rewrite <- Rinv_1; apply Rinv_le_contravar; [ lra | pose proof (pos_INR k); lra ] ]. }
  assert (HAk1 : forall k, 1 <= Ak k).
  { intro k; unfold Ak; apply Rle_trans with mu; [ exact Hmu1 | ].
    rewrite <- (Rmult_1_r mu) at 1; apply Rmult_le_compat_l; [ lra | pose proof (pos_INR k); lra ]. }
  assert (HcAk1 : forall k, 1 <= c * Ak k).
  { intro k; unfold Ak; rewrite <- Rmult_assoc.
    apply Rle_trans with (c * mu); [ exact Hcmu | ].
    rewrite <- (Rmult_1_r (c * mu)) at 1; apply Rmult_le_compat_l;
      [ left; apply Rmult_lt_0_compat; [ exact Hc | lra ] | pose proof (pos_INR k); lra ]. }
  assert (HekAk : forall k, ek k <= Ak k) by (intro k; pose proof (Hek1 k); pose proof (HAk1 k); lra).
  assert (Hek_cv : Un_cv ek 0).
  { unfold ek; apply (Un_cv_ext (fun k => dm * / (1 + INR k))).
    - intro k; unfold Rdiv; reflexivity.
    - apply Un_cv_scale0; apply Un_cv_recip_0; [ intro k; apply Hp | apply cv_infty_1_INR ]. }
  assert (Hcek_cv : Un_cv (fun k => c * ek k) 0) by (apply Un_cv_scale0; exact Hek_cv).
  assert (HAk_cv : cv_infty Ak) by (unfold Ak; apply cv_infty_scale; [ lra | apply cv_infty_1_INR ]).
  assert (HcAk_cv : cv_infty (fun k => c * Ak k)) by (apply cv_infty_scale; [ exact Hc | exact HAk_cv ]).
  (* the two single finite integrals per k, and the substitution *)
  set (Mint := fun k => RiemannInt (Hf_near a c (ek k) (Ak k) (Hek0 k) (HekAk k))).
  set (Nint := fun k => RiemannInt (Hf_near a 1 (c * ek k) (c * Ak k) (Hcek0 k)
                          (Rmult_le_compat_l c (ek k) (Ak k) (Rlt_le _ _ Hc) (HekAk k)))).
  assert (Hsub : forall k, Nint k = Rpower c a * Mint k).
  { intro k; unfold Nint, Mint.
    (* substitution t ↦ c t on [ek k, Ak k] *)
    assert (prL : Riemann_integrable (fun t => gnk a 1 (c * t) * c) (ek k) (Ak k)).
    { apply continuity_implies_RiemannInt; [ apply HekAk | intros t Ht ].
      apply continuity_pt_mult; [ | apply continuity_pt_const; intros p q; reflexivity ].
      apply (continuity_pt_comp (fun t => c * t) (gnk a 1) t).
      - apply (continuity_pt_scal (fun t => t) c t);
          apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
      - apply cont_gnk; apply Rmult_lt_0_compat; [ exact Hc | pose proof (Hek0 k); lra ]. }
    assert (Hcov : RiemannInt prL
                   = RiemannInt (Hf_near a 1 (c * ek k) (c * Ak k) (Hcek0 k)
                       (Rmult_le_compat_l c (ek k) (Ak k) (Rlt_le _ _ Hc) (HekAk k)))).
    { pose proof (cov_local (fun t => c * t) (fun _ => c) (gnk a 1) (ek k) (Ak k) (HekAk k)) as Hcv.
      assert (Hg : forall t, ek k <= t <= Ak k -> derivable_pt_lim (fun t => c * t) t c).
      { intros t _; pose proof (derivable_pt_lim_scal (fun x => x) c t 1 (derivable_pt_lim_id t)) as Hd;
          rewrite Rmult_1_r in Hd; exact Hd. }
      assert (Hg'c : forall t, ek k <= t <= Ak k -> continuity_pt (fun _ => c) t)
        by (intros t _; apply continuity_pt_const; intros p q; reflexivity).
      assert (Hmap : forall t, ek k <= t <= Ak k -> c * ek k <= c * t <= c * Ak k)
        by (intros t [Ht1 Ht2]; split; apply Rmult_le_compat_l; solve [ left; exact Hc | exact Ht1 | exact Ht2 ]).
      assert (Hfc : forall u, c * ek k <= u <= c * Ak k -> continuity_pt (gnk a 1) u)
        by (intros u [Hu1 Hu2]; apply cont_gnk; pose proof (Hcek0 k); lra).
      exact (Hcv Hg Hg'c Hmap Hfc prL
               (Hf_near a 1 (c * ek k) (c * Ak k) (Hcek0 k)
                  (Rmult_le_compat_l c (ek k) (Ak k) (Rlt_le _ _ Hc) (HekAk k)))). }
    rewrite <- Hcov.
    assert (prL' : Riemann_integrable (fun t => Rpower c a * gnk a c t) (ek k) (Ak k))
      by (apply continuity_implies_RiemannInt; [ apply HekAk | intros t Ht;
          apply continuity_pt_scal; apply cont_gnk; pose proof (Hek0 k); lra ]).
    assert (HL : RiemannInt prL = RiemannInt prL').
    { apply RiemannInt_P18; [ apply HekAk | intros t Ht; apply gnk_scale_pt;
        [ exact Hc | pose proof (Hek0 k); lra ] ]. }
    rewrite HL, (RInt_scal_val (gnk a c) (Rpower c a) (ek k) (Ak k)
                  (Hf_near a c (ek k) (Ak k) (Hek0 k) (HekAk k)) prL' (HekAk k)); reflexivity. }
  (* Mint → mellin a c *)
  assert (HMchas : forall k, Mint k
                   = rint01 (gnk a c) (Hf_near a c) (ek k) + pint1 (gtk a c) (gtk_int a c) (Ak k)).
  { intro k; unfold Mint.
    pose proof (RiemannInt_P26 (Hf_near a c (ek k) 1 (Hek0 k) (Hek1 k))
                  (Hf_near a c 1 (Ak k) Rlt_0_1 (HAk1 k))
                  (Hf_near a c (ek k) (Ak k) (Hek0 k) (HekAk k))) as Hadd.
    rewrite <- Hadd, (rint01_val (gnk a c) (Hf_near a c) (ek k) (Hek0 k) (Hek1 k)).
    f_equal; unfold pint1; apply RiemannInt_P18; [ apply HAk1 | intros t Ht;
      unfold gnk, gtk; rewrite (clamp_id t); [ reflexivity | lra ] ]. }
  assert (HMcv : Un_cv Mint (mellin a c Ha Hc)).
  { unfold mellin; apply (Un_cv_ext (fun k => rint01 (gnk a c) (Hf_near a c) (ek k)
                                            + pint1 (gtk a c) (gtk_int a c) (Ak k)));
      [ intro k; symmetry; apply HMchas | ].
    apply CV_plus.
    - unfold gnear; exact (proj2_sig (gnear_sig a c Ha Hc) ek Hek0 Hek1 Hek_cv).
    - unfold gtail; exact (proj2_sig (gtail_sig a c Hc) Ak HAk1 HAk_cv). }
  (* Nint → Gam a *)
  assert (HNchas : forall k, Nint k
                   = rint01 (gnk a 1) (Hf_near a 1) (c * ek k)
                     + pint1 (gtk a 1) (gtk_int a 1) (c * Ak k)).
  { intro k; unfold Nint.
    pose proof (RiemannInt_P26 (Hf_near a 1 (c * ek k) 1 (Hcek0 k) (Hcek1 k))
                  (Hf_near a 1 1 (c * Ak k) Rlt_0_1 (HcAk1 k))
                  (Hf_near a 1 (c * ek k) (c * Ak k) (Hcek0 k)
                     (Rmult_le_compat_l c (ek k) (Ak k) (Rlt_le _ _ Hc) (HekAk k)))) as Hadd.
    rewrite <- Hadd, (rint01_val (gnk a 1) (Hf_near a 1) (c * ek k) (Hcek0 k) (Hcek1 k)).
    f_equal; unfold pint1; apply RiemannInt_P18; [ apply HcAk1 | intros t Ht;
      unfold gnk, gtk; rewrite (clamp_id t); [ reflexivity | lra ] ]. }
  assert (HNcv : Un_cv Nint (Gam a Ha)).
  { unfold Gam, mellin.
    apply (Un_cv_ext (fun k => rint01 (gnk a 1) (Hf_near a 1) (c * ek k)
                             + pint1 (gtk a 1) (gtk_int a 1) (c * Ak k)));
      [ intro k; symmetry; apply HNchas | ].
    apply CV_plus.
    - unfold gnear; exact (proj2_sig (gnear_sig a 1 Ha Rlt_0_1) (fun k => c * ek k) Hcek0 Hcek1 Hcek_cv).
    - unfold gtail; exact (proj2_sig (gtail_sig a 1 Rlt_0_1) (fun k => c * Ak k) HcAk1 HcAk_cv). }
  (* combine *)
  assert (HMcv2 : Un_cv Mint (Rpower c (- a) * Gam a Ha)).
  { apply (Un_cv_ext (fun k => Rpower c (- a) * Nint k)).
    - intro k; rewrite (Hsub k), <- Rmult_assoc, <- Rpower_plus.
      replace (- a + a) with 0 by ring; rewrite Rpower_O by exact Hc; ring.
    - apply (CV_mult (fun _ => Rpower c (- a)) Nint (Rpower c (- a)) (Gam a Ha));
        [ apply Un_cv_const | exact HNcv ]. }
  exact (UL_sequence Mint (mellin a c Ha Hc) (Rpower c (- a) * Gam a Ha) HMcv HMcv2).
Qed.

Print Assumptions mellin_scale.

(* ================================================================= *)
(*  END MellinKernel.v  —  Riemann FE milestone R2 COMPLETE.         *)
(*     ∫₀^∞ t^{a-1}e^{-ct}dt = c^{-a}·Γ(a).                          *)
(* ================================================================= *)
