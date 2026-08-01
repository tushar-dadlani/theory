(* ================================================================= *)
(*  GammaContinuity.v  —  Γ(a+1) → 1 as a → 0⁺, discharging the        *)
(*  hypothesis of ZetaZero and making ζ(0) = −1/2 unconditional.       *)
(*                                                                    *)
(*  Elementary squeeze on Γ(a+1) = gnear(a+1)1 + gtail(a+1)1, a∈(0,1): *)
(*    near:  gnear(1)1 − a/(a+1) ≤ gnear(a+1)1 ≤ gnear(1)1             *)
(*           (t^a ≤ 1 on (0,1]; ∫₀^1(1−t^a) = a/(a+1) by FTC);         *)
(*    tail:  gtail(1)1 ≤ gtail(a+1)1 ≤ e^{−1}/(1−a)                    *)
(*           (t^a ≥ 1 on [1,∞); t^a ≤ e^{a(t−1)} since ln t ≤ t−1,     *)
(*            and ∫₁^∞ e^{a(t−1)−t} = e^{−1}/(1−a) by FTC).            *)
(*  Summing (Gam_1, gnear_1, gtail_1): 1 − a ≤ Γ(a+1) ≤ 1 + e^{−1}a/(1−a),*)
(*  a squeeze → 1.  Hence ζ_ext(a)→−1/2 outright (zeta_ext_zero).      *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaOne ImproperCv0 ImproperCv1 MellinElem
        ContinuousCoV ZetaContinuation RpowerZero GammaFunction XiTwoSided ZetaZero.
Open Scope R_scope.

(* --- elementary Rpower bounds --- *)

Lemma ln_le_sub : forall t, 0 < t -> ln t <= t - 1.
Proof.
  intros t Ht; destruct (Req_dec t 1) as [-> | Hne].
  - rewrite ln_1; lra.
  - assert (Ht1 : t - 1 <> 0) by (intro Hc; apply Hne; lra).
    pose proof (exp_ineq1 (t - 1) Ht1) as H.
    apply Rlt_le; rewrite <- (ln_exp (t - 1)); apply ln_increasing; lra.
Qed.

Lemma Rpower_le1 : forall t a, 0 < t -> t <= 1 -> 0 <= a -> Rpower t a <= 1.
Proof.
  intros t a Ht Ht1 Ha; unfold Rpower; rewrite <- exp_0.
  assert (Hln : ln t <= 0).
  { destruct (Req_dec t 1) as [-> | Hn]; [ rewrite ln_1; apply Rle_refl | ].
    rewrite <- ln_1; apply Rlt_le; apply ln_increasing; lra. }
  assert (Halnt : a * ln t <= 0).
  { apply Rle_trans with (a * 0);
      [ apply Rmult_le_compat_l; [ exact Ha | exact Hln ] | rewrite Rmult_0_r; apply Rle_refl ]. }
  destruct Halnt as [Hlt | Heq];
    [ apply Rlt_le; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma Rpower_ge1 : forall t a, 1 <= t -> 0 <= a -> 1 <= Rpower t a.
Proof.
  intros t a Ht Ha; unfold Rpower; rewrite <- exp_0.
  assert (Hln : 0 <= ln t).
  { destruct (Req_dec t 1) as [-> | Hn]; [ rewrite ln_1; apply Rle_refl | ].
    rewrite <- ln_1; apply Rlt_le; apply ln_increasing; lra. }
  assert (Halnt : 0 <= a * ln t) by (apply Rmult_le_pos; assumption).
  destruct Halnt as [Hlt | Heq];
    [ apply Rlt_le; apply exp_increasing; exact Hlt | rewrite <- Heq; apply Rle_refl ].
Qed.

Lemma Rpower_exp_ub : forall t a, 1 <= t -> 0 <= a -> Rpower t a <= exp (a * (t - 1)).
Proof.
  intros t a Ht Ha; unfold Rpower.
  assert (Hle : a * ln t <= a * (t - 1))
    by (apply Rmult_le_compat_l; [ exact Ha | apply ln_le_sub; lra ]).
  destruct Hle as [Hlt | Heq];
    [ apply Rlt_le; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma exp_le1_neg : forall x, 0 <= x -> exp (- x) <= 1.
Proof.
  intros x Hx; rewrite <- exp_0; destruct Hx as [Hlt | Heq];
    [ apply Rlt_le; apply exp_increasing; lra | rewrite <- Heq; rewrite Ropp_0; apply Rle_refl ].
Qed.

(* --- limit helpers --- *)

Lemma Un_cv_maj_0 : forall (u b : nat -> R), (forall n, Rabs (u n) <= b n) -> Un_cv b 0 -> Un_cv u 0.
Proof.
  intros u b Hle Hb eps He; destruct (Hb eps He) as [N HN]; exists N; intros n Hn.
  unfold R_dist; rewrite Rminus_0_r; apply Rle_lt_trans with (b n); [ apply Hle | ].
  pose proof (HN n Hn) as H; unfold R_dist in H; rewrite Rminus_0_r in H.
  apply Rle_lt_trans with (Rabs (b n)); [ apply Rle_abs | exact H ].
Qed.

Lemma cv_infty_ge : forall (u v : nat -> R), (forall k, u k <= v k) -> cv_infty u -> cv_infty v.
Proof.
  intros u v Huv Hu M; destruct (Hu M) as [N HN]; exists N; intros n Hn;
    apply Rlt_le_trans with (u n); [ apply HN; exact Hn | apply Huv ].
Qed.

Lemma improper_mono0 : forall f Hf g Hg If Ig,
  ImproperCv0 f Hf If -> ImproperCv0 g Hg Ig ->
  (forall x, 0 < x -> x <= 1 -> f x <= g x) -> If <= Ig.
Proof.
  intros f Hf g Hg If Ig HIf HIg Hle.
  set (e := fun k => / (1 + INR k)).
  assert (He0 : forall k, 0 < e k) by (intro k; unfold e; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (He1 : forall k, e k <= 1) by (intro k; unfold e; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hecv : Un_cv e 0) by (unfold e; apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  apply (Un_cv_le_lim (fun k => rint01 f Hf (e k)) (fun k => rint01 g Hg (e k)) If Ig).
  - intro k; rewrite (rint01_val f Hf (e k) (He0 k) (He1 k)), (rint01_val g Hg (e k) (He0 k) (He1 k)).
    apply RiemannInt_P19; [ apply He1 | intros x Hx; pose proof (He0 k); apply Hle; lra ].
  - exact (HIf e He0 He1 Hecv).
  - exact (HIg e He0 He1 Hecv).
Qed.

(* --- near integrand nf a t = 1 − t^a  and its integral a/(a+1) --- *)

Definition nf (a : R) (t : R) : R := 1 - Rpower t a.

Lemma cont_Rpow : forall a t, 0 < t -> continuity_pt (fun s => Rpower s a) t.
Proof.
  intros a t Ht; unfold Rpower; apply (continuity_pt_comp (fun s => a * ln s) exp t).
  - apply (continuity_pt_scal ln a t); apply derivable_continuous_pt;
      exists (/ t); apply derivable_pt_lim_ln; exact Ht.
  - apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

Lemma cont_nf : forall a t, 0 < t -> continuity_pt (nf a) t.
Proof.
  intros a t Ht; unfold nf; apply continuity_pt_minus;
    [ apply continuity_pt_const; intros p q; reflexivity | apply cont_Rpow; exact Ht ].
Qed.

Lemma nf_int : forall a x y, 0 < x -> x <= y -> Riemann_integrable (nf a) x y.
Proof.
  intros a x y Hx Hxy; apply continuity_implies_RiemannInt;
    [ exact Hxy | intros t Ht; apply cont_nf; lra ].
Qed.

Lemma nf_deriv : forall a t, 0 < t -> 0 < a + 1 ->
  derivable_pt_lim (fun s => s - / (a + 1) * Rpower s (a + 1)) t (nf a t).
Proof.
  intros a t Ht Ha1; unfold nf.
  assert (Hp2 : derivable_pt_lim (fun s => / (a + 1) * Rpower s (a + 1)) t (Rpower t a)).
  { pose proof (derivable_pt_lim_scal (fun s => Rpower s (a + 1)) (/ (a + 1)) t
                  ((a + 1) * Rpower t ((a + 1) - 1)) (Rpower_deriv (a + 1) t Ht)) as H2.
    replace (Rpower t a) with (/ (a + 1) * ((a + 1) * Rpower t ((a + 1) - 1)))
      by (replace ((a + 1) - 1) with a by ring; field; lra).
    exact H2. }
  exact (derivable_pt_lim_minus (fun s => s) (fun s => / (a + 1) * Rpower s (a + 1))
           t 1 (Rpower t a) (derivable_pt_lim_id t) Hp2).
Qed.

Lemma near_val : forall a e (He : 0 < e) (He1 : e <= 1) (Ha1 : 0 < a + 1),
  RiemannInt (nf_int a e 1 He He1) = a / (a + 1) - e + / (a + 1) * Rpower e (a + 1).
Proof.
  intros a e He He1 Ha1.
  assert (Hanti : antiderivative (nf a) (fun s => s - / (a + 1) * Rpower s (a + 1)) e 1).
  { split; [ | exact He1 ]. intros x Hx.
    assert (Hd : derivable_pt_lim (fun s => s - / (a + 1) * Rpower s (a + 1)) x (nf a x))
      by (apply nf_deriv; [ lra | exact Ha1 ]).
    exists (exist (fun l => derivable_pt_lim (fun s => s - / (a + 1) * Rpower s (a + 1)) x l) (nf a x) Hd);
      reflexivity. }
  rewrite (FTC_antideriv (nf a) (fun s => s - / (a + 1) * Rpower s (a + 1)) e 1 He1
             (fun x Hx => cont_nf a x ltac:(lra)) (nf_int a e 1 He He1) Hanti).
  cbv beta; rewrite (Rpower_base1 (a + 1)); field; lra.
Qed.

Lemma nf_improper : forall a (Ha : 0 <= a) (Ha1 : 0 < a + 1),
  ImproperCv0 (nf a) (nf_int a) (a / (a + 1)).
Proof.
  intros a Ha Ha1.
  set (e := fun k => / (1 + INR k)).
  assert (He0 : forall k, 0 < e k) by (intro k; unfold e; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (He1 : forall k, e k <= 1) by (intro k; unfold e; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hecv : Un_cv e 0) by (unfold e; apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  apply (improper_welldef0 (nf a) (nf_int a)
           (fun x Hx Hx1 => ltac:(unfold nf; pose proof (Rpower_le1 x a Hx Hx1 Ha); lra))
           e (a / (a + 1)) He0 He1 Hecv).
  apply (Un_cv_ext (fun k => a / (a + 1) - e k + / (a + 1) * Rpower (e k) (a + 1))
                   (fun k => rint01 (nf a) (nf_int a) (e k))).
  - intro k; rewrite (rint01_val (nf a) (nf_int a) (e k) (He0 k) (He1 k));
      symmetry; apply near_val; exact Ha1.
  - apply Un_cv_shift0.
    apply (Un_cv_ext (fun k => / (a + 1) * Rpower (e k) (a + 1) - e k)
                     (fun k => (a / (a + 1) - e k + / (a + 1) * Rpower (e k) (a + 1)) - a / (a + 1))).
    + intro k; ring.
    + replace 0 with (0 - 0) by ring.
      apply (CV_minus (fun k => / (a + 1) * Rpower (e k) (a + 1)) e 0 0); [ | exact Hecv ].
      replace 0 with (/ (a + 1) * 0) by ring.
      apply (CV_mult (fun _ => / (a + 1)) (fun k => Rpower (e k) (a + 1)) (/ (a + 1)) 0);
        [ apply Un_cv_const | apply Rpower_pos_cv0; [ exact Ha1 | exact He0 | exact Hecv ] ].
Qed.

(* --- tail majorant mf a u = e^{(a−1)u−a}  and its integral e^{−1}/(1−a) --- *)

Definition mf (a : R) (u : R) : R := exp ((a - 1) * u - a).

Lemma cont_mf : forall a u, continuity_pt (mf a) u.
Proof.
  intros a u; unfold mf; apply (continuity_pt_comp (fun s => (a - 1) * s - a) exp u).
  - apply continuity_pt_minus;
      [ apply (continuity_pt_scal (fun s => s) (a - 1) u); apply derivable_continuous_pt; apply derivable_pt_id
      | apply continuity_pt_const; intros p q; reflexivity ].
  - apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

Lemma mf_int : forall a x y, Riemann_integrable (mf a) x y.
Proof.
  intros a x y; destruct (Rle_dec x y);
    [ apply continuity_implies_RiemannInt; [ assumption | intros u _; apply cont_mf ]
    | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros u _; apply cont_mf ] ].
Qed.

Lemma mf_deriv : forall a u, a - 1 <> 0 ->
  derivable_pt_lim (fun s => / (a - 1) * exp ((a - 1) * s - a)) u (mf a u).
Proof.
  intros a u Hane; unfold mf.
  assert (Hlin : derivable_pt_lim (fun s => (a - 1) * s - a) u (a - 1)).
  { pose proof (derivable_pt_lim_minus (fun s => (a - 1) * s) (fun _ => a) u ((a - 1) * 1) 0
                  (derivable_pt_lim_scal (fun s => s) (a - 1) u 1 (derivable_pt_lim_id u))
                  (derivable_pt_lim_const a u)) as H.
    replace ((a - 1) * 1 - 0) with (a - 1) in H by ring; exact H. }
  pose proof (derivable_pt_lim_comp (fun s => (a - 1) * s - a) exp u (a - 1) (exp ((a - 1) * u - a))
                Hlin (derivable_pt_lim_exp ((a - 1) * u - a))) as Hcomp.
  pose proof (derivable_pt_lim_scal (fun s => exp ((a - 1) * s - a)) (/ (a - 1)) u
                (exp ((a - 1) * u - a) * (a - 1)) Hcomp) as Hsc.
  replace (exp ((a - 1) * u - a)) with (/ (a - 1) * (exp ((a - 1) * u - a) * (a - 1)))
    by (field; exact Hane).
  exact Hsc.
Qed.

Lemma mf_val : forall a A (HA : 1 <= A) (Hane : a - 1 <> 0),
  RiemannInt (mf_int a 1 A) = (exp ((a - 1) * A - a) - exp (-1)) / (a - 1).
Proof.
  intros a A HA Hane.
  assert (Hanti : antiderivative (mf a) (fun s => / (a - 1) * exp ((a - 1) * s - a)) 1 A).
  { split; [ | exact HA ]. intros x Hx.
    assert (Hd : derivable_pt_lim (fun s => / (a - 1) * exp ((a - 1) * s - a)) x (mf a x))
      by (apply mf_deriv; exact Hane).
    exists (exist (fun l => derivable_pt_lim (fun s => / (a - 1) * exp ((a - 1) * s - a)) x l) (mf a x) Hd);
      reflexivity. }
  rewrite (FTC_antideriv (mf a) (fun s => / (a - 1) * exp ((a - 1) * s - a)) 1 A HA
             (fun x _ => cont_mf a x) (mf_int a 1 A) Hanti).
  cbv beta; replace ((a - 1) * 1 - a) with (-1) by ring; field; exact Hane.
Qed.

Lemma exp_lin_cv0 : forall a A, a < 1 -> (forall k, 1 <= A k) -> cv_infty A ->
  Un_cv (fun k => exp ((a - 1) * A k - a)) 0.
Proof.
  intros a A Ha1 HA1 Hinf.
  apply (Un_cv_squeeze0 (fun k => exp ((a - 1) * A k - a)) (fun k => exp (- a) / (1 - a) * / A k)).
  - exists 0%nat; intros k _; assert (HAk : 1 <= A k) by apply HA1.
    assert (Hd : 0 < (1 - a) * A k) by (apply Rmult_lt_0_compat; lra).
    split; [ left; apply exp_pos | ].
    replace (exp ((a - 1) * A k - a)) with (exp (- a) * exp ((a - 1) * A k))
      by (rewrite <- exp_plus; f_equal; ring).
    replace (exp (- a) / (1 - a) * / A k) with (exp (- a) * (/ (1 - a) * / A k))
      by (unfold Rdiv; ring).
    apply Rmult_le_compat_l; [ left; apply exp_pos | ].
    rewrite <- Rinv_mult.
    replace (exp ((a - 1) * A k)) with (/ exp ((1 - a) * A k))
      by (rewrite <- exp_Ropp; f_equal; ring).
    apply Rinv_le_contravar; [ exact Hd | ].
    pose proof (exp_lb2 0 ((1 - a) * A k) ltac:(lra)) as Hlb; simpl in Hlb; lra.
  - replace 0 with (exp (- a) / (1 - a) * 0) by ring.
    apply (CV_mult (fun _ => exp (- a) / (1 - a)) (fun k => / A k) (exp (- a) / (1 - a)) 0);
      [ apply Un_cv_const | apply Un_cv_recip_0; [ intro k; pose proof (HA1 k); lra | exact Hinf ] ].
Qed.

Lemma mf_improper : forall a (Hane : a - 1 <> 0) (Ha1 : a < 1),
  ImproperCv1 (mf a) (mf_int a) (exp (-1) / (1 - a)).
Proof.
  intros a Hane Ha1.
  set (A := fun k => 1 + INR k).
  assert (HA1 : forall k, 1 <= A k) by (intro k; unfold A; pose proof (pos_INR k); lra).
  assert (HAinf : cv_infty A) by (unfold A; apply cv_infty_1_INR).
  apply (improper_welldef1 (mf a) (mf_int a) (fun u _ => Rlt_le _ _ (exp_pos _))
           A (exp (-1) / (1 - a)) HA1 HAinf).
  apply (Un_cv_ext (fun k => (exp ((a - 1) * A k - a) - exp (-1)) / (a - 1))
                   (fun k => pint1 (mf a) (mf_int a) (A k))).
  - intro k; unfold pint1; rewrite (mf_val a (A k) (HA1 k) Hane); reflexivity.
  - replace (exp (-1) / (1 - a)) with ((0 - exp (-1)) / (a - 1)) by (field; lra).
    apply (CV_mult (fun k => exp ((a - 1) * A k - a) - exp (-1)) (fun _ => / (a - 1))
             (0 - exp (-1)) (/ (a - 1))); [ | apply Un_cv_const ].
    apply (CV_minus (fun k => exp ((a - 1) * A k - a)) (fun _ => exp (-1)) 0 (exp (-1)));
      [ apply exp_lin_cv0; assumption | apply Un_cv_const ].
Qed.

(* --- the four one-sided bounds --- *)

Lemma gnk_shift_le : forall a t, 0 < t -> t <= 1 -> 0 <= a -> gnk (a + 1) 1 t <= gnk 1 1 t.
Proof.
  intros a t Ht Ht1 Ha; unfold gnk; apply Rmult_le_compat_r; [ left; apply exp_pos | ].
  replace ((a + 1) - 1) with a by ring; replace (1 - 1) with 0 by ring.
  rewrite (Rpower_O t Ht); apply Rpower_le1; assumption.
Qed.

Lemma gtk_shift_ge : forall a u, 1 <= u -> 0 <= a -> gtk 1 1 u <= gtk (a + 1) 1 u.
Proof.
  intros a u Hu Ha; unfold gtk; apply Rmult_le_compat_r; [ left; apply exp_pos | ].
  replace (1 - 1) with 0 by ring; replace ((a + 1) - 1) with a by ring.
  rewrite (Rpower_O (clamp u) ltac:(pose proof (clamp_ge1 u); lra));
    apply Rpower_ge1; [ apply clamp_ge1 | exact Ha ].
Qed.

Lemma gtk_shift_mf : forall a u, 1 <= u -> 0 <= a -> gtk (a + 1) 1 u <= mf a u.
Proof.
  intros a u Hu Ha; unfold gtk, mf; rewrite (clamp_id u Hu); replace (1 * u) with u by ring.
  replace ((a + 1) - 1) with a by ring.
  apply Rle_trans with (exp (a * (u - 1)) * exp (- u)).
  - apply Rmult_le_compat_r; [ left; apply exp_pos | apply Rpower_exp_ub; [ exact Hu | exact Ha ] ].
  - rewrite <- exp_plus; replace (a * (u - 1) + - u) with ((a - 1) * u - a) by ring; apply Rle_refl.
Qed.

Lemma gnear_upper : forall a (Ha : 0 <= a) (H : 0 < a + 1),
  gnear (a + 1) 1 H Rlt_0_1 <= gnear 1 1 Rlt_0_1 Rlt_0_1.
Proof.
  intros a Ha H.
  apply (improper_mono0 (gnk (a + 1) 1) (Hf_near (a + 1) 1) (gnk 1 1) (Hf_near 1 1)
           (gnear (a + 1) 1 H Rlt_0_1) (gnear 1 1 Rlt_0_1 Rlt_0_1)
           (proj2_sig (gnear_sig (a + 1) 1 H Rlt_0_1)) (proj2_sig (gnear_sig 1 1 Rlt_0_1 Rlt_0_1))).
  intros x Hx Hx1; apply gnk_shift_le; assumption.
Qed.

Lemma gnear_lower : forall a (Ha : 0 <= a) (H : 0 < a + 1),
  gnear 1 1 Rlt_0_1 Rlt_0_1 - a / (a + 1) <= gnear (a + 1) 1 H Rlt_0_1.
Proof.
  intros a Ha H.
  assert (Hfg : forall x y, 0 < x -> x <= y ->
            Riemann_integrable (fun t => gnk 1 1 t + (-1) * gnk (a + 1) 1 t) x y).
  { intros x y Hx Hxy; apply continuity_implies_RiemannInt; [ exact Hxy | intros t Ht;
      apply continuity_pt_plus; [ apply cont_gnk; lra | apply continuity_pt_scal; apply cont_gnk; lra ] ]. }
  assert (Hcomb : ImproperCv0 (fun t => gnk 1 1 t + (-1) * gnk (a + 1) 1 t) Hfg
                    (gnear 1 1 Rlt_0_1 Rlt_0_1 + (-1) * gnear (a + 1) 1 H Rlt_0_1)).
  { apply (improper_linear0 (gnk 1 1) (gnk (a + 1) 1) (-1) (Hf_near 1 1) (Hf_near (a + 1) 1) Hfg
             (gnear 1 1 Rlt_0_1 Rlt_0_1) (gnear (a + 1) 1 H Rlt_0_1));
      [ exact (proj2_sig (gnear_sig 1 1 Rlt_0_1 Rlt_0_1)) | exact (proj2_sig (gnear_sig (a + 1) 1 H Rlt_0_1)) ]. }
  assert (Hb : gnear 1 1 Rlt_0_1 Rlt_0_1 + (-1) * gnear (a + 1) 1 H Rlt_0_1 <= a / (a + 1)).
  { apply (improper_mono0 (fun t => gnk 1 1 t + (-1) * gnk (a + 1) 1 t) Hfg (nf a) (nf_int a)
             (gnear 1 1 Rlt_0_1 Rlt_0_1 + (-1) * gnear (a + 1) 1 H Rlt_0_1) (a / (a + 1))
             Hcomb (nf_improper a Ha H)).
    intros x Hx Hx1; unfold gnk, nf.
    replace (1 - 1) with 0 by ring; replace ((a + 1) - 1) with a by ring.
    rewrite (Rpower_O x Hx); replace (1 * x) with x by ring; rewrite Rmult_1_l.
    replace (exp (- x) + (-1) * (Rpower x a * exp (- x))) with ((1 - Rpower x a) * exp (- x)) by ring.
    apply Rle_trans with ((1 - Rpower x a) * 1);
      [ apply Rmult_le_compat_l;
          [ pose proof (Rpower_le1 x a Hx Hx1 Ha); lra | apply exp_le1_neg; lra ]
      | rewrite Rmult_1_r; apply Rle_refl ]. }
  lra.
Qed.

Lemma gtail_lower : forall a (Ha : 0 <= a),
  gtail 1 1 Rlt_0_1 <= gtail (a + 1) 1 Rlt_0_1.
Proof.
  intros a Ha.
  apply (improper_mono (gtk 1 1) (gtk_int 1 1) (gtk (a + 1) 1) (gtk_int (a + 1) 1)
           (gtail 1 1 Rlt_0_1) (gtail (a + 1) 1 Rlt_0_1)
           (proj2_sig (gtail_sig 1 1 Rlt_0_1)) (proj2_sig (gtail_sig (a + 1) 1 Rlt_0_1))).
  intros u Hu; apply gtk_shift_ge; assumption.
Qed.

Lemma gtail_upper : forall a (Ha : 0 <= a) (Hane : a - 1 <> 0) (Ha1 : a < 1),
  gtail (a + 1) 1 Rlt_0_1 <= exp (-1) / (1 - a).
Proof.
  intros a Ha Hane Ha1.
  apply (improper_mono (gtk (a + 1) 1) (gtk_int (a + 1) 1) (mf a) (mf_int a)
           (gtail (a + 1) 1 Rlt_0_1) (exp (-1) / (1 - a))
           (proj2_sig (gtail_sig (a + 1) 1 Rlt_0_1)) (mf_improper a Hane Ha1)).
  intros u Hu; apply gtk_shift_mf; assumption.
Qed.

(* --- the squeeze  1 − a ≤ Γ(a+1) ≤ 1 + e^{−1}·a/(1−a) --- *)

Lemma gam_shift_bounds : forall a (Ha0 : 0 < a) (Ha1 : a < 1) (H : 0 < a + 1),
  1 - a <= Gam (a + 1) H <= 1 + exp (-1) * (a / (1 - a)).
Proof.
  intros a Ha0 Ha1 H; unfold Gam, mellin.
  pose proof (gnear_1 Rlt_0_1 Rlt_0_1) as HN1.
  pose proof (gtail_1 Rlt_0_1) as HT1.
  pose proof (gnear_lower a (Rlt_le _ _ Ha0) H) as GL.
  pose proof (gnear_upper a (Rlt_le _ _ Ha0) H) as GU.
  pose proof (gtail_lower a (Rlt_le _ _ Ha0)) as TL.
  pose proof (gtail_upper a (Rlt_le _ _ Ha0) ltac:(lra) Ha1) as TU.
  assert (Hle : a / (a + 1) <= a).
  { apply Rmult_le_reg_r with (a + 1); [ lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; nra. }
  assert (Heq : exp (-1) / (1 - a) = exp (-1) + exp (-1) * (a / (1 - a))) by (field; lra).
  split; lra.
Qed.

(* --- Γ(a/2+1) → 1, discharging ZetaZero's hypothesis --- *)

Theorem gam_shift_cont : forall a (Ha0 : forall k, 0 < a k) (Ha1 : forall k, a k < 1)
  (Hcv : Un_cv a 0) (H : forall k, 0 < a k / 2 + 1),
  Un_cv (fun k => Gam (a k / 2 + 1) (H k)) 1.
Proof.
  intros a Ha0 Ha1 Hcv H; apply Un_cv_shift0.
  apply (Un_cv_maj_0 (fun k => Gam (a k / 2 + 1) (H k) - 1) a); [ | exact Hcv ].
  intro k; pose proof (Ha0 k) as Hk0; pose proof (Ha1 k) as Hk1.
  assert (Hak0 : 0 < a k / 2) by lra.
  assert (Hak1 : a k / 2 < 1) by lra.
  destruct (gam_shift_bounds (a k / 2) Hak0 Hak1 (H k)) as [GL GU].
  assert (Hd : 0 < 1 - a k / 2) by lra.
  assert (HX : a k / 2 / (1 - a k / 2) <= a k).
  { apply Rmult_le_reg_r with (1 - a k / 2); [ exact Hd | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; nra. }
  assert (HX0 : 0 <= a k / 2 / (1 - a k / 2))
    by (apply Rle_mult_inv_pos; lra).
  assert (Hexp1 : exp (-1) <= 1) by (rewrite <- exp_0; apply Rlt_le; apply exp_increasing; lra).
  assert (Hexp0 : 0 <= exp (-1)) by (left; apply exp_pos).
  set (XV := a k / 2 / (1 - a k / 2)) in *.
  assert (Hkey : exp (-1) * XV <= a k).
  { apply Rle_trans with XV; [ | exact HX ].
    apply Rle_trans with (1 * XV);
      [ apply Rmult_le_compat_r; [ exact HX0 | exact Hexp1 ] | rewrite Rmult_1_l; apply Rle_refl ]. }
  apply Rabs_le; split; lra.
Qed.

(* --- the payoff: ζ(0) = −1/2 unconditionally --- *)

Theorem zeta_zero_unconditional : forall a (Ha0 : forall k, 0 < a k) (Ha1 : forall k, a k < 1)
  (Hcv : Un_cv a 0) (Hp : forall k, 0 < a k / 2 + 1),
  Un_cv (fun k => zeta_ext (a k)) (- (1 / 2)).
Proof.
  intros a Ha0 Ha1 Hcv Hp.
  apply (zeta_zero a Ha0 Ha1 Hcv Hp); apply (gam_shift_cont a Ha0 Ha1 Hcv Hp).
Qed.

Corollary zeta_ext_zero : Un_cv (fun k => zeta_ext (/ (2 + INR k))) (- (1 / 2)).
Proof.
  assert (Hpos : forall k, 0 < 2 + INR k) by (intro k; pose proof (pos_INR k); lra).
  assert (Hinf : cv_infty (fun k => 2 + INR k))
    by (apply (cv_infty_ge (fun k => 1 + INR k)); [ intro k; lra | apply cv_infty_1_INR ]).
  apply (zeta_zero_unconditional (fun k => / (2 + INR k))).
  - intro k; apply Rinv_0_lt_compat; apply Hpos.
  - intro k; pose proof (Hpos k); pose proof (pos_INR k);
      rewrite <- Rinv_1; apply Rinv_lt_contravar; [ nra | lra ].
  - apply Un_cv_recip_0; [ intro k; apply Hpos | exact Hinf ].
  - intro k; pose proof (Rinv_0_lt_compat (2 + INR k) (Hpos k)); lra.
Qed.

Print Assumptions gam_shift_cont.
Print Assumptions zeta_ext_zero.

(* ================================================================= *)
(*  END GammaContinuity.v.  Γ(a+1)→1; ζ_ext(a)→−1/2 with no hypotheses.*)
(* ================================================================= *)
