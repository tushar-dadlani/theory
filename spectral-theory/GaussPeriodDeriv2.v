(* ================================================================= *)
(*  GaussPeriodDeriv2.v  —  Poisson→θ line, P3 step 3: Θ_t is C² in x, *)
(*  and the 2π-rescaled representative ftil.                          *)
(*                                                                    *)
(*  A second pass of the derivable_pt_lim_CVU engine (reusing the      *)
(*  Part-A analytic helpers from GaussPeriodDeriv) gives the second    *)
(*  x-derivative                                                      *)
(*     Θ_t''(x) = Σ_{n∈ℤ} ((2πt(x+n))² − 2πt) e^{−π(x+n)²t}.          *)
(*  C² is exactly what the removable-singularity localiser needs (a    *)
(*  second-order Taylor of the periodization at the evaluation point). *)
(*  Domination now needs the SECOND Gaussian moment u²e^{−a u²}≤1/a.   *)
(*                                                                    *)
(*  Finally we package ftil t Ht u := Θ_t(u/2π), the 2π-periodic       *)
(*  globally-C² representative fed to the Fourier tower, with          *)
(*  ftil 0 = θ(t) and ftil(u+2π)=ftil u.                              *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 PSeries_reg FunctionalExtensionality Lra Lia.
Require Import JacobiTheta GaussPeriodization GaussPeriodicity GaussPeriodTotal
        GaussPeriodDeriv GaussCauchy GaussSubst.
Open Scope R_scope.

(* ================================================================= *)
(*  Part A'.  Second-moment analytic helpers.                        *)
(* ================================================================= *)

Lemma t_exp_neg_le1 : forall w, 0 <= w -> w * exp (- w) <= 1.
Proof.
  intros w Hw.
  assert (Hexp : w <= exp w).
  { destruct (Req_dec w 0) as [-> | Hne]; [ rewrite exp_0; lra | ].
    pose proof (exp_ineq1 w Hne); lra. }
  apply Rle_trans with (exp w * exp (- w)).
  - apply Rmult_le_compat_r; [ left; apply exp_pos | exact Hexp ].
  - rewrite <- exp_plus; replace (w + - w) with 0 by ring; rewrite exp_0; apply Rle_refl.
Qed.

Lemma abs_gauss_bound2 : forall a u, 0 < a -> u ^ 2 * exp (- (a * u ^ 2)) <= / a.
Proof.
  intros a u Ha; assert (Ha' : a <> 0) by (apply Rgt_not_eq; exact Ha).
  assert (Hu2 : 0 <= u ^ 2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr).
  assert (Hval : u ^ 2 * exp (- (a * u ^ 2)) = / a * (a * u ^ 2 * exp (- (a * u ^ 2))))
    by (field; exact Ha').
  rewrite Hval.
  rewrite <- (Rmult_1_r (/ a)) at 2.
  apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; exact Ha | ].
  apply t_exp_neg_le1; apply Rmult_le_pos; [ left; exact Ha | exact Hu2 ].
Qed.

Lemma poly2_gauss_bound : forall a u, 0 < a -> (1 + u ^ 2) * exp (- (a * u ^ 2)) <= 1 + / a.
Proof.
  intros a u Ha.
  replace ((1 + u ^ 2) * exp (- (a * u ^ 2)))
    with (exp (- (a * u ^ 2)) + u ^ 2 * exp (- (a * u ^ 2))) by ring.
  apply Rplus_le_compat.
  - apply Rle_trans with (exp 0).
    + apply exp_le_compat; assert (0 <= u ^ 2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr); nra.
    + rewrite exp_0; apply Rle_refl.
  - apply abs_gauss_bound2; exact Ha.
Qed.

(* ================================================================= *)
(*  Part B'.  Second derivative of the periodization.                *)
(* ================================================================= *)

Section Deriv2.

Variable t : R.
Hypothesis Ht : 0 < t.

Definition gRq2 (x : R) (k : nat) : R :=
  ((2 * PI * t * (x + INR k)) ^ 2 - 2 * PI * t) * gR t x k.
Definition gLq2 (x : R) (k : nat) : R :=
  ((2 * PI * t * (x - INR (S k))) ^ 2 - 2 * PI * t) * gL t x k.
Definition gTheta_deriv2_partial (x : R) (N : nat) : R :=
  sum_f_R0 (gRq2 x) N + sum_f_R0 (gLq2 x) N.

Definition KR2 (x0 : R) :=
  ((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + / (PI * t / 2)) * exp (PI * t / 2 * (/ 4 - x0 + 1)).
Definition KL2 (x0 : R) :=
  ((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + / (PI * t / 2)) * exp (PI * t / 2 * (x0 + 1 / 4)).

Lemma half_pos2 : 0 < PI * t / 2.
Proof. pose proof PI_RGT_0; nra. Qed.

(* --- second derivative of the kernels --- *)

Lemma dgRq : forall x k, derivable_pt_lim (fun s => gRq t s k) x (gRq2 x k).
Proof.
  intros x k.
  assert (Hp : derivable_pt_lim (fun s => - (2 * PI * t * (s + INR k))) x (- (2 * PI * t))).
  { replace (- (2 * PI * t)) with (- (2 * PI * t * 1)) by ring.
    apply derivable_pt_lim_opp.
    apply (derivable_pt_lim_scal (fun s => s + INR k) (2 * PI * t) x 1).
    replace 1 with (1 + 0) by ring.
    apply derivable_pt_lim_plus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  pose proof (derivable_pt_lim_mult (fun s => - (2 * PI * t * (s + INR k)))
                (fun s => gR t s k) x (- (2 * PI * t)) (gRq t x k) Hp (dgR t x k)) as Hm.
  assert (Hval : gRq2 x k = - (2 * PI * t) * gR t x k + - (2 * PI * t * (x + INR k)) * gRq t x k)
    by (unfold gRq2, gRq, gR; ring).
  rewrite Hval; exact Hm.
Qed.

Lemma dgLq : forall x k, derivable_pt_lim (fun s => gLq t s k) x (gLq2 x k).
Proof.
  intros x k.
  assert (Hp : derivable_pt_lim (fun s => - (2 * PI * t * (s - INR (S k)))) x (- (2 * PI * t))).
  { replace (- (2 * PI * t)) with (- (2 * PI * t * 1)) by ring.
    apply derivable_pt_lim_opp.
    apply (derivable_pt_lim_scal (fun s => s - INR (S k)) (2 * PI * t) x 1).
    replace 1 with (1 - 0) by ring.
    apply derivable_pt_lim_minus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  pose proof (derivable_pt_lim_mult (fun s => - (2 * PI * t * (s - INR (S k))))
                (fun s => gL t s k) x (- (2 * PI * t)) (gLq t x k) Hp (dgL t x k)) as Hm.
  assert (Hval : gLq2 x k = - (2 * PI * t) * gL t x k + - (2 * PI * t * (x - INR (S k))) * gLq t x k)
    by (unfold gLq2, gLq, gL; ring).
  rewrite Hval; exact Hm.
Qed.

Lemma gTheta_deriv_partial_derives : forall x N,
  derivable_pt_lim (fun s => gTheta_deriv_partial t s N) x (gTheta_deriv2_partial x N).
Proof.
  intros x N; unfold gTheta_deriv_partial, gTheta_deriv2_partial.
  apply derivable_pt_lim_plus;
    [ apply (deriv_sum (fun k s => gRq t s k) (fun k s => gRq2 s k) N x); intro k; apply dgRq
    | apply (deriv_sum (fun k s => gLq t s k) (fun k s => gLq2 s k) N x); intro k; apply dgLq ].
Qed.

(* --- continuity of the second-derivative partials --- *)

Lemma cont_gRq2 : forall k, continuity (fun s => gRq2 s k).
Proof.
  intros k s; unfold gRq2.
  apply continuity_pt_mult; [ | apply cont_gR ].
  apply continuity_pt_minus.
  - apply (cont_pow (fun s => 2 * PI * t * (s + INR k)) 2).
    intro y; apply (continuity_pt_scal (fun s => s + INR k) (2 * PI * t) y).
    apply continuity_pt_plus;
      [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
  - apply continuity_pt_const; intros a b; reflexivity.
Qed.

Lemma cont_gLq2 : forall k, continuity (fun s => gLq2 s k).
Proof.
  intros k s; unfold gLq2.
  apply continuity_pt_mult; [ | apply cont_gL ].
  apply continuity_pt_minus.
  - apply (cont_pow (fun s => 2 * PI * t * (s - INR (S k))) 2).
    intro y; apply (continuity_pt_scal (fun s => s - INR (S k)) (2 * PI * t) y).
    apply continuity_pt_minus;
      [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
  - apply continuity_pt_const; intros a b; reflexivity.
Qed.

Lemma cont_gTheta_deriv2_partial : forall N, continuity (fun s => gTheta_deriv2_partial s N).
Proof.
  intro N; unfold gTheta_deriv2_partial; intro s.
  apply continuity_pt_plus;
    [ apply (cont_sum (fun k s => gRq2 s k) N); intro k; apply cont_gRq2
    | apply (cont_sum (fun k s => gLq2 s k) N); intro k; apply cont_gLq2 ].
Qed.

(* --- per-term geometric domination of the second-derivative terms --- *)

Lemma gRq2_ball : forall x0 y k, Rabs (y - x0) < 1 -> Rabs (gRq2 y k) <= KR2 x0 * wt t ^ k.
Proof.
  intros x0 y k Hb; pose proof PI_RGT_0 as HPI; pose proof half_pos2 as Hhp.
  unfold gRq2, gR.
  rewrite Rabs_mult.
  rewrite (Rabs_right (exp (- (PI * (y + INR k) ^ 2 * t)))) by (apply Rle_ge; left; apply exp_pos).
  assert (Esplit : exp (- (PI * (y + INR k) ^ 2 * t))
                   = exp (- (PI * t / 2 * (y + INR k) ^ 2)) * exp (- (PI * t / 2 * (y + INR k) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Esplit.
  (* bound the polynomial factor by ((2πt)²+2πt)(1+u²) *)
  apply Rle_trans with
    ((((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + (y + INR k) ^ 2))
     * (exp (- (PI * t / 2 * (y + INR k) ^ 2)) * exp (- (PI * t / 2 * (y + INR k) ^ 2)))).
  - apply Rmult_le_compat_r.
    + apply Rmult_le_pos; left; apply exp_pos.
    + assert (Hu2 : 0 <= (y + INR k) ^ 2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr).
      replace ((2 * PI * t * (y + INR k)) ^ 2 - 2 * PI * t)
        with ((2 * PI * t * (y + INR k)) ^ 2 + - (2 * PI * t)) by ring.
      eapply Rle_trans; [ apply Rabs_triang | ].
      rewrite Rabs_Ropp.
      rewrite (Rabs_right ((2 * PI * t * (y + INR k)) ^ 2))
        by (apply Rle_ge; rewrite <- Rsqr_pow2; apply Rle_0_sqr).
      rewrite (Rabs_right (2 * PI * t)) by (apply Rle_ge; nra).
      nra.
  - replace ((((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + (y + INR k) ^ 2))
             * (exp (- (PI * t / 2 * (y + INR k) ^ 2)) * exp (- (PI * t / 2 * (y + INR k) ^ 2))))
      with (((2 * PI * t) ^ 2 + 2 * PI * t)
            * (((1 + (y + INR k) ^ 2) * exp (- (PI * t / 2 * (y + INR k) ^ 2)))
               * exp (- (PI * t / 2 * (y + INR k) ^ 2)))) by ring.
    unfold KR2.
    replace (((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + / (PI * t / 2)) * exp (PI * t / 2 * (/ 4 - x0 + 1)) * wt t ^ k)
      with (((2 * PI * t) ^ 2 + 2 * PI * t)
            * ((1 + / (PI * t / 2)) * (exp (PI * t / 2 * (/ 4 - x0 + 1)) * wt t ^ k))) by ring.
    apply Rmult_le_compat_l; [ nra | ].
    apply Rle_trans with ((1 + / (PI * t / 2)) * (exp (PI * t / 2 * (/ 4 - y)) * wt t ^ k)).
    + apply Rmult_le_compat.
      * apply Rmult_le_pos;
          [ assert (0 <= (y + INR k) ^ 2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr); nra
          | left; apply exp_pos ].
      * left; apply exp_pos.
      * exact (poly2_gauss_bound (PI * t / 2) (y + INR k) Hhp).
      * unfold wt; exact (exp_sq_geom_R (PI * t / 2) y k Hhp).
    + apply Rmult_le_compat_l; [ assert (0 < / (PI * t / 2)) by (apply Rinv_0_lt_compat; exact Hhp); lra | ].
      apply Rmult_le_compat_r; [ apply pow_le; left; apply exp_pos | ].
      apply exp_le_compat; apply Rmult_le_compat_l; [ lra | ].
      apply Rabs_def2 in Hb; destruct Hb as [Hb1 Hb2]; lra.
Qed.

Lemma gLq2_ball : forall x0 y k, Rabs (y - x0) < 1 -> Rabs (gLq2 y k) <= KL2 x0 * wt t ^ k.
Proof.
  intros x0 y k Hb; pose proof PI_RGT_0 as HPI; pose proof half_pos2 as Hhp.
  unfold gLq2, gL.
  rewrite Rabs_mult.
  rewrite (Rabs_right (exp (- (PI * (y - INR (S k)) ^ 2 * t)))) by (apply Rle_ge; left; apply exp_pos).
  assert (Esplit : exp (- (PI * (y - INR (S k)) ^ 2 * t))
                   = exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Esplit.
  apply Rle_trans with
    ((((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + (y - INR (S k)) ^ 2))
     * (exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))).
  - apply Rmult_le_compat_r.
    + apply Rmult_le_pos; left; apply exp_pos.
    + assert (Hu2 : 0 <= (y - INR (S k)) ^ 2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr).
      replace ((2 * PI * t * (y - INR (S k))) ^ 2 - 2 * PI * t)
        with ((2 * PI * t * (y - INR (S k))) ^ 2 + - (2 * PI * t)) by ring.
      eapply Rle_trans; [ apply Rabs_triang | ].
      rewrite Rabs_Ropp.
      rewrite (Rabs_right ((2 * PI * t * (y - INR (S k))) ^ 2))
        by (apply Rle_ge; rewrite <- Rsqr_pow2; apply Rle_0_sqr).
      rewrite (Rabs_right (2 * PI * t)) by (apply Rle_ge; nra).
      nra.
  - replace ((((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + (y - INR (S k)) ^ 2))
             * (exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2))))
      with (((2 * PI * t) ^ 2 + 2 * PI * t)
            * (((1 + (y - INR (S k)) ^ 2) * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))
               * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))) by ring.
    unfold KL2.
    replace (((2 * PI * t) ^ 2 + 2 * PI * t) * (1 + / (PI * t / 2)) * exp (PI * t / 2 * (x0 + 1 / 4)) * wt t ^ k)
      with (((2 * PI * t) ^ 2 + 2 * PI * t)
            * ((1 + / (PI * t / 2)) * (exp (PI * t / 2 * (x0 + 1 / 4)) * wt t ^ k))) by ring.
    apply Rmult_le_compat_l; [ nra | ].
    apply Rle_trans with ((1 + / (PI * t / 2)) * (exp (PI * t / 2 * (y - 3 / 4)) * wt t ^ k)).
    + apply Rmult_le_compat.
      * apply Rmult_le_pos;
          [ assert (0 <= (y - INR (S k)) ^ 2) by (rewrite <- Rsqr_pow2; apply Rle_0_sqr); nra
          | left; apply exp_pos ].
      * left; apply exp_pos.
      * exact (poly2_gauss_bound (PI * t / 2) (y - INR (S k)) Hhp).
      * unfold wt; exact (exp_sq_geom_L (PI * t / 2) y k Hhp).
    + apply Rmult_le_compat_l; [ assert (0 < / (PI * t / 2)) by (apply Rinv_0_lt_compat; exact Hhp); lra | ].
      apply Rmult_le_compat_r; [ apply pow_le; left; apply exp_pos | ].
      apply exp_le_compat; apply Rmult_le_compat_l; [ lra | ].
      apply Rabs_def2 in Hb; destruct Hb as [Hb1 Hb2]; lra.
Qed.

Lemma gRq2_self : forall x k, Rabs (gRq2 x k) <= KR2 x * wt t ^ k.
Proof. intros x k; apply (gRq2_ball x x k); replace (x - x) with 0 by ring; rewrite Rabs_R0; lra. Qed.
Lemma gLq2_self : forall x k, Rabs (gLq2 x k) <= KL2 x * wt t ^ k.
Proof. intros x k; apply (gLq2_ball x x k); replace (x - x) with 0 by ring; rewrite Rabs_R0; lra. Qed.

(* --- pointwise second-derivative limit GTheta2 --- *)

Lemma KR2_nonneg : forall x0, 0 <= KR2 x0.
Proof.
  intro x0; unfold KR2; pose proof PI_RGT_0; pose proof half_pos2.
  apply Rmult_le_pos; [ apply Rmult_le_pos | left; apply exp_pos ].
  - nra.
  - assert (0 < / (PI * t / 2)) by (apply Rinv_0_lt_compat; exact half_pos2); lra.
Qed.
Lemma KL2_nonneg : forall x0, 0 <= KL2 x0.
Proof.
  intro x0; unfold KL2; pose proof PI_RGT_0; pose proof half_pos2.
  apply Rmult_le_pos; [ apply Rmult_le_pos | left; apply exp_pos ].
  - nra.
  - assert (0 < / (PI * t / 2)) by (apply Rinv_0_lt_compat; exact half_pos2); lra.
Qed.

Definition GTheta2R (x : R) : R :=
  proj1_sig (dom_series_cv (gRq2 x) (KR2 x) (wt t)
              (wt_nonneg t) (wt_lt1 t Ht) (KR2_nonneg x) (gRq2_self x)).
Definition GTheta2L (x : R) : R :=
  proj1_sig (dom_series_cv (gLq2 x) (KL2 x) (wt t)
              (wt_nonneg t) (wt_lt1 t Ht) (KL2_nonneg x) (gLq2_self x)).
Definition GTheta2 (x : R) : R := GTheta2R x + GTheta2L x.

Lemma GTheta2R_spec : forall x, Un_cv (sum_f_R0 (gRq2 x)) (GTheta2R x).
Proof. intro x; unfold GTheta2R; apply proj2_sig. Qed.
Lemma GTheta2L_spec : forall x, Un_cv (sum_f_R0 (gLq2 x)) (GTheta2L x).
Proof. intro x; unfold GTheta2L; apply proj2_sig. Qed.

Lemma GTheta2_spec : forall x, Un_cv (fun N => gTheta_deriv2_partial x N) (GTheta2 x).
Proof.
  intro x; unfold gTheta_deriv2_partial, GTheta2;
    apply CV_plus; [ apply GTheta2R_spec | apply GTheta2L_spec ].
Qed.

Lemma gTheta_deriv2_cvu : forall x0,
  CVU (fun N s => gTheta_deriv2_partial s N) GTheta2 x0 (mkposreal 1 (Hr1)).
Proof.
  intros x0 eps He.
  set (K := KR2 x0 + KL2 x0).
  assert (HK0 : 0 <= K) by (unfold K; pose proof (KR2_nonneg x0); pose proof (KL2_nonneg x0); lra).
  assert (Hw1w : 0 < 1 - wt t) by (pose proof (wt_lt1 t Ht); lra).
  (* choose N so that the geometric tail is < eps; if K = 0 any N works *)
  destruct (Rle_lt_or_eq_dec 0 K HK0) as [HKpos | HKzero].
  - assert (He' : 0 < eps * (1 - wt t) / K)
      by (apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; [ exact He | exact Hw1w ]
                                   | apply Rinv_0_lt_compat; exact HKpos ]).
    destruct (pow_lt_1_zero (wt t) (wt_abs_lt1 t Ht) (eps * (1 - wt t) / K) He') as [N HN].
    exists N; intros n y Hn Hby.
    unfold Boule in Hby; simpl in Hby.
    apply Rle_lt_trans with (KR2 x0 * wt t ^ (S n) / (1 - wt t) + KL2 x0 * wt t ^ (S n) / (1 - wt t)).
    + unfold GTheta2, gTheta_deriv2_partial.
      replace (GTheta2R y + GTheta2L y - (sum_f_R0 (gRq2 y) n + sum_f_R0 (gLq2 y) n))
        with ((GTheta2R y - sum_f_R0 (gRq2 y) n) + (GTheta2L y - sum_f_R0 (gLq2 y) n)) by ring.
      eapply Rle_trans; [ apply Rabs_triang | ].
      apply Rplus_le_compat.
      * apply (geom_tail_est (gRq2 y) (GTheta2R y) (KR2 x0) (wt t) (wt_nonneg t) (wt_lt1 t Ht)
                 (KR2_nonneg x0) (GTheta2R_spec y) (fun k => gRq2_ball x0 y k Hby) n).
      * apply (geom_tail_est (gLq2 y) (GTheta2L y) (KL2 x0) (wt t) (wt_nonneg t) (wt_lt1 t Ht)
                 (KL2_nonneg x0) (GTheta2L_spec y) (fun k => gLq2_ball x0 y k Hby) n).
    + replace (KR2 x0 * wt t ^ (S n) / (1 - wt t) + KL2 x0 * wt t ^ (S n) / (1 - wt t))
        with (K * wt t ^ (S n) / (1 - wt t)) by (unfold K; field; lra).
      apply Rmult_lt_reg_r with (1 - wt t); [ exact Hw1w | ].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_r.
      specialize (HN (S n) ltac:(lia)).
      rewrite Rabs_right in HN by (apply Rle_ge; apply pow_le; apply wt_nonneg).
      apply Rlt_le_trans with (K * (eps * (1 - wt t) / K)).
      * apply Rmult_lt_compat_l; [ exact HKpos | exact HN ].
      * apply Req_le; field; apply Rgt_not_eq; exact HKpos.
  - exists 0%nat; intros n y Hn Hby; unfold Boule in Hby; simpl in Hby.
    apply Rle_lt_trans with (KR2 x0 * wt t ^ (S n) / (1 - wt t) + KL2 x0 * wt t ^ (S n) / (1 - wt t)).
    + unfold GTheta2, gTheta_deriv2_partial.
      replace (GTheta2R y + GTheta2L y - (sum_f_R0 (gRq2 y) n + sum_f_R0 (gLq2 y) n))
        with ((GTheta2R y - sum_f_R0 (gRq2 y) n) + (GTheta2L y - sum_f_R0 (gLq2 y) n)) by ring.
      eapply Rle_trans; [ apply Rabs_triang | ].
      apply Rplus_le_compat.
      * apply (geom_tail_est (gRq2 y) (GTheta2R y) (KR2 x0) (wt t) (wt_nonneg t) (wt_lt1 t Ht)
                 (KR2_nonneg x0) (GTheta2R_spec y) (fun k => gRq2_ball x0 y k Hby) n).
      * apply (geom_tail_est (gLq2 y) (GTheta2L y) (KL2 x0) (wt t) (wt_nonneg t) (wt_lt1 t Ht)
                 (KL2_nonneg x0) (GTheta2L_spec y) (fun k => gLq2_ball x0 y k Hby) n).
    + assert (HK' : 0 = KR2 x0 + KL2 x0) by (unfold K in HKzero; exact HKzero).
      assert (HKR : KR2 x0 = 0) by (pose proof (KR2_nonneg x0); pose proof (KL2_nonneg x0); lra).
      assert (HKL : KL2 x0 = 0) by (pose proof (KR2_nonneg x0); pose proof (KL2_nonneg x0); lra).
      rewrite HKR, HKL.
      replace (0 * wt t ^ (S n) / (1 - wt t) + 0 * wt t ^ (S n) / (1 - wt t)) with 0
        by (field; lra).
      exact He.
Qed.

Theorem GTheta_C2 : forall x, derivable_pt_lim (GTheta1 t Ht) x (GTheta2 x).
Proof.
  intro x.
  assert (Hcvu : CVU (fun N s => gTheta_deriv2_partial s N) GTheta2 x (mkposreal 1 Hr1))
    by apply gTheta_deriv2_cvu.
  apply (derivable_pt_lim_CVU (fun N s => gTheta_deriv_partial t s N)
           (fun N s => gTheta_deriv2_partial s N) (GTheta1 t Ht) GTheta2 x x (mkposreal 1 Hr1)).
  - unfold Boule; simpl; replace (x - x) with 0 by ring; rewrite Rabs_R0; exact Hr1.
  - intros y n _; apply gTheta_deriv_partial_derives.
  - intros y _; apply (GTheta1_spec t Ht y).
  - exact Hcvu.
  - apply (CVU_continuity (fun N s => gTheta_deriv2_partial s N) GTheta2 x (mkposreal 1 Hr1) Hcvu).
    intros n y _; apply cont_gTheta_deriv2_partial.
Qed.

Corollary GTheta1_cont : continuity (GTheta1 t Ht).
Proof. intro x; apply derivable_continuous_pt; exists (GTheta2 x); apply GTheta_C2. Qed.

End Deriv2.

(* ================================================================= *)
(*  Part C.  The 2π-rescaled representative ftil.                    *)
(* ================================================================= *)

Definition ftil (t : R) (Ht : 0 < t) (u : R) : R := GTheta t Ht (u / (2 * PI)).
Definition ftil1 (t : R) (Ht : 0 < t) (u : R) : R := / (2 * PI) * GTheta1 t Ht (u / (2 * PI)).
Definition ftil2 (t : R) (Ht : 0 < t) (u : R) : R :=
  / (2 * PI) * (/ (2 * PI) * GTheta2 t Ht (u / (2 * PI))).

Lemma twoPI_pos : 0 < 2 * PI.
Proof. pose proof PI_RGT_0; lra. Qed.

Lemma twoPI_ne : 2 * PI <> 0.
Proof. apply Rgt_not_eq; apply twoPI_pos. Qed.

Lemma dcov : forall u, derivable_pt_lim (fun v => v / (2 * PI)) u (/ (2 * PI)).
Proof.
  intro u.
  pose proof (derivable_pt_lim_mult (fun v => v) (fun _ => / (2 * PI)) u 1 0
                (derivable_pt_lim_id u) (derivable_pt_lim_const (/ (2 * PI)) u)) as Hm.
  cbv beta in Hm.
  replace (1 * / (2 * PI) + u * 0) with (/ (2 * PI)) in Hm by ring.
  unfold mult_fct in Hm; unfold Rdiv; exact Hm.
Qed.

Lemma ftil_at_0 : forall t Ht, ftil t Ht 0 = theta t Ht.
Proof.
  intros t Ht; unfold ftil.
  replace (0 / (2 * PI)) with 0 by (unfold Rdiv; ring).
  apply GTheta_at_0.
Qed.

Lemma ftil_period_2PI : forall t Ht u, ftil t Ht (u + 2 * PI) = ftil t Ht u.
Proof.
  intros t Ht u; unfold ftil.
  replace ((u + 2 * PI) / (2 * PI)) with (u / (2 * PI) + 1)
    by (field; apply Rgt_not_eq; apply PI_RGT_0).
  apply GTheta_periodic.
Qed.

Lemma ftil_cont : forall t Ht, continuity (ftil t Ht).
Proof.
  intros t Ht u; unfold ftil.
  apply (continuity_pt_comp (fun v => v / (2 * PI)) (GTheta t Ht) u).
  - apply derivable_continuous_pt; exists (/ (2 * PI)); apply dcov.
  - apply GTheta_cont.
Qed.

Lemma ftil_C1 : forall t Ht u, derivable_pt_lim (ftil t Ht) u (ftil1 t Ht u).
Proof.
  intros t Ht u; unfold ftil, ftil1.
  pose proof (derivable_pt_lim_comp (fun v => v / (2 * PI)) (GTheta t Ht) u
                (/ (2 * PI)) (GTheta1 t Ht (u / (2 * PI))) (dcov u) (GTheta_C1 t Ht (u / (2 * PI)))) as Hc.
  replace (/ (2 * PI) * GTheta1 t Ht (u / (2 * PI)))
    with (GTheta1 t Ht (u / (2 * PI)) * / (2 * PI)) by ring.
  exact Hc.
Qed.

Lemma ftil_C2 : forall t Ht u, derivable_pt_lim (ftil1 t Ht) u (ftil2 t Ht u).
Proof.
  intros t Ht u; unfold ftil1, ftil2.
  pose proof (derivable_pt_lim_comp (fun v => v / (2 * PI)) (GTheta1 t Ht) u
                (/ (2 * PI)) (GTheta2 t Ht (u / (2 * PI))) (dcov u) (GTheta_C2 t Ht (u / (2 * PI)))) as Hc.
  apply (derivable_pt_lim_scal (fun v => GTheta1 t Ht (v / (2 * PI))) (/ (2 * PI)) u
           (GTheta2 t Ht (u / (2 * PI)) * / (2 * PI))) in Hc.
  replace (/ (2 * PI) * (/ (2 * PI) * GTheta2 t Ht (u / (2 * PI))))
    with (/ (2 * PI) * (GTheta2 t Ht (u / (2 * PI)) * / (2 * PI))) by ring.
  exact Hc.
Qed.

Lemma ftil1_cont : forall t Ht, continuity (ftil1 t Ht).
Proof.
  intros t Ht u; unfold ftil1.
  apply (continuity_pt_scal (fun v => GTheta1 t Ht (v / (2 * PI))) (/ (2 * PI)) u).
  apply (continuity_pt_comp (fun v => v / (2 * PI)) (GTheta1 t Ht) u).
  - apply derivable_continuous_pt; exists (/ (2 * PI)); apply dcov.
  - apply GTheta1_cont.
Qed.

Print Assumptions GTheta_C2.

(* ================================================================= *)
(*  END GaussPeriodDeriv2.v                                          *)
(*  Θ_t is C² (GTheta_C2); ftil t Ht = Θ_t(·/2π) is the 2π-periodic,  *)
(*  globally-C² representative (ftil_C1/ftil_C2/ftil1_cont), with     *)
(*  ftil 0 = θ(t) and ftil(u+2π)=ftil u.  Ready for the localiser.    *)
(* ================================================================= *)
