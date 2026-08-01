(* ================================================================= *)
(*  GaussPeriodDeriv.v  —  Poisson→θ line, P3 step 2: Θ_t is C¹ in x.  *)
(*                                                                    *)
(*  The periodized Gaussian GTheta t Ht (total, from GaussPeriodTotal) *)
(*  is continuously differentiable in x, with termwise derivative      *)
(*     Θ_t'(x) = Σ_{n∈ℤ} −2πt(x+n) e^{−π(x+n)²t}.                     *)
(*                                                                    *)
(*  Spine = the Leibniz-gap CVU engine (derivable_pt_lim_CVU): each     *)
(*  derivative partial is a genuine derivative of the partial (chain    *)
(*  rule, deriv_sum), the partials converge pointwise (GTheta_spec),    *)
(*  and the derivative partials converge UNIFORMLY on every unit ball.  *)
(*  Uniformity uses a per-term geometric domination with room to        *)
(*  spare — split e^{−πt u²} in half and absorb the |u| factor:         *)
(*     |−2πt·u·e^{−πt u²}| ≤ 2πt·(|u|e^{−(πt/2)u²})·e^{−(πt/2)u²}      *)
(*                        ≤ 2πt·(1/√(πt/2))·e^{(πt/2)(¼−x)}·(e^{−πt/2})ⁿ *)
(*  via abs_gauss_bound (|u|e^{−a u²}≤1/√a) and the perfect-square      *)
(*  geometric bound.  No new axioms (classical Reals only).            *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 PSeries_reg FunctionalExtensionality Lra Lia.
Require Import JacobiTheta GaussPeriodization GaussPeriodicity GaussPeriodTotal
        GaussCauchy GaussSubst.
Open Scope R_scope.

(* ================================================================= *)
(*  Part A.  Reusable analytic helpers (no section variables).       *)
(* ================================================================= *)

Lemma exp_sq_geom_R : forall a x m, 0 < a ->
  exp (- (a * (x + INR m) ^ 2)) <= exp (a * (/ 4 - x)) * exp (- a) ^ m.
Proof.
  intros a x m Ha; rewrite exp_INR_pow, <- exp_plus; apply exp_le_compat.
  replace ((x + INR m) ^ 2) with ((x + INR m) * (x + INR m)) by ring.
  assert (Hsq : 0 <= (x + INR m - / 2) * (x + INR m - / 2))
    by (pose proof (Rle_0_sqr (x + INR m - / 2)); unfold Rsqr in *; lra).
  assert (Hkey : 0 <= a * ((x + INR m - / 2) * (x + INR m - / 2)))
    by (apply Rmult_le_pos; [ lra | exact Hsq ]).
  nra.
Qed.

Lemma exp_sq_geom_L : forall a x m, 0 < a ->
  exp (- (a * (x - INR (S m)) ^ 2)) <= exp (a * (x - 3 / 4)) * exp (- a) ^ m.
Proof.
  intros a x m Ha; rewrite exp_INR_pow, <- exp_plus; apply exp_le_compat.
  rewrite S_INR.
  replace ((x - (INR m + 1)) ^ 2) with ((x - (INR m + 1)) * (x - (INR m + 1))) by ring.
  assert (Hsq : 0 <= (x - INR m - / 2) * (x - INR m - / 2))
    by (pose proof (Rle_0_sqr (x - INR m - / 2)); unfold Rsqr in *; lra).
  assert (Hkey : 0 <= a * ((x - INR m - / 2) * (x - INR m - / 2)))
    by (apply Rmult_le_pos; [ lra | exact Hsq ]).
  nra.
Qed.

Lemma s_exp_neg_sq_le1 : forall s, 0 <= s -> s * exp (- s ^ 2) <= 1.
Proof.
  intros s Hs.
  assert (Hexp : s <= exp (s ^ 2)).
  { destruct (Req_dec s 0) as [-> | Hne].
    - replace (0 ^ 2) with 0 by ring; rewrite exp_0; lra.
    - assert (Hlt : 0 < s) by (destruct Hs; [ assumption | congruence ]).
      assert (Hs2 : 0 < s ^ 2) by (apply pow_lt; exact Hlt).
      pose proof (exp_ineq1 (s ^ 2) (Rgt_not_eq (s ^ 2) 0 Hs2)) as Hi.
      assert (s <= 1 + s ^ 2) by nra; lra. }
  apply Rle_trans with (exp (s ^ 2) * exp (- s ^ 2)).
  - apply Rmult_le_compat_r; [ left; apply exp_pos | exact Hexp ].
  - rewrite <- exp_plus; replace (s ^ 2 + - s ^ 2) with 0 by ring;
      rewrite exp_0; apply Rle_refl.
Qed.

Lemma abs_gauss_bound : forall a u, 0 < a -> Rabs u * exp (- (a * u ^ 2)) <= / sqrt a.
Proof.
  intros a u Ha.
  assert (Hsa : 0 < sqrt a) by (apply sqrt_lt_R0; exact Ha).
  set (s := sqrt a * Rabs u).
  assert (Hs0 : 0 <= s) by (apply Rmult_le_pos; [ left; exact Hsa | apply Rabs_pos ]).
  assert (Hau : a * u ^ 2 = s ^ 2).
  { unfold s; rewrite <- Rsqr_pow2, <- Rsqr_pow2, Rsqr_mult.
    rewrite Rsqr_sqrt by (left; exact Ha); rewrite <- Rsqr_abs; reflexivity. }
  assert (Hru : Rabs u = s / sqrt a) by (unfold s; field; apply Rgt_not_eq; exact Hsa).
  rewrite Hru, Hau.
  replace (s / sqrt a * exp (- s ^ 2)) with (/ sqrt a * (s * exp (- s ^ 2)))
    by (field; apply Rgt_not_eq; exact Hsa).
  rewrite <- (Rmult_1_r (/ sqrt a)) at 2.
  apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; exact Hsa | ].
  apply s_exp_neg_sq_le1; exact Hs0.
Qed.

Lemma geom_sum_closed : forall w, w <> 1 ->
  forall n, sum_f_R0 (fun k => w ^ k) n = (1 - w ^ (S n)) / (1 - w).
Proof.
  intros w Hw n; assert (H1w : 1 - w <> 0) by lra.
  pose proof (GP_finite w n) as G.
  apply Rmult_eq_reg_r with (1 - w); [ | exact H1w ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by exact H1w; rewrite Rmult_1_r.
  replace (S n) with (n + 1)%nat by lia.
  replace (1 - w ^ (n + 1)) with (- (w ^ (n + 1) - 1)) by ring.
  rewrite <- G; ring.
Qed.

Lemma sum_absdom : forall (f b : nat -> R),
  (forall k, Rabs (f k) <= b k) -> (forall k, 0 <= b k) ->
  forall i j, Rabs (sum_f_R0 f i - sum_f_R0 f j) <= Rabs (sum_f_R0 b i - sum_f_R0 b j).
Proof.
  intros f b Hfb Hb.
  assert (Hge : forall j d,
    Rabs (sum_f_R0 f (j + d) - sum_f_R0 f j) <= sum_f_R0 b (j + d) - sum_f_R0 b j).
  { intros j d; induction d as [| d IH].
    - rewrite Nat.add_0_r; replace (sum_f_R0 f j - sum_f_R0 f j) with 0 by ring;
        rewrite Rabs_R0; lra.
    - rewrite Nat.add_succ_r, (tech5 f (j + d)), (tech5 b (j + d)).
      replace (sum_f_R0 f (j + d) + f (S (j + d)) - sum_f_R0 f j)
        with ((sum_f_R0 f (j + d) - sum_f_R0 f j) + f (S (j + d))) by ring.
      eapply Rle_trans; [ apply Rabs_triang | ].
      replace (sum_f_R0 b (j + d) + b (S (j + d)) - sum_f_R0 b j)
        with ((sum_f_R0 b (j + d) - sum_f_R0 b j) + b (S (j + d))) by ring.
      apply Rplus_le_compat; [ exact IH | apply Hfb ]. }
  intros i j; destruct (Nat.le_ge_cases j i) as [Hle | Hle].
  - remember (i - j)%nat as d eqn:Hd.
    assert (Ei : i = (j + d)%nat) by lia; rewrite Ei.
    rewrite (Rabs_right (sum_f_R0 b (j + d) - sum_f_R0 b j));
      [ apply Hge | apply Rle_ge; eapply Rle_trans; [ apply Rabs_pos | apply Hge ] ].
  - remember (j - i)%nat as d eqn:Hd.
    assert (Ej : j = (i + d)%nat) by lia; rewrite Ej.
    rewrite Rabs_minus_sym, (Rabs_minus_sym (sum_f_R0 b i)).
    rewrite (Rabs_right (sum_f_R0 b (i + d) - sum_f_R0 b i));
      [ apply Hge | apply Rle_ge; eapply Rle_trans; [ apply Rabs_pos | apply Hge ] ].
Qed.

Lemma geom_cv : forall w, 0 <= w -> w < 1 ->
  Un_cv (sum_f_R0 (fun k => w ^ k)) (/ (1 - w)).
Proof.
  intros w Hw0 Hw1.
  assert (Hab : Rabs w < 1) by (rewrite Rabs_right by (apply Rle_ge; exact Hw0); exact Hw1).
  intros eps He.
  assert (He' : (1 - w) * eps > 0) by (apply Rmult_gt_0_compat; lra).
  destruct (pow_lt_1_zero w Hab ((1 - w) * eps) He') as [N HN].
  exists N; intros n Hn.
  unfold R_dist; rewrite geom_sum_closed by lra.
  replace ((1 - w ^ S n) / (1 - w) - / (1 - w)) with (- (w ^ S n / (1 - w))) by (field; lra).
  rewrite Rabs_Ropp, Rabs_right by
    (apply Rle_ge; apply Rmult_le_pos;
     [ apply pow_le; exact Hw0 | left; apply Rinv_0_lt_compat; lra ]).
  apply Rmult_lt_reg_r with (1 - w); [ lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_r.
  specialize (HN (S n) ltac:(lia)).
  rewrite Rabs_right in HN by (apply Rle_ge; apply pow_le; exact Hw0).
  rewrite Rmult_comm; exact HN.
Qed.

Lemma geom_mono : forall w, 0 <= w -> forall N M,
  sum_f_R0 (fun k => w ^ k) N <= sum_f_R0 (fun k => w ^ k) (N + M).
Proof.
  intros w Hw N M; induction M as [| M IH].
  - rewrite Nat.add_0_r; apply Rle_refl.
  - rewrite Nat.add_succ_r, (tech5 (fun k => w ^ k) (N + M));
      assert (0 <= w ^ (S (N + M))) by (apply pow_le; exact Hw); lra.
Qed.

Lemma geom_diff_nonneg : forall w, 0 <= w -> forall N M,
  0 <= sum_f_R0 (fun k => w ^ k) (N + M) - sum_f_R0 (fun k => w ^ k) N.
Proof. intros w Hw N M; pose proof (geom_mono w Hw N M); lra. Qed.

Lemma geom_window : forall w, 0 <= w -> w < 1 ->
  forall N M, sum_f_R0 (fun k => w ^ k) (N + M) - sum_f_R0 (fun k => w ^ k) N
              <= w ^ (S N) / (1 - w).
Proof.
  intros w Hw0 Hw1 N M; assert (Hne : w <> 1) by lra.
  rewrite !geom_sum_closed by exact Hne.
  replace ((1 - w ^ (S (N + M))) / (1 - w) - (1 - w ^ (S N)) / (1 - w))
    with ((w ^ (S N) - w ^ (S (N + M))) * / (1 - w)) by (field; lra).
  unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | ].
  assert (0 <= w ^ (S (N + M))) by (apply pow_le; exact Hw0); lra.
Qed.

Lemma geom_tail_est : forall (f : nat -> R) (L C w : R),
  0 <= w -> w < 1 -> 0 <= C ->
  Un_cv (sum_f_R0 f) L -> (forall k, Rabs (f k) <= C * w ^ k) ->
  forall N, Rabs (L - sum_f_R0 f N) <= C * w ^ (S N) / (1 - w).
Proof.
  intros f L C w Hw0 Hw1 HC HL Hdom N.
  set (g := sum_f_R0 f).
  set (B0 := C * w ^ (S N) / (1 - w)).
  assert (Hb : forall k, 0 <= C * w ^ k)
    by (intro k; apply Rmult_le_pos; [ exact HC | apply pow_le; exact Hw0 ]).
  assert (Hshift : Un_cv (fun M => g (N + M)%nat) L)
    by (intros eps He; destruct (HL eps He) as [N0 H0]; exists N0; intros M HM; apply H0; lia).
  assert (Hdiff : Un_cv (fun M => g (N + M)%nat - g N) (L - g N)).
  { apply (CV_minus (fun M => g (N + M)%nat) (fun _ => g N) L (g N)); [ exact Hshift | ].
    intros eps He; exists 0%nat; intros; unfold R_dist;
      replace (g N - g N) with 0 by ring; rewrite Rabs_R0; exact He. }
  assert (Habs : Un_cv (fun M => Rabs (g (N + M)%nat - g N)) (Rabs (L - g N))).
  { intros eps He; destruct (Hdiff eps He) as [N0 H0]; exists N0; intros M HM;
      unfold R_dist; eapply Rle_lt_trans; [ apply Rabs_triang_inv2 | apply H0; exact HM ]. }
  assert (Hbnd : forall M, Rabs (g (N + M)%nat - g N) <= B0).
  { intro M; unfold g.
    eapply Rle_trans; [ apply (sum_absdom f (fun k => C * w ^ k) Hdom Hb) | ].
    rewrite !sum_f_R0_scal, <- Rmult_minus_distr_l.
    rewrite Rabs_right by
      (apply Rle_ge; apply Rmult_le_pos;
       [ exact HC | apply geom_diff_nonneg; exact Hw0 ]).
    unfold B0, Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l; [ exact HC | ].
    pose proof (geom_window w Hw0 Hw1 N M) as Hw; unfold Rdiv in Hw; exact Hw. }
  apply (Un_cv_le_const (fun M => Rabs (g (N + M)%nat - g N)) (Rabs (L - g N)) B0);
    [ exact Hbnd | exact Habs ].
Qed.

Lemma dom_series_cv : forall (f : nat -> R) (C w : R),
  0 <= w -> w < 1 -> 0 <= C ->
  (forall k, Rabs (f k) <= C * w ^ k) -> { L : R | Un_cv (sum_f_R0 f) L }.
Proof.
  intros f C w Hw0 Hw1 HC Hdom.
  assert (Hb : forall k, 0 <= C * w ^ k)
    by (intro k; apply Rmult_le_pos; [ exact HC | apply pow_le; exact Hw0 ]).
  apply (cauchy_dominated_cv (sum_f_R0 f) (sum_f_R0 (fun k => C * w ^ k)) (C * / (1 - w))).
  - intros i j; apply (sum_absdom f (fun k => C * w ^ k) Hdom Hb).
  - assert (HcC : Un_cv (fun _ : nat => C) C)
      by (intros e He; exists 0%nat; intros; unfold R_dist;
          replace (C - C) with 0 by ring; rewrite Rabs_R0; exact He).
    pose proof (CV_mult (fun _ => C) (sum_f_R0 (fun k => w ^ k)) C (/ (1 - w))
                  HcC (geom_cv w Hw0 Hw1)) as Hcv.
    intros eps He; destruct (Hcv eps He) as [N HN]; exists N; intros n Hn.
    rewrite sum_f_R0_scal; apply HN; exact Hn.
Qed.

Lemma deriv_sum : forall (F F' : nat -> R -> R) N x,
  (forall k, derivable_pt_lim (fun s => F k s) x (F' k x)) ->
  derivable_pt_lim (fun s => sum_f_R0 (fun k => F k s) N) x
                   (sum_f_R0 (fun k => F' k x) N).
Proof.
  intros F F' N x H; induction N as [| N IH]; cbn [sum_f_R0].
  - apply H.
  - apply derivable_pt_lim_plus; [ exact IH | apply H ].
Qed.

Lemma cont_sum : forall (F : nat -> R -> R) N,
  (forall k, continuity (fun s => F k s)) ->
  continuity (fun s => sum_f_R0 (fun k => F k s) N).
Proof.
  intros F N H; induction N as [| N IH]; intro s; cbn [sum_f_R0].
  - apply H.
  - apply continuity_pt_plus; [ apply IH | apply H ].
Qed.

(* ================================================================= *)
(*  Part B.  Θ_t-specific derivative work.                           *)
(* ================================================================= *)

Section Deriv.

Variable t : R.
Hypothesis Ht : 0 < t.

Definition gRq (x : R) (k : nat) : R := - (2 * PI * t * (x + INR k)) * gR t x k.
Definition gLq (x : R) (k : nat) : R := - (2 * PI * t * (x - INR (S k))) * gL t x k.
Definition gTheta_deriv_partial (x : R) (N : nat) : R :=
  sum_f_R0 (gRq x) N + sum_f_R0 (gLq x) N.

Definition wt := exp (- (PI * t / 2)).
Definition KR (x0 : R) := 2 * PI * t * / sqrt (PI * t / 2) * exp (PI * t / 2 * (/ 4 - x0 + 1)).
Definition KL (x0 : R) := 2 * PI * t * / sqrt (PI * t / 2) * exp (PI * t / 2 * (x0 + 1 / 4)).

Lemma half_pos : 0 < PI * t / 2.
Proof. pose proof PI_RGT_0; nra. Qed.

Lemma wt_pos : 0 < wt.
Proof. apply exp_pos. Qed.

Lemma wt_nonneg : 0 <= wt.
Proof. left; apply wt_pos. Qed.

Lemma wt_lt1 : wt < 1.
Proof. unfold wt; rewrite <- exp_0; apply exp_increasing; pose proof PI_RGT_0; nra. Qed.

Lemma wt_abs_lt1 : Rabs wt < 1.
Proof. rewrite Rabs_right by (apply Rle_ge; apply wt_nonneg); apply wt_lt1. Qed.

Lemma KR_pos : forall x0, 0 < KR x0.
Proof.
  intro x0; unfold KR; pose proof PI_RGT_0; pose proof half_pos.
  apply Rmult_lt_0_compat;
    [ apply Rmult_lt_0_compat;
      [ nra | apply Rinv_0_lt_compat; apply sqrt_lt_R0; exact half_pos ]
    | apply exp_pos ].
Qed.

Lemma KL_pos : forall x0, 0 < KL x0.
Proof.
  intro x0; unfold KL; pose proof PI_RGT_0; pose proof half_pos.
  apply Rmult_lt_0_compat;
    [ apply Rmult_lt_0_compat;
      [ nra | apply Rinv_0_lt_compat; apply sqrt_lt_R0; exact half_pos ]
    | apply exp_pos ].
Qed.

Lemma KR_nonneg : forall x0, 0 <= KR x0.
Proof. intro x0; left; apply KR_pos. Qed.
Lemma KL_nonneg : forall x0, 0 <= KL x0.
Proof. intro x0; left; apply KL_pos. Qed.

(* --- per-term derivatives of the Gaussian kernels --- *)

Lemma dgR : forall x n, derivable_pt_lim (fun s => gR t s n) x (gRq x n).
Proof.
  intros x n; unfold gRq, gR.
  assert (Haff : derivable_pt_lim (fun s => s + INR n) x 1).
  { replace 1 with (1 + 0) by ring;
      apply derivable_pt_lim_plus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hsq : derivable_pt_lim (fun s => (s + INR n) ^ 2) x (2 * (x + INR n))).
  { pose proof (derivable_pt_lim_comp (fun s => s + INR n) (fun z => z ^ 2) x
        1 (INR 2 * (x + INR n) ^ Init.Nat.pred 2) Haff
        (derivable_pt_lim_pow (x + INR n) 2)) as Hc.
    replace (2 * (x + INR n)) with (INR 2 * (x + INR n) ^ Init.Nat.pred 2 * 1)
      by (simpl; ring); exact Hc. }
  assert (Hin : derivable_pt_lim (fun s => - (PI * (s + INR n) ^ 2 * t)) x
                  (- (2 * PI * t * (x + INR n)))).
  { assert (Hpt : derivable_pt_lim (fun s => t * (PI * (s + INR n) ^ 2)) x
                    (t * (PI * (2 * (x + INR n)))))
      by (apply derivable_pt_lim_scal; apply derivable_pt_lim_scal; exact Hsq).
    assert (Heq : (fun s => - (PI * (s + INR n) ^ 2 * t))
                  = (fun s => - (t * (PI * (s + INR n) ^ 2))))
      by (apply functional_extensionality; intro s; ring).
    rewrite Heq.
    replace (- (2 * PI * t * (x + INR n))) with (- (t * (PI * (2 * (x + INR n))))) by ring.
    apply derivable_pt_lim_opp; exact Hpt. }
  pose proof (derivable_pt_lim_comp (fun s => - (PI * (s + INR n) ^ 2 * t)) exp x
                (- (2 * PI * t * (x + INR n))) (exp (- (PI * (x + INR n) ^ 2 * t)))
                Hin (derivable_pt_lim_exp _)) as Hc.
  replace (- (2 * PI * t * (x + INR n)) * exp (- (PI * (x + INR n) ^ 2 * t)))
    with (exp (- (PI * (x + INR n) ^ 2 * t)) * - (2 * PI * t * (x + INR n))) by ring.
  exact Hc.
Qed.

Lemma dgL : forall x n, derivable_pt_lim (fun s => gL t s n) x (gLq x n).
Proof.
  intros x n; unfold gLq, gL.
  assert (Haff : derivable_pt_lim (fun s => s - INR (S n)) x 1).
  { replace 1 with (1 - 0) by ring;
      apply derivable_pt_lim_minus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hsq : derivable_pt_lim (fun s => (s - INR (S n)) ^ 2) x (2 * (x - INR (S n)))).
  { pose proof (derivable_pt_lim_comp (fun s => s - INR (S n)) (fun z => z ^ 2) x
        1 (INR 2 * (x - INR (S n)) ^ Init.Nat.pred 2) Haff
        (derivable_pt_lim_pow (x - INR (S n)) 2)) as Hc.
    replace (2 * (x - INR (S n))) with (INR 2 * (x - INR (S n)) ^ Init.Nat.pred 2 * 1)
      by (simpl; ring); exact Hc. }
  assert (Hin : derivable_pt_lim (fun s => - (PI * (s - INR (S n)) ^ 2 * t)) x
                  (- (2 * PI * t * (x - INR (S n))))).
  { assert (Hpt : derivable_pt_lim (fun s => t * (PI * (s - INR (S n)) ^ 2)) x
                    (t * (PI * (2 * (x - INR (S n))))))
      by (apply derivable_pt_lim_scal; apply derivable_pt_lim_scal; exact Hsq).
    assert (Heq : (fun s => - (PI * (s - INR (S n)) ^ 2 * t))
                  = (fun s => - (t * (PI * (s - INR (S n)) ^ 2))))
      by (apply functional_extensionality; intro s; ring).
    rewrite Heq.
    replace (- (2 * PI * t * (x - INR (S n)))) with (- (t * (PI * (2 * (x - INR (S n)))))) by ring.
    apply derivable_pt_lim_opp; exact Hpt. }
  pose proof (derivable_pt_lim_comp (fun s => - (PI * (s - INR (S n)) ^ 2 * t)) exp x
                (- (2 * PI * t * (x - INR (S n)))) (exp (- (PI * (x - INR (S n)) ^ 2 * t)))
                Hin (derivable_pt_lim_exp _)) as Hc.
  replace (- (2 * PI * t * (x - INR (S n))) * exp (- (PI * (x - INR (S n)) ^ 2 * t)))
    with (exp (- (PI * (x - INR (S n)) ^ 2 * t)) * - (2 * PI * t * (x - INR (S n)))) by ring.
  exact Hc.
Qed.

Lemma gTheta_partial_derives : forall x N,
  derivable_pt_lim (fun s => gTheta_partial t s N) x (gTheta_deriv_partial x N).
Proof.
  intros x N; unfold gTheta_partial, gTheta_deriv_partial, gRp, gLp.
  apply derivable_pt_lim_plus;
    [ apply (deriv_sum (fun k s => gR t s k) (fun k s => gRq s k) N x); intro k; apply dgR
    | apply (deriv_sum (fun k s => gL t s k) (fun k s => gLq s k) N x); intro k; apply dgL ].
Qed.

(* --- continuity of the derivative terms and partials --- *)

Lemma cont_gR : forall k, continuity (fun s => gR t s k).
Proof.
  intros k s; unfold gR.
  apply (continuity_pt_comp (fun s => - (PI * (s + INR k) ^ 2 * t)) exp s).
  - apply continuity_pt_opp.
    apply (continuity_pt_mult (fun s => PI * (s + INR k) ^ 2) (fun _ => t) s).
    + apply (continuity_pt_scal (fun s => (s + INR k) ^ 2) PI s).
      apply (cont_pow (fun s => s + INR k) 2).
      intro y; apply continuity_pt_plus;
        [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
    + apply continuity_pt_const; intros a b; reflexivity.
  - apply derivable_continuous_pt; exists (exp (- (PI * (s + INR k) ^ 2 * t)));
      apply derivable_pt_lim_exp.
Qed.

Lemma cont_gL : forall k, continuity (fun s => gL t s k).
Proof.
  intros k s; unfold gL.
  apply (continuity_pt_comp (fun s => - (PI * (s - INR (S k)) ^ 2 * t)) exp s).
  - apply continuity_pt_opp.
    apply (continuity_pt_mult (fun s => PI * (s - INR (S k)) ^ 2) (fun _ => t) s).
    + apply (continuity_pt_scal (fun s => (s - INR (S k)) ^ 2) PI s).
      apply (cont_pow (fun s => s - INR (S k)) 2).
      intro y; apply continuity_pt_minus;
        [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
    + apply continuity_pt_const; intros a b; reflexivity.
  - apply derivable_continuous_pt; exists (exp (- (PI * (s - INR (S k)) ^ 2 * t)));
      apply derivable_pt_lim_exp.
Qed.

Lemma cont_gRq : forall k, continuity (fun s => gRq s k).
Proof.
  intros k s; unfold gRq.
  apply continuity_pt_mult; [ | apply cont_gR ].
  apply continuity_pt_opp.
  apply (continuity_pt_scal (fun s => s + INR k) (2 * PI * t) s).
  apply continuity_pt_plus;
    [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
Qed.

Lemma cont_gLq : forall k, continuity (fun s => gLq s k).
Proof.
  intros k s; unfold gLq.
  apply continuity_pt_mult; [ | apply cont_gL ].
  apply continuity_pt_opp.
  apply (continuity_pt_scal (fun s => s - INR (S k)) (2 * PI * t) s).
  apply continuity_pt_minus;
    [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
Qed.

Lemma cont_gTheta_deriv_partial : forall N, continuity (fun s => gTheta_deriv_partial s N).
Proof.
  intro N; unfold gTheta_deriv_partial; intro s.
  apply continuity_pt_plus;
    [ apply (cont_sum (fun k s => gRq s k) N); intro k; apply cont_gRq
    | apply (cont_sum (fun k s => gLq s k) N); intro k; apply cont_gLq ].
Qed.

(* --- per-term geometric domination of the derivative terms --- *)

Lemma gRq_ball : forall x0 y k, Rabs (y - x0) < 1 -> Rabs (gRq y k) <= KR x0 * wt ^ k.
Proof.
  intros x0 y k Hb; pose proof PI_RGT_0 as HPI; pose proof half_pos as Hhp.
  unfold gRq, gR.
  rewrite Rabs_mult, Rabs_Ropp.
  rewrite (Rabs_right (exp (- (PI * (y + INR k) ^ 2 * t)))) by (apply Rle_ge; left; apply exp_pos).
  rewrite Rabs_mult, (Rabs_right (2 * PI * t)) by (apply Rle_ge; nra).
  assert (Esplit : exp (- (PI * (y + INR k) ^ 2 * t))
                   = exp (- (PI * t / 2 * (y + INR k) ^ 2)) * exp (- (PI * t / 2 * (y + INR k) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Esplit.
  apply Rle_trans with
    (2 * PI * t * (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (/ 4 - y)) * wt ^ k))).
  - replace (2 * PI * t * Rabs (y + INR k)
             * (exp (- (PI * t / 2 * (y + INR k) ^ 2)) * exp (- (PI * t / 2 * (y + INR k) ^ 2))))
      with (2 * PI * t
            * ((Rabs (y + INR k) * exp (- (PI * t / 2 * (y + INR k) ^ 2)))
               * exp (- (PI * t / 2 * (y + INR k) ^ 2)))) by ring.
    apply Rmult_le_compat_l; [ nra | ].
    apply Rmult_le_compat.
    + apply Rmult_le_pos; [ apply Rabs_pos | left; apply exp_pos ].
    + left; apply exp_pos.
    + exact (abs_gauss_bound (PI * t / 2) (y + INR k) Hhp).
    + unfold wt; exact (exp_sq_geom_R (PI * t / 2) y k Hhp).
  - unfold KR.
    replace (2 * PI * t * (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (/ 4 - y)) * wt ^ k)))
      with ((2 * PI * t * / sqrt (PI * t / 2) * exp (PI * t / 2 * (/ 4 - y))) * wt ^ k) by ring.
    apply Rmult_le_compat_r; [ apply pow_le; apply wt_nonneg | ].
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos;
        [ nra | left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; exact Hhp ].
    + apply exp_le_compat; apply Rmult_le_compat_l; [ lra | ].
      apply Rabs_def2 in Hb; destruct Hb as [Hb1 Hb2]; lra.
Qed.

Lemma gLq_ball : forall x0 y k, Rabs (y - x0) < 1 -> Rabs (gLq y k) <= KL x0 * wt ^ k.
Proof.
  intros x0 y k Hb; pose proof PI_RGT_0 as HPI; pose proof half_pos as Hhp.
  unfold gLq, gL.
  rewrite Rabs_mult, Rabs_Ropp.
  rewrite (Rabs_right (exp (- (PI * (y - INR (S k)) ^ 2 * t)))) by (apply Rle_ge; left; apply exp_pos).
  rewrite Rabs_mult, (Rabs_right (2 * PI * t)) by (apply Rle_ge; nra).
  assert (Esplit : exp (- (PI * (y - INR (S k)) ^ 2 * t))
                   = exp (- (PI * t / 2 * (y - INR (S k)) ^ 2))
                     * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Esplit.
  apply Rle_trans with
    (2 * PI * t * (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (y - 3 / 4)) * wt ^ k))).
  - replace (2 * PI * t * Rabs (y - INR (S k))
             * (exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2))))
      with (2 * PI * t
            * ((Rabs (y - INR (S k)) * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))
               * exp (- (PI * t / 2 * (y - INR (S k)) ^ 2)))) by ring.
    apply Rmult_le_compat_l; [ nra | ].
    apply Rmult_le_compat.
    + apply Rmult_le_pos; [ apply Rabs_pos | left; apply exp_pos ].
    + left; apply exp_pos.
    + exact (abs_gauss_bound (PI * t / 2) (y - INR (S k)) Hhp).
    + unfold wt; exact (exp_sq_geom_L (PI * t / 2) y k Hhp).
  - unfold KL.
    replace (2 * PI * t * (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (y - 3 / 4)) * wt ^ k)))
      with ((2 * PI * t * / sqrt (PI * t / 2) * exp (PI * t / 2 * (y - 3 / 4))) * wt ^ k) by ring.
    apply Rmult_le_compat_r; [ apply pow_le; apply wt_nonneg | ].
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos;
        [ nra | left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; exact Hhp ].
    + apply exp_le_compat; apply Rmult_le_compat_l; [ lra | ].
      apply Rabs_def2 in Hb; destruct Hb as [Hb1 Hb2]; lra.
Qed.

Lemma gRq_self : forall x k, Rabs (gRq x k) <= KR x * wt ^ k.
Proof.
  intros x k; apply (gRq_ball x x k); replace (x - x) with 0 by ring; rewrite Rabs_R0; lra.
Qed.
Lemma gLq_self : forall x k, Rabs (gLq x k) <= KL x * wt ^ k.
Proof.
  intros x k; apply (gLq_ball x x k); replace (x - x) with 0 by ring; rewrite Rabs_R0; lra.
Qed.

(* --- pointwise limit derivative GTheta1 --- *)

Definition GTheta1R (x : R) : R :=
  proj1_sig (dom_series_cv (gRq x) (KR x) wt wt_nonneg wt_lt1 (KR_nonneg x) (gRq_self x)).
Definition GTheta1L (x : R) : R :=
  proj1_sig (dom_series_cv (gLq x) (KL x) wt wt_nonneg wt_lt1 (KL_nonneg x) (gLq_self x)).
Definition GTheta1 (x : R) : R := GTheta1R x + GTheta1L x.

Lemma GTheta1R_spec : forall x, Un_cv (sum_f_R0 (gRq x)) (GTheta1R x).
Proof. intro x; unfold GTheta1R; apply proj2_sig. Qed.
Lemma GTheta1L_spec : forall x, Un_cv (sum_f_R0 (gLq x)) (GTheta1L x).
Proof. intro x; unfold GTheta1L; apply proj2_sig. Qed.

Lemma GTheta1_spec : forall x, Un_cv (fun N => gTheta_deriv_partial x N) (GTheta1 x).
Proof.
  intro x; unfold gTheta_deriv_partial, GTheta1;
    apply CV_plus; [ apply GTheta1R_spec | apply GTheta1L_spec ].
Qed.

(* --- the uniform (CVU) convergence of the derivative partials --- *)

Lemma Hr1 : 0 < 1.
Proof. lra. Qed.

Lemma gTheta_deriv_cvu : forall x0,
  CVU (fun N s => gTheta_deriv_partial s N) GTheta1 x0 (mkposreal 1 Hr1).
Proof.
  intros x0 eps He.
  set (K := KR x0 + KL x0).
  assert (HK : 0 < K) by (unfold K; pose proof (KR_pos x0); pose proof (KL_pos x0); lra).
  assert (Hw1w : 0 < 1 - wt) by (pose proof wt_lt1; lra).
  assert (He' : 0 < eps * (1 - wt) / K)
    by (apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; [ exact He | exact Hw1w ]
                                 | apply Rinv_0_lt_compat; exact HK ]).
  destruct (pow_lt_1_zero wt wt_abs_lt1 (eps * (1 - wt) / K) He') as [N HN].
  exists N; intros n y Hn Hby.
  unfold Boule in Hby; simpl in Hby.
  apply Rle_lt_trans with (KR x0 * wt ^ (S n) / (1 - wt) + KL x0 * wt ^ (S n) / (1 - wt)).
  - unfold GTheta1, gTheta_deriv_partial.
    replace (GTheta1R y + GTheta1L y - (sum_f_R0 (gRq y) n + sum_f_R0 (gLq y) n))
      with ((GTheta1R y - sum_f_R0 (gRq y) n) + (GTheta1L y - sum_f_R0 (gLq y) n)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    + apply (geom_tail_est (gRq y) (GTheta1R y) (KR x0) wt wt_nonneg wt_lt1 (KR_nonneg x0)
               (GTheta1R_spec y) (fun k => gRq_ball x0 y k Hby) n).
    + apply (geom_tail_est (gLq y) (GTheta1L y) (KL x0) wt wt_nonneg wt_lt1 (KL_nonneg x0)
               (GTheta1L_spec y) (fun k => gLq_ball x0 y k Hby) n).
  - replace (KR x0 * wt ^ (S n) / (1 - wt) + KL x0 * wt ^ (S n) / (1 - wt))
      with (K * wt ^ (S n) / (1 - wt)) by (unfold K; field; lra).
    apply Rmult_lt_reg_r with (1 - wt); [ exact Hw1w | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_r.
    specialize (HN (S n) ltac:(lia)).
    rewrite Rabs_right in HN by (apply Rle_ge; apply pow_le; apply wt_nonneg).
    apply Rlt_le_trans with (K * (eps * (1 - wt) / K)).
    + apply Rmult_lt_compat_l; [ exact HK | exact HN ].
    + apply Req_le; field; apply Rgt_not_eq; exact HK.
Qed.

(* --- Θ_t is C¹ --- *)

Theorem GTheta_C1 : forall x, derivable_pt_lim (GTheta t Ht) x (GTheta1 x).
Proof.
  intro x.
  assert (Hcvu : CVU (fun N s => gTheta_deriv_partial s N) GTheta1 x (mkposreal 1 Hr1))
    by apply gTheta_deriv_cvu.
  apply (derivable_pt_lim_CVU (fun N s => gTheta_partial t s N)
           (fun N s => gTheta_deriv_partial s N) (GTheta t Ht) GTheta1 x x (mkposreal 1 Hr1)).
  - unfold Boule; simpl; replace (x - x) with 0 by ring; rewrite Rabs_R0; exact Hr1.
  - intros y n _; apply gTheta_partial_derives.
  - intros y _; apply (GTheta_spec t Ht y).
  - exact Hcvu.
  - apply (CVU_continuity (fun N s => gTheta_deriv_partial s N) GTheta1 x (mkposreal 1 Hr1) Hcvu).
    intros n y _; apply cont_gTheta_deriv_partial.
Qed.

Corollary GTheta_cont : continuity (GTheta t Ht).
Proof. intro x; apply derivable_continuous_pt; exists (GTheta1 x); apply GTheta_C1. Qed.

End Deriv.

Print Assumptions GTheta_C1.

(* ================================================================= *)
(*  END GaussPeriodDeriv.v                                           *)
(*  Θ_t is C¹ in x (GTheta_C1) with the termwise derivative GTheta1;   *)
(*  in particular Θ_t is continuous (GTheta_cont).  Next: the second   *)
(*  derivative (C²), needed for the removable-singularity localiser.   *)
(* ================================================================= *)
