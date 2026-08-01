(* ================================================================= *)
(*  GaussPeriodTotal.v  —  Poisson→θ line, P3 step 1: the periodized   *)
(*  Gaussian Θ_t as a TOTAL function on ℝ.                            *)
(*                                                                    *)
(*  GaussPeriodization builds Θ_t only on x∈[0,1] (gauss_theta carries *)
(*  the interval proof arguments).  P3 needs Θ_t as a genuine          *)
(*  function ℝ→ℝ (globally continuous, feeding the Fourier tower).     *)
(*  The key is convergence of gTheta_partial for EVERY real x, which   *)
(*  the [0,1]-specific domination (gR_le/gL_le) does not give.         *)
(*                                                                    *)
(*  A single perfect-square bound closes it for all x at once:         *)
(*     gR t x n = e^{−π(x+n)²t} ≤ e^{πt(¼−x)}·(e^{−πt})ⁿ,             *)
(*     gL t x n = e^{−π(x−n−1)²t} ≤ e^{πt(x−¾)}·(e^{−πt})ⁿ,          *)
(*  each equivalent to (x+n−½)² ≥ 0.  Every one-sided partial is then  *)
(*  geometrically dominated, so both halves converge (positive terms → *)
(*  growing_cv), and GTheta t Ht x := their sum.  Periodicity is       *)
(*  transported for all x by the boundary-term shift (gTheta_shift).   *)
(*                                                                    *)
(*  Built on GaussPeriodization, GaussPeriodicity.  No new axioms.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import JacobiTheta GaussPeriodization GaussPeriodicity.
Open Scope R_scope.

Section Total.

Variable t : R.
Hypothesis Ht : 0 < t.

(* the geometric ratio q = e^{−πt} ∈ (0,1) *)
Lemma q_pos : 0 < exp (- (PI * t)).
Proof. apply exp_pos. Qed.

Lemma q_abs_lt1 : Rabs (exp (- (PI * t))) < 1.
Proof.
  rewrite Rabs_right by (apply Rle_ge; left; apply q_pos).
  apply theta_ratio_lt1; exact Ht.
Qed.

(* ----------------------------------------------------------------- *)
(*  The perfect-square geometric domination, valid for ALL x.        *)
(* ----------------------------------------------------------------- *)

Lemma gR_geom : forall x n,
  gR t x n <= exp (PI * t * (/ 4 - x)) * exp (- (PI * t)) ^ n.
Proof.
  intros x n; unfold gR; rewrite exp_INR_pow, <- exp_plus; apply exp_le_compat.
  replace ((x + INR n) ^ 2) with ((x + INR n) * (x + INR n)) by ring.
  pose proof PI_RGT_0.
  assert (Hpt : 0 <= PI * t) by nra.
  assert (Hsq : 0 <= (x + INR n - / 2) * (x + INR n - / 2))
    by (pose proof (Rle_0_sqr (x + INR n - / 2)); unfold Rsqr in *; lra).
  assert (Hkey : 0 <= PI * t * ((x + INR n - / 2) * (x + INR n - / 2)))
    by (apply Rmult_le_pos; assumption).
  nra.
Qed.

Lemma gL_geom : forall x n,
  gL t x n <= exp (PI * t * (x - 3 / 4)) * exp (- (PI * t)) ^ n.
Proof.
  intros x n; unfold gL; rewrite exp_INR_pow, <- exp_plus; apply exp_le_compat.
  rewrite S_INR.
  replace ((x - (INR n + 1)) ^ 2) with ((x - (INR n + 1)) * (x - (INR n + 1))) by ring.
  pose proof PI_RGT_0.
  assert (Hpt : 0 <= PI * t) by nra.
  assert (Hsq : 0 <= (x - INR n - / 2) * (x - INR n - / 2))
    by (pose proof (Rle_0_sqr (x - INR n - / 2)); unfold Rsqr in *; lra).
  assert (Hkey : 0 <= PI * t * ((x - INR n - / 2) * (x - INR n - / 2)))
    by (apply Rmult_le_pos; assumption).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  One-sided partials are bounded above (for every x).              *)
(* ----------------------------------------------------------------- *)

Lemma gRp_bound_all : forall x N,
  gRp t x N <= exp (PI * t * (/ 4 - x)) * / (1 - exp (- (PI * t))).
Proof.
  intros x N; unfold gRp.
  apply Rle_trans with
    (sum_f_R0 (fun n => exp (PI * t * (/ 4 - x)) * exp (- (PI * t)) ^ n) N).
  - apply sum_f_R0_le; intro i; apply gR_geom.
  - rewrite sum_f_R0_scal.
    apply Rmult_le_compat_l; [ left; apply exp_pos | ].
    apply geom_partial_bound; [ left; apply exp_pos | apply theta_ratio_lt1; exact Ht ].
Qed.

Lemma gLp_bound_all : forall x N,
  gLp t x N <= exp (PI * t * (x - 3 / 4)) * / (1 - exp (- (PI * t))).
Proof.
  intros x N; unfold gLp.
  apply Rle_trans with
    (sum_f_R0 (fun n => exp (PI * t * (x - 3 / 4)) * exp (- (PI * t)) ^ n) N).
  - apply sum_f_R0_le; intro i; apply gL_geom.
  - rewrite sum_f_R0_scal.
    apply Rmult_le_compat_l; [ left; apply exp_pos | ].
    apply geom_partial_bound; [ left; apply exp_pos | apply theta_ratio_lt1; exact Ht ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Convergence for EVERY real x, and the total function GTheta.     *)
(* ----------------------------------------------------------------- *)

Theorem gauss_conv_all : forall x, { L : R | Un_cv (gTheta_partial t x) L }.
Proof.
  intro x.
  assert (HR : { L : R | Un_cv (gRp t x) L }).
  { apply growing_cv; [ apply gRp_growing | ].
    unfold has_ub, EUn, bound, is_upper_bound.
    exists (exp (PI * t * (/ 4 - x)) * / (1 - exp (- (PI * t)))).
    intros r [n ->]; apply gRp_bound_all. }
  assert (HL : { L : R | Un_cv (gLp t x) L }).
  { apply growing_cv; [ apply gLp_growing | ].
    unfold has_ub, EUn, bound, is_upper_bound.
    exists (exp (PI * t * (x - 3 / 4)) * / (1 - exp (- (PI * t)))).
    intros r [n ->]; apply gLp_bound_all. }
  destruct HR as [LR HR']; destruct HL as [LL HL'].
  exists (LR + LL); apply (CV_plus (gRp t x) (gLp t x) LR LL HR' HL').
Qed.

Definition GTheta (x : R) : R := proj1_sig (gauss_conv_all x).

Lemma GTheta_spec : forall x, Un_cv (gTheta_partial t x) (GTheta x).
Proof. intro x; unfold GTheta; exact (proj2_sig (gauss_conv_all x)). Qed.

(* ----------------------------------------------------------------- *)
(*  Value at the lattice: GTheta 0 = θ(t).                            *)
(* ----------------------------------------------------------------- *)

Lemma GTheta_at_0 : GTheta 0 = theta t Ht.
Proof.
  apply (UL_sequence (gTheta_partial t 0));
    [ apply GTheta_spec | apply gauss_period_at_0 ].
Qed.

(* ----------------------------------------------------------------- *)
(*  1-periodicity for ALL x (general boundary-term shift).           *)
(* ----------------------------------------------------------------- *)

Lemma gR_edge_cv0 : forall x, Un_cv (fun N => gR t x (S N)) 0.
Proof.
  intros x eps Heps.
  set (C := exp (PI * t * (/ 4 - x))).
  assert (HC : 0 < C) by apply exp_pos.
  destruct (pow_lt_1_zero (exp (- (PI * t))) q_abs_lt1 (eps / C)
              (Rdiv_lt_0_compat eps C Heps HC)) as [N0 HN0].
  exists N0; intros n Hn; unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; unfold gR; apply exp_pos).
  apply Rle_lt_trans with (C * exp (- (PI * t)) ^ (S n)); [ apply gR_geom | ].
  specialize (HN0 (S n) ltac:(lia)).
  rewrite Rabs_right in HN0 by (apply Rle_ge; left; apply pow_lt; apply q_pos).
  assert (Eeps : eps = C * (eps / C)) by (field; apply Rgt_not_eq; exact HC).
  rewrite Eeps; apply Rmult_lt_compat_l; [ exact HC | exact HN0 ].
Qed.

Lemma gL_edge_cv0 : forall x, Un_cv (fun N => gL t x N) 0.
Proof.
  intros x eps Heps.
  set (C := exp (PI * t * (x - 3 / 4))).
  assert (HC : 0 < C) by apply exp_pos.
  destruct (pow_lt_1_zero (exp (- (PI * t))) q_abs_lt1 (eps / C)
              (Rdiv_lt_0_compat eps C Heps HC)) as [N0 HN0].
  exists N0; intros n Hn; unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; unfold gL; apply exp_pos).
  apply Rle_lt_trans with (C * exp (- (PI * t)) ^ n); [ apply gL_geom | ].
  specialize (HN0 n Hn).
  rewrite Rabs_right in HN0 by (apply Rle_ge; left; apply pow_lt; apply q_pos).
  assert (Eeps : eps = C * (eps / C)) by (field; apply Rgt_not_eq; exact HC).
  rewrite Eeps; apply Rmult_lt_compat_l; [ exact HC | exact HN0 ].
Qed.

Lemma gTheta_shift_cv : forall x L,
  Un_cv (gTheta_partial t x) L -> Un_cv (gTheta_partial t (x + 1)) L.
Proof.
  intros x L HL.
  assert (H1 : Un_cv (fun N => gTheta_partial t x N + gR t x (S N)) (L + 0))
    by (apply CV_plus; [ exact HL | apply gR_edge_cv0 ]).
  assert (H2 : Un_cv (fun N => (gTheta_partial t x N + gR t x (S N)) - gL t x N)
                     ((L + 0) - 0))
    by (apply CV_minus; [ exact H1 | apply gL_edge_cv0 ]).
  replace ((L + 0) - 0) with L in H2 by ring.
  intros eps He; destruct (H2 eps He) as [N0 H0]; exists N0; intros n Hn.
  rewrite gTheta_shift; apply H0; exact Hn.
Qed.

Lemma GTheta_periodic : forall x, GTheta (x + 1) = GTheta x.
Proof.
  intro x; apply (UL_sequence (gTheta_partial t (x + 1)));
    [ apply GTheta_spec | apply gTheta_shift_cv; apply GTheta_spec ].
Qed.

Lemma GTheta_periodic_rev : forall x, GTheta (x - 1) = GTheta x.
Proof.
  intro x; pose proof (GTheta_periodic (x - 1)) as H.
  replace (x - 1 + 1) with x in H by ring; symmetry; exact H.
Qed.

End Total.

Print Assumptions GTheta_at_0.
Print Assumptions GTheta_periodic.

(* ================================================================= *)
(*  END GaussPeriodTotal.v                                           *)
(*  Θ_t is now a total function GTheta t Ht : ℝ→ℝ (GTheta_spec), with  *)
(*  GTheta 0 = θ(t) and 1-periodicity for all x.  Regularity in x     *)
(*  (C¹, C²) is the next step, via the derivable_pt_lim_CVU engine.   *)
(* ================================================================= *)
