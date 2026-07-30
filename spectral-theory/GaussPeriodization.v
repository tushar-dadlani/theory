(* ================================================================= *)
(*  GaussPeriodization.v  —  the LEFT side of continuous Poisson       *)
(*  summation for the Gaussian: the periodized theta kernel.          *)
(*                                                                    *)
(*  Toward the Jacobi θ modular transformation θ(1/t) = √t·θ(t) (the   *)
(*  analytic engine of the ζ functional equation), the Poisson route   *)
(*  periodizes the Gaussian g_t(y) = e^{−πy²t}:                        *)
(*                                                                    *)
(*     Θ_t(x) := Σ_{n∈ℤ} e^{−π(x+n)²t}                                *)
(*             = Σ_{n≥0} e^{−π(x+n)²t} + Σ_{n≥1} e^{−π(x−n)²t}.        *)
(*                                                                    *)
(*  This file builds that LEFT-side lattice sum axiom-free (the θ      *)
(*  analogue of PoissonLHS's Σ 1/(1+n²)).  For x ∈ [0,1] BOTH one-     *)
(*  sided halves are dominated termwise by the geometric (e^{−πt})ⁿ,   *)
(*  since (x+n)² ≥ n and (x−(n+1))² ≥ n there, so each converges by    *)
(*  comparison with JacobiTheta's kernel (gauss_period_converges);     *)
(*  and at the lattice x = 0 the periodization IS θ:                   *)
(*     gauss_period_at_0 : Un_cv (Θ_t partial at 0) (theta t).         *)
(*                                                                    *)
(*  HONEST BOUNDARY.  This is the LHS (lattice sum) only.  The         *)
(*  transformation needs the RIGHT side — the Fourier side — which     *)
(*  rests on the Gaussian self-duality ∫ e^{−πy²t}e^{−2πiky}dy =       *)
(*  t^{−1/2} e^{−πk²/t}, i.e. the improper Gaussian integral (the      *)
(*  wall PoissonLHS also flagged).  Built directly on JacobiTheta.     *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import JacobiTheta.
Open Scope R_scope.

Lemma sqr_ge_self : forall n, INR n <= INR n * INR n.
Proof.
  intro n; destruct n as [| k];
    [ replace (INR 0) with 0 by reflexivity; lra
    | rewrite S_INR; pose proof (pos_INR k); nra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The two one-sided lattice kernels and their partial sums.        *)
(* ----------------------------------------------------------------- *)

Definition gR (t x : R) (n : nat) : R := exp (- (PI * (x + INR n) ^ 2 * t)).
Definition gL (t x : R) (n : nat) : R := exp (- (PI * (x - INR (S n)) ^ 2 * t)).
Definition gRp (t x : R) (N : nat) : R := sum_f_R0 (gR t x) N.
Definition gLp (t x : R) (N : nat) : R := sum_f_R0 (gL t x) N.
Definition gTheta_partial (t x : R) (N : nat) : R := gRp t x N + gLp t x N.

(* ----------------------------------------------------------------- *)
(*  Termwise geometric domination on x ∈ [0,1].                      *)
(* ----------------------------------------------------------------- *)

Lemma gR_le : forall t x n, 0 < t -> 0 <= x -> gR t x n <= exp (- (PI * t)) ^ n.
Proof.
  intros t x n Ht Hx0; unfold gR.
  apply Rle_trans with (exp (- (PI * INR n * t))).
  - apply exp_le_compat, Ropp_le_contravar.
    apply Rmult_le_compat_r; [ left; exact Ht | ].
    apply Rmult_le_compat_l; [ left; exact PI_RGT_0 | ].
    pose proof (pos_INR n); pose proof (sqr_ge_self n); nra.
  - rewrite (exp_INR_pow (- (PI * t)) n); apply Req_le; f_equal; ring.
Qed.

Lemma gL_le : forall t x n, 0 < t -> 0 <= x -> x <= 1 -> gL t x n <= exp (- (PI * t)) ^ n.
Proof.
  intros t x n Ht Hx0 Hx1; unfold gL.
  apply Rle_trans with (exp (- (PI * INR n * t))).
  - apply exp_le_compat, Ropp_le_contravar.
    apply Rmult_le_compat_r; [ left; exact Ht | ].
    apply Rmult_le_compat_l; [ left; exact PI_RGT_0 | ].
    rewrite S_INR; pose proof (pos_INR n); pose proof (sqr_ge_self n); nra.
  - rewrite (exp_INR_pow (- (PI * t)) n); apply Req_le; f_equal; ring.
Qed.

Lemma gRp_bound : forall t x N, 0 < t -> 0 <= x -> gRp t x N <= / (1 - exp (- (PI * t))).
Proof.
  intros t x N Ht Hx0; unfold gRp.
  apply Rle_trans with (sum_f_R0 (fun n => exp (- (PI * t)) ^ n) N).
  - apply sum_f_R0_le; intro; apply gR_le; assumption.
  - apply geom_partial_bound; [ left; apply exp_pos | apply theta_ratio_lt1; exact Ht ].
Qed.

Lemma gLp_bound : forall t x N, 0 < t -> 0 <= x -> x <= 1 -> gLp t x N <= / (1 - exp (- (PI * t))).
Proof.
  intros t x N Ht Hx0 Hx1; unfold gLp.
  apply Rle_trans with (sum_f_R0 (fun n => exp (- (PI * t)) ^ n) N).
  - apply sum_f_R0_le; intro; apply gL_le; assumption.
  - apply geom_partial_bound; [ left; apply exp_pos | apply theta_ratio_lt1; exact Ht ].
Qed.

Lemma gRp_growing : forall t x, Un_growing (gRp t x).
Proof.
  intros t x N; unfold gRp; cbn [sum_f_R0].
  assert (0 < gR t x (S N)) by (unfold gR; apply exp_pos); lra.
Qed.

Lemma gLp_growing : forall t x, Un_growing (gLp t x).
Proof.
  intros t x N; unfold gLp; cbn [sum_f_R0].
  assert (0 < gL t x (S N)) by (unfold gL; apply exp_pos); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The periodized Gaussian converges on x ∈ [0,1].                  *)
(* ----------------------------------------------------------------- *)

Theorem gauss_period_converges : forall t x,
  0 < t -> 0 <= x -> x <= 1 -> { L : R | Un_cv (gTheta_partial t x) L }.
Proof.
  intros t x Ht Hx0 Hx1.
  assert (HR : { L : R | Un_cv (gRp t x) L }).
  { apply growing_cv; [ apply gRp_growing | ].
    unfold has_ub, EUn, bound, is_upper_bound.
    exists (/ (1 - exp (- (PI * t)))); intros r [n ->]; apply gRp_bound; assumption. }
  assert (HL : { L : R | Un_cv (gLp t x) L }).
  { apply growing_cv; [ apply gLp_growing | ].
    unfold has_ub, EUn, bound, is_upper_bound.
    exists (/ (1 - exp (- (PI * t)))); intros r [n ->]; apply gLp_bound; assumption. }
  destruct HR as [LR HR']; destruct HL as [LL HL'].
  exists (LR + LL); apply (CV_plus (gRp t x) (gLp t x) LR LL HR' HL').
Qed.

Definition gauss_theta (t x : R) (Ht : 0 < t) (Hx0 : 0 <= x) (Hx1 : x <= 1) : R :=
  proj1_sig (gauss_period_converges t x Ht Hx0 Hx1).

(* ----------------------------------------------------------------- *)
(*  At the lattice x = 0 the periodization is θ.                      *)
(* ----------------------------------------------------------------- *)

Lemma gL0 : forall t n, gL t 0 n = theta_term t n.
Proof. intros t n; unfold gL, theta_term; f_equal; ring. Qed.

Lemma gR0_0 : forall t, gR t 0 0 = 1.
Proof.
  intro t; unfold gR.
  replace (- (PI * (0 + INR 0) ^ 2 * t)) with 0
    by (replace (INR 0) with 0 by reflexivity; ring).
  apply exp_0.
Qed.

Lemma gR0_S : forall t n, gR t 0 (S n) = theta_term t n.
Proof. intros t n; unfold gR, theta_term; f_equal; ring. Qed.

Lemma gLp0 : forall t N, gLp t 0 N = theta_partial t N.
Proof. intros t N; unfold gLp, theta_partial; apply sum_eq; intros i _; apply gL0. Qed.

Lemma gRp0_S : forall t N, gRp t 0 (S N) = 1 + theta_partial t N.
Proof.
  intros t N; unfold gRp.
  rewrite (decomp_sum (gR t 0) (S N) (Nat.lt_0_succ N)); simpl (pred (S N)).
  rewrite gR0_0; f_equal.
  unfold theta_partial; apply sum_eq; intros i _; apply gR0_S.
Qed.

Lemma gLp0_cv : forall t (Ht : 0 < t),
  Un_cv (gLp t 0) (proj1_sig (theta_half_converges t Ht)).
Proof.
  intros t Ht; destruct (theta_half_converges t Ht) as [L HL]; simpl.
  intros eps He; destruct (HL eps He) as [N0 H0]; exists N0; intros n Hn.
  rewrite gLp0; apply H0; exact Hn.
Qed.

Lemma gRp0_cv : forall t (Ht : 0 < t),
  Un_cv (gRp t 0) (1 + proj1_sig (theta_half_converges t Ht)).
Proof.
  intros t Ht; destruct (theta_half_converges t Ht) as [L HL]; simpl.
  intros eps He; destruct (HL eps He) as [N0 H0]; exists (S N0); intros n Hn.
  destruct n as [| m]; [ lia | ].
  rewrite gRp0_S; unfold R_dist.
  replace (1 + theta_partial t m - (1 + L)) with (theta_partial t m - L) by ring.
  apply H0; lia.
Qed.

Theorem gauss_period_at_0 : forall t (Ht : 0 < t),
  Un_cv (gTheta_partial t 0) (theta t Ht).
Proof.
  intros t Ht.
  assert (Hsum : Un_cv (fun N => gRp t 0 N + gLp t 0 N)
                   ((1 + proj1_sig (theta_half_converges t Ht))
                    + proj1_sig (theta_half_converges t Ht)))
    by (apply CV_plus; [ apply gRp0_cv | apply gLp0_cv ]).
  unfold gTheta_partial.
  replace (theta t Ht) with ((1 + proj1_sig (theta_half_converges t Ht))
                             + proj1_sig (theta_half_converges t Ht))
    by (unfold theta; ring).
  exact Hsum.
Qed.

Print Assumptions gauss_period_converges.
Print Assumptions gauss_period_at_0.

(* ================================================================= *)
(*  END GaussPeriodization.v                                         *)
(*  The periodized Gaussian Θ_t(x) is a well-defined real on x∈[0,1]  *)
(*  (gauss_theta), converging to θ(t) at the lattice.  This is the    *)
(*  Poisson LHS for the Gaussian; the Fourier (RHS) side, resting on  *)
(*  the improper Gaussian integral, is the next wall.                *)
(* ================================================================= *)
