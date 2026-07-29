(* ================================================================= *)
(*  JacobiTheta.v  —  the Jacobi theta function θ(t) = Σ e^{-πn²t}     *)
(*  CONVERGES for t > 0.                                              *)
(*                                                                    *)
(*  θ(t) = Σ_{n∈ℤ} e^{-πn²t} = 1 + 2·Σ_{n≥1} e^{-πn²t}  (t>0).         *)
(*  The half-sum Σ_{n≥1} e^{-πn²t} converges by monotone-bounded      *)
(*  convergence: its partial sums increase and are dominated,         *)
(*  termwise, by the geometric series Σ q^n with q = e^{-πt} ∈ (0,1),  *)
(*  since  e^{-πn²t} ≤ e^{-πnt} = q^n.  So                            *)
(*      theta_half_converges : { L | Un_cv (theta_partial t) L },     *)
(*      theta t := 1 + 2·L,  with  theta t > 1  (theta_gt_1).         *)
(*                                                                    *)
(*  θ is THE object of the ζ functional equation.  This file builds   *)
(*  θ and its convergence only; the modular transformation            *)
(*  θ(1/t) = √t · θ(t) (continuous Poisson summation) — the hard      *)
(*  engine of the functional equation — is NOT here.                 *)
(*                                                                    *)
(*  Over the standard classical Reals (`exp`, `PI`); standalone.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Open Scope R_scope.

(* n-th term e^{-π(n+1)²t}, so theta_partial sums e^{-πm²t} for m=1..N+1 *)
Definition theta_term (t : R) (n : nat) : R := exp (- (PI * INR (S n) ^ 2 * t)).
Definition theta_partial (t : R) (N : nat) : R := sum_f_R0 (theta_term t) N.

(* ----------------------------------------------------------------- *)
(*  Elementary toolkit (stdlib only).                                *)
(* ----------------------------------------------------------------- *)

Lemma exp_le_compat : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H; destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma exp_INR_pow : forall x k, (exp x) ^ k = exp (INR k * x).
Proof.
  intros x k; induction k as [| k IH].
  - simpl; rewrite Rmult_0_l, exp_0; reflexivity.
  - cbn [pow]; rewrite IH, <- exp_plus, S_INR; f_equal; ring.
Qed.

Lemma sum_f_R0_le : forall (A B : nat -> R) N,
  (forall i, A i <= B i) -> sum_f_R0 A N <= sum_f_R0 B N.
Proof.
  intros A B N H; induction N; cbn [sum_f_R0]; [ apply H | pose proof (H (S N)); lra ].
Qed.

(* geometric partial sums are bounded by 1/(1-x), for 0 ≤ x < 1 *)
Lemma geom_partial_bound : forall x N, 0 <= x -> x < 1 ->
  sum_f_R0 (fun k => x ^ k) N <= / (1 - x).
Proof.
  intros x N Hx0 Hx1.
  pose proof (GP_finite x N) as G.
  assert (Hxn : 0 <= x ^ (N + 1)) by (apply pow_le; exact Hx0).
  assert (H1x : 0 < 1 - x) by lra.
  apply Rmult_le_reg_r with (1 - x); [ exact H1x | ].
  replace (/ (1 - x) * (1 - x)) with 1 by (field; lra).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Convergence of the half-theta series (t > 0).                    *)
(* ----------------------------------------------------------------- *)

Section Theta.

Variable t : R.
Hypothesis Ht : 0 < t.

Lemma theta_ratio_lt1 : exp (- (PI * t)) < 1.
Proof. rewrite <- exp_0; apply exp_increasing; pose proof PI_RGT_0; nra. Qed.

(* the quadratic term is dominated by the geometric term q^n *)
Lemma theta_term_le : forall n, theta_term t n <= exp (- (PI * t)) ^ n.
Proof.
  intro n; unfold theta_term.
  assert (H1 : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  apply Rle_trans with (exp (- (PI * INR (S n) * t))).
  - apply exp_le_compat.
    assert (H2 : INR (S n) <= INR (S n) ^ 2) by nra.
    pose proof PI_RGT_0.
    apply Ropp_le_contravar.
    apply Rmult_le_compat_r; [ lra | ].
    apply Rmult_le_compat_l; [ lra | exact H2 ].
  - replace (- (PI * INR (S n) * t)) with (INR (S n) * (- (PI * t))) by ring.
    rewrite <- exp_INR_pow; cbn [pow].
    rewrite <- (Rmult_1_l (exp (- (PI * t)) ^ n)) at 2.
    apply Rmult_le_compat_r;
      [ apply pow_le; left; apply exp_pos | apply Rlt_le, theta_ratio_lt1 ].
Qed.

Lemma theta_partial_bound : forall N, theta_partial t N <= / (1 - exp (- (PI * t))).
Proof.
  intro N; unfold theta_partial.
  apply Rle_trans with (sum_f_R0 (fun k => exp (- (PI * t)) ^ k) N).
  - apply sum_f_R0_le; intro i; apply theta_term_le.
  - apply geom_partial_bound; [ left; apply exp_pos | apply theta_ratio_lt1 ].
Qed.

Lemma theta_partial_growing : Un_growing (theta_partial t).
Proof.
  intro N; unfold theta_partial; cbn [sum_f_R0]; unfold theta_term.
  pose proof (exp_pos (- (PI * INR (S (S N)) ^ 2 * t))); lra.
Qed.

Theorem theta_half_converges : { L : R | Un_cv (theta_partial t) L }.
Proof.
  apply growing_cv; [ apply theta_partial_growing | ].
  unfold has_ub, EUn, bound, is_upper_bound.
  exists (/ (1 - exp (- (PI * t)))); intros r [n ->]; apply theta_partial_bound.
Qed.

End Theta.

(* the full Jacobi theta function θ(t) = 1 + 2·Σ_{n≥1} e^{-πn²t} *)
Definition theta (t : R) (Ht : 0 < t) : R :=
  1 + 2 * proj1_sig (theta_half_converges t Ht).

(* θ(t) > 1 for every t > 0 *)
Theorem theta_gt_1 : forall t (Ht : 0 < t), 1 < theta t Ht.
Proof.
  intros t Ht; unfold theta; destruct (theta_half_converges t Ht) as [L HL]; simpl.
  assert (Hle : theta_partial t 0 <= L)
    by (apply (growing_ineq (theta_partial t)); [ apply theta_partial_growing | exact HL ]).
  assert (0 < theta_partial t 0)
    by (unfold theta_partial; simpl; apply exp_pos).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The shape of θ: monotone decreasing, with a tight upper bound.   *)
(* ----------------------------------------------------------------- *)

Lemma sum_f_R0_scal : forall c f N, sum_f_R0 (fun n => c * f n) N = c * sum_f_R0 f N.
Proof. intros c f N; induction N; cbn [sum_f_R0]; [ ring | rewrite IHN; ring ]. Qed.

Lemma Un_cv_le : forall U V u v,
  (forall n, U n <= V n) -> Un_cv U u -> Un_cv V v -> u <= v.
Proof.
  intros U V u v Hle HU HV; destruct (Rle_or_lt u v) as [Hok | Hlt]; [ exact Hok | exfalso ].
  destruct (HU ((u - v) / 2) ltac:(lra)) as [N1 H1].
  destruct (HV ((u - v) / 2) ltac:(lra)) as [N2 H2].
  specialize (H1 (max N1 N2) (Nat.le_max_l _ _)); specialize (H2 (max N1 N2) (Nat.le_max_r _ _)).
  specialize (Hle (max N1 N2)); unfold R_dist in *;
    apply Rabs_def2 in H1; apply Rabs_def2 in H2; lra.
Qed.

Lemma Un_cv_le_const : forall U l B, (forall n, U n <= B) -> Un_cv U l -> l <= B.
Proof.
  intros U l B Hb HU; apply (Un_cv_le U (fun _ => B) l B); [ exact Hb | exact HU | ].
  intros eps He; exists 0%nat; intros n _; unfold R_dist;
    rewrite Rminus_diag_eq by reflexivity; rewrite Rabs_R0; exact He.
Qed.

(* each term, hence θ, is decreasing in t *)
Lemma theta_term_antitone : forall t1 t2 n, t1 <= t2 -> theta_term t2 n <= theta_term t1 n.
Proof.
  intros t1 t2 n Hle; unfold theta_term; apply exp_le_compat, Ropp_le_contravar.
  apply Rmult_le_compat_l;
    [ apply Rmult_le_pos; [ pose proof PI_RGT_0; lra | apply pow_le; apply pos_INR ] | exact Hle ].
Qed.

Lemma theta_partial_antitone : forall t1 t2 N, t1 <= t2 -> theta_partial t2 N <= theta_partial t1 N.
Proof.
  intros t1 t2 N Hle; unfold theta_partial; apply sum_f_R0_le; intro i;
    apply theta_term_antitone; exact Hle.
Qed.

Theorem theta_antitone : forall t1 t2 (H1 : 0 < t1) (H2 : 0 < t2),
  t1 <= t2 -> theta t2 H2 <= theta t1 H1.
Proof.
  intros t1 t2 H1 H2 Hle; unfold theta.
  destruct (theta_half_converges t1 H1) as [L1 HL1].
  destruct (theta_half_converges t2 H2) as [L2 HL2]; simpl.
  assert (L2 <= L1)
    by (apply (Un_cv_le (theta_partial t2) (theta_partial t1));
        [ intro N; apply theta_partial_antitone; exact Hle | exact HL2 | exact HL1 ]).
  lra.
Qed.

(* the tighter termwise bound  e^{-πn²t} ≤ q^{n+1},  q = e^{-πt} *)
Lemma theta_term_le' : forall t n, 0 < t -> theta_term t n <= exp (- (PI * t)) ^ (S n).
Proof.
  intros t n Ht; unfold theta_term.
  assert (H1 : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  apply Rle_trans with (exp (- (PI * INR (S n) * t))).
  - apply exp_le_compat.
    assert (H2 : INR (S n) <= INR (S n) ^ 2) by nra.
    pose proof PI_RGT_0.
    apply Ropp_le_contravar.
    apply Rmult_le_compat_r; [ lra | ].
    apply Rmult_le_compat_l; [ lra | exact H2 ].
  - replace (- (PI * INR (S n) * t)) with (INR (S n) * (- (PI * t))) by ring.
    rewrite <- exp_INR_pow; apply Rle_refl.
Qed.

Lemma theta_partial_upper : forall t N, 0 < t ->
  theta_partial t N <= exp (- (PI * t)) / (1 - exp (- (PI * t))).
Proof.
  intros t N Ht; unfold theta_partial.
  apply Rle_trans with (sum_f_R0 (fun n => exp (- (PI * t)) * exp (- (PI * t)) ^ n) N).
  - apply sum_f_R0_le; intro i.
    change (exp (- (PI * t)) * exp (- (PI * t)) ^ i) with (exp (- (PI * t)) ^ (S i)).
    apply theta_term_le'; exact Ht.
  - rewrite sum_f_R0_scal.
    apply Rle_trans with (exp (- (PI * t)) * / (1 - exp (- (PI * t)))).
    + apply Rmult_le_compat_l;
        [ left; apply exp_pos
        | apply geom_partial_bound; [ left; apply exp_pos | apply theta_ratio_lt1; exact Ht ] ].
    + unfold Rdiv; apply Rle_refl.
Qed.

(* θ(t) ≤ 1 + 2·q/(1−q):  θ(t) → 1 as t → ∞ (q = e^{-πt} → 0) *)
Theorem theta_upper : forall t (Ht : 0 < t),
  theta t Ht <= 1 + 2 * (exp (- (PI * t)) / (1 - exp (- (PI * t)))).
Proof.
  intros t Ht; unfold theta; destruct (theta_half_converges t Ht) as [L HL]; simpl.
  assert (L <= exp (- (PI * t)) / (1 - exp (- (PI * t))))
    by (apply (Un_cv_le_const (theta_partial t) L);
        [ intro N; apply theta_partial_upper; exact Ht | exact HL ]).
  lra.
Qed.

Print Assumptions theta_half_converges.
Print Assumptions theta_gt_1.
Print Assumptions theta_antitone.
Print Assumptions theta_upper.

(* ================================================================= *)
(*  END JacobiTheta.v                                                *)
(*  θ(t) = Σ_{n∈ℤ} e^{-πn²t} is a well-defined real number for every   *)
(*  t > 0 (theta), bounded below by 1.  The modular transformation    *)
(*  θ(1/t) = √t·θ(t) — the analytic engine of the ζ functional         *)
(*  equation — remains the open next milestone.                      *)
(* ================================================================= *)
