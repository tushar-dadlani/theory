(* ================================================================= *)
(*  GaussPeriodicity.v  —  Poisson→θ line, step 2: the periodized      *)
(*  Gaussian Θ_t is 1-PERIODIC.                                       *)
(*                                                                    *)
(*  Θ_t(x) = Σ_{n∈ℤ} e^{−π(x+n)²t} is invariant under x ↦ x+1 (the     *)
(*  lattice shift), the property that makes it a genuine function on   *)
(*  the circle ℝ/ℤ and lets its Fourier coefficients be the Gaussian   *)
(*  Fourier transform (the eventual Poisson RHS).                     *)
(*                                                                    *)
(*  Proof — a BOUNDARY-TERM telescoping.  Shifting x↦x+1 reindexes the *)
(*  bilateral partial sum, changing it by exactly two edge terms:      *)
(*                                                                    *)
(*    gTheta_partial t (x+1) N                                        *)
(*        = gTheta_partial t x N + gR t x (S N) − gL t x N,           *)
(*                                                                    *)
(*  (the new right edge e^{−π(x+N+1)²t} enters, the old left edge      *)
(*  e^{−π(x−(N+1))²t} leaves).  Both edges → 0 (geometric bound, so    *)
(*  gR/gL_cv0), hence the shifted partial sums have the SAME limit:    *)
(*                                                                    *)
(*    gauss_period_shift : Un_cv (Θ_t x) L → Un_cv (Θ_t (x+1)) L,      *)
(*                                                                    *)
(*  which also grants convergence on [1,2] for free, and gives         *)
(*    gauss_period_at_1 : Un_cv (Θ_t partial at 1) (theta t)          *)
(*  so Θ_t(1) = θ(t) = Θ_t(0).                                        *)
(*                                                                    *)
(*  Built on GaussPeriodization.  No new axioms (classical Reals).   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import JacobiTheta GaussPeriodization.
Open Scope R_scope.

(* one-step unfoldings of the partial sums *)
Lemma gRp_S : forall t x N, gRp t x (S N) = gRp t x N + gR t x (S N).
Proof. intros; unfold gRp; apply tech5. Qed.
Lemma gLp_S : forall t x N, gLp t x (S N) = gLp t x N + gL t x (S N).
Proof. intros; unfold gLp; apply tech5. Qed.

(* ----------------------------------------------------------------- *)
(*  The boundary-term shift identities.                              *)
(* ----------------------------------------------------------------- *)

Lemma gRp_shift : forall t x N, gRp t (x + 1) N = gRp t x N + gR t x (S N) - gR t x 0.
Proof.
  intros t x N; induction N as [| N IH].
  - unfold gRp; cbn [sum_f_R0].
    assert (E : gR t (x + 1) 0 = gR t x 1)
      by (unfold gR; f_equal; rewrite INR_0, INR_1; ring).
    rewrite E; ring.
  - rewrite (gRp_S t (x + 1) N), IH.
    assert (E2 : gR t (x + 1) (S N) = gR t x (S (S N)))
      by (unfold gR; f_equal; rewrite !S_INR; ring).
    rewrite E2, (gRp_S t x N); ring.
Qed.

Lemma gLp_shift : forall t x N, gLp t (x + 1) N = gR t x 0 + gLp t x N - gL t x N.
Proof.
  intros t x N; induction N as [| N IH].
  - unfold gLp; cbn [sum_f_R0].
    assert (E : gL t (x + 1) 0 = gR t x 0)
      by (unfold gL, gR; f_equal; rewrite INR_0, INR_1; ring).
    rewrite E; ring.
  - rewrite (gLp_S t (x + 1) N), IH.
    assert (E2 : gL t (x + 1) (S N) = gL t x N)
      by (unfold gL; f_equal; rewrite !S_INR; ring).
    rewrite E2, (gLp_S t x N); ring.
Qed.

Lemma gTheta_shift : forall t x N,
  gTheta_partial t (x + 1) N = gTheta_partial t x N + gR t x (S N) - gL t x N.
Proof.
  intros t x N; unfold gTheta_partial; rewrite gRp_shift, gLp_shift; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The two edge terms vanish (geometric bound).                     *)
(* ----------------------------------------------------------------- *)

Lemma gR_cv0 : forall t x, 0 < t -> 0 <= x -> Un_cv (fun N => gR t x (S N)) 0.
Proof.
  intros t x Ht Hx0.
  assert (Hpos : 0 < exp (- (PI * t))) by apply exp_pos.
  assert (Hq : Rabs (exp (- (PI * t))) < 1)
    by (rewrite Rabs_right by (apply Rle_ge; left; exact Hpos); apply theta_ratio_lt1; exact Ht).
  intros eps Heps.
  destruct (pow_lt_1_zero (exp (- (PI * t))) Hq eps Heps) as [N0 HN0].
  exists N0; intros n Hn; unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; unfold gR; apply exp_pos).
  apply Rle_lt_trans with (exp (- (PI * t)) ^ (S n)); [ apply gR_le; assumption | ].
  specialize (HN0 (S n) ltac:(lia)).
  rewrite Rabs_right in HN0 by (apply Rle_ge; left; apply pow_lt; exact Hpos); exact HN0.
Qed.

Lemma gL_cv0 : forall t x, 0 < t -> 0 <= x -> x <= 1 -> Un_cv (fun N => gL t x N) 0.
Proof.
  intros t x Ht Hx0 Hx1.
  assert (Hpos : 0 < exp (- (PI * t))) by apply exp_pos.
  assert (Hq : Rabs (exp (- (PI * t))) < 1)
    by (rewrite Rabs_right by (apply Rle_ge; left; exact Hpos); apply theta_ratio_lt1; exact Ht).
  intros eps Heps.
  destruct (pow_lt_1_zero (exp (- (PI * t))) Hq eps Heps) as [N0 HN0].
  exists N0; intros n Hn; unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; unfold gL; apply exp_pos).
  apply Rle_lt_trans with (exp (- (PI * t)) ^ n); [ apply gL_le; assumption | ].
  specialize (HN0 n Hn).
  rewrite Rabs_right in HN0 by (apply Rle_ge; left; apply pow_lt; exact Hpos); exact HN0.
Qed.

(* ----------------------------------------------------------------- *)
(*  1-periodicity of the limit.                                       *)
(* ----------------------------------------------------------------- *)

Theorem gauss_period_shift : forall t x L,
  0 < t -> 0 <= x -> x <= 1 ->
  Un_cv (gTheta_partial t x) L -> Un_cv (gTheta_partial t (x + 1)) L.
Proof.
  intros t x L Ht Hx0 Hx1 HL.
  assert (H1 : Un_cv (fun N => gTheta_partial t x N + gR t x (S N)) (L + 0))
    by (apply CV_plus; [ exact HL | apply gR_cv0; assumption ]).
  assert (Hcv : Un_cv (fun N => (gTheta_partial t x N + gR t x (S N)) - gL t x N) ((L + 0) - 0))
    by (apply CV_minus; [ exact H1 | apply gL_cv0; assumption ]).
  replace ((L + 0) - 0) with L in Hcv by ring.
  intros eps Heps; destruct (Hcv eps Heps) as [N0 H0]; exists N0; intros n Hn.
  rewrite gTheta_shift; apply H0; exact Hn.
Qed.

Corollary gauss_period_at_1 : forall t (Ht : 0 < t),
  Un_cv (gTheta_partial t 1) (theta t Ht).
Proof.
  intros t Ht.
  pose proof (gauss_period_shift t 0 (theta t Ht) Ht (Rle_refl 0) Rle_0_1
                (gauss_period_at_0 t Ht)) as H.
  replace 1 with (0 + 1) by ring; exact H.
Qed.

Print Assumptions gauss_period_shift.
Print Assumptions gauss_period_at_1.

(* ================================================================= *)
(*  END GaussPeriodicity.v                                           *)
(*  Θ_t is 1-periodic (gauss_period_shift), so it descends to ℝ/ℤ;    *)
(*  Θ_t(1) = θ(t) = Θ_t(0).  Next on the line: its Fourier            *)
(*  coefficients = the Gaussian Fourier transform (the integral wall).*)
(* ================================================================= *)
