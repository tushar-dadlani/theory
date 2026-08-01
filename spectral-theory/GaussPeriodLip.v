(* ================================================================= *)
(*  GaussPeriodLip.v  —  Θ_t'' is LIPSCHITZ on bounded sets.          *)
(*                                                                    *)
(*  The bounded-interval Leibniz rule (leibniz_interval_local) needs a *)
(*  SECOND-order Taylor bound of ftil' = Θ_t'(·/2π), which follows from *)
(*  ftil'' Lipschitz — i.e. Θ_t'' Lipschitz.  We prove Θ_t'' (=GTheta2) *)
(*  Lipschitz on every [-R,R] by a THIRD termwise derivative:          *)
(*     d/dx gRq2 = gRq3 = (3c²u − c³u³)·e^{−πt u²}   (c=2πt, u=x+n),    *)
(*  bounded on [-R,R] by K3(R)·(e^{−πt/2})ⁿ using the first and third   *)
(*  Gaussian moments, and MVT + termwise summation.  No C³ CVU limit,  *)
(*  no periodicity/compactness argument — the geometric domination     *)
(*  does it directly.  No new axioms (classical Reals only).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 FunctionalExtensionality Lra Lia.
Require Import JacobiTheta GaussPeriodization GaussPeriodDeriv GaussPeriodDeriv2.
Open Scope R_scope.

(* ================================================================= *)
(*  Part A.  General helpers.                                         *)
(* ================================================================= *)

(* the third Gaussian moment split:  |u|·u²·e^{−a u²} ≤ (1/√(a/2))·(1/(a/2)). *)
Lemma cube_gauss_bound : forall a u, 0 < a ->
  Rabs u * u ^ 2 * exp (- (a * u ^ 2)) <= / sqrt (a / 2) * / (a / 2).
Proof.
  intros a u Ha; assert (Ha2 : 0 < a / 2) by lra.
  assert (Es : exp (- (a * u ^ 2)) = exp (- (a / 2 * u ^ 2)) * exp (- (a / 2 * u ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Es.
  replace (Rabs u * u ^ 2 * (exp (- (a / 2 * u ^ 2)) * exp (- (a / 2 * u ^ 2))))
    with ((Rabs u * exp (- (a / 2 * u ^ 2))) * (u ^ 2 * exp (- (a / 2 * u ^ 2)))) by ring.
  apply Rmult_le_compat.
  - apply Rmult_le_pos; [ apply Rabs_pos | left; apply exp_pos ].
  - apply Rmult_le_pos; [ rewrite <- Rsqr_pow2; apply Rle_0_sqr | left; apply exp_pos ].
  - exact (abs_gauss_bound (a / 2) u Ha2).
  - exact (abs_gauss_bound2 (a / 2) u Ha2).
Qed.

(* triangle inequality for a finite sum *)
Lemma sum_f_R0_Rabs : forall (a : nat -> R) N,
  Rabs (sum_f_R0 a N) <= sum_f_R0 (fun k => Rabs (a k)) N.
Proof.
  intros a N; induction N as [| N IH]; cbn [sum_f_R0].
  - apply Rle_refl.
  - eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat; [ exact IH | apply Rle_refl ] ].
Qed.

(* MVT-Lipschitz on an interval, from a bound on the derivative there. *)
Lemma mvt_lip : forall (f f' : R -> R) (K lo hi : R),
  (forall x, derivable_pt_lim f x (f' x)) ->
  (forall x, lo <= x <= hi -> Rabs (f' x) <= K) ->
  forall x1 x2, lo <= x1 <= hi -> lo <= x2 <= hi ->
    Rabs (f x1 - f x2) <= K * Rabs (x1 - x2).
Proof.
  intros f f' K lo hi Hd Hb x1 x2 H1 H2.
  set (pr := fun x => exist (fun l => derivable_pt_lim f x l) (f' x) (Hd x) : derivable_pt f x).
  destruct (total_order_T x1 x2) as [[Hlt | Heq] | Hgt].
  - destruct (MVT_cor1 f x1 x2 pr Hlt) as [c [Hc [Hc1 Hc2]]].
    assert (Hderc : derive_pt f c (pr c) = f' c) by reflexivity.
    rewrite Hderc in Hc.
    rewrite Rabs_minus_sym.
    replace (f x2 - f x1) with (f' c * (x2 - x1)) by (rewrite Hc; ring).
    rewrite Rabs_mult; rewrite (Rabs_minus_sym x2 x1).
    apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb; split; lra ].
  - subst x2; replace (f x1 - f x1) with 0 by ring; replace (x1 - x1) with 0 by ring;
      rewrite !Rabs_R0, Rmult_0_r; apply Rle_refl.
  - destruct (MVT_cor1 f x2 x1 pr Hgt) as [c [Hc [Hc1 Hc2]]].
    assert (Hderc : derive_pt f c (pr c) = f' c) by reflexivity.
    rewrite Hderc in Hc.
    replace (f x1 - f x2) with (f' c * (x1 - x2)) by (rewrite Hc; ring).
    rewrite Rabs_mult.
    apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb; split; lra ].
Qed.

(* ================================================================= *)
(*  Part B.  The third derivative term and its bound.                *)
(* ================================================================= *)

Section Lip.

Variable t : R.
Hypothesis Ht : 0 < t.

Definition gRq3 (x : R) (k : nat) : R :=
  (3 * (2 * PI * t) ^ 2 * (x + INR k) - (2 * PI * t) ^ 3 * (x + INR k) ^ 3) * gR t x k.
Definition gLq3 (x : R) (k : nat) : R :=
  (3 * (2 * PI * t) ^ 2 * (x - INR (S k)) - (2 * PI * t) ^ 3 * (x - INR (S k)) ^ 3) * gL t x k.

Lemma hp2 : 0 < PI * t / 2.
Proof. pose proof PI_RGT_0; nra. Qed.

Lemma c2nn : 0 <= 3 * (2 * PI * t) ^ 2.
Proof. rewrite <- Rsqr_pow2; pose proof (Rle_0_sqr (2 * PI * t)); lra. Qed.

Lemma c3nn : 0 <= (2 * PI * t) ^ 3.
Proof. apply pow_le; pose proof PI_RGT_0; nra. Qed.

(* --- the third derivative of the kernels --- *)

Lemma dgRq2 : forall x k, derivable_pt_lim (fun s => gRq2 t s k) x (gRq3 x k).
Proof.
  intros x k.
  assert (Haff : derivable_pt_lim (fun s => s + INR k) x 1)
    by (replace 1 with (1 + 0) by ring;
        apply derivable_pt_lim_plus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]).
  assert (Hg : derivable_pt_lim (fun s => 2 * PI * t * (s + INR k)) x (2 * PI * t)).
  { pose proof (derivable_pt_lim_scal (fun s => s + INR k) (2 * PI * t) x 1 Haff) as Hsc.
    replace (2 * PI * t * 1) with (2 * PI * t) in Hsc by ring; exact Hsc. }
  assert (Hpoly : derivable_pt_lim (fun s => (2 * PI * t * (s + INR k)) ^ 2 - 2 * PI * t) x
                    (2 * (2 * PI * t) ^ 2 * (x + INR k))).
  { pose proof (derivable_pt_lim_comp (fun s => 2 * PI * t * (s + INR k)) (fun z => z ^ 2) x
        (2 * PI * t) (INR 2 * (2 * PI * t * (x + INR k)) ^ Init.Nat.pred 2) Hg
        (derivable_pt_lim_pow (2 * PI * t * (x + INR k)) 2)) as Hsq.
    replace (2 * (2 * PI * t) ^ 2 * (x + INR k))
      with (INR 2 * (2 * PI * t * (x + INR k)) ^ Init.Nat.pred 2 * (2 * PI * t) - 0)
      by (simpl; ring).
    apply derivable_pt_lim_minus; [ exact Hsq | apply derivable_pt_lim_const ]. }
  pose proof (derivable_pt_lim_mult (fun s => (2 * PI * t * (s + INR k)) ^ 2 - 2 * PI * t)
                (fun s => gR t s k) x (2 * (2 * PI * t) ^ 2 * (x + INR k)) (gRq t x k)
                Hpoly (dgR t x k)) as Hm.
  assert (Hval : gRq3 x k = 2 * (2 * PI * t) ^ 2 * (x + INR k) * gR t x k
                          + ((2 * PI * t * (x + INR k)) ^ 2 - 2 * PI * t) * gRq t x k)
    by (unfold gRq3, gRq, gR; ring).
  rewrite Hval; exact Hm.
Qed.

Lemma dgLq2 : forall x k, derivable_pt_lim (fun s => gLq2 t s k) x (gLq3 x k).
Proof.
  intros x k.
  assert (Haff : derivable_pt_lim (fun s => s - INR (S k)) x 1)
    by (replace 1 with (1 - 0) by ring;
        apply derivable_pt_lim_minus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]).
  assert (Hg : derivable_pt_lim (fun s => 2 * PI * t * (s - INR (S k))) x (2 * PI * t)).
  { pose proof (derivable_pt_lim_scal (fun s => s - INR (S k)) (2 * PI * t) x 1 Haff) as Hsc.
    replace (2 * PI * t * 1) with (2 * PI * t) in Hsc by ring; exact Hsc. }
  assert (Hpoly : derivable_pt_lim (fun s => (2 * PI * t * (s - INR (S k))) ^ 2 - 2 * PI * t) x
                    (2 * (2 * PI * t) ^ 2 * (x - INR (S k)))).
  { pose proof (derivable_pt_lim_comp (fun s => 2 * PI * t * (s - INR (S k))) (fun z => z ^ 2) x
        (2 * PI * t) (INR 2 * (2 * PI * t * (x - INR (S k))) ^ Init.Nat.pred 2) Hg
        (derivable_pt_lim_pow (2 * PI * t * (x - INR (S k))) 2)) as Hsq.
    replace (2 * (2 * PI * t) ^ 2 * (x - INR (S k)))
      with (INR 2 * (2 * PI * t * (x - INR (S k))) ^ Init.Nat.pred 2 * (2 * PI * t) - 0)
      by (simpl; ring).
    apply derivable_pt_lim_minus; [ exact Hsq | apply derivable_pt_lim_const ]. }
  pose proof (derivable_pt_lim_mult (fun s => (2 * PI * t * (s - INR (S k))) ^ 2 - 2 * PI * t)
                (fun s => gL t s k) x (2 * (2 * PI * t) ^ 2 * (x - INR (S k))) (gLq t x k)
                Hpoly (dgL t x k)) as Hm.
  assert (Hval : gLq3 x k = 2 * (2 * PI * t) ^ 2 * (x - INR (S k)) * gL t x k
                          + ((2 * PI * t * (x - INR (S k))) ^ 2 - 2 * PI * t) * gLq t x k)
    by (unfold gLq3, gLq, gL; ring).
  rewrite Hval; exact Hm.
Qed.

(* --- moment bounds on [-R,R] --- *)

Definition Ebnd (R : R) := exp (PI * t / 2 * (R + 1)).
Definition D3 : R :=
  3 * (2 * PI * t) ^ 2 * / sqrt (PI * t / 2)
  + (2 * PI * t) ^ 3 * (/ sqrt (PI * t / 4) * / (PI * t / 4)).
Definition K3 (R : R) := D3 * Ebnd R.

Lemma mom1R : forall R x k, 0 <= R -> - R <= x <= R ->
  Rabs (x + INR k) * gR t x k <= / sqrt (PI * t / 2) * Ebnd R * wt t ^ k.
Proof.
  intros R x k HR [Hlo Hhi]; unfold gR, Ebnd; pose proof PI_RGT_0 as HPI; pose proof hp2 as Hhp.
  assert (Es : exp (- (PI * (x + INR k) ^ 2 * t))
               = exp (- (PI * t / 2 * (x + INR k) ^ 2)) * exp (- (PI * t / 2 * (x + INR k) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Es.
  replace (Rabs (x + INR k) * (exp (- (PI * t / 2 * (x + INR k) ^ 2))
                               * exp (- (PI * t / 2 * (x + INR k) ^ 2))))
    with ((Rabs (x + INR k) * exp (- (PI * t / 2 * (x + INR k) ^ 2)))
          * exp (- (PI * t / 2 * (x + INR k) ^ 2))) by ring.
  apply Rle_trans with (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (/ 4 - x)) * wt t ^ k)).
  - apply Rmult_le_compat.
    + apply Rmult_le_pos; [ apply Rabs_pos | left; apply exp_pos ].
    + left; apply exp_pos.
    + exact (abs_gauss_bound (PI * t / 2) (x + INR k) Hhp).
    + unfold wt; exact (exp_sq_geom_R (PI * t / 2) x k Hhp).
  - replace (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (/ 4 - x)) * wt t ^ k))
      with ((/ sqrt (PI * t / 2) * exp (PI * t / 2 * (/ 4 - x))) * wt t ^ k) by ring.
    apply Rmult_le_compat_r; [ apply pow_le; apply wt_nonneg | ].
    apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; exact Hhp | ].
    apply exp_le_compat; apply Rmult_le_compat_l; [ lra | lra ].
Qed.

Lemma mom3R : forall R x k, 0 <= R -> - R <= x <= R ->
  Rabs (x + INR k) * (x + INR k) ^ 2 * gR t x k
  <= (/ sqrt (PI * t / 4) * / (PI * t / 4)) * Ebnd R * wt t ^ k.
Proof.
  intros R x k HR [Hlo Hhi]; unfold gR, Ebnd; pose proof PI_RGT_0 as HPI; pose proof hp2 as Hhp.
  assert (Es : exp (- (PI * (x + INR k) ^ 2 * t))
               = exp (- (PI * t / 2 * (x + INR k) ^ 2)) * exp (- (PI * t / 2 * (x + INR k) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Es.
  replace (Rabs (x + INR k) * (x + INR k) ^ 2
           * (exp (- (PI * t / 2 * (x + INR k) ^ 2)) * exp (- (PI * t / 2 * (x + INR k) ^ 2))))
    with ((Rabs (x + INR k) * (x + INR k) ^ 2 * exp (- (PI * t / 2 * (x + INR k) ^ 2)))
          * exp (- (PI * t / 2 * (x + INR k) ^ 2))) by ring.
  apply Rle_trans with
    ((/ sqrt (PI * t / 4) * / (PI * t / 4)) * (exp (PI * t / 2 * (/ 4 - x)) * wt t ^ k)).
  - apply Rmult_le_compat.
    + apply Rmult_le_pos; [ apply Rmult_le_pos;
        [ apply Rabs_pos | rewrite <- Rsqr_pow2; apply Rle_0_sqr ] | left; apply exp_pos ].
    + left; apply exp_pos.
    + assert (E4 : PI * t / 2 / 2 = PI * t / 4) by field.
      pose proof (cube_gauss_bound (PI * t / 2) (x + INR k) Hhp) as Hcb; rewrite E4 in Hcb; exact Hcb.
    + unfold wt; exact (exp_sq_geom_R (PI * t / 2) x k Hhp).
  - replace ((/ sqrt (PI * t / 4) * / (PI * t / 4)) * (exp (PI * t / 2 * (/ 4 - x)) * wt t ^ k))
      with (((/ sqrt (PI * t / 4) * / (PI * t / 4)) * exp (PI * t / 2 * (/ 4 - x))) * wt t ^ k) by ring.
    apply Rmult_le_compat_r; [ apply pow_le; apply wt_nonneg | ].
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [ left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; nra
                          | left; apply Rinv_0_lt_compat; nra ].
    + apply exp_le_compat; apply Rmult_le_compat_l; [ lra | lra ].
Qed.

Lemma mom1L : forall R x k, 0 <= R -> - R <= x <= R ->
  Rabs (x - INR (S k)) * gL t x k <= / sqrt (PI * t / 2) * Ebnd R * wt t ^ k.
Proof.
  intros R x k HR [Hlo Hhi]; unfold gL, Ebnd; pose proof PI_RGT_0 as HPI; pose proof hp2 as Hhp.
  assert (Es : exp (- (PI * (x - INR (S k)) ^ 2 * t))
               = exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Es.
  replace (Rabs (x - INR (S k)) * (exp (- (PI * t / 2 * (x - INR (S k)) ^ 2))
                               * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2))))
    with ((Rabs (x - INR (S k)) * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)))
          * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2))) by ring.
  apply Rle_trans with (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (x - 3 / 4)) * wt t ^ k)).
  - apply Rmult_le_compat.
    + apply Rmult_le_pos; [ apply Rabs_pos | left; apply exp_pos ].
    + left; apply exp_pos.
    + exact (abs_gauss_bound (PI * t / 2) (x - INR (S k)) Hhp).
    + unfold wt; exact (exp_sq_geom_L (PI * t / 2) x k Hhp).
  - replace (/ sqrt (PI * t / 2) * (exp (PI * t / 2 * (x - 3 / 4)) * wt t ^ k))
      with ((/ sqrt (PI * t / 2) * exp (PI * t / 2 * (x - 3 / 4))) * wt t ^ k) by ring.
    apply Rmult_le_compat_r; [ apply pow_le; apply wt_nonneg | ].
    apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; exact Hhp | ].
    apply exp_le_compat; apply Rmult_le_compat_l; [ lra | lra ].
Qed.

Lemma mom3L : forall R x k, 0 <= R -> - R <= x <= R ->
  Rabs (x - INR (S k)) * (x - INR (S k)) ^ 2 * gL t x k
  <= (/ sqrt (PI * t / 4) * / (PI * t / 4)) * Ebnd R * wt t ^ k.
Proof.
  intros R x k HR [Hlo Hhi]; unfold gL, Ebnd; pose proof PI_RGT_0 as HPI; pose proof hp2 as Hhp.
  assert (Es : exp (- (PI * (x - INR (S k)) ^ 2 * t))
               = exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Es.
  replace (Rabs (x - INR (S k)) * (x - INR (S k)) ^ 2
           * (exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)) * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2))))
    with ((Rabs (x - INR (S k)) * (x - INR (S k)) ^ 2 * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2)))
          * exp (- (PI * t / 2 * (x - INR (S k)) ^ 2))) by ring.
  apply Rle_trans with
    ((/ sqrt (PI * t / 4) * / (PI * t / 4)) * (exp (PI * t / 2 * (x - 3 / 4)) * wt t ^ k)).
  - apply Rmult_le_compat.
    + apply Rmult_le_pos; [ apply Rmult_le_pos;
        [ apply Rabs_pos | rewrite <- Rsqr_pow2; apply Rle_0_sqr ] | left; apply exp_pos ].
    + left; apply exp_pos.
    + assert (E4 : PI * t / 2 / 2 = PI * t / 4) by field.
      pose proof (cube_gauss_bound (PI * t / 2) (x - INR (S k)) Hhp) as Hcb; rewrite E4 in Hcb; exact Hcb.
    + unfold wt; exact (exp_sq_geom_L (PI * t / 2) x k Hhp).
  - replace ((/ sqrt (PI * t / 4) * / (PI * t / 4)) * (exp (PI * t / 2 * (x - 3 / 4)) * wt t ^ k))
      with (((/ sqrt (PI * t / 4) * / (PI * t / 4)) * exp (PI * t / 2 * (x - 3 / 4))) * wt t ^ k) by ring.
    apply Rmult_le_compat_r; [ apply pow_le; apply wt_nonneg | ].
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [ left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; nra
                          | left; apply Rinv_0_lt_compat; nra ].
    + apply exp_le_compat; apply Rmult_le_compat_l; [ lra | lra ].
Qed.

Lemma sum_f_R0_minus : forall (a b : nat -> R) N,
  sum_f_R0 a N - sum_f_R0 b N = sum_f_R0 (fun k => a k - b k) N.
Proof.
  intros a b N; induction N as [| N IH]; cbn [sum_f_R0]; [ ring | rewrite <- IH; ring ].
Qed.

Lemma gRq3_bound : forall R x k, 0 <= R -> - R <= x <= R -> Rabs (gRq3 x k) <= K3 R * wt t ^ k.
Proof.
  intros R x k HR Hx; unfold gRq3, K3, D3; pose proof PI_RGT_0 as HPI.
  rewrite Rabs_mult, (Rabs_right (gR t x k)) by (apply Rle_ge; left; unfold gR; apply exp_pos).
  apply Rle_trans with
    ((3 * (2 * PI * t) ^ 2 * Rabs (x + INR k)
      + (2 * PI * t) ^ 3 * (Rabs (x + INR k) * (x + INR k) ^ 2)) * gR t x k).
  - apply Rmult_le_compat_r; [ left; unfold gR; apply exp_pos | ].
    replace (3 * (2 * PI * t) ^ 2 * (x + INR k) - (2 * PI * t) ^ 3 * (x + INR k) ^ 3)
      with (3 * (2 * PI * t) ^ 2 * (x + INR k) + - ((2 * PI * t) ^ 3 * (x + INR k) ^ 3)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat ].
    + rewrite Rabs_mult, (Rabs_right (3 * (2 * PI * t) ^ 2)) by (apply Rle_ge; apply c2nn); apply Rle_refl.
    + rewrite Rabs_Ropp, Rabs_mult, (Rabs_right ((2 * PI * t) ^ 3)) by (apply Rle_ge; apply c3nn).
      apply Rmult_le_compat_l; [ apply c3nn | ].
      replace ((x + INR k) ^ 3) with ((x + INR k) * (x + INR k) ^ 2) by ring.
      rewrite Rabs_mult, (Rabs_right ((x + INR k) ^ 2))
        by (apply Rle_ge; rewrite <- Rsqr_pow2; apply Rle_0_sqr); apply Rle_refl.
  - replace ((3 * (2 * PI * t) ^ 2 * Rabs (x + INR k)
              + (2 * PI * t) ^ 3 * (Rabs (x + INR k) * (x + INR k) ^ 2)) * gR t x k)
      with (3 * (2 * PI * t) ^ 2 * (Rabs (x + INR k) * gR t x k)
            + (2 * PI * t) ^ 3 * (Rabs (x + INR k) * (x + INR k) ^ 2 * gR t x k)) by ring.
    apply Rle_trans with
      (3 * (2 * PI * t) ^ 2 * (/ sqrt (PI * t / 2) * Ebnd R * wt t ^ k)
       + (2 * PI * t) ^ 3 * ((/ sqrt (PI * t / 4) * / (PI * t / 4)) * Ebnd R * wt t ^ k)).
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_l; [ apply c2nn | apply mom1R; assumption ].
      * apply Rmult_le_compat_l; [ apply c3nn | apply mom3R; assumption ].
    + apply Req_le; ring.
Qed.

Lemma gLq3_bound : forall R x k, 0 <= R -> - R <= x <= R -> Rabs (gLq3 x k) <= K3 R * wt t ^ k.
Proof.
  intros R x k HR Hx; unfold gLq3, K3, D3; pose proof PI_RGT_0 as HPI.
  rewrite Rabs_mult, (Rabs_right (gL t x k)) by (apply Rle_ge; left; unfold gL; apply exp_pos).
  apply Rle_trans with
    ((3 * (2 * PI * t) ^ 2 * Rabs (x - INR (S k))
      + (2 * PI * t) ^ 3 * (Rabs (x - INR (S k)) * (x - INR (S k)) ^ 2)) * gL t x k).
  - apply Rmult_le_compat_r; [ left; unfold gL; apply exp_pos | ].
    replace (3 * (2 * PI * t) ^ 2 * (x - INR (S k)) - (2 * PI * t) ^ 3 * (x - INR (S k)) ^ 3)
      with (3 * (2 * PI * t) ^ 2 * (x - INR (S k)) + - ((2 * PI * t) ^ 3 * (x - INR (S k)) ^ 3)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat ].
    + rewrite Rabs_mult, (Rabs_right (3 * (2 * PI * t) ^ 2)) by (apply Rle_ge; apply c2nn); apply Rle_refl.
    + rewrite Rabs_Ropp, Rabs_mult, (Rabs_right ((2 * PI * t) ^ 3)) by (apply Rle_ge; apply c3nn).
      apply Rmult_le_compat_l; [ apply c3nn | ].
      replace ((x - INR (S k)) ^ 3) with ((x - INR (S k)) * (x - INR (S k)) ^ 2) by ring.
      rewrite Rabs_mult, (Rabs_right ((x - INR (S k)) ^ 2))
        by (apply Rle_ge; rewrite <- Rsqr_pow2; apply Rle_0_sqr); apply Rle_refl.
  - replace ((3 * (2 * PI * t) ^ 2 * Rabs (x - INR (S k))
              + (2 * PI * t) ^ 3 * (Rabs (x - INR (S k)) * (x - INR (S k)) ^ 2)) * gL t x k)
      with (3 * (2 * PI * t) ^ 2 * (Rabs (x - INR (S k)) * gL t x k)
            + (2 * PI * t) ^ 3 * (Rabs (x - INR (S k)) * (x - INR (S k)) ^ 2 * gL t x k)) by ring.
    apply Rle_trans with
      (3 * (2 * PI * t) ^ 2 * (/ sqrt (PI * t / 2) * Ebnd R * wt t ^ k)
       + (2 * PI * t) ^ 3 * ((/ sqrt (PI * t / 4) * / (PI * t / 4)) * Ebnd R * wt t ^ k)).
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_l; [ apply c2nn | apply mom1L; assumption ].
      * apply Rmult_le_compat_l; [ apply c3nn | apply mom3L; assumption ].
    + apply Req_le; ring.
Qed.

(* --- termwise Lipschitz via MVT --- *)

Lemma termR_lip : forall R k x1 x2, 0 <= R -> - R <= x1 <= R -> - R <= x2 <= R ->
  Rabs (gRq2 t x1 k - gRq2 t x2 k) <= K3 R * wt t ^ k * Rabs (x1 - x2).
Proof.
  intros R k x1 x2 HR H1 H2.
  apply (mvt_lip (fun s => gRq2 t s k) (fun s => gRq3 s k) (K3 R * wt t ^ k) (- R) R);
    [ intro x; apply dgRq2 | intros x Hx; apply gRq3_bound; [ exact HR | exact Hx ]
    | exact H1 | exact H2 ].
Qed.

Lemma termL_lip : forall R k x1 x2, 0 <= R -> - R <= x1 <= R -> - R <= x2 <= R ->
  Rabs (gLq2 t x1 k - gLq2 t x2 k) <= K3 R * wt t ^ k * Rabs (x1 - x2).
Proof.
  intros R k x1 x2 HR H1 H2.
  apply (mvt_lip (fun s => gLq2 t s k) (fun s => gLq3 s k) (K3 R * wt t ^ k) (- R) R);
    [ intro x; apply dgLq2 | intros x Hx; apply gLq3_bound; [ exact HR | exact Hx ]
    | exact H1 | exact H2 ].
Qed.

Lemma K3_nonneg : forall R, 0 <= K3 R.
Proof.
  intro R; unfold K3, D3, Ebnd; pose proof PI_RGT_0.
  apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; [ apply c2nn | left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; nra ].
  - apply Rmult_le_pos; [ apply c3nn | apply Rmult_le_pos;
      [ left; apply Rinv_0_lt_compat; apply sqrt_lt_R0; nra | left; apply Rinv_0_lt_compat; nra ] ].
Qed.

(* --- one side's partial-sum Lipschitz bound --- *)

Lemma side_partial_lip : forall (g3 : R -> nat -> R) R,
  0 <= R ->
  (forall k x1 x2, - R <= x1 <= R -> - R <= x2 <= R ->
     Rabs (g3 x1 k - g3 x2 k) <= K3 R * wt t ^ k * Rabs (x1 - x2)) ->
  forall N x1 x2, - R <= x1 <= R -> - R <= x2 <= R ->
    Rabs (sum_f_R0 (g3 x1) N - sum_f_R0 (g3 x2) N)
    <= K3 R / (1 - wt t) * Rabs (x1 - x2).
Proof.
  intros g3 R HR Hlip N x1 x2 H1 H2.
  assert (Hw1 : 0 < 1 - wt t) by (pose proof (wt_lt1 t Ht); lra).
  rewrite sum_f_R0_minus.
  eapply Rle_trans; [ apply sum_f_R0_Rabs | ].
  eapply Rle_trans.
  { apply sum_f_R0_le with (B := fun k => K3 R * Rabs (x1 - x2) * wt t ^ k).
    intro k; eapply Rle_trans; [ apply Hlip; assumption | apply Req_le; ring ]. }
  rewrite sum_f_R0_scal.
  apply Rle_trans with (K3 R * Rabs (x1 - x2) * / (1 - wt t)).
  - apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [ apply K3_nonneg | apply Rabs_pos ].
    + apply geom_partial_bound; [ apply wt_nonneg | apply wt_lt1; exact Ht ].
  - apply Req_le; unfold Rdiv; ring.
Qed.

(* --- Θ_t'' is Lipschitz on [-R,R] --- *)

Theorem GTheta2_lip : forall R, 0 <= R -> forall x1 x2, - R <= x1 <= R -> - R <= x2 <= R ->
  Rabs (GTheta2 t Ht x1 - GTheta2 t Ht x2) <= 2 * (K3 R / (1 - wt t)) * Rabs (x1 - x2).
Proof.
  intros R HR x1 x2 H1 H2.
  set (C := 2 * (K3 R / (1 - wt t)) * Rabs (x1 - x2)).
  assert (Hpart : forall N, Rabs (gTheta_deriv2_partial t x1 N - gTheta_deriv2_partial t x2 N) <= C).
  { intro N; unfold gTheta_deriv2_partial, C.
    replace (sum_f_R0 (gRq2 t x1) N + sum_f_R0 (gLq2 t x1) N
             - (sum_f_R0 (gRq2 t x2) N + sum_f_R0 (gLq2 t x2) N))
      with ((sum_f_R0 (gRq2 t x1) N - sum_f_R0 (gRq2 t x2) N)
            + (sum_f_R0 (gLq2 t x1) N - sum_f_R0 (gLq2 t x2) N)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    replace (2 * (K3 R / (1 - wt t)) * Rabs (x1 - x2))
      with (K3 R / (1 - wt t) * Rabs (x1 - x2) + K3 R / (1 - wt t) * Rabs (x1 - x2)) by ring.
    apply Rplus_le_compat.
    - apply (side_partial_lip (fun x k => gRq2 t x k) R HR
               (fun k a b Ha Hb => termR_lip R k a b HR Ha Hb) N x1 x2 H1 H2).
    - apply (side_partial_lip (fun x k => gLq2 t x k) R HR
               (fun k a b Ha Hb => termL_lip R k a b HR Ha Hb) N x1 x2 H1 H2). }
  assert (Hdiff : Un_cv (fun N => gTheta_deriv2_partial t x1 N - gTheta_deriv2_partial t x2 N)
                        (GTheta2 t Ht x1 - GTheta2 t Ht x2))
    by (apply CV_minus; apply GTheta2_spec).
  assert (Habs : Un_cv (fun N => Rabs (gTheta_deriv2_partial t x1 N - gTheta_deriv2_partial t x2 N))
                       (Rabs (GTheta2 t Ht x1 - GTheta2 t Ht x2))).
  { intros eps He; destruct (Hdiff eps He) as [N0 H0]; exists N0; intros n Hn;
      unfold R_dist; eapply Rle_lt_trans; [ apply Rabs_triang_inv2 | apply H0; exact Hn ]. }
  apply (Un_cv_le_const (fun N => Rabs (gTheta_deriv2_partial t x1 N - gTheta_deriv2_partial t x2 N))
           (Rabs (GTheta2 t Ht x1 - GTheta2 t Ht x2)) C Hpart Habs).
Qed.

(* --- ftil'' = ftil2 is Lipschitz on every bounded set --- *)

Lemma scale_in : forall a R, - R <= a <= R ->
  - (R / (2 * PI)) <= a / (2 * PI) <= R / (2 * PI).
Proof.
  intros a R [Hlo Hhi]; pose proof PI_RGT_0; assert (0 < 2 * PI) by lra.
  assert (Hi : 0 < / (2 * PI)) by (apply Rinv_0_lt_compat; lra).
  unfold Rdiv; split.
  - replace (- (R * / (2 * PI))) with ((- R) * / (2 * PI)) by ring.
    apply Rmult_le_compat_r; [ lra | exact Hlo ].
  - apply Rmult_le_compat_r; [ lra | exact Hhi ].
Qed.

Theorem ftil2_lip : forall R, 0 <= R -> exists L, 0 <= L /\
  forall u1 u2, - R <= u1 <= R -> - R <= u2 <= R ->
    Rabs (ftil2 t Ht u1 - ftil2 t Ht u2) <= L * Rabs (u1 - u2).
Proof.
  intros R HR; pose proof PI_RGT_0 as HPI; assert (H2pi : 0 < 2 * PI) by lra.
  assert (Hw1 : 0 < 1 - wt t) by (pose proof (wt_lt1 t Ht); lra).
  set (R' := R / (2 * PI)).
  assert (HR' : 0 <= R')
    by (unfold R', Rdiv; apply Rmult_le_pos; [ exact HR | left; apply Rinv_0_lt_compat; exact H2pi ]).
  exists ((/ (2 * PI)) ^ 2 * (2 * (K3 R' / (1 - wt t))) * (/ (2 * PI))); split.
  - apply Rmult_le_pos; [ apply Rmult_le_pos | left; apply Rinv_0_lt_compat; exact H2pi ].
    + left; apply pow_lt; apply Rinv_0_lt_compat; exact H2pi.
    + apply Rmult_le_pos; [ lra | apply Rmult_le_pos;
        [ apply K3_nonneg | left; apply Rinv_0_lt_compat; exact Hw1 ] ].
  - intros u1 u2 H1 H2; unfold ftil2.
    replace (/ (2 * PI) * (/ (2 * PI) * GTheta2 t Ht (u1 / (2 * PI)))
             - / (2 * PI) * (/ (2 * PI) * GTheta2 t Ht (u2 / (2 * PI))))
      with ((/ (2 * PI)) ^ 2 * (GTheta2 t Ht (u1 / (2 * PI)) - GTheta2 t Ht (u2 / (2 * PI)))) by ring.
    rewrite Rabs_mult, (Rabs_right ((/ (2 * PI)) ^ 2))
      by (apply Rle_ge; left; apply pow_lt; apply Rinv_0_lt_compat; exact H2pi).
    eapply Rle_trans.
    { apply Rmult_le_compat_l; [ left; apply pow_lt; apply Rinv_0_lt_compat; exact H2pi | ].
      apply GTheta2_lip; [ exact HR' | apply scale_in; exact H1 | apply scale_in; exact H2 ]. }
    replace (u1 / (2 * PI) - u2 / (2 * PI)) with ((u1 - u2) * / (2 * PI)) by (unfold Rdiv; ring).
    rewrite Rabs_mult, (Rabs_right (/ (2 * PI)))
      by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact H2pi).
    apply Req_le; unfold R'; ring.
Qed.

Print Assumptions GTheta2_lip.
Print Assumptions ftil2_lip.

End Lip.

(* ================================================================= *)
(*  END GaussPeriodLip.v                                             *)
(*  GTheta2 (=Θ_t'') is Lipschitz on every [-R,R] (GTheta2_lip), hence  *)
(*  ftil2 (=ftil'') is Lipschitz on bounded sets (ftil2_lip).  This    *)
(*  supplies the second-order Taylor bound the local Leibniz rule      *)
(*  needs for the Hadamard localiser factor.                          *)
(* ================================================================= *)
