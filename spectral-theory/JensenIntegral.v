(* ================================================================= *)
(*  JensenIntegral.v  —  Hadamard keystone, brick 2: the Jensen integral *)
(*                                                                    *)
(*    int_0^{2pi} ln|1 - r e^{i theta}| d theta = 0     (0 <= r < 1)   *)
(*                                                                    *)
(*  the seed of Jensen's formula (and hence of the complex zero-count   *)
(*  n(r)=O(r) the Hadamard product needs).  Proof: the log kernel is    *)
(*  the uniform limit of its Fourier partial sums                       *)
(*    lsum theta N r = sum_{k=1}^{N+1} (r^k/k) cos(k theta)            *)
(*  (LogGeomSeries.log_geom_series), EACH of which has zero mean over   *)
(*  [0,2pi] (int_lsum_zero, via the vanishing antiderivative), and the  *)
(*  convergence is UNIFORM in theta (Weierstrass M-test: the majorant   *)
(*  r^k is theta-independent).  Swapping the limit past the integral    *)
(*  (UniformIntegralSwap.RiemannInt_unif_limit) gives 0.               *)
(*                                                                    *)
(*  Axiom-clean.  Brick 2 of ~6 toward the full Hadamard product.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import UniformIntegralSwap LogGeomSeries JensenOrthogonality ContinuousCoV.
Open Scope R_scope.

Lemma CV_const : forall a : R, Un_cv (fun _ => a) a.
Proof.
  intros a eps Heps. exists 0%nat. intros n _. unfold R_dist.
  replace (a - a) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

(* ----------------------------------------------------------------- *)
(*  1. each Fourier partial sum has zero mean over [0,2pi]            *)
(* ----------------------------------------------------------------- *)

Definition gterm (r : R) (k : nat) (θ : R) : R :=
  r ^ (S k) / (INR (S k)) ^ 2 * sin (INR (S k) * θ).
Definition Gfun (r : R) (N : nat) (θ : R) : R := sum_f_R0 (fun k => gterm r k θ) N.

Lemma gterm_deriv : forall r k θ, derivable_pt_lim (fun t => gterm r k t) θ (lterm θ k r).
Proof.
  intros r k θ. unfold gterm.
  pose proof (dsin_scaled (INR (S k)) θ) as Hs.
  apply (derivable_pt_lim_scal (fun t => sin (INR (S k) * t))
           (r ^ (S k) / (INR (S k)) ^ 2) θ (INR (S k) * cos (INR (S k) * θ))) in Hs.
  replace (r ^ (S k) / (INR (S k)) ^ 2 * (INR (S k) * cos (INR (S k) * θ)))
     with (lterm θ k r) in Hs
     by (unfold lterm; field; apply not_0_INR; lia).
  exact Hs.
Qed.

Lemma Gfun_deriv : forall r N θ, derivable_pt_lim (fun t => Gfun r N t) θ (lsum θ N r).
Proof.
  intros r N θ. induction N as [| N IH].
  - unfold Gfun, lsum. simpl. apply gterm_deriv.
  - unfold Gfun, lsum. rewrite !tech5.
    apply (derivable_pt_lim_plus (fun t => sum_f_R0 (fun k => gterm r k t) N)
             (fun t => gterm r (S N) t) θ); [ exact IH | apply gterm_deriv ].
Qed.

Lemma Gfun_0 : forall r N, Gfun r N 0 = 0.
Proof. intros r N. unfold Gfun. apply sum_eq_R0. intros k _. unfold gterm.
  replace (INR (S k) * 0) with 0 by ring. rewrite sin_0. ring. Qed.

Lemma Gfun_2PI : forall r N, Gfun r N (2 * PI) = 0.
Proof. intros r N. unfold Gfun. apply sum_eq_R0. intros k _. unfold gterm.
  replace (INR (S k) * (2 * PI)) with (0 + 2 * INR (S k) * PI) by ring.
  rewrite sin_period, sin_0. ring. Qed.

Lemma lterm_cont : forall r k θ, continuity_pt (fun t => lterm t k r) θ.
Proof. intros r k θ. unfold lterm. reg. Qed.

Lemma cont_sum : forall (g : nat -> R -> R) N θ,
  (forall k, continuity_pt (fun t => g k t) θ) ->
  continuity_pt (fun t => sum_f_R0 (fun k => g k t) N) θ.
Proof.
  intros g N θ Hg. induction N as [| N IH].
  - apply (Hg 0%nat).
  - change (continuity_pt (fun t => sum_f_R0 (fun k => g k t) N + g (S N) t) θ).
    apply continuity_pt_plus; [ exact IH | apply Hg ].
Qed.

Lemma lsum_cont : forall r N θ, continuity_pt (fun t => lsum t N r) θ.
Proof. intros r N θ. apply (cont_sum (fun k t => lterm t k r) N θ). intro k. apply lterm_cont. Qed.

Theorem int_lsum_zero : forall r N (pr : Riemann_integrable (fun θ => lsum θ N r) 0 (2 * PI)),
  RiemannInt pr = 0.
Proof.
  intros r N pr.
  assert (H2pi : 0 <= 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hanti : antiderivative (fun θ => lsum θ N r) (Gfun r N) 0 (2 * PI)).
  { split; [ | exact H2pi ]. intros x _.
    exists (exist (fun l => derivable_pt_lim (Gfun r N) x l) (lsum x N r) (Gfun_deriv r N x)).
    reflexivity. }
  rewrite (FTC_antideriv (fun θ => lsum θ N r) (Gfun r N) 0 (2 * PI) H2pi
             (fun x _ => lsum_cont r N x) pr Hanti).
  rewrite Gfun_2PI, Gfun_0. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  2. uniform-in-theta convergence (Weierstrass M-test)             *)
(* ----------------------------------------------------------------- *)

Definition msum (r : R) (N : nat) : R := sum_f_R0 (fun k => r ^ (S k)) N.

Lemma lterm_abs_le : forall θ r k, 0 <= r -> Rabs (lterm θ k r) <= r ^ (S k).
Proof.
  intros θ r k Hr. unfold lterm, Rdiv.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  rewrite Rabs_mult, Rabs_mult.
  assert (Hcos : Rabs (cos (INR (S k) * θ)) <= 1) by (apply Rabs_le; apply COS_bound).
  assert (Hinv : Rabs (/ INR (S k)) <= 1).
  { rewrite Rabs_right by (apply Rle_ge, Rlt_le, Rinv_0_lt_compat, Hpos).
    rewrite <- Rinv_1. apply Rinv_le_contravar; [ lra | ].
    rewrite <- INR_1; apply le_INR; lia. }
  assert (Hrpow : Rabs (r ^ S k) = r ^ S k)
    by (apply Rabs_right; apply Rle_ge; apply pow_le; exact Hr).
  rewrite Hrpow.
  replace (r ^ S k) with (1 * 1 * r ^ S k) at 2 by ring.
  apply Rmult_le_compat.
  - apply Rmult_le_pos; [ apply Rabs_pos | apply Rabs_pos ].
  - apply pow_le; exact Hr.
  - apply Rmult_le_compat; [ apply Rabs_pos | apply Rabs_pos | exact Hcos | exact Hinv ].
  - apply Rle_refl.
Qed.

Lemma msum_closed : forall r N, r <> 1 ->
  msum r N = r * (1 - r ^ (S N)) / (1 - r).
Proof.
  intros r N Hr. unfold msum.
  rewrite (sum_eq (fun k => r ^ S k) (fun k => r ^ k * r) N) by (intros i _; simpl; ring).
  rewrite <- (scal_sum (fun k => r ^ k) N r).
  rewrite (tech3 r N Hr). field. lra.
Qed.

Lemma lsum_S : forall θ r n, lsum θ (S n) r = lsum θ n r + lterm θ (S n) r.
Proof. intros θ r n. unfold lsum. rewrite tech5. reflexivity. Qed.

Lemma msum_S : forall r n, msum r (S n) = msum r n + r ^ (S (S n)).
Proof. intros r n. unfold msum. rewrite tech5. reflexivity. Qed.

(* the Cauchy increment bound: theta-independent, dominated by the majorant *)
Lemma shifted_diff_le : forall θ r N M, 0 <= r ->
  Rabs (lsum θ (M + N) r - lsum θ N r) <= msum r (M + N) - msum r N.
Proof.
  intros θ r N M Hr. induction M as [| M IH].
  - replace (0 + N)%nat with N by lia.
    replace (lsum θ N r - lsum θ N r) with 0 by ring. rewrite Rabs_R0. lra.
  - replace (S M + N)%nat with (S (M + N)) by lia.
    rewrite (lsum_S θ r (M + N)), (msum_S r (M + N)).
    replace (lsum θ (M + N) r + lterm θ (S (M + N)) r - lsum θ N r)
       with ((lsum θ (M + N) r - lsum θ N r) + lterm θ (S (M + N)) r) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    replace (msum r (M + N) + r ^ S (S (M + N)) - msum r N)
       with ((msum r (M + N) - msum r N) + r ^ S (S (M + N))) by ring.
    apply Rplus_le_compat; [ exact IH | apply lterm_abs_le; exact Hr ].
Qed.

(* the uniform tail bound *)
Lemma lsum_tail_bound : forall θ r N, 0 <= r < 1 ->
  Rabs (- (/2) * ln (1 - 2 * r * cos θ + r ^ 2) - lsum θ N r)
    <= r ^ (S (S N)) / (1 - r).
Proof.
  intros θ r N [Hr0 Hr1].
  set (L := - (/2) * ln (1 - 2 * r * cos θ + r ^ 2)).
  set (c := lsum θ N r).
  (* Un M := |lsum θ (M+N) r - c| -> |L - c| *)
  assert (HcvL : Un_cv (fun M => lsum θ (M + N) r) L)
    by (apply CV_shift'; apply log_geom_series; lra).
  assert (HcvU : Un_cv (fun M => Rabs (lsum θ (M + N) r - c)) (Rabs (L - c))).
  { intros eps Heps. destruct (HcvL eps Heps) as [P HP]. exists P. intros M HM.
    unfold R_dist.
    eapply Rle_lt_trans; [ apply Rabs_triang_inv2 | ].
    replace (lsum θ (M + N) r - c - (L - c)) with (lsum θ (M + N) r - L) by ring.
    specialize (HP M HM). unfold R_dist in HP.
    exact HP. }
  apply Rle_cv_lim with (Un := fun M => Rabs (lsum θ (M + N) r - c))
                        (Vn := fun _ => r ^ (S (S N)) / (1 - r)).
  - intro M. eapply Rle_trans; [ apply (shifted_diff_le θ r N M Hr0) | ].
    assert (Hne : r <> 1) by lra.
    assert (Hb : 0 <= r ^ (S (M + N))) by (apply pow_le; exact Hr0).
    rewrite (msum_closed r (M + N) Hne), (msum_closed r N Hne).
    replace (r * (1 - r ^ S (M + N)) / (1 - r) - r * (1 - r ^ S N) / (1 - r))
       with ((r * r ^ S N - r * r ^ S (M + N)) / (1 - r)) by (field; lra).
    replace (r ^ S (S N)) with (r * r ^ S N) by (symmetry; apply tech_pow_Rmult).
    unfold Rdiv. apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | ].
    assert (0 <= r * r ^ S (M + N)) by (apply Rmult_le_pos; [ exact Hr0 | exact Hb ]). lra.
  - exact HcvU.
  - intros eps Heps. exists 0%nat. intros. unfold R_dist. rewrite Rminus_diag, Rabs_R0. exact Heps.
Qed.

Lemma pow_tail_cv0 : forall r, 0 <= r < 1 -> Un_cv (fun N => r ^ (S (S N)) / (1 - r)) 0.
Proof.
  intros r [Hr0 Hr1].
  apply (Un_cv_ext (fun N => (/ (1 - r)) * (r * r * r ^ N))).
  - intro N. simpl. field. lra.
  - replace 0 with (/ (1 - r) * 0) by ring. apply CV_mult; [ apply CV_const | ].
    replace 0 with (r * r * 0) by ring. apply CV_mult; [ apply CV_const | ].
    apply pow_cv0. rewrite Rabs_right by lra. exact Hr1.
Qed.

Lemma lsum_unif : forall r, 0 <= r < 1 ->
  Unif_conv (fun N θ => lsum θ N r)
            (fun θ => - (/2) * ln (1 - 2 * r * cos θ + r ^ 2)) 0 (2 * PI).
Proof.
  intros r Hr eps Heps. destruct (pow_tail_cv0 r Hr eps Heps) as [N0 HN0].
  exists N0. intros N HN θ _.
  eapply Rle_trans; [ | ].
  2:{ specialize (HN0 N HN). unfold R_dist in HN0. rewrite Rminus_0_r in HN0.
      rewrite Rabs_right in HN0
        by (apply Rle_ge, Rmult_le_pos; [ apply pow_le; lra | apply Rlt_le, Rinv_0_lt_compat; lra ]).
      apply Rlt_le; exact HN0. }
  rewrite Rabs_minus_sym. apply lsum_tail_bound; exact Hr.
Qed.

(* ----------------------------------------------------------------- *)
(*  3. integrability of the log kernel + assembly                    *)
(* ----------------------------------------------------------------- *)

Lemma kernel_pos : forall r θ, 0 <= r < 1 -> 0 < 1 - 2 * r * cos θ + r ^ 2.
Proof.
  intros r θ [Hr0 Hr1].
  assert (Hc : -1 <= cos θ <= 1) by apply COS_bound.
  nra.
Qed.

Lemma logker_cont : forall r θ, 0 <= r < 1 ->
  continuity_pt (fun t => - (/2) * ln (1 - 2 * r * cos t + r ^ 2)) θ.
Proof.
  intros r θ Hr.
  apply continuity_pt_scal.
  apply (continuity_pt_comp (fun t => 1 - 2 * r * cos t + r ^ 2) ln).
  - reg.
  - apply derivable_continuous_pt.
    exists (/ (1 - 2 * r * cos θ + r ^ 2)).
    apply derivable_pt_lim_ln. apply kernel_pos; exact Hr.
Qed.

Definition logker_int (r : R) (Hr : 0 <= r < 1) :
  Riemann_integrable (fun θ => - (/2) * ln (1 - 2 * r * cos θ + r ^ 2)) 0 (2 * PI) :=
  continuity_implies_RiemannInt (Rlt_le _ _ (Rmult_lt_0_compat 2 PI Rlt_0_2 PI_RGT_0))
    (fun θ _ => logker_cont r θ Hr).

Definition lsum_int (r : R) (N : nat) :
  Riemann_integrable (fun θ => lsum θ N r) 0 (2 * PI) :=
  continuity_implies_RiemannInt (Rlt_le _ _ (Rmult_lt_0_compat 2 PI Rlt_0_2 PI_RGT_0))
    (fun θ _ => lsum_cont r N θ).

(* THE Jensen integral (in kernel form): int_0^{2pi} ln(1-2r cos + r^2) = 0 *)
Theorem jensen_log_kernel_integral : forall r (Hr : 0 <= r < 1),
  RiemannInt (logker_int r Hr) = 0.
Proof.
  intros r Hr.
  assert (Hcv : Un_cv (fun N => RiemannInt (lsum_int r N)) (RiemannInt (logker_int r Hr))).
  { apply (RiemannInt_unif_limit (fun N θ => lsum θ N r)
             (fun θ => - (/2) * ln (1 - 2 * r * cos θ + r ^ 2)) 0 (2 * PI)
             (Rlt_le _ _ (Rmult_lt_0_compat 2 PI Rlt_0_2 PI_RGT_0))
             (fun N => lsum_int r N) (logker_int r Hr)).
    apply lsum_unif; exact Hr. }
  assert (Hzero : forall N, RiemannInt (lsum_int r N) = 0) by (intro N; apply int_lsum_zero).
  apply (UL_sequence (fun N => RiemannInt (lsum_int r N))).
  - exact Hcv.
  - apply (Un_cv_ext (fun _ => 0)); [ intro N; symmetry; apply Hzero | apply CV_const ].
Qed.

Print Assumptions jensen_log_kernel_integral.
