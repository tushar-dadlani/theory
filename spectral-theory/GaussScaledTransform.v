(* ================================================================= *)
(*  GaussScaledTransform.v  —  Poisson→θ, Phase P1b: the SCALED        *)
(*  Gaussian cosine transform.                                        *)
(*                                                                    *)
(*    scaled_transform : ∫_ℝ e^{−πtx²}cos(2πxξ) dx = (1/√t)·e^{−πξ²/t}  *)
(*                                                                    *)
(*  (as the limit of ∫_{−N}^N over integer N).  Proof: substitute      *)
(*  u = √t·x (cov_local, g = √t·u), which turns the integrand into      *)
(*  (1/√t)·e^{−πv²}cos(2πv·(ξ/√t)) on bounds ±√t·N; then                *)
(*  Tpart_cv_all (P1a) carries the √t·N-bounded transform to            *)
(*  F(ξ/√t) = e^{−πξ²/t} (fourier_self_dual).  No new axioms.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst GaussPiValue GaussSqrtStep GaussTransform GaussFourier
  GaussSelfDual GaussCauchy LocalCoV GaussScaledTail.
Open Scope R_scope.

Theorem scaled_transform : forall t xi, 0 < t ->
  forall (pr : forall N, Riemann_integrable
                 (fun x => exp (- (PI * t * x ^ 2)) * cos (2 * PI * x * xi)) (- INR N) (INR N)),
  Un_cv (fun N => RiemannInt (pr N)) (/ sqrt t * exp (- (PI * xi ^ 2 / t))).
Proof.
  intros t xi Ht pr.
  set (rt := sqrt t).
  assert (Hrt : 0 < rt) by (unfold rt; apply sqrt_lt_R0; exact Ht).
  assert (Hrt2 : rt * rt = t) by (unfold rt; apply sqrt_sqrt; lra).
  set (xi' := xi / rt).
  set (g := fun u => rt * u).
  set (g' := fun _ : R => rt).
  set (f := fun v => / rt * fcos xi' v).
  assert (Hcov : forall N, RiemannInt (pr N) = / rt * Tpart xi' (rt * INR N)).
  { intro N.
    assert (Hab : - INR N <= INR N) by (pose proof (pos_INR N); lra).
    assert (Hderiv : forall u, - INR N <= u <= INR N -> derivable_pt_lim g u (g' u))
      by (intros u _; apply dscal).
    assert (Hcont' : forall u, - INR N <= u <= INR N -> continuity_pt g' u)
      by (intros u _; apply continuity_pt_const; intros a b; reflexivity).
    assert (Hmap : forall u, - INR N <= u <= INR N -> g (- INR N) <= g u <= g (INR N))
      by (intros u [Hu1 Hu2]; unfold g; split; apply Rmult_le_compat_l; solve [ left; exact Hrt | lra ]).
    assert (Hfc : forall v, g (- INR N) <= v <= g (INR N) -> continuity_pt f v)
      by (intros v _; unfold f; apply (continuity_pt_scal (fcos xi') (/ rt) v); apply cont_fcos).
    assert (prL : Riemann_integrable (fun u => f (g u) * g' u) (- INR N) (INR N)).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros u Hu ].
      apply continuity_pt_mult; [ | apply continuity_pt_const; intros a b; reflexivity ].
      apply (continuity_pt_comp g f u);
        [ apply derivable_continuous_pt; exists (g' u); apply Hderiv; exact Hu
        | unfold f; apply (continuity_pt_scal (fcos xi') (/ rt) (g u)); apply cont_fcos ]. }
    assert (prR : Riemann_integrable f (g (- INR N)) (g (INR N)))
      by (apply continuity_implies_RiemannInt;
          [ unfold g; apply Rmult_le_compat_l; [ left; exact Hrt | lra ]
          | intros v _; unfold f; apply (continuity_pt_scal (fcos xi') (/ rt) v); apply cont_fcos ]).
    pose proof (cov_local g g' f (- INR N) (INR N) Hab Hderiv Hcont' Hmap Hfc prL prR) as Hcv.
    assert (HL : RiemannInt (pr N) = RiemannInt prL).
    { apply RiemannInt_P18; [ exact Hab | intros u _; unfold f, g, g', fcos, exp_pi, xi' ].
      replace (PI * (rt * u) ^ 2) with (PI * t * u ^ 2) by (rewrite <- Hrt2; ring).
      replace (2 * PI * (rt * u) * (xi / rt)) with (2 * PI * u * xi) by (field; lra).
      field; lra. }
    assert (HR : RiemannInt prR = / rt * Tpart xi' (rt * INR N)).
    { assert (Hab' : g (- INR N) <= g (INR N))
        by (unfold g; apply Rmult_le_compat_l; [ left; exact Hrt | lra ]).
      assert (prF : Riemann_integrable (fcos xi') (g (- INR N)) (g (INR N)))
        by (apply continuity_implies_RiemannInt; [ exact Hab' | intros v _; apply (cont_fcos xi') ]).
      assert (HT : RiemannInt prF = Tpart xi' (rt * INR N)).
      { unfold Tpart.
        assert (Hgm : g (- INR N) = - (rt * INR N)) by (unfold g; ring).
        assert (HgP : g (INR N) = rt * INR N) by (unfold g; reflexivity).
        revert prF; rewrite Hgm, HgP; intro prF; apply RiemannInt_P5. }
      rewrite <- HT.
      exact (RInt_scal_cont (fcos xi') (/ rt) (g (- INR N)) (g (INR N)) Hab' (cont_fcos xi') prF prR). }
    rewrite HL, Hcv, HR; reflexivity. }
  assert (Hlim : Un_cv (fun N => / rt * Tpart xi' (rt * INR N)) (/ rt * F_transform xi')).
  { apply (CV_mult (fun _ => / rt) (fun N => Tpart xi' (rt * INR N)) (/ rt) (F_transform xi')).
    - intros e He; exists 0%nat; intros n _; unfold R_dist;
        replace (/ rt - / rt) with 0 by ring; rewrite Rabs_R0; exact He.
    - apply Tpart_cv_all; apply (cv_infty_scale rt Hrt (fun N => INR N) cv_infty_INR). }
  assert (Hval : / rt * F_transform xi' = / sqrt t * exp (- (PI * xi ^ 2 / t))).
  { rewrite (fourier_self_dual xi'); f_equal; f_equal; f_equal.
    unfold xi'; replace ((xi / rt) ^ 2) with (xi ^ 2 / (rt * rt)) by (field; lra).
    rewrite Hrt2; field; lra. }
  apply (Un_cv_ext (fun N => / rt * Tpart xi' (rt * INR N)) (fun N => RiemannInt (pr N))
           (/ sqrt t * exp (- (PI * xi ^ 2 / t)))).
  - intro N; symmetry; exact (Hcov N).
  - rewrite <- Hval; exact Hlim.
Qed.

Print Assumptions scaled_transform.

(* ================================================================= *)
(*  END GaussScaledTransform.v (P1 complete)                        *)
(*  ∫_ℝ e^{−πtx²}cos(2πxξ) = (1/√t)e^{−πξ²/t}.  This is the f̂_t(k) that  *)
(*  the periodization's Fourier coefficient c_k (P2) reduces to.       *)
(* ================================================================= *)
