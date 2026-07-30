(* ================================================================= *)
(*  GaussPiValue.v  —  Gaussian finale step 1b: ∫_ℝ e^{−πx²} = 1.      *)
(*                                                                    *)
(*  The normalised Gaussian, by scaling ∫_ℝ e^{−x²} = √π (GaussFull).  *)
(*  Substituting u = √π·t (cov_local, g = √π·t globally C¹) gives      *)
(*    √π·∫_{−A}^A e^{−πt²} dt = ∫_{−√π A}^{√π A} e^{−u²} du,             *)
(*  since e^{−(√π t)²} = e^{−πt²} and du = √π dt.  As A→∞ the right     *)
(*  side → √π (gauss_R along √π·√k → ∞), so                            *)
(*                                                                    *)
(*      ∫_ℝ e^{−πx²} = (1/√π)·√π = 1   (gauss_pi).                     *)
(*                                                                    *)
(*  This is the archimedean normalisation for the θ functional         *)
(*  equation.  No new axioms (classical Reals only).                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV GaussSubst GaussSqrtStep GaussImproper GaussValue
  GaussFull LocalCoV.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A RiemannInt scalar-out lemma (continuous integrand).            *)
(* ----------------------------------------------------------------- *)

Lemma RInt_scal_cont : forall (f : R -> R) (c : R) (a b : R), a <= b -> continuity f ->
  forall (prf : Riemann_integrable f a b) (prcf : Riemann_integrable (fun x => c * f x) a b),
  RiemannInt prcf = c * RiemannInt prf.
Proof.
  intros f c a b Hab Hcont prf prcf.
  pose proof (RiemannInt_P14 a b 0) as pr0.
  assert (pr3 : Riemann_integrable (fun x => fct_cte 0 x + c * f x) a b).
  { apply continuity_implies_RiemannInt; [ exact Hab | intros x _ ].
    apply continuity_pt_plus.
    - apply continuity_pt_const; intros u v; reflexivity.
    - apply (continuity_pt_scal f c x); apply Hcont. }
  pose proof (RiemannInt_P13 pr0 prf pr3) as HP13.
  rewrite (RiemannInt_P15 pr0) in HP13.
  assert (HE : RiemannInt prcf = RiemannInt pr3)
    by (apply RiemannInt_P18; [ exact Hab | intros x _; unfold fct_cte; ring ]).
  rewrite HE, HP13; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The normalised Gaussian.                                         *)
(* ----------------------------------------------------------------- *)

Definition exp_pi (x : R) : R := exp (- (PI * x ^ 2)).

Lemma cont_exp_pi : forall x, continuity_pt exp_pi x.
Proof.
  intro x; unfold exp_pi.
  apply (continuity_pt_comp (fun y => - (PI * y ^ 2)) exp x).
  - apply (continuity_pt_opp (fun y => PI * y ^ 2) x).
    apply (continuity_pt_scal (fun y => y ^ 2) PI x).
    apply (cont_pow (fun y => y) 2); apply cont_id.
  - apply derivable_continuous_pt; exists (exp (- (PI * x ^ 2))); apply derivable_pt_lim_exp.
Qed.

Lemma exp_pi_int : forall a b, Riemann_integrable exp_pi a b.
Proof.
  intros a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_exp_pi ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros x _; apply cont_exp_pi ].
Qed.

Lemma exp_sq_scale : forall t, exp_sq (sqrt PI * t) = exp_pi t.
Proof.
  intro t; unfold exp_sq, exp_pi; f_equal.
  assert (Hsp : sqrt PI * sqrt PI = PI) by (apply sqrt_sqrt; pose proof PI_RGT_0; lra).
  replace ((sqrt PI * t) ^ 2) with (sqrt PI * sqrt PI * t ^ 2) by ring.
  rewrite Hsp; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The scaling identity  √π·∫_{−A}^A e^{−πt²} = ∫_{−√π A}^{√π A} e^{−u²}. *)
(* ----------------------------------------------------------------- *)

Lemma gauss_scale : forall A, 0 <= A ->
  forall (prPi : Riemann_integrable exp_pi (- A) A)
         (prSq : Riemann_integrable exp_sq (- (sqrt PI * A)) (sqrt PI * A)),
  sqrt PI * RiemannInt prPi = RiemannInt prSq.
Proof.
  intros A HA prPi prSq.
  assert (Hsp : 0 < sqrt PI) by (apply sqrt_lt_R0; pose proof PI_RGT_0; lra).
  assert (Hsp0 : 0 <= sqrt PI) by lra.
  assert (Hab : - A <= A) by lra.
  set (g := fun t => sqrt PI * t).
  set (g' := fun _ : R => sqrt PI).
  assert (Hderiv : forall t, - A <= t <= A -> derivable_pt_lim g t (g' t)).
  { intros t _.
    assert (Hs : derivable_pt_lim g t (sqrt PI * 1))
      by exact (derivable_pt_lim_scal (fun s => s) (sqrt PI) t 1 (derivable_pt_lim_id t)).
    unfold g'; replace (sqrt PI) with (sqrt PI * 1) by ring; exact Hs. }
  assert (Hcont' : forall t, - A <= t <= A -> continuity_pt g' t)
    by (intros t _; apply continuity_pt_const; intros u v; reflexivity).
  assert (Hmap : forall t, - A <= t <= A -> g (- A) <= g t <= g (A)).
  { intros t [Ht1 Ht2]; unfold g; split; apply Rmult_le_compat_l; try exact Hsp0; lra. }
  assert (Hfc : forall u, g (- A) <= u <= g (A) -> continuity_pt exp_sq u)
    by (intros u _; apply cont_exp_sq).
  assert (prL : Riemann_integrable (fun t => exp_sq (g t) * g' t) (- A) A).
  { apply continuity_implies_RiemannInt; [ exact Hab | intros t Ht ].
    apply continuity_pt_mult; [ | apply continuity_pt_const; intros u v; reflexivity ].
    apply (continuity_pt_comp g exp_sq t);
      [ apply derivable_continuous_pt; exists (g' t); apply Hderiv; exact Ht | apply cont_exp_sq ]. }
  assert (prR : Riemann_integrable exp_sq (g (- A)) (g (A)))
    by (apply continuity_implies_RiemannInt;
        [ unfold g; apply Rmult_le_compat_l; [ exact Hsp0 | lra ] | intros u _; apply cont_exp_sq ]).
  (* RiemannInt prR = RiemannInt prSq (bounds g(±A) = ∓√π A) *)
  assert (HR : RiemannInt prR = RiemannInt prSq).
  { assert (HgmA : g (- A) = - (sqrt PI * A)) by (unfold g; ring).
    assert (HgA : g (A) = sqrt PI * A) by (unfold g; reflexivity).
    revert prR; rewrite HgmA, HgA; intro prR; apply RiemannInt_P5. }
  pose proof (cov_local g g' exp_sq (- A) A Hab Hderiv Hcont' Hmap Hfc prL prR) as Hcov.
  (* RiemannInt prL = √π · RiemannInt prPi *)
  assert (prPiScal : Riemann_integrable (fun t => sqrt PI * exp_pi t) (- A) A)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros t _ ];
        apply (continuity_pt_scal exp_pi (sqrt PI) t); apply cont_exp_pi).
  assert (HL : RiemannInt prL = sqrt PI * RiemannInt prPi).
  { assert (HLe : RiemannInt prL = RiemannInt prPiScal).
    { apply RiemannInt_P18; [ exact Hab | intros t _; unfold g, g'; rewrite exp_sq_scale; ring ]. }
    rewrite HLe.
    apply (RInt_scal_cont exp_pi (sqrt PI) (- A) A Hab (fun x => cont_exp_pi x) prPi prPiScal). }
  transitivity (RiemannInt prL); [ symmetry; exact HL | ].
  transitivity (RiemannInt prR); [ exact Hcov | exact HR ].
Qed.

(* ----------------------------------------------------------------- *)
(*  ∫_ℝ e^{−πx²} = 1.                                                *)
(* ----------------------------------------------------------------- *)

Lemma cv_infty_scale : forall c, 0 < c -> forall a, cv_infty a -> cv_infty (fun k => c * a k).
Proof.
  intros c Hc a Ha M.
  destruct (Ha (M / c)) as [N HN]; exists N; intros k Hk.
  pose proof (HN k Hk) as Hak.
  replace M with (c * (M / c)) by (field; apply Rgt_not_eq; exact Hc).
  apply Rmult_lt_compat_l; [ exact Hc | exact Hak ].
Qed.

Lemma gauss_pi_seq :
  forall (pr : forall k, Riemann_integrable exp_pi (- sqrt (INR k)) (sqrt (INR k))),
  Un_cv (fun k => RiemannInt (pr k)) 1.
Proof.
  intro pr.
  assert (Hsp : 0 < sqrt PI) by (apply sqrt_lt_R0; pose proof PI_RGT_0; lra).
  pose proof (gauss_R (fun k => sqrt PI * sqrt (INR k))
                (fun k => Rmult_le_pos _ _ (Rlt_le _ _ Hsp) (sqrt_pos _))
                (cv_infty_scale (sqrt PI) Hsp (fun k => sqrt (INR k)) cv_infty_sqrt)) as Hgr.
  assert (H1 : Un_cv (fun k => / sqrt PI * pintR exp_sq exp_sq_int (sqrt PI * sqrt (INR k))) 1).
  { replace 1 with (/ sqrt PI * sqrt PI) by (field; apply Rgt_not_eq; exact Hsp).
    apply (CV_mult (fun _ => / sqrt PI)
             (fun k => pintR exp_sq exp_sq_int (sqrt PI * sqrt (INR k))) (/ sqrt PI) (sqrt PI)).
    - intros eps He; exists 0%nat; intros n _; unfold R_dist; replace (/ sqrt PI - / sqrt PI) with 0 by ring;
        rewrite Rabs_R0; exact He.
    - exact Hgr. }
  apply (Un_cv_ext (fun k => / sqrt PI * pintR exp_sq exp_sq_int (sqrt PI * sqrt (INR k)))
                   (fun k => RiemannInt (pr k)) 1).
  - intro k; apply Rmult_eq_reg_l with (sqrt PI); [ | apply Rgt_not_eq; exact Hsp ].
    rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l by (apply Rgt_not_eq; exact Hsp).
    unfold pintR; symmetry;
      exact (gauss_scale (sqrt (INR k)) (sqrt_pos _) (pr k)
               (exp_sq_int (- (sqrt PI * sqrt (INR k))) (sqrt PI * sqrt (INR k)))).
  - exact H1.
Qed.

Theorem gauss_pi : ImproperCvR exp_pi exp_pi_int 1.
Proof.
  apply (improperR_welldef exp_pi exp_pi_int
           (fun x => Rlt_le _ _ (exp_pos (- (PI * x ^ 2))))
           (fun k => sqrt (INR k)) 1).
  - intro k; apply sqrt_pos.
  - exact cv_infty_sqrt.
  - exact (gauss_pi_seq (fun k => exp_pi_int (- sqrt (INR k)) (sqrt (INR k)))).
Qed.

Print Assumptions gauss_pi.

(* ================================================================= *)
(*  END GaussPiValue.v                                              *)
(*  ∫_ℝ e^{−πx²} = 1, the archimedean normalisation for the θ          *)
(*  functional equation.  Axiom-free.  Next: the Gaussian Fourier      *)
(*  self-duality, then Poisson summation → θ(1/t) = √t·θ(t).           *)
(* ================================================================= *)
