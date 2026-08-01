(* ================================================================= *)
(*  GaussCoeffTrue.v  —  Poisson→θ P3 step 8: the coefficient as the   *)
(*  integral of the TRUE limit Θ_t.                                   *)
(*                                                                    *)
(*  coeff_value gives  lim_M ∫₀¹ gTheta_partial(·,M)·cos(2πx m) dx     *)
(*                     = (1/√t) e^{−πm²/t}.                           *)
(*  gTheta_partial → Θ_t UNIFORMLY on [0,1] (geometric tail, dominated *)
(*  by 2(e^{−πt})ⁿ), so the M-limit passes inside the integral:        *)
(*     ∫₀¹ Θ_t(x)·cos(2πx m) dx = (1/√t) e^{−πm²/t}  (coeff_true).     *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals FunctionalExtensionality Lra Lia.
Require Import JacobiTheta GaussPeriodization GaussPeriodTotal GaussPeriodDeriv
        GaussCoeffValue FourierConverge.
Open Scope R_scope.

Section CoeffTrue.

Variable t : R.
Hypothesis Ht : 0 < t.

Lemma sum_f_R0_plus : forall (a b : nat -> R) N,
  sum_f_R0 (fun n => a n + b n) N = sum_f_R0 a N + sum_f_R0 b N.
Proof. intros a b N; induction N; cbn [sum_f_R0]; [ ring | rewrite IHN; ring ]. Qed.

Lemma gTheta_as_sum : forall x M,
  gTheta_partial t x M = sum_f_R0 (fun n => gR t x n + gL t x n) M.
Proof. intros x M; unfold gTheta_partial, gRp, gLp; rewrite sum_f_R0_plus; reflexivity. Qed.

Lemma qlt1 : exp (- (PI * t)) < 1. Proof. apply theta_ratio_lt1; exact Ht. Qed.
Lemma qnn : 0 <= exp (- (PI * t)). Proof. left; apply exp_pos. Qed.

Lemma gTheta_tail_bound : forall x M, 0 <= x <= 1 ->
  Rabs (GTheta t Ht x - gTheta_partial t x M)
  <= 2 * exp (- (PI * t)) ^ (S M) / (1 - exp (- (PI * t))).
Proof.
  intros x M [Hx0 Hx1]; rewrite gTheta_as_sum.
  apply (geom_tail_est (fun n => gR t x n + gL t x n) (GTheta t Ht x) 2 (exp (- (PI * t)))
           qnn qlt1 ltac:(lra)).
  - assert (Heq : sum_f_R0 (fun n => gR t x n + gL t x n) = gTheta_partial t x)
      by (apply functional_extensionality; intro M0; symmetry; apply gTheta_as_sum).
    rewrite Heq; apply GTheta_spec.
  - intro n; rewrite Rabs_right
      by (apply Rle_ge; apply Rplus_le_le_0_compat; [ unfold gR | unfold gL ]; left; apply exp_pos).
    pose proof (gR_le t x n Ht Hx0) as HR; pose proof (gL_le t x n Ht Hx0 Hx1) as HL; lra.
Qed.

Lemma tailseq_cv : Un_cv (fun M => 2 * exp (- (PI * t)) ^ (S M) / (1 - exp (- (PI * t)))) 0.
Proof.
  assert (Hw1 : 0 < 1 - exp (- (PI * t))) by (pose proof qlt1; lra).
  assert (Hab : Rabs (exp (- (PI * t))) < 1)
    by (rewrite Rabs_right by (apply Rle_ge; apply qnn); apply qlt1).
  replace (fun M => 2 * exp (- (PI * t)) ^ (S M) / (1 - exp (- (PI * t))))
    with (fun M => 2 / (1 - exp (- (PI * t))) * exp (- (PI * t)) ^ (S M))
    by (apply functional_extensionality; intro M; field; lra).
  apply Un_cv_scal0.
  intros eps He; destruct (pow_lt_1_zero (exp (- (PI * t))) Hab eps He) as [N HN].
  exists N; intros n Hn; unfold R_dist; rewrite Rminus_0_r; apply HN; lia.
Qed.

(* --- integrability of the two integrands --- *)

Lemma cont_cosm : forall m, continuity (fun x => cos (2 * PI * x * INR m)).
Proof.
  intros m x; apply (continuity_pt_comp (fun x => 2 * PI * x * INR m) cos x).
  - apply (continuity_pt_mult (fun x => 2 * PI * x) (fun _ => INR m) x).
    + apply (continuity_pt_scal (fun x => x) (2 * PI) x);
        apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
    + apply continuity_pt_const; intros a b; reflexivity.
  - apply continuity_cos.
Qed.

Lemma cont_gTheta_partial : forall M, continuity (fun x => gTheta_partial t x M).
Proof.
  intro M; unfold gTheta_partial, gRp, gLp; intro x.
  apply continuity_pt_plus;
    [ apply (cont_sum (fun k s => gR t s k) M); intro k; apply cont_gR
    | apply (cont_sum (fun k s => gL t s k) M); intro k; apply cont_gL ].
Qed.

Lemma prT : forall m M, Riemann_integrable (fun x => gTheta_partial t x M * cos (2 * PI * x * INR m)) 0 1.
Proof.
  intros m M; apply continuity_implies_RiemannInt; [ lra | intros x _ ];
    apply continuity_pt_mult; [ apply cont_gTheta_partial | apply cont_cosm ].
Qed.

Lemma pr_GTc : forall m, Riemann_integrable (fun x => GTheta t Ht x * cos (2 * PI * x * INR m)) 0 1.
Proof.
  intros m; apply continuity_implies_RiemannInt; [ lra | intros x _ ];
    apply continuity_pt_mult; [ apply (GTheta_cont t Ht) | apply cont_cosm ].
Qed.

(* --- the M→∞ / ∫ interchange --- *)

Theorem coeff_true : forall m (prh : Riemann_integrable (fun x => GTheta t Ht x * cos (2 * PI * x * INR m)) 0 1),
  RiemannInt prh = / sqrt t * exp (- (PI * INR m ^ 2 / t)).
Proof.
  intros m prh.
  pose proof (coeff_value t m Ht (prT m)) as Hcv1.
  assert (Hcv2 : Un_cv (fun M => RiemannInt (prT m M)) (RiemannInt prh)).
  { intros eps He; destruct (tailseq_cv eps He) as [N HN]; exists N; intros M HM.
    specialize (HN M HM); unfold R_dist in HN |- *; rewrite Rminus_0_r in HN.
    rewrite Rabs_right in HN by
      (apply Rle_ge; apply Rmult_le_pos; [ apply Rmult_le_pos;
         [ lra | apply pow_le; apply qnn ] | left; apply Rinv_0_lt_compat; pose proof qlt1; lra ]).
    apply Rle_lt_trans with (2 * exp (- (PI * t)) ^ S M / (1 - exp (- (PI * t)))); [ | exact HN ].
    set (dq := fun x => gTheta_partial t x M * cos (2 * PI * x * INR m)
                        - GTheta t Ht x * cos (2 * PI * x * INR m)).
    assert (prdq : Riemann_integrable dq 0 1)
      by (apply continuity_implies_RiemannInt; [ lra | intros x _; unfold dq;
          apply continuity_pt_minus; apply continuity_pt_mult;
          solve [ apply cont_gTheta_partial | apply cont_cosm | apply (GTheta_cont t Ht) ] ]).
    assert (Hlin : RiemannInt (prT m M) - RiemannInt prh = RiemannInt prdq).
    { assert (prg : Riemann_integrable
                (fun x => gTheta_partial t x M * cos (2 * PI * x * INR m)
                        + (-1) * (GTheta t Ht x * cos (2 * PI * x * INR m))) 0 1)
        by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
            [ apply continuity_pt_mult; [ apply cont_gTheta_partial | apply cont_cosm ]
            | apply (continuity_pt_scal (fun x => GTheta t Ht x * cos (2 * PI * x * INR m)) (-1) x);
              apply continuity_pt_mult; [ apply (GTheta_cont t Ht) | apply cont_cosm ] ] ]).
      pose proof (RiemannInt_P13 (prT m M) prh prg) as HP.
      assert (Hdg : RiemannInt prdq = RiemannInt prg)
        by (apply RiemannInt_P18; [ lra | intros x _; unfold dq; ring ]).
      rewrite Hdg, HP; ring. }
    rewrite Hlin.
    assert (prcst : Riemann_integrable
              (fun _ => 2 * exp (- (PI * t)) ^ S M / (1 - exp (- (PI * t)))) 0 1)
      by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_const;
          intros a b; reflexivity ]).
    apply Rle_trans with (RiemannInt (RiemannInt_P16 prdq)); [ apply RiemannInt_P17; lra | ].
    apply Rle_trans with (RiemannInt prcst).
    - apply RiemannInt_P19; [ lra | intros x [Hx0 Hx1]; unfold dq ].
      replace (gTheta_partial t x M * cos (2 * PI * x * INR m)
               - GTheta t Ht x * cos (2 * PI * x * INR m))
        with ((gTheta_partial t x M - GTheta t Ht x) * cos (2 * PI * x * INR m)) by ring.
      rewrite Rabs_mult.
      apply Rle_trans with (Rabs (gTheta_partial t x M - GTheta t Ht x) * 1).
      + apply Rmult_le_compat_l; [ apply Rabs_pos | pose proof (COS_bound (2 * PI * x * INR m)); apply Rabs_le; lra ].
      + rewrite Rmult_1_r, Rabs_minus_sym; apply gTheta_tail_bound; lra.
    - assert (Hval : RiemannInt prcst = 2 * exp (- (PI * t)) ^ S M / (1 - exp (- (PI * t))) * (1 - 0)).
      { pose proof (RiemannInt_P15 (RiemannInt_P14 0 1 (2 * exp (- (PI * t)) ^ S M / (1 - exp (- (PI * t)))))) as HP15.
        rewrite <- HP15; apply RiemannInt_P18; [ lra | intros x _; unfold fct_cte; reflexivity ]. }
      rewrite Hval; apply Req_le; ring. }
  exact (UL_sequence _ _ _ Hcv2 Hcv1).
Qed.

End CoeffTrue.

Print Assumptions coeff_true.

(* ================================================================= *)
(*  END GaussCoeffTrue.v                                             *)
(*  ∫₀¹ Θ_t(x)·cos(2πx m) dx = (1/√t) e^{−πm²/t}.                     *)
(* ================================================================= *)
