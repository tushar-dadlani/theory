(* ================================================================= *)
(*  PsiXDeriv.v  --  the x-space derivative of Psi(e^x).               *)
(*                                                                    *)
(*    GPsi x := Psi (exp x)      DG x := DPsi (exp x) * exp x          *)
(*                                                                    *)
(*    GPsi_deriv     : 0 <= x -> derivable_pt_lim GPsi x (DG x)        *)
(*    DG_bound       : 0 <= x -> |DG x| <= 2/(1-q)                     *)
(*    DG_lipschitz   : 0 <= x -> 0 <= y ->                             *)
(*                       |DG x - DG y| <= 18/(1-q) * |x - y|           *)
(*                                                                    *)
(*  Why not just compose DPsi_bound / DPsi_lipschitz with the chain    *)
(*  rule?  Because the composition is where all the sharpness dies.    *)
(*  |DG| <= |DPsi(u)| . u would use sup|DPsi| (attained near u = 1/2)  *)
(*  times sup u = e^L = 5, and the Lipschitz constant would pick up    *)
(*  e^{2L} = 25 -- multiplying the worst case of Psi'' by the largest  *)
(*  u, when in fact Psi'' is ~10^{-6} there.  For the t = 16 sign      *)
(*  change that route inflates the midpoint constant by 2200x: 44000   *)
(*  quadrature nodes instead of 940.                                   *)
(*                                                                    *)
(*  Bounding a u e^{-a u} and (a u)^2 e^{-a u} DIRECTLY (majorants     *)
(*  xterm_bound / xterm2_bound) keeps u inside the exponent where it   *)
(*  belongs and costs nothing: the same half-split works, with u       *)
(*  simply riding along inside v = a u.                                *)
(*                                                                    *)
(*  As in ThetaDeriv2, the Lipschitz bound needs no third CVU pass:    *)
(*  the finite partials are Lipschitz with an N-free constant by       *)
(*  MVT_cor2, and the constant survives the limit.  Axiom-clean.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp ThetaDerivMajorant ThetaDeriv ThetaDeriv2.
Open Scope R_scope.

Definition GPsi (x : R) : R := Psi (exp x).
Definition DG (x : R) : R := DPsi (exp x) * exp x.

Definition gterm (x : R) (n : nat) : R :=
  PI * INR (S n) ^ 2 * exp x * exp (- (PI * INR (S n) ^ 2 * exp x)).
Definition gpartial (x : R) (N : nat) : R := sum_f_R0 (gterm x) N.

Definition gterm' (x : R) (n : nat) : R :=
  (PI * INR (S n) ^ 2 * exp x - (PI * INR (S n) ^ 2 * exp x) ^ 2)
    * exp (- (PI * INR (S n) ^ 2 * exp x)).
Definition g2partial (x : R) (N : nat) : R := sum_f_R0 (gterm' x) N.

Definition Kg1 : R := 2 / (1 - qd).
Definition Kg2 : R := 18 / (1 - qd).

Lemma exp_ge_1 : forall x, 0 <= x -> 1 <= exp x.
Proof. intros x Hx. rewrite <- exp_0. apply exp_le_compat; exact Hx. Qed.

Lemma Kg1_nonneg : 0 <= Kg1.
Proof.
  pose proof qd_bounds as [H0 H1]. unfold Kg1, Rdiv.
  apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
Qed.

Lemma Kg2_nonneg : 0 <= Kg2.
Proof.
  pose proof qd_bounds as [H0 H1]. unfold Kg2, Rdiv.
  apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the partials, and their limit                                 *)
(* ----------------------------------------------------------------- *)
Lemma gpartial_eq : forall x N, gpartial x N = dtheta_partial (exp x) N * exp x.
Proof.
  intros x N. unfold gpartial, dtheta_partial.
  induction N; cbn [sum_f_R0].
  - unfold gterm, dtheta_term. ring.
  - rewrite IHN.
    assert (E : gterm x (S N) = dtheta_term (exp x) (S N) * exp x)
      by (unfold gterm, dtheta_term; ring).
    rewrite E. ring.
Qed.

Lemma gpartial_cv : forall x, 0 <= x -> Un_cv (gpartial x) (- DG x).
Proof.
  intros x Hx.
  assert (Hu : / 2 <= exp x) by (pose proof (exp_ge_1 x Hx); lra).
  assert (Hcv : Un_cv (fun N => dtheta_partial (exp x) N * exp x)
                  (- DPsi (exp x) * exp x))
    by (apply CV_mult; [ apply DPsi_spec; exact Hu | apply Un_cv_const' ]).
  assert (E : - DG x = - DPsi (exp x) * exp x) by (unfold DG; ring).
  rewrite E.
  intros eps He. destruct (Hcv eps He) as [N HN]. exists N. intros n Hn.
  rewrite gpartial_eq. apply HN; exact Hn.
Qed.

Lemma gterm_nonneg : forall x n, 0 <= gterm x n.
Proof.
  intros x n. unfold gterm. pose proof PI_RGT_0.
  apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ].
Qed.

Lemma gpartial_nonneg : forall x N, 0 <= gpartial x N.
Proof.
  intros x N. unfold gpartial. induction N; cbn [sum_f_R0].
  - apply gterm_nonneg.
  - pose proof (gterm_nonneg x (S N)). lra.
Qed.

Lemma gpartial_bound : forall x N, 0 <= x -> gpartial x N <= Kg1.
Proof.
  intros x N Hx. pose proof qd_bounds as [Hq0 Hq1].
  pose proof (exp_ge_1 x Hx) as He1.
  unfold gpartial, Kg1.
  apply Rle_trans with (sum_f_R0 (fun k => 2 * qd ^ k) N).
  - apply sum_f_R0_le. intro i. unfold gterm, qd.
    apply xterm_bound; exact He1.
  - assert (E : sum_f_R0 (fun k => 2 * qd ^ k) N
              = 2 * sum_f_R0 (fun k => qd ^ k) N).
    { rewrite (scal_sum (fun k => qd ^ k) N 2). apply sum_eq; intros i _; ring. }
    rewrite E. unfold Rdiv.
    apply Rmult_le_compat_l; [ lra | apply geom_partial_bound; lra ].
Qed.

Theorem DG_bound : forall x, 0 <= x -> Rabs (DG x) <= Kg1.
Proof.
  intros x Hx. pose proof (gpartial_cv x Hx) as Hcv.
  assert (Hlo : 0 <= - DG x).
  { apply Rle_trans with (gpartial x 0); [ apply gpartial_nonneg | ].
    apply (growing_ineq (gpartial x)); [ | exact Hcv ].
    intro N. unfold gpartial. cbn [sum_f_R0].
    pose proof (gterm_nonneg x (S N)). lra. }
  assert (Hhi : - DG x <= Kg1).
  { eapply Rle_cv_lim.
    2: exact Hcv.
    2: apply Un_cv_const'.
    intro N. apply gpartial_bound; exact Hx. }
  rewrite Rabs_left1 by lra. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  differentiating the partials in x                             *)
(* ----------------------------------------------------------------- *)
Lemma gterm_deriv : forall n x, derivable_pt_lim (fun s => gterm s n) x (gterm' x n).
Proof.
  intros n x. unfold gterm, gterm'. set (c := PI * INR (S n) ^ 2).
  assert (H1 : derivable_pt_lim (fun s => c * exp s) x (c * exp x))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_exp).
  assert (H2 : derivable_pt_lim (fun s => exp (- (c * exp s))) x
                 (exp (- (c * exp x)) * - (c * exp x))).
  { apply (derivable_pt_lim_comp (fun s => - (c * exp s)) exp x
             (- (c * exp x)) (exp (- (c * exp x)))).
    - apply derivable_pt_lim_opp; exact H1.
    - apply derivable_pt_lim_exp. }
  pose proof (derivable_pt_lim_mult (fun s => c * exp s)
                (fun s => exp (- (c * exp s))) x
                (c * exp x) (exp (- (c * exp x)) * - (c * exp x)) H1 H2) as Hm.
  replace ((c * exp x - (c * exp x) ^ 2) * exp (- (c * exp x)))
    with (c * exp x * exp (- (c * exp x))
          + c * exp x * (exp (- (c * exp x)) * - (c * exp x))) by ring.
  exact Hm.
Qed.

Lemma gpartial_deriv : forall N x,
  derivable_pt_lim (fun s => gpartial s N) x (g2partial x N).
Proof.
  intros N x. unfold gpartial, g2partial.
  apply (deriv_sum (fun k s => gterm s k) (fun k s => gterm' s k) N x).
  intro k. apply gterm_deriv.
Qed.

Lemma sum_f_R0_abs : forall (A : nat -> R) N,
  Rabs (sum_f_R0 A N) <= sum_f_R0 (fun i => Rabs (A i)) N.
Proof.
  intros A N. induction N; cbn [sum_f_R0].
  - apply Rle_refl.
  - eapply Rle_trans; [ apply Rabs_triang | ]. lra.
Qed.

Lemma gterm'_abs_bound : forall x n, 0 <= x -> Rabs (gterm' x n) <= 18 * qd ^ n.
Proof.
  intros x n Hx. pose proof (exp_ge_1 x Hx) as He1.
  assert (Hmaj : (( PI * INR (S n) ^ 2 * exp x) ^ 2 + PI * INR (S n) ^ 2 * exp x)
                   * exp (- (PI * INR (S n) ^ 2 * exp x)) <= 18 * qd ^ n)
    by (unfold qd; apply xterm2_bound; exact He1).
  set (w := PI * INR (S n) ^ 2 * exp x) in *.
  assert (Hw : 0 <= w).
  { unfold w. pose proof PI_RGT_0.
    apply Rmult_le_pos; [ | left; apply exp_pos ].
    apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ]. }
  assert (He : 0 < exp (- w)) by apply exp_pos.
  unfold gterm'. fold w.
  apply Rabs_le. split; nra.
Qed.

Lemma g2partial_abs_bound : forall x N, 0 <= x -> Rabs (g2partial x N) <= Kg2.
Proof.
  intros x N Hx. pose proof qd_bounds as [Hq0 Hq1].
  unfold g2partial, Kg2.
  eapply Rle_trans; [ apply sum_f_R0_abs | ].
  apply Rle_trans with (sum_f_R0 (fun k => 18 * qd ^ k) N).
  - apply sum_f_R0_le. intro i. apply gterm'_abs_bound; exact Hx.
  - assert (E : sum_f_R0 (fun k => 18 * qd ^ k) N
              = 18 * sum_f_R0 (fun k => qd ^ k) N).
    { rewrite (scal_sum (fun k => qd ^ k) N 18). apply sum_eq; intros i _; ring. }
    rewrite E. unfold Rdiv.
    apply Rmult_le_compat_l; [ lra | apply geom_partial_bound; lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Lipschitz, uniformly in N, then in the limit                  *)
(* ----------------------------------------------------------------- *)
Lemma gpartial_lip : forall N x y, 0 <= x -> 0 <= y ->
  Rabs (gpartial x N - gpartial y N) <= Kg2 * Rabs (x - y).
Proof.
  intros N x y Hx Hy.
  assert (Hgen : forall p q, 0 <= p -> 0 <= q -> p < q ->
    Rabs (gpartial p N - gpartial q N) <= Kg2 * Rabs (p - q)).
  { intros p q Hp Hq Hpq.
    destruct (MVT_cor2 (fun s => gpartial s N) (fun s => g2partial s N) p q Hpq
                (fun c _ => gpartial_deriv N c)) as [c [Hc Hcr]].
    assert (Hc0 : 0 <= c) by lra.
    replace (gpartial p N - gpartial q N)
      with (- (gpartial q N - gpartial p N)) by ring.
    rewrite Rabs_Ropp, Hc, Rabs_mult.
    replace (Rabs (p - q)) with (Rabs (q - p))
      by (rewrite <- (Rabs_Ropp (q - p)); f_equal; ring).
    apply Rmult_le_compat_r;
      [ apply Rabs_pos | apply g2partial_abs_bound; exact Hc0 ]. }
  destruct (Rtotal_order x y) as [H | [H | H]].
  - apply Hgen; assumption.
  - subst y. replace (gpartial x N - gpartial x N) with 0 by ring.
    rewrite Rabs_R0. apply Rmult_le_pos; [ apply Kg2_nonneg | apply Rabs_pos ].
  - replace (gpartial x N - gpartial y N)
      with (- (gpartial y N - gpartial x N)) by ring.
    rewrite Rabs_Ropp.
    replace (Rabs (x - y)) with (Rabs (y - x))
      by (rewrite <- (Rabs_Ropp (y - x)); f_equal; ring).
    apply Hgen; assumption.
Qed.

Theorem DG_lipschitz : forall x y, 0 <= x -> 0 <= y ->
  Rabs (DG x - DG y) <= Kg2 * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  pose proof (CV_minus (gpartial x) (gpartial y) (- DG x) (- DG y)
                (gpartial_cv x Hx) (gpartial_cv y Hy)) as Hcv.
  assert (Hup : - DG x - - DG y <= Kg2 * Rabs (x - y)).
  { eapply Rle_cv_lim.
    2: exact Hcv.
    2: apply Un_cv_const'.
    intro N. pose proof (gpartial_lip N x y Hx Hy) as HL.
    apply abs_le_inv in HL. destruct HL as [_ H2]. exact H2. }
  assert (Hlo : - (Kg2 * Rabs (x - y)) <= - DG x - - DG y).
  { eapply Rle_cv_lim.
    2: apply Un_cv_const'.
    2: exact Hcv.
    intro N. pose proof (gpartial_lip N x y Hx Hy) as HL.
    apply abs_le_inv in HL. destruct HL as [H1 _]. exact H1. }
  apply Rabs_le. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the chain rule                                                *)
(* ----------------------------------------------------------------- *)
Theorem GPsi_deriv : forall x, 0 <= x -> derivable_pt_lim GPsi x (DG x).
Proof.
  intros x Hx. unfold GPsi, DG.
  apply (derivable_pt_lim_comp exp Psi x (exp x) (DPsi (exp x))).
  - apply derivable_pt_lim_exp.
  - apply Psi_derivable. apply exp_ge_1; exact Hx.
Qed.

Print Assumptions DG_bound.
Print Assumptions DG_lipschitz.
Print Assumptions GPsi_deriv.
