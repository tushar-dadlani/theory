(* ================================================================= *)
(*  ThetaDeriv.v  --  Psi is differentiable, termwise.                 *)
(*                                                                    *)
(*    Psi_derivable : 1 <= x -> derivable_pt_lim Psi x (DPsi x)        *)
(*    DPsi x  =  - sum_{n>=1} pi n^2 e^{-pi n^2 x}                     *)
(*    DPsi_abs_bound : 1/2 <= x -> |DPsi x| <= 4/(1 - e^{-pi/4})       *)
(*                                                                    *)
(*  Stage 4c.  The x-space integrand of XirIntegralReduction carries   *)
(*  Psi(e^x), and midpoint_single needs its derivative.  Psi is an     *)
(*  INFINITE sum, so differentiating it termwise is a theorem, not a   *)
(*  rewrite: it needs derivable_pt_lim_CVU, whose load-bearing         *)
(*  hypothesis is that the DIFFERENTIATED partials converge            *)
(*  UNIFORMLY on a ball.  That is what this file supplies.             *)
(*                                                                    *)
(*  The uniformity comes from ThetaDerivMajorant.dtheta_term_bound,    *)
(*  pi n^2 e^{-pi n^2 u} <= 4 q^n with q = e^{-pi/4}, valid for every  *)
(*  u >= 1/2 at once -- the bound does not depend on u, which is       *)
(*  exactly what makes the Weierstrass M-test applicable.  The tail    *)
(*  past N is then 4 q^{N+1}/(1-q), uniformly in u, and CVU falls out  *)
(*  of pow_lt_1_zero.                                                  *)
(*                                                                    *)
(*  Note that the limit function DPsi has to be CONSTRUCTED, not       *)
(*  merely asserted: derivable_pt_lim_CVU takes the limit as an        *)
(*  argument.  It is built the same way JacobiTheta builds theta --    *)
(*  growing_cv on the partial sums, which are increasing (the terms    *)
(*  are positive) and bounded (by the same majorant) -- and made TOTAL *)
(*  by an Rle_dec guard, so it can be fed to RiemannInt later.         *)
(*  Sign convention: dtheta_partial is the POSITIVE series, and        *)
(*  DPsi = - its limit.                                                *)
(*                                                                    *)
(*  Axiom-clean (functional extensionality is not used here).          *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 PSeries_reg Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp ThetaDerivMajorant.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the differentiated series and its limit                       *)
(* ----------------------------------------------------------------- *)

Definition dtheta_term (t : R) (n : nat) : R :=
  PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2 * t)).
Definition dtheta_partial (t : R) (N : nat) : R := sum_f_R0 (dtheta_term t) N.

Definition qd : R := exp (- (PI / 4)).
Definition Md : R := 4 / (1 - qd).

Lemma qd_bounds : 0 < qd < 1.
Proof. split; [ apply exp_pos | apply dtheta_ratio_lt1 ]. Qed.

Lemma dtheta_term_nonneg : forall t n, 0 <= dtheta_term t n.
Proof.
  intros t n. unfold dtheta_term. pose proof PI_RGT_0.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ].
  - left; apply exp_pos.
Qed.

Lemma dtheta_partial_growing : forall t, Un_growing (dtheta_partial t).
Proof.
  intros t N. unfold dtheta_partial. cbn [sum_f_R0].
  pose proof (dtheta_term_nonneg t (S N)). lra.
Qed.

Lemma dtheta_partial_bound : forall t N, / 2 <= t -> dtheta_partial t N <= Md.
Proof.
  intros t N Ht. pose proof qd_bounds as [Hq0 Hq1].
  unfold dtheta_partial, Md.
  apply Rle_trans with (sum_f_R0 (fun k => 4 * qd ^ k) N).
  - apply sum_f_R0_le. intro i. unfold dtheta_term, qd.
    apply dtheta_term_bound; exact Ht.
  - assert (E : sum_f_R0 (fun k => 4 * qd ^ k) N = 4 * sum_f_R0 (fun k => qd ^ k) N).
    { rewrite (scal_sum (fun k => qd ^ k) N 4). apply sum_eq; intros i _; ring. }
    rewrite E. unfold Rdiv.
    apply Rmult_le_compat_l; [ lra | ].
    apply geom_partial_bound; lra.
Qed.

Lemma dtheta_converges : forall t, / 2 <= t -> { L : R | Un_cv (dtheta_partial t) L }.
Proof.
  intros t Ht. apply growing_cv; [ apply dtheta_partial_growing | ].
  unfold has_ub, EUn, bound, is_upper_bound.
  exists Md. intros r [n ->]. apply dtheta_partial_bound; exact Ht.
Qed.

(* the TOTAL derivative function; negative, since Psi is decreasing *)
Definition DPsi (t : R) : R :=
  match Rle_dec (/ 2) t with
  | left H => - proj1_sig (dtheta_converges t H)
  | right _ => 0
  end.

Lemma DPsi_spec : forall t, / 2 <= t -> Un_cv (dtheta_partial t) (- DPsi t).
Proof.
  intros t Ht. unfold DPsi. destruct (Rle_dec (/ 2) t) as [H | H].
  - destruct (dtheta_converges t H) as [L HL]. simpl.
    replace (- - L) with L by ring. exact HL.
  - exfalso; lra.
Qed.

Lemma DPsi_range : forall t, / 2 <= t -> 0 <= - DPsi t <= Md.
Proof.
  intros t Ht. pose proof (DPsi_spec t Ht) as HL. split.
  - apply Rle_trans with (dtheta_partial t 0).
    + unfold dtheta_partial; cbn [sum_f_R0]. apply dtheta_term_nonneg.
    + apply (growing_ineq (dtheta_partial t));
        [ apply dtheta_partial_growing | exact HL ].
  - eapply Rle_cv_lim.
    + intro n. apply dtheta_partial_bound; exact Ht.
    + exact HL.
    + apply Un_cv_const'.
Qed.

Theorem DPsi_abs_bound : forall t, / 2 <= t -> Rabs (DPsi t) <= Md.
Proof.
  intros t Ht. pose proof (DPsi_range t Ht) as [H1 H2].
  rewrite Rabs_left1 by lra. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  each partial derivative IS the derivative of the partial      *)
(* ----------------------------------------------------------------- *)

Lemma dexp_lin : forall c x,
  derivable_pt_lim (fun u => exp (- (c * u))) x (- c * exp (- (c * x))).
Proof.
  intros c x.
  assert (Hin : derivable_pt_lim (fun u => - (c * u)) x (- c)).
  { assert (Hm : derivable_pt_lim (fun u => c * u) x (c * 1))
      by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
    replace (- c) with (- (c * 1)) by ring.
    apply derivable_pt_lim_opp; exact Hm. }
  pose proof (derivable_pt_lim_comp (fun u => - (c * u)) exp x
                (- c) (exp (- (c * x))) Hin (derivable_pt_lim_exp _)) as Hc.
  replace (- c * exp (- (c * x))) with (exp (- (c * x)) * - c) by ring.
  exact Hc.
Qed.

Lemma deriv_sum : forall (F F' : nat -> R -> R) N x,
  (forall k, derivable_pt_lim (fun s => F k s) x (F' k x)) ->
  derivable_pt_lim (fun s => sum_f_R0 (fun k => F k s) N) x
                   (sum_f_R0 (fun k => F' k x) N).
Proof.
  intros F F' N x H; induction N as [| N IH]; cbn [sum_f_R0].
  - apply H.
  - apply derivable_pt_lim_plus; [ exact IH | apply H ].
Qed.

Lemma sum_f_R0_opp : forall (A : nat -> R) N,
  sum_f_R0 (fun k => - A k) N = - sum_f_R0 A N.
Proof. intros A N; induction N; cbn [sum_f_R0]; lra. Qed.

Lemma theta_term_derives : forall n x,
  derivable_pt_lim (fun u => theta_term u n) x (- dtheta_term x n).
Proof.
  intros n x. unfold theta_term, dtheta_term.
  replace (- (PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2 * x))))
    with (- (PI * INR (S n) ^ 2) * exp (- (PI * INR (S n) ^ 2 * x))) by ring.
  apply dexp_lin.
Qed.

Lemma theta_partial_derives : forall N x,
  derivable_pt_lim (fun u => theta_partial u N) x (- dtheta_partial x N).
Proof.
  intros N x. unfold theta_partial, dtheta_partial.
  rewrite <- (sum_f_R0_opp (dtheta_term x) N).
  apply (deriv_sum (fun k u => theta_term u k) (fun k u => - dtheta_term u k) N x).
  intro k. apply theta_term_derives.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the uniform tail bound, and CVU                               *)
(* ----------------------------------------------------------------- *)

Definition dfn (N : nat) (u : R) : R := - dtheta_partial u N.

Lemma dtheta_partial_tail : forall t N M, / 2 <= t ->
  dtheta_partial t M <= dtheta_partial t N + 4 * qd ^ (S N) / (1 - qd).
Proof.
  intros t N M Ht. pose proof qd_bounds as [Hq0 Hq1].
  assert (HqN : 0 < qd ^ (S N)) by (apply pow_lt; exact Hq0).
  assert (Htail : 0 <= 4 * qd ^ (S N) / (1 - qd)).
  { unfold Rdiv. apply Rmult_le_pos;
      [ nra | left; apply Rinv_0_lt_compat; lra ]. }
  destruct (Nat.le_gt_cases M N) as [Hle | Hgt].
  - assert (dtheta_partial t M <= dtheta_partial t N)
      by (apply tech9; [ apply dtheta_partial_growing | exact Hle ]).
    lra.
  - unfold dtheta_partial. rewrite (tech2 (dtheta_term t) N M Hgt).
    apply Rplus_le_compat_l.
    apply Rle_trans with (sum_f_R0 (fun i => 4 * qd ^ (S N) * qd ^ i) (M - S N)).
    + apply sum_f_R0_le. intro i. unfold dtheta_term.
      eapply Rle_trans; [ apply (dtheta_term_bound t (S N + i) Ht) | ].
      unfold qd. rewrite pow_add. right; ring.
    + assert (E : sum_f_R0 (fun i => 4 * qd ^ (S N) * qd ^ i) (M - S N)
                = 4 * qd ^ (S N) * sum_f_R0 (fun i => qd ^ i) (M - S N)).
      { rewrite (scal_sum (fun i => qd ^ i) (M - S N) (4 * qd ^ (S N))).
        apply sum_eq; intros i _; ring. }
      rewrite E.
      assert (Hgp : sum_f_R0 (fun i => qd ^ i) (M - S N) <= / (1 - qd))
        by (apply geom_partial_bound; lra).
      unfold Rdiv. apply Rmult_le_compat_l; [ nra | exact Hgp ].
Qed.

Lemma DPsi_tail : forall t N, / 2 <= t ->
  - DPsi t <= dtheta_partial t N + 4 * qd ^ (S N) / (1 - qd).
Proof.
  intros t N Ht. eapply Rle_cv_lim.
  - intro M. apply (dtheta_partial_tail t N M Ht).
  - apply DPsi_spec; exact Ht.
  - apply Un_cv_const'.
Qed.

Theorem dtheta_CVU : forall c (r : posreal),
  (forall y : R, Boule c r y -> / 2 <= y) -> CVU dfn DPsi c r.
Proof.
  intros c r Hdom eps Heps. pose proof qd_bounds as [Hq0 Hq1].
  assert (Habs : Rabs qd < 1) by (rewrite Rabs_pos_eq; lra).
  assert (Hy : 0 < eps * (1 - qd) / 4) by (unfold Rdiv; nra).
  destruct (pow_lt_1_zero qd Habs _ Hy) as [N HN].
  exists N. intros n y Hn Hby.
  assert (Ht : / 2 <= y) by (apply Hdom; exact Hby).
  pose proof (DPsi_tail y n Ht) as Hup.
  pose proof (growing_ineq (dtheta_partial y) (- DPsi y)
                (dtheta_partial_growing y) (DPsi_spec y Ht) n) as Hlo.
  assert (Hsm : Rabs (qd ^ (S n)) < eps * (1 - qd) / 4) by (apply HN; lia).
  rewrite Rabs_pos_eq in Hsm by (apply pow_le; lra).
  unfold dfn.
  replace (DPsi y - - dtheta_partial y n)
    with (- (- DPsi y - dtheta_partial y n)) by ring.
  rewrite Rabs_Ropp, Rabs_pos_eq by lra.
  assert (Hfin : 4 * qd ^ (S n) / (1 - qd) < eps).
  { apply (Rmult_lt_reg_r (1 - qd)); [ lra | ].
    assert (E2 : 4 * qd ^ (S n) / (1 - qd) * (1 - qd) = 4 * qd ^ (S n))
      by (field; lra).
    rewrite E2. nra. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  continuity of the derivative partials (for CVU_continuity)    *)
(* ----------------------------------------------------------------- *)

Lemma dtheta_partial_derivable : forall N x,
  derivable_pt (fun u => dtheta_partial u N) x.
Proof.
  intros N x.
  exists (sum_f_R0 (fun k => PI * INR (S k) ^ 2
            * (- (PI * INR (S k) ^ 2) * exp (- (PI * INR (S k) ^ 2 * x)))) N).
  unfold dtheta_partial.
  apply (deriv_sum (fun k u => dtheta_term u k)
           (fun k u => PI * INR (S k) ^ 2
              * (- (PI * INR (S k) ^ 2) * exp (- (PI * INR (S k) ^ 2 * u)))) N x).
  intro k. unfold dtheta_term.
  apply (derivable_pt_lim_scal (fun u => exp (- (PI * INR (S k) ^ 2 * u)))
           (PI * INR (S k) ^ 2) x _).
  apply dexp_lin.
Qed.

Lemma cont_dfn : forall n y, continuity_pt (dfn n) y.
Proof.
  intros n y. apply derivable_continuous_pt.
  destruct (dtheta_partial_derivable n y) as [l Hl].
  exists (- l). unfold dfn. apply derivable_pt_lim_opp. exact Hl.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  pointwise convergence of the partials to Psi                  *)
(* ----------------------------------------------------------------- *)

Lemma Psi_is_limit : forall y (Hy : 0 < y), Un_cv (theta_partial y) (Psi y).
Proof.
  intros y Hy. rewrite (Psi_val y Hy). unfold theta.
  destruct (theta_half_converges y Hy) as [L HL]; simpl.
  replace ((1 + 2 * L - 1) / 2) with L by field. exact HL.
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  THE THEOREM                                                    *)
(* ----------------------------------------------------------------- *)

Lemma Hr4 : 0 < / 4. Proof. lra. Qed.
Definition r4 : posreal := mkposreal (/ 4) Hr4.

Theorem Psi_derivable : forall x, 1 <= x -> derivable_pt_lim Psi x (DPsi x).
Proof.
  intros x Hx.
  assert (Hdom : forall y : R, Boule x r4 y -> / 2 <= y).
  { intros y Hy. unfold Boule, r4 in Hy; simpl in Hy.
    destruct (Rabs_def2 _ _ Hy) as [H1 H2]. lra. }
  assert (Hcvu : CVU dfn DPsi x r4) by (apply dtheta_CVU; exact Hdom).
  apply (derivable_pt_lim_CVU (fun N u => theta_partial u N) dfn Psi DPsi x x r4).
  - unfold Boule, r4; simpl.
    replace (x - x) with 0 by ring; rewrite Rabs_R0; lra.
  - intros y n _. apply theta_partial_derives.
  - intros y Hy. apply Psi_is_limit.
    specialize (Hdom y Hy). lra.
  - exact Hcvu.
  - apply (CVU_continuity dfn DPsi x r4 Hcvu).
    intros n y _. apply cont_dfn.
Qed.

Print Assumptions DPsi_abs_bound.
Print Assumptions dtheta_CVU.
Print Assumptions Psi_derivable.
