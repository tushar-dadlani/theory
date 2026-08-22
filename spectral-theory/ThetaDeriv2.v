(* ================================================================= *)
(*  ThetaDeriv2.v  --  Psi' is LIPSCHITZ.                              *)
(*                                                                    *)
(*    DPsi_lipschitz : 1/2 <= y -> 1/2 <= z ->                         *)
(*      |DPsi y - DPsi z| <= Md2 * |y - z|,   Md2 = 64/(1-e^{-pi/4})   *)
(*                                                                    *)
(*  This is exactly the shape midpoint_single asks for.  Note what it  *)
(*  does NOT ask for: a bound on Psi''.  MidpointQuad states its       *)
(*  second-order hypothesis as a Lipschitz condition on f' precisely   *)
(*  so that f'' need not exist -- and here that pays, because it means *)
(*  the twice-differentiated series never has to be summed into a      *)
(*  FUNCTION.  Only its uniform bound is needed, so the whole second   *)
(*  CVU pass of ThetaDeriv.v is avoided.                               *)
(*                                                                    *)
(*  The route: each FINITE partial dtheta_partial . N is Lipschitz     *)
(*  with constant Md2, by MVT_cor2 plus the second majorant            *)
(*  dtheta2_term_bound (pi^2 n^4 e^{-pi n^2 u} <= 64 q^n).  The        *)
(*  constant does not depend on N, so it survives the limit -- taken   *)
(*  two-sidedly through CV_minus, which avoids needing continuity of   *)
(*  Rabs.  Axiom-clean.                                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp ThetaDerivMajorant ThetaDeriv.
Open Scope R_scope.

Definition d2theta_term (t : R) (n : nat) : R :=
  PI ^ 2 * INR (S n) ^ 4 * exp (- (PI * INR (S n) ^ 2 * t)).
Definition d2theta_partial (t : R) (N : nat) : R := sum_f_R0 (d2theta_term t) N.
Definition Md2 : R := 64 / (1 - qd).

Lemma Md2_nonneg : 0 <= Md2.
Proof.
  pose proof qd_bounds as [H0 H1]. unfold Md2, Rdiv.
  apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
Qed.

Lemma d2theta_term_nonneg : forall t n, 0 <= d2theta_term t n.
Proof.
  intros t n. unfold d2theta_term. pose proof PI_RGT_0.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; [ nra | apply pow_le; apply pos_INR ].
  - left; apply exp_pos.
Qed.

Lemma d2theta_partial_nonneg : forall t N, 0 <= d2theta_partial t N.
Proof.
  intros t N. unfold d2theta_partial. induction N; cbn [sum_f_R0].
  - apply d2theta_term_nonneg.
  - pose proof (d2theta_term_nonneg t (S N)). lra.
Qed.

Lemma d2theta_partial_bound : forall t N, / 2 <= t -> d2theta_partial t N <= Md2.
Proof.
  intros t N Ht. pose proof qd_bounds as [Hq0 Hq1].
  unfold d2theta_partial, Md2.
  apply Rle_trans with (sum_f_R0 (fun k => 64 * qd ^ k) N).
  - apply sum_f_R0_le. intro i. unfold d2theta_term, qd.
    apply dtheta2_term_bound; exact Ht.
  - assert (E : sum_f_R0 (fun k => 64 * qd ^ k) N
              = 64 * sum_f_R0 (fun k => qd ^ k) N).
    { rewrite (scal_sum (fun k => qd ^ k) N 64). apply sum_eq; intros i _; ring. }
    rewrite E. unfold Rdiv.
    apply Rmult_le_compat_l; [ lra | apply geom_partial_bound; lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the partials, differentiated a second time                        *)
(* ----------------------------------------------------------------- *)
Lemma dtheta_partial_deriv : forall N x,
  derivable_pt_lim (fun u => dtheta_partial u N) x (- d2theta_partial x N).
Proof.
  intros N x. unfold dtheta_partial, d2theta_partial.
  rewrite <- (sum_f_R0_opp (d2theta_term x) N).
  apply (deriv_sum (fun k u => dtheta_term u k) (fun k u => - d2theta_term u k) N x).
  intro k. unfold dtheta_term, d2theta_term.
  replace (- (PI ^ 2 * INR (S k) ^ 4 * exp (- (PI * INR (S k) ^ 2 * x))))
    with (PI * INR (S k) ^ 2
          * (- (PI * INR (S k) ^ 2) * exp (- (PI * INR (S k) ^ 2 * x)))) by ring.
  apply (derivable_pt_lim_scal (fun u => exp (- (PI * INR (S k) ^ 2 * u)))
           (PI * INR (S k) ^ 2) x _).
  apply dexp_lin.
Qed.

(* ----------------------------------------------------------------- *)
(*  each finite partial is Lipschitz, with an N-free constant         *)
(* ----------------------------------------------------------------- *)
Lemma abs_le_inv : forall x a, Rabs x <= a -> - a <= x <= a.
Proof.
  intros x a H. split.
  - pose proof (Rle_abs (- x)) as H1. rewrite Rabs_Ropp in H1. lra.
  - pose proof (Rle_abs x). lra.
Qed.

Lemma dtheta_partial_lip : forall N y z, / 2 <= y -> / 2 <= z ->
  Rabs (dtheta_partial y N - dtheta_partial z N) <= Md2 * Rabs (y - z).
Proof.
  intros N y z Hy Hz.
  assert (Hgen : forall p q, / 2 <= p -> / 2 <= q -> p < q ->
    Rabs (dtheta_partial p N - dtheta_partial q N) <= Md2 * Rabs (p - q)).
  { intros p q Hp Hq Hpq.
    destruct (MVT_cor2 (fun u => dtheta_partial u N)
                (fun u => - d2theta_partial u N) p q Hpq
                (fun c _ => dtheta_partial_deriv N c)) as [c [Hc Hcr]].
    assert (Hc2 : / 2 <= c) by lra.
    assert (Hb : Rabs (- d2theta_partial c N) <= Md2).
    { rewrite Rabs_Ropp, Rabs_pos_eq;
        [ apply d2theta_partial_bound; exact Hc2 | apply d2theta_partial_nonneg ]. }
    replace (dtheta_partial p N - dtheta_partial q N)
      with (- (dtheta_partial q N - dtheta_partial p N)) by ring.
    rewrite Rabs_Ropp, Hc, Rabs_mult.
    replace (Rabs (p - q)) with (Rabs (q - p))
      by (rewrite <- (Rabs_Ropp (q - p)); f_equal; ring).
    apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hb ]. }
  destruct (Rtotal_order y z) as [H | [H | H]].
  - apply Hgen; assumption.
  - subst z. replace (dtheta_partial y N - dtheta_partial y N) with 0 by ring.
    rewrite Rabs_R0.
    apply Rmult_le_pos; [ apply Md2_nonneg | apply Rabs_pos ].
  - replace (dtheta_partial y N - dtheta_partial z N)
      with (- (dtheta_partial z N - dtheta_partial y N)) by ring.
    rewrite Rabs_Ropp.
    replace (Rabs (y - z)) with (Rabs (z - y))
      by (rewrite <- (Rabs_Ropp (z - y)); f_equal; ring).
    apply Hgen; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE THEOREM: the constant survives the limit                      *)
(* ----------------------------------------------------------------- *)
Theorem DPsi_lipschitz : forall y z, / 2 <= y -> / 2 <= z ->
  Rabs (DPsi y - DPsi z) <= Md2 * Rabs (y - z).
Proof.
  intros y z Hy Hz.
  pose proof (CV_minus (dtheta_partial y) (dtheta_partial z)
                (- DPsi y) (- DPsi z) (DPsi_spec y Hy) (DPsi_spec z Hz)) as Hcv.
  assert (Hup : - DPsi y - - DPsi z <= Md2 * Rabs (y - z)).
  { eapply Rle_cv_lim.
    2: exact Hcv.
    2: apply Un_cv_const'.
    intro N.
    pose proof (dtheta_partial_lip N y z Hy Hz) as HL.
    apply abs_le_inv in HL. destruct HL as [_ H2]. exact H2. }
  assert (Hlo : - (Md2 * Rabs (y - z)) <= - DPsi y - - DPsi z).
  { eapply Rle_cv_lim.
    2: apply Un_cv_const'.
    2: exact Hcv.
    intro N.
    pose proof (dtheta_partial_lip N y z Hy Hz) as HL.
    apply abs_le_inv in HL. destruct HL as [H1 _]. exact H1. }
  apply Rabs_le. lra.
Qed.

Print Assumptions d2theta_partial_bound.
Print Assumptions dtheta_partial_lip.
Print Assumptions DPsi_lipschitz.
