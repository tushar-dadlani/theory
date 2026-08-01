(* ================================================================= *)
(*  GaussThetaTransform.v  —  Poisson→θ P3 CAPSTONE:                   *)
(*     θ(1/t) = √t · θ(t).                                            *)
(*                                                                    *)
(*  Fourier inversion of the periodization at 0 (fourier_pointwise_loc *)
(*  with the localiser gloc) gives  S_N ftil(0) → ftil(0) = θ(t).      *)
(*  At x=0 every sine vanishes and every cosine is 1, so               *)
(*     S_N ftil(0) = acoef 0/2 + Σ_{k=1}^N acoef k                     *)
(*                 = (1/√t)(1 + 2 Σ_{k=1}^N e^{−πk²/t})               *)
(*  (acoef_value).  Passing N→∞, the inner sum is θ(1/t)'s lattice     *)
(*  sum, so  θ(t) = (1/√t) θ(1/t),  i.e.  θ(1/t) = √t θ(t).           *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import JacobiTheta GaussPeriodTotal GaussPeriodDeriv2 FourierKernelRep
        DirichletKernel FourierConvergeLoc FourierLocalizeGauss GaussFourierCoeff.
Open Scope R_scope.

Section Transform.

Variable t : R.
Hypothesis Ht : 0 < t.
Notation Cft := (ftil_cont t Ht).

Definition ee (k : nat) : R := exp (- (PI * INR k ^ 2 / t)).

(* --- Rsum algebra --- *)

Lemma Rsum_ext : forall (f g : nat -> R) N, (forall k, f k = g k) -> Rsum f N = Rsum g N.
Proof. intros f g N H; induction N; cbn [Rsum]; [ reflexivity | rewrite IHN, H; reflexivity ]. Qed.

Lemma Rsum_scal : forall (f : nat -> R) (c : R) N, Rsum (fun k => c * f k) N = c * Rsum f N.
Proof. intros f c N; induction N; cbn [Rsum]; [ ring | rewrite IHN; ring ]. Qed.

Lemma sum_f_R0_ext : forall (f g : nat -> R) N, (forall k, f k = g k) -> sum_f_R0 f N = sum_f_R0 g N.
Proof. intros f g N H; induction N; cbn [sum_f_R0]; [ apply H | rewrite IHN, H; reflexivity ]. Qed.

Lemma Rsum_S_sum : forall (f : nat -> R) M, Rsum f (S M) = sum_f_R0 (fun k => f (S k)) M.
Proof.
  intros f M; induction M.
  - simpl; ring.
  - change (Rsum f (S (S M))) with (Rsum f (S M) + f (S (S M))).
    rewrite IHM; cbn [sum_f_R0]; ring.
Qed.

(* --- S_N ftil (0) in closed form --- *)

Lemma SN_ftil_at_0 : forall N,
  SN (ftil t Ht) Cft N 0 = / sqrt t * (1 + 2 * Rsum ee N).
Proof.
  intro N; unfold SN.
  assert (Hsum : Rsum (fun k => acoef (ftil t Ht) Cft k * cos (INR k * 0)
                              + bcoef (ftil t Ht) Cft k * sin (INR k * 0)) N
                 = 2 * / sqrt t * Rsum ee N).
  { rewrite (Rsum_ext _ (fun k => 2 * / sqrt t * ee k)).
    - apply Rsum_scal.
    - intro k; rewrite Rmult_0_r, cos_0, sin_0, Rmult_1_r, Rmult_0_r, Rplus_0_r.
      rewrite (acoef_value t Ht k); unfold ee; ring. }
  rewrite Hsum.
  rewrite (acoef_value t Ht 0).
  replace (- (PI * INR 0 ^ 2 / t)) with 0
    by (simpl; field; apply Rgt_not_eq; exact Ht).
  rewrite exp_0.
  field; apply Rgt_not_eq; apply sqrt_lt_R0; exact Ht.
Qed.

(* --- P3 endpoint --- *)

Theorem theta_transform_limit :
  Un_cv (fun N => / sqrt t * (1 + 2 * Rsum ee N)) (theta t Ht).
Proof.
  pose proof (fourier_pointwise_loc (ftil t Ht) Cft 0 (gloc t Ht) (gloc_identity t Ht)) as Hfp.
  rewrite (ftil_at_0 t Ht) in Hfp.
  intros eps He; destruct (Hfp eps He) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); rewrite <- (SN_ftil_at_0 n); exact HN.
Qed.

(* --- the inner sum converges to θ(1/t)'s half-sum --- *)

Lemma ee_S : forall k, ee (S k) = theta_term (/ t) k.
Proof.
  intro k; unfold ee, theta_term; reflexivity.
Qed.

Lemma Rsum_ee_cv : forall (H1t : 0 < / t),
  Un_cv (fun N => Rsum ee N) (proj1_sig (theta_half_converges (/ t) H1t)).
Proof.
  intro H1t; destruct (theta_half_converges (/ t) H1t) as [L HL]; simpl.
  intros eps He; destruct (HL eps He) as [N0 H0]; exists (S N0); intros n Hn.
  destruct n as [| m]; [ lia | ].
  rewrite Rsum_S_sum, (sum_f_R0_ext (fun k => ee (S k)) (theta_term (/ t)) m ee_S).
  apply H0; lia.
Qed.

(* --- the capstone --- *)

Theorem theta_transform : forall (H1t : 0 < / t),
  theta (/ t) H1t = sqrt t * theta t Ht.
Proof.
  intro H1t; pose proof (sqrt_lt_R0 t Ht) as Hst.
  set (L := proj1_sig (theta_half_converges (/ t) H1t)).
  assert (Hlim2 : Un_cv (fun N => / sqrt t * (1 + 2 * Rsum ee N)) (/ sqrt t * theta (/ t) H1t)).
  { assert (Hcv : Un_cv (fun N => 1 + 2 * Rsum ee N) (1 + 2 * L)).
    { apply (CV_plus (fun _ => 1) (fun N => 2 * Rsum ee N) 1 (2 * L)).
      - intros e He; exists 0%nat; intros; unfold R_dist;
          replace (1 - 1) with 0 by ring; rewrite Rabs_R0; exact He.
      - apply (CV_mult (fun _ => 2) (fun N => Rsum ee N) 2 L).
        + intros e He; exists 0%nat; intros; unfold R_dist;
            replace (2 - 2) with 0 by ring; rewrite Rabs_R0; exact He.
        + apply Rsum_ee_cv. }
    replace (/ sqrt t * theta (/ t) H1t) with (/ sqrt t * (1 + 2 * L))
      by (unfold theta, L; reflexivity).
    apply (CV_mult (fun _ => / sqrt t) (fun N => 1 + 2 * Rsum ee N) (/ sqrt t) (1 + 2 * L)).
    - intros e He; exists 0%nat; intros; unfold R_dist;
        replace (/ sqrt t - / sqrt t) with 0 by ring; rewrite Rabs_R0; exact He.
    - exact Hcv. }
  assert (Heq : theta t Ht = / sqrt t * theta (/ t) H1t)
    by (apply (UL_sequence (fun N => / sqrt t * (1 + 2 * Rsum ee N)));
        [ apply theta_transform_limit | exact Hlim2 ]).
  apply Rmult_eq_reg_l with (/ sqrt t);
    [ | apply Rinv_neq_0_compat; apply Rgt_not_eq; exact Hst ].
  rewrite <- Rmult_assoc, Rinv_l by (apply Rgt_not_eq; exact Hst).
  rewrite Rmult_1_l, <- Heq; reflexivity.
Qed.

End Transform.

Print Assumptions theta_transform.

(* ================================================================= *)
(*  END GaussThetaTransform.v  —  Poisson→θ P3 COMPLETE.              *)
(*     θ(1/t) = √t · θ(t).                                            *)
(* ================================================================= *)
