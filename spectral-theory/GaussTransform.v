(* ================================================================= *)
(*  GaussTransform.v  —  Leibniz-gap Phase 1 (cos side): the transform *)
(*  value F(ξ) = ∫_ℝ e^{−πx²}cos(2πxξ), via the Cauchy engine.         *)
(*                                                                    *)
(*  fcos ξ x = e^{−πx²}·cos(2πxξ).  The partial integrals              *)
(*  S_transform ξ k = ∫_{−k}^k fcos ξ have increments dominated by      *)
(*  those of D_k = ∫_{−k}^k e^{−πx²} (convergent, D_cv), because        *)
(*  |fcos| ≤ e^{−πx²} pointwise (|cos| ≤ 1).  cauchy_dominated_cv then  *)
(*  gives the limit F(ξ) with S_transform ξ k → F(ξ).                  *)
(*                                                                    *)
(*    transform_tail : |S_transform ξ i − S_transform ξ j| ≤ |D i − D j|;*)
(*    F_transform_cv : ∀ξ, S_transform ξ k → F_transform ξ.            *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst GaussFull GaussPiValue GaussCauchy.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The transform integrand and its integrability.                   *)
(* ----------------------------------------------------------------- *)

Definition fcos (xi : R) : R -> R := fun x => exp_pi x * cos (2 * PI * x * xi).

Lemma cont_fcos : forall xi, continuity (fcos xi).
Proof.
  intros xi x; unfold fcos; apply continuity_pt_mult; [ apply cont_exp_pi | ].
  apply (continuity_pt_comp (fun y => 2 * PI * y * xi) cos x); [ | apply continuity_cos ].
  apply continuity_pt_mult; [ | apply continuity_pt_const; intros u v; reflexivity ].
  apply (continuity_pt_scal (fun y => y) (2 * PI) x); apply cont_id.
Qed.

Lemma fcos_int : forall xi a b, Riemann_integrable (fcos xi) a b.
Proof.
  intros xi a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_fcos ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros x _; apply cont_fcos ].
Qed.

(* ----------------------------------------------------------------- *)
(*  |∫ fcos| ≤ ∫ e^{−πx²}  (|cos| ≤ 1).                              *)
(* ----------------------------------------------------------------- *)

Lemma abs_int_fcos_le : forall xi a b
  (prF : Riemann_integrable (fcos xi) a b)
  (prE : Riemann_integrable exp_pi a b),
  a <= b -> Rabs (RiemannInt prF) <= RiemannInt prE.
Proof.
  intros xi a b prF prE Hab.
  apply Rle_trans with (RiemannInt (RiemannInt_P16 prF)).
  - apply RiemannInt_P17; exact Hab.
  - apply RiemannInt_P19; [ exact Hab | intros x _ ].
    unfold fcos; rewrite Rabs_mult, (Rabs_pos_eq (exp_pi x)) by (unfold exp_pi; left; apply exp_pos).
    apply Rle_trans with (exp_pi x * 1); [ | rewrite Rmult_1_r; apply Rle_refl ].
    apply Rmult_le_compat_l; [ unfold exp_pi; left; apply exp_pos | ].
    pose proof (COS_bound (2 * PI * x * xi)) as [Hlo Hhi].
    unfold Rabs; destruct (Rcase_abs (cos (2 * PI * x * xi))); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The partial integrals and the dominating sequence.               *)
(* ----------------------------------------------------------------- *)

Definition S_transform (xi : R) (k : nat) : R := RiemannInt (fcos_int xi (- INR k) (INR k)).
Definition Dseq (k : nat) : R := RiemannInt (exp_pi_int (- INR k) (INR k)).

Lemma D_cv' : Un_cv Dseq 1.
Proof. exact D_cv. Qed.

(* ----------------------------------------------------------------- *)
(*  The tail bound.                                                  *)
(* ----------------------------------------------------------------- *)

Lemma transform_tail : forall xi i j, (i <= j)%nat ->
  Rabs (S_transform xi i - S_transform xi j) <= Rabs (Dseq i - Dseq j).
Proof.
  intros xi i j Hij.
  assert (HAB : INR i <= INR j) by (apply le_INR; exact Hij).
  assert (HA0 : 0 <= INR i) by apply pos_INR.
  assert (Hmm : - INR j <= - INR i) by lra.
  pose proof (RiemannInt_P26 (fcos_int xi (- INR j) (- INR i)) (fcos_int xi (- INR i) (INR i))
                (fcos_int xi (- INR j) (INR i))) as Hf1.
  pose proof (RiemannInt_P26 (fcos_int xi (- INR j) (INR i)) (fcos_int xi (INR i) (INR j))
                (fcos_int xi (- INR j) (INR j))) as Hf2.
  pose proof (RiemannInt_P26 (exp_pi_int (- INR j) (- INR i)) (exp_pi_int (- INR i) (INR i))
                (exp_pi_int (- INR j) (INR i))) as He1.
  pose proof (RiemannInt_P26 (exp_pi_int (- INR j) (INR i)) (exp_pi_int (INR i) (INR j))
                (exp_pi_int (- INR j) (INR j))) as He2.
  pose proof (abs_int_fcos_le xi (- INR j) (- INR i) (fcos_int xi (- INR j) (- INR i))
                (exp_pi_int (- INR j) (- INR i)) Hmm) as Habs1.
  pose proof (abs_int_fcos_le xi (INR i) (INR j) (fcos_int xi (INR i) (INR j))
                (exp_pi_int (INR i) (INR j)) HAB) as Habs2.
  assert (HDm : Dseq i <= Dseq j).
  { pose proof (pintR_mono exp_pi exp_pi_int
                  (fun x => Rlt_le _ _ (exp_pos (- (PI * x ^ 2)))) (INR i) (INR j) HA0 HAB) as Hpm.
    unfold pintR in Hpm; unfold Dseq; exact Hpm. }
  assert (Heq : S_transform xi i - S_transform xi j
              = - (RiemannInt (fcos_int xi (- INR j) (- INR i))
                   + RiemannInt (fcos_int xi (INR i) (INR j))))
    by (unfold S_transform; lra).
  assert (HDeq : RiemannInt (exp_pi_int (- INR j) (- INR i))
               + RiemannInt (exp_pi_int (INR i) (INR j)) = Dseq j - Dseq i)
    by (unfold Dseq; lra).
  assert (HRabsD : Rabs (Dseq i - Dseq j) = Dseq j - Dseq i)
    by (rewrite Rabs_minus_sym; apply Rabs_pos_eq; lra).
  rewrite Heq, Rabs_Ropp, HRabsD, <- HDeq.
  eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat; [ exact Habs1 | exact Habs2 ] ].
Qed.

Lemma transform_tail_sym : forall xi i j,
  Rabs (S_transform xi i - S_transform xi j) <= Rabs (Dseq i - Dseq j).
Proof.
  intros xi i j; destruct (Nat.le_ge_cases i j) as [H | H].
  - apply transform_tail; exact H.
  - rewrite (Rabs_minus_sym (S_transform xi i) (S_transform xi j)),
            (Rabs_minus_sym (Dseq i) (Dseq j)); apply transform_tail; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  The transform value F(ξ) and its convergence.                    *)
(* ----------------------------------------------------------------- *)

Definition F_transform (xi : R) : R :=
  proj1_sig (cauchy_dominated_cv (S_transform xi) Dseq 1 (transform_tail_sym xi) D_cv').

Theorem F_transform_cv : forall xi, Un_cv (S_transform xi) (F_transform xi).
Proof.
  intro xi; unfold F_transform.
  exact (proj2_sig (cauchy_dominated_cv (S_transform xi) Dseq 1 (transform_tail_sym xi) D_cv')).
Qed.

Print Assumptions F_transform_cv.

(* ================================================================= *)
(*  END GaussTransform.v (Phase 1 cos side)                         *)
(*  F(ξ) = ∫_ℝ e^{−πx²}cos(2πxξ) exists as the limit of ∫_{−k}^k, with  *)
(*  S_transform ξ k → F(ξ).  Next: the sin-derivative value g(ξ) with   *)
(*  the SAME structure (dominated by 2 E_k = 2 e^{−πk²}), then the       *)
(*  ξ-uniform tail (CVU) that feeds Phase 3's derivable_pt_lim_CVU.     *)
(* ================================================================= *)
