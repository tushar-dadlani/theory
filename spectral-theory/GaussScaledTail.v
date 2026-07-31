(* ================================================================= *)
(*  GaussScaledTail.v  —  Poisson→θ, Phase P1a: the cosine transform    *)
(*  converges along EVERY A→∞ (not just integer bounds).              *)
(*                                                                    *)
(*  The scaling u = √t·x needed for the scaled Gaussian transform (P1b) *)
(*  sends integer bounds ±N to ±√t·N, which are not integers.  So we    *)
(*  first upgrade F_transform (proved as the limit of the integer-bound *)
(*  partials S_transform) to the limit along ANY sequence of real       *)
(*  bounds → ∞.  The key is an explicit, ξ-independent Gaussian tail:   *)
(*    |Tpart ξ a − Tpart ξ b| ≤ e^{−πa²}   (1 ≤ a ≤ b),                 *)
(*  from the exact antiderivative (GaussDeriv) — no measure theory.     *)
(*                                                                    *)
(*    cauchy_real_transfer : uniform Cauchy tail + convergence along    *)
(*        one A→∞  ⇒  convergence along every A→∞;                     *)
(*    Tpart_cv_all : ∀ b→∞, ∫_{−b}^{b} e^{−πx²}cos(2πxξ) → F(ξ).        *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst GaussFull GaussPiValue GaussDeriv GaussDerivValue GaussTransform.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  e^{−πa²} → 0 as a → ∞ (real bound).                             *)
(* ----------------------------------------------------------------- *)

Lemma exp_pi_small : forall eps, eps > 0 -> exists M, forall a, M <= a -> exp_pi a < eps.
Proof.
  intros eps He; pose proof PI_RGT_0 as HPI.
  exists (Rmax 2 ((/ eps - 1) / PI + 1)); intros a Ha.
  assert (Ha2 : 2 <= a) by (apply Rle_trans with (Rmax 2 ((/ eps - 1) / PI + 1)); [ apply Rmax_l | exact Ha ]).
  assert (Hae : (/ eps - 1) / PI + 1 <= a) by (apply Rle_trans with (Rmax 2 ((/ eps - 1) / PI + 1)); [ apply Rmax_r | exact Ha ]).
  assert (Haa : a < a ^ 2) by (replace (a ^ 2) with (a * a) by ring; nra).
  unfold exp_pi; rewrite exp_Ropp.
  apply Rlt_trans with (/ (1 + PI * a)).
  - apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat; [ nra | apply exp_pos ] | ].
    apply Rlt_le_trans with (1 + PI * a ^ 2); [ nra | pose proof (exp_ineq1_le (PI * a ^ 2)); lra ].
  - assert (Hgt : / eps < 1 + PI * a).
    { assert (Hlt : (/ eps - 1) / PI < a) by lra.
      pose proof (Rmult_lt_compat_r PI ((/ eps - 1) / PI) a HPI Hlt) as Hm.
      replace ((/ eps - 1) / PI * PI) with (/ eps - 1) in Hm by (field; lra); lra. }
    apply Rlt_le_trans with (/ / eps); [ | rewrite Rinv_inv; apply Rle_refl ].
    apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact He | nra ] | exact Hgt ].
Qed.

Lemma exp_pi_tail_cv0 : forall eps, eps > 0 -> exists M, forall a, M <= a -> exp_pi a / (PI * a) < eps.
Proof.
  intros eps He; pose proof PI_RGT_0 as HPI.
  destruct (exp_pi_small (PI * eps) ltac:(nra)) as [M0 HM0].
  exists (Rmax M0 1); intros a Ha.
  assert (Ha1 : 1 <= a) by (apply Rle_trans with (Rmax M0 1); [ apply Rmax_r | exact Ha ]).
  assert (HaM0 : M0 <= a) by (apply Rle_trans with (Rmax M0 1); [ apply Rmax_l | exact Ha ]).
  pose proof (HM0 a HaM0) as Hexp.
  assert (Hexp0 : 0 < exp_pi a) by (unfold exp_pi; apply exp_pos).
  apply Rle_lt_trans with (exp_pi a / PI).
  - unfold Rdiv; apply Rmult_le_compat_l; [ left; exact Hexp0 | apply Rinv_le_contravar; nra ].
  - unfold Rdiv; apply Rmult_lt_reg_r with PI; [ exact HPI | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Gaussian tail integrals ∫ e^{−πx²} ≤ e^{−πa²}/(2πa).             *)
(* ----------------------------------------------------------------- *)

Lemma exp_pi_tail : forall a b, 0 < a -> a <= b -> RiemannInt (exp_pi_int a b) <= exp_pi a / (2 * PI * a).
Proof.
  intros a b Ha Hab; pose proof PI_RGT_0 as HPI.
  assert (Ha2 : 0 < 2 * PI * a) by nra.
  assert (prDer : Riemann_integrable (fun x => 2 * PI * x * exp_pi x) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_deriv_integrand ]).
  assert (prD : Riemann_integrable (fun x => / (2 * PI * a) * (2 * PI * x * exp_pi x)) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
        apply (continuity_pt_scal (fun s => 2 * PI * s * exp_pi s) (/ (2 * PI * a)) x); apply cont_deriv_integrand ]).
  apply Rle_trans with (RiemannInt prD).
  - apply RiemannInt_P19; [ exact Hab | intros x [Hx1 Hx2] ].
    assert (Hx0 : 0 < exp_pi x) by (unfold exp_pi; apply exp_pos).
    apply Rmult_le_reg_r with (2 * PI * a); [ exact Ha2 | ].
    replace (/ (2 * PI * a) * (2 * PI * x * exp_pi x) * (2 * PI * a)) with (2 * PI * x * exp_pi x) by (field; nra).
    assert (Hprod : 0 <= (x - a) * exp_pi x) by (apply Rmult_le_pos; lra); nra.
  - rewrite (RInt_scal_cont (fun x => 2 * PI * x * exp_pi x) (/ (2 * PI * a)) a b Hab
              cont_deriv_integrand prDer prD), (gauss_deriv_ftc a b prDer Hab).
    assert (0 <= exp_pi b) by (left; unfold exp_pi; apply exp_pos).
    unfold Rdiv; rewrite (Rmult_comm (/ (2 * PI * a)) (exp_pi a - exp_pi b)).
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; nra | lra ].
Qed.

Lemma exp_pi_tail_neg : forall a b, 0 < a -> a <= b -> RiemannInt (exp_pi_int (- b) (- a)) <= exp_pi a / (2 * PI * a).
Proof.
  intros a b Ha Hab; pose proof PI_RGT_0 as HPI.
  assert (Ha2 : 0 < 2 * PI * a) by nra.
  assert (Hba : - b <= - a) by lra.
  assert (prDer : Riemann_integrable (fun x => - (2 * PI * x * exp_pi x)) (- b) (- a))
    by (apply continuity_implies_RiemannInt; [ exact Hba | intros x _; apply cont_neg_deriv_integrand ]).
  assert (prD : Riemann_integrable (fun x => / (2 * PI * a) * - (2 * PI * x * exp_pi x)) (- b) (- a))
    by (apply continuity_implies_RiemannInt; [ exact Hba | intros x _;
        apply (continuity_pt_scal (fun s => - (2 * PI * s * exp_pi s)) (/ (2 * PI * a)) x); apply cont_neg_deriv_integrand ]).
  apply Rle_trans with (RiemannInt prD).
  - apply RiemannInt_P19; [ exact Hba | intros x [Hx1 Hx2] ].
    assert (Hx0 : 0 < exp_pi x) by (unfold exp_pi; apply exp_pos).
    apply Rmult_le_reg_r with (2 * PI * a); [ exact Ha2 | ].
    replace (/ (2 * PI * a) * - (2 * PI * x * exp_pi x) * (2 * PI * a)) with (- (2 * PI * x * exp_pi x)) by (field; nra).
    assert (Hprod : 0 <= (- a - x) * exp_pi x) by (apply Rmult_le_pos; lra); nra.
  - rewrite (RInt_scal_cont (fun x => - (2 * PI * x * exp_pi x)) (/ (2 * PI * a)) (- b) (- a) Hba
              cont_neg_deriv_integrand prDer prD), (gauss_deriv_ftc2 (- b) (- a) prDer Hba),
      (exp_pi_even a), (exp_pi_even b).
    assert (0 <= exp_pi b) by (left; unfold exp_pi; apply exp_pos).
    unfold Rdiv; rewrite (Rmult_comm (/ (2 * PI * a)) (exp_pi a - exp_pi b)).
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; nra | lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The real-bound cosine partial integral and its uniform tail.     *)
(* ----------------------------------------------------------------- *)

Definition Tpart (xi A : R) : R := RiemannInt (fcos_int xi (- A) A).

Lemma Tpart_tail : forall xi a b, 1 <= a -> a <= b -> Rabs (Tpart xi a - Tpart xi b) <= exp_pi a / (PI * a).
Proof.
  intros xi a b Ha Hab; pose proof PI_RGT_0 as HPI.
  assert (Ha0 : 0 < a) by lra.
  assert (Hmm : - b <= - a) by lra.
  pose proof (RiemannInt_P26 (fcos_int xi (- b) (- a)) (fcos_int xi (- a) a) (fcos_int xi (- b) a)) as Hf1.
  pose proof (RiemannInt_P26 (fcos_int xi (- b) a) (fcos_int xi a b) (fcos_int xi (- b) b)) as Hf2.
  pose proof (abs_int_fcos_le xi (- b) (- a) (fcos_int xi (- b) (- a)) (exp_pi_int (- b) (- a)) Hmm) as Habs1.
  pose proof (abs_int_fcos_le xi a b (fcos_int xi a b) (exp_pi_int a b) Hab) as Habs2.
  pose proof (exp_pi_tail_neg a b Ha0 Hab) as Ht1.
  pose proof (exp_pi_tail a b Ha0 Hab) as Ht2.
  assert (Heq : Tpart xi a - Tpart xi b
              = - (RiemannInt (fcos_int xi (- b) (- a)) + RiemannInt (fcos_int xi a b)))
    by (unfold Tpart; lra).
  rewrite Heq, Rabs_Ropp.
  apply Rle_trans with (exp_pi a / (2 * PI * a) + exp_pi a / (2 * PI * a)).
  - eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat ];
      (eapply Rle_trans; [ eassumption | eassumption ]).
  - apply Req_le; field; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Uniform-Cauchy transfer: one sequence ⇒ all sequences.          *)
(* ----------------------------------------------------------------- *)

Lemma cauchy_real_transfer : forall (T : R -> R) (L : R) (phi : R -> R),
  (forall a b, 1 <= a -> a <= b -> Rabs (T a - T b) <= phi a) ->
  (forall eps, eps > 0 -> exists M, forall a, M <= a -> phi a < eps) ->
  forall (u : nat -> R), (forall k, 1 <= u k) -> cv_infty u -> Un_cv (fun k => T (u k)) L ->
  forall (b : nat -> R), cv_infty b -> Un_cv (fun k => T (b k)) L.
Proof.
  intros T L phi Htail Hphi u Hu1 Huinf HuL b Hbinf eps He.
  destruct (Hphi (eps / 2) ltac:(lra)) as [M HM].
  destruct (HuL (eps / 2) ltac:(lra)) as [K1 HK1].
  destruct (Huinf (Rmax M 1)) as [Nu HNu].
  set (k0 := max Nu K1).
  assert (Hu0M : Rmax M 1 < u k0) by (apply HNu; apply Nat.le_max_l).
  assert (Hu01 : 1 <= u k0) by (apply Rle_trans with (Rmax M 1); [ apply Rmax_r | left; exact Hu0M ]).
  assert (Hu0K : (K1 <= k0)%nat) by (apply Nat.le_max_r).
  pose proof (HK1 k0 Hu0K) as HL0; unfold R_dist in HL0.
  destruct (Hbinf (u k0)) as [Nb HNb].
  exists Nb; intros n Hn; unfold R_dist.
  assert (Hbn : u k0 < b n) by (apply HNb; exact Hn).
  apply Rle_lt_trans with (Rabs (T (b n) - T (u k0)) + Rabs (T (u k0) - L)).
  - replace (T (b n) - L) with ((T (b n) - T (u k0)) + (T (u k0) - L)) by ring; apply Rabs_triang.
  - apply Rlt_le_trans with (eps / 2 + eps / 2); [ | lra ].
    apply Rplus_lt_compat.
    + rewrite Rabs_minus_sym; apply Rle_lt_trans with (phi (u k0)); [ apply Htail; [ exact Hu01 | left; exact Hbn ] | ].
      apply HM; apply Rle_trans with (Rmax M 1); [ apply Rmax_l | left; exact Hu0M ].
    + exact HL0.
Qed.

(* ----------------------------------------------------------------- *)
(*  The transform converges along every A → ∞.                       *)
(* ----------------------------------------------------------------- *)

Lemma Tpart_cv_all : forall xi (b : nat -> R), cv_infty b ->
  Un_cv (fun k => Tpart xi (b k)) (F_transform xi).
Proof.
  intros xi b Hbinf.
  apply (cauchy_real_transfer (Tpart xi) (F_transform xi) (fun a => exp_pi a / (PI * a))
           (Tpart_tail xi) exp_pi_tail_cv0 (fun k => INR (S k))).
  - intro k; rewrite S_INR; pose proof (pos_INR k); lra.
  - intro M; destruct (INR_unbounded M) as [N HN]; exists N; intros n Hn;
      apply Rlt_le_trans with (INR N); [ exact HN | rewrite S_INR; pose proof (le_INR N n Hn); lra ].
  - (* Un_cv (fun k => Tpart xi (INR (S k))) (F_transform xi) *)
    intros eps He; destruct (F_transform_cv xi eps He) as [Np HNp]; exists Np; intros n Hn.
    unfold Tpart; exact (HNp (S n) (le_S _ _ Hn)).
  - exact Hbinf.
Qed.

Print Assumptions Tpart_cv_all.

(* ================================================================= *)
(*  END GaussScaledTail.v (P1a)                                     *)
(*  ∫_{−A}^{A} e^{−πx²}cos(2πxξ) → F(ξ) along every A → ∞.  Next (P1b): *)
(*  substitute u = √t·x to land the scaled transform value            *)
(*  ∫_ℝ e^{−πtx²}cos(2πxξ) = (1/√t) e^{−πξ²/t}.                        *)
(* ================================================================= *)
