(* ================================================================= *)
(*  GaussDerivValue.v  —  Leibniz-gap Phase 1 (sin side): the          *)
(*  derivative value g(ξ) = ∫_ℝ −2πx e^{−πx²}sin(2πxξ), and the         *)
(*  ξ-UNIFORM tail (the CVU input for Phase 3).                        *)
(*                                                                    *)
(*  fsin ξ x = −2πx·e^{−πx²}·sin(2πxξ) = ∂_ξ(e^{−πx²}cos(2πxξ)).        *)
(*  Its |·| is dominated by the EXACT tail 2πx e^{−πx²} (Phase 0), so   *)
(*  the partial integrals S_deriv ξ k = ∫_{−k}^k fsin ξ have increments *)
(*  dominated by 2 E_k = 2 e^{−πk²} (convergent, E_cv), giving the      *)
(*  limit g(ξ).  Because the dominating tail is ξ-INDEPENDENT, the      *)
(*  bound |g ξ − S_deriv ξ n| ≤ |2 E_n − 2 L| holds UNIFORMLY in ξ —    *)
(*  exactly the CVU hypothesis derivable_pt_lim_CVU wants (Phase 3).    *)
(*                                                                    *)
(*    deriv_tail   : |S_deriv ξ i − S_deriv ξ j| ≤ |2 E_i − 2 E_j|;     *)
(*    g_deriv_cv   : ∀ξ, S_deriv ξ k → g_deriv ξ;                       *)
(*    g_deriv_cvu  : ∀ε>0 ∃N ∀n≥N ∀ξ, |g_deriv ξ − S_deriv ξ n| < ε.    *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV GaussSubst GaussFull GaussPiValue GaussDeriv GaussCauchy.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The derivative integrand, evenness, and the second FTC.          *)
(* ----------------------------------------------------------------- *)

Definition fsin (xi : R) : R -> R := fun x => - (2 * PI * x * exp_pi x) * sin (2 * PI * x * xi).

Lemma exp_pi_even : forall x, exp_pi (- x) = exp_pi x.
Proof. intro x; unfold exp_pi; f_equal; ring. Qed.

Lemma cont_fsin : forall xi, continuity (fsin xi).
Proof.
  intros xi x; unfold fsin; apply continuity_pt_mult.
  - apply (continuity_pt_opp (fun y => 2 * PI * y * exp_pi y) x); apply cont_deriv_integrand.
  - apply (continuity_pt_comp (fun y => 2 * PI * y * xi) sin x); [ | apply continuity_sin ].
    apply continuity_pt_mult; [ | apply continuity_pt_const; intros u v; reflexivity ].
    apply (continuity_pt_scal (fun y => y) (2 * PI) x); apply cont_id.
Qed.

Lemma fsin_int : forall xi a b, Riemann_integrable (fsin xi) a b.
Proof.
  intros xi a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_fsin ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros x _; apply cont_fsin ].
Qed.

Lemma dexp_pi' : forall x, derivable_pt_lim exp_pi x (- (2 * PI * x * exp_pi x)).
Proof. intro x; replace (- (2 * PI * x * exp_pi x)) with (- (2 * PI * x) * exp_pi x) by ring; apply dexp_pi. Qed.

Lemma cont_neg_deriv_integrand : continuity (fun x => - (2 * PI * x * exp_pi x)).
Proof. intro x; apply (continuity_pt_opp (fun y => 2 * PI * y * exp_pi y) x); apply cont_deriv_integrand. Qed.

Lemma gauss_deriv_ftc2 : forall a b
  (pr : Riemann_integrable (fun x => - (2 * PI * x * exp_pi x)) a b),
  a <= b -> RiemannInt pr = exp_pi b - exp_pi a.
Proof.
  intros a b pr Hab.
  assert (Hanti : antiderivative (fun x => - (2 * PI * x * exp_pi x)) exp_pi a b).
  { split; [ | exact Hab ]. intros t Ht.
    exists (exist _ (- (2 * PI * t * exp_pi t)) (dexp_pi' t)); reflexivity. }
  rewrite (FTC_antideriv (fun x => - (2 * PI * x * exp_pi x)) exp_pi a b Hab
             (fun x _ => cont_neg_deriv_integrand x) pr Hanti); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  |∫ fsin| bounds on sign-definite intervals.                      *)
(* ----------------------------------------------------------------- *)

Lemma abs_int_fsin_pos : forall xi a b (prF : Riemann_integrable (fsin xi) a b),
  0 <= a -> a <= b -> Rabs (RiemannInt prF) <= exp_pi a - exp_pi b.
Proof.
  intros xi a b prF Ha Hab.
  assert (prD : Riemann_integrable (fun x => 2 * PI * x * exp_pi x) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_deriv_integrand ]).
  apply Rle_trans with (RiemannInt (RiemannInt_P16 prF)); [ apply RiemannInt_P17; exact Hab | ].
  apply Rle_trans with (RiemannInt prD); [ | rewrite (gauss_deriv_ftc a b prD Hab); apply Rle_refl ].
  apply RiemannInt_P19; [ exact Hab | intros x [Hx1 Hx2] ].
  assert (Hx : 0 <= x) by lra.
  assert (Hpos : 0 <= 2 * PI * x * exp_pi x).
  { apply Rmult_le_pos; [ apply Rmult_le_pos; [ pose proof PI_RGT_0; lra | exact Hx ] |
                          left; unfold exp_pi; apply exp_pos ]. }
  unfold fsin; rewrite Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (2 * PI * x * exp_pi x)) by exact Hpos.
  apply Rle_trans with (2 * PI * x * exp_pi x * 1); [ | rewrite Rmult_1_r; apply Rle_refl ].
  apply Rmult_le_compat_l; [ exact Hpos | ].
  pose proof (SIN_bound (2 * PI * x * xi)) as [Hlo Hhi].
  unfold Rabs; destruct (Rcase_abs (sin (2 * PI * x * xi))); lra.
Qed.

Lemma abs_int_fsin_neg : forall xi a b (prF : Riemann_integrable (fsin xi) a b),
  b <= 0 -> a <= b -> Rabs (RiemannInt prF) <= exp_pi b - exp_pi a.
Proof.
  intros xi a b prF Hb Hab.
  assert (prD : Riemann_integrable (fun x => - (2 * PI * x * exp_pi x)) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_neg_deriv_integrand ]).
  apply Rle_trans with (RiemannInt (RiemannInt_P16 prF)); [ apply RiemannInt_P17; exact Hab | ].
  apply Rle_trans with (RiemannInt prD); [ | rewrite (gauss_deriv_ftc2 a b prD Hab); apply Rle_refl ].
  apply RiemannInt_P19; [ exact Hab | intros x [Hx1 Hx2] ].
  assert (Hx : x <= 0) by lra.
  assert (Hexpos : 0 < exp_pi x) by (unfold exp_pi; apply exp_pos).
  assert (Hneg : 2 * PI * x * exp_pi x <= 0).
  { pose proof PI_RGT_0 as Hp. assert (H2px : 2 * PI * x <= 0) by nra. nra. }
  unfold fsin; rewrite Rabs_mult, Rabs_Ropp, (Rabs_left1 (2 * PI * x * exp_pi x)) by exact Hneg.
  apply Rle_trans with (- (2 * PI * x * exp_pi x) * 1); [ | rewrite Rmult_1_r; apply Rle_refl ].
  apply Rmult_le_compat_l; [ lra | ].
  pose proof (SIN_bound (2 * PI * x * xi)) as [Hlo Hhi].
  unfold Rabs; destruct (Rcase_abs (sin (2 * PI * x * xi))); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Partial integrals, tail bound, and the value g.                  *)
(* ----------------------------------------------------------------- *)

Definition S_deriv (xi : R) (k : nat) : R := RiemannInt (fsin_int xi (- INR k) (INR k)).

Lemma deriv_tail : forall xi i j, (i <= j)%nat ->
  Rabs (S_deriv xi i - S_deriv xi j) <= Rabs (2 * exp_pi (INR i) - 2 * exp_pi (INR j)).
Proof.
  intros xi i j Hij.
  assert (HAB : INR i <= INR j) by (apply le_INR; exact Hij).
  assert (HA0 : 0 <= INR i) by apply pos_INR.
  assert (Hmm : - INR j <= - INR i) by lra.
  assert (Hni : - INR i <= 0) by lra.
  pose proof (RiemannInt_P26 (fsin_int xi (- INR j) (- INR i)) (fsin_int xi (- INR i) (INR i))
                (fsin_int xi (- INR j) (INR i))) as Hf1.
  pose proof (RiemannInt_P26 (fsin_int xi (- INR j) (INR i)) (fsin_int xi (INR i) (INR j))
                (fsin_int xi (- INR j) (INR j))) as Hf2.
  pose proof (abs_int_fsin_neg xi (- INR j) (- INR i) (fsin_int xi (- INR j) (- INR i)) Hni Hmm) as Habs1.
  pose proof (abs_int_fsin_pos xi (INR i) (INR j) (fsin_int xi (INR i) (INR j)) HA0 HAB) as Habs2.
  rewrite (exp_pi_even (INR i)), (exp_pi_even (INR j)) in Habs1.
  assert (Heq : S_deriv xi i - S_deriv xi j
              = - (RiemannInt (fsin_int xi (- INR j) (- INR i))
                   + RiemannInt (fsin_int xi (INR i) (INR j))))
    by (unfold S_deriv; lra).
  assert (HRabs : Rabs (2 * exp_pi (INR i) - 2 * exp_pi (INR j)) = 2 * exp_pi (INR i) - 2 * exp_pi (INR j)).
  { apply Rabs_pos_eq; pose proof (exp_pi_decr (INR i) (INR j) HA0 HAB); lra. }
  rewrite Heq, Rabs_Ropp, HRabs.
  eapply Rle_trans; [ apply Rabs_triang | lra ].
Qed.

Lemma deriv_tail_sym : forall xi i j,
  Rabs (S_deriv xi i - S_deriv xi j) <= Rabs (2 * exp_pi (INR i) - 2 * exp_pi (INR j)).
Proof.
  intros xi i j; destruct (Nat.le_ge_cases i j) as [H | H].
  - apply deriv_tail; exact H.
  - rewrite (Rabs_minus_sym (S_deriv xi i) (S_deriv xi j)),
            (Rabs_minus_sym (2 * exp_pi (INR i)) (2 * exp_pi (INR j))); apply deriv_tail; exact H.
Qed.

Definition Lg : R := 2 * proj1_sig E_cv.

Lemma E2_cv : Un_cv (fun k => 2 * exp_pi (INR k)) Lg.
Proof.
  unfold Lg; apply (CV_mult (fun _ => 2) (fun k => exp_pi (INR k)) 2 (proj1_sig E_cv)).
  - intros eps He; exists 0%nat; intros n _; unfold R_dist; replace (2 - 2) with 0 by ring;
      rewrite Rabs_R0; exact He.
  - exact (proj2_sig E_cv).
Qed.

Definition g_deriv (xi : R) : R :=
  proj1_sig (cauchy_dominated_cv (S_deriv xi) (fun k => 2 * exp_pi (INR k)) Lg (deriv_tail_sym xi) E2_cv).

Theorem g_deriv_cv : forall xi, Un_cv (S_deriv xi) (g_deriv xi).
Proof.
  intro xi; unfold g_deriv.
  exact (proj2_sig (cauchy_dominated_cv (S_deriv xi) (fun k => 2 * exp_pi (INR k)) Lg (deriv_tail_sym xi) E2_cv)).
Qed.

(* ----------------------------------------------------------------- *)
(*  The ξ-uniform tail (CVU input).                                  *)
(* ----------------------------------------------------------------- *)

Lemma deriv_uniform_tail : forall xi n,
  Rabs (S_deriv xi n - g_deriv xi) <= Rabs (2 * exp_pi (INR n) - Lg).
Proof.
  intros xi n.
  (* a m = |S_deriv ξ n − S_deriv ξ m| → |S_deriv ξ n − g ξ|;
     b m = |2 E n − 2 E m|          → |2 E n − Lg|;  a(m'+n) ≤ b(m'+n). *)
  apply Rle_cv_lim with
    (Un := fun m => Rabs (S_deriv xi n - S_deriv xi (m + n)%nat))
    (Vn := fun m => Rabs (2 * exp_pi (INR n) - 2 * exp_pi (INR (m + n)%nat))).
  - intro m; apply deriv_tail; lia.
  - apply (CV_shift' (fun m => Rabs (S_deriv xi n - S_deriv xi m)) n).
    apply (continuity_seq Rabs (fun m => S_deriv xi n - S_deriv xi m)
             (S_deriv xi n - g_deriv xi)); [ apply Rcontinuity_abs | ].
    apply (CV_minus (fun _ => S_deriv xi n) (S_deriv xi) (S_deriv xi n) (g_deriv xi));
      [ intros eps He; exists 0%nat; intros p _; unfold R_dist;
        replace (S_deriv xi n - S_deriv xi n) with 0 by ring; rewrite Rabs_R0; exact He
      | apply g_deriv_cv ].
  - apply (CV_shift' (fun m => Rabs (2 * exp_pi (INR n) - 2 * exp_pi (INR m))) n).
    apply (continuity_seq Rabs (fun m => 2 * exp_pi (INR n) - 2 * exp_pi (INR m))
             (2 * exp_pi (INR n) - Lg)); [ apply Rcontinuity_abs | ].
    apply (CV_minus (fun _ => 2 * exp_pi (INR n)) (fun k => 2 * exp_pi (INR k))
             (2 * exp_pi (INR n)) Lg);
      [ intros eps He; exists 0%nat; intros p _; unfold R_dist;
        replace (2 * exp_pi (INR n) - 2 * exp_pi (INR n)) with 0 by ring; rewrite Rabs_R0; exact He
      | exact E2_cv ].
Qed.

Theorem g_deriv_cvu : forall eps, eps > 0 ->
  exists N, forall n, (N <= n)%nat -> forall xi, Rabs (g_deriv xi - S_deriv xi n) < eps.
Proof.
  intros eps He.
  (* |2 E n − Lg| → 0 *)
  assert (Hb0 : Un_cv (fun n => Rabs (2 * exp_pi (INR n) - Lg)) 0).
  { replace 0 with (Rabs (Lg - Lg)) by (rewrite Rminus_diag, Rabs_R0; reflexivity).
    apply (continuity_seq Rabs (fun n => 2 * exp_pi (INR n) - Lg) (Lg - Lg));
      [ apply Rcontinuity_abs | ].
    apply (CV_minus (fun k => 2 * exp_pi (INR k)) (fun _ => Lg) Lg Lg);
      [ exact E2_cv
      | intros e2 He2; exists 0%nat; intros p _; unfold R_dist;
        replace (Lg - Lg) with 0 by ring; rewrite Rabs_R0; exact He2 ]. }
  destruct (Hb0 eps He) as [N HN]; exists N; intros n Hn xi.
  rewrite Rabs_minus_sym.
  apply Rle_lt_trans with (Rabs (2 * exp_pi (INR n) - Lg)); [ apply deriv_uniform_tail | ].
  pose proof (HN n Hn) as Ht; unfold R_dist in Ht; rewrite Rminus_0_r in Ht.
  apply Rle_lt_trans with (Rabs (Rabs (2 * exp_pi (INR n) - Lg))); [ apply Rle_abs | exact Ht ].
Qed.

Print Assumptions g_deriv_cv.
Print Assumptions g_deriv_cvu.

(* ================================================================= *)
(*  END GaussDerivValue.v (Phase 1 sin side)                        *)
(*  g(ξ) = ∫_ℝ −2πx e^{−πx²}sin(2πxξ) exists, S_deriv ξ k → g(ξ), AND    *)
(*  the tail is UNIFORM in ξ (g_deriv_cvu).  With F_transform (cos side) *)
(*  Phase 1 is complete: both value functions and the CVU hypothesis    *)
(*  are in hand for Phase 3's derivable_pt_lim_CVU.                     *)
(* ================================================================= *)
