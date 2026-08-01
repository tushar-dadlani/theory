(* ================================================================= *)
(*  MellinCoV.v  —  Riemann FE milestone R3, file 1:                *)
(*  the per-term reciprocal↔near change of variables.               *)
(*                                                                    *)
(*  The head integral Hu is built on the reciprocal side (∫₁^∞ of     *)
(*  hker), while the Gamma near-piece gnear is ∫₀^1.  The bridge is   *)
(*  the DECREASING substitution t = 1/u, which cov_local cannot do    *)
(*  (it needs an increasing g).  So we prove `cov_recip` directly via *)
(*  FTC on both sides with a shared primitive:                        *)
(*     ∫_1^B f(1/u)/u² du = ∫_{1/B}^1 f.                              *)
(*  Then the k-th reciprocal term rk integrates (over ∫₁^∞) to the    *)
(*  k-th Gamma near-value gnear (s/2)(π(k+1)²)  (recip_eq_gnear).     *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import ImproperCv0 ImproperCv1 MellinElem GammaReal RpowerZero
        JacobiTheta ContinuousCoV RiemannPsiCont.
Open Scope R_scope.

(* --- derivative of the reciprocal --- *)

Lemma recip_deriv : forall u, 0 < u -> derivable_pt_lim (fun x => / x) u (- / (u * u)).
Proof.
  intros u Hu.
  assert (Hd := derivable_pt_lim_div (fun _ => 1) (fun x => x) u 0 1
                  (derivable_pt_lim_const 1 u) (derivable_pt_lim_id u)
                  (Rgt_not_eq u 0 Hu)).
  replace (- / (u * u)) with ((0 * u - 1 * 1) / (u)²) by (unfold Rsqr; field; lra).
  eapply derivable_pt_lim_ext; [ | exact Hd ].
  intro x; unfold div_fct, inv_fct, mult_fct, fct_cte, Rdiv; ring.
Qed.

(* --- continuity of u ↦ f(1/u)·/(u·u) on [1,B] --- *)

Lemma cont_recip_integrand : forall (f : R -> R) u, 0 < u ->
  continuity_pt f (/ u) -> continuity_pt (fun u => f (/ u) * / (u * u)) u.
Proof.
  intros f u Hu Hcf; apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun u => / u) f u); [ | exact Hcf ].
    apply (continuity_pt_inv (fun u => u) u);
      [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id | lra ].
  - apply (continuity_pt_inv (fun u => u * u) u);
      [ apply continuity_pt_mult;
        apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
      | apply Rgt_not_eq; apply Rmult_lt_0_compat; exact Hu ].
Qed.

(* --- the decreasing change of variables --- *)

Theorem cov_recip : forall (f : R -> R) (B : R), 1 <= B ->
  (forall x, / B <= x <= 1 -> continuity_pt f x) ->
  forall (prL : Riemann_integrable (fun u => f (/ u) * / (u * u)) 1 B)
         (prR : Riemann_integrable f (/ B) 1),
  RiemannInt prL = RiemannInt prR.
Proof.
  intros f B HB Hcf prL prR.
  assert (HBpos : 0 < B) by lra.
  assert (HinvB : / B <= 1) by (apply inv_le_1; exact HB).
  destruct (RiemannInt_P30 HinvB Hcf) as [Phi HPhi].
  destruct HPhi as [HPhid _].
  (* RHS via FTC *)
  rewrite (FTC_antideriv f Phi (/ B) 1 HinvB Hcf prR (conj HPhid HinvB)).
  (* LHS via FTC with antiderivative -Phi(1/u) *)
  assert (Hcont : forall u, 1 <= u <= B -> continuity_pt (fun u => f (/ u) * / (u * u)) u).
  { intros u [Hu1 HuB]; apply cont_recip_integrand; [ lra | apply Hcf; split ].
    - apply Rinv_le_contravar; lra.
    - apply inv_le_1; lra. }
  assert (Hanti : antiderivative (fun u => f (/ u) * / (u * u)) (fun u => - Phi (/ u)) 1 B).
  { split; [ | exact HB ]. intros u [Hu1 HuB].
    assert (Hupos : 0 < u) by lra.
    assert (Hinvu : / B <= / u <= 1).
    { split; [ apply Rinv_le_contravar; lra | apply inv_le_1; lra ]. }
    destruct (HPhid (/ u) Hinvu) as [prP HprP].
    assert (HdP : derivable_pt_lim Phi (/ u) (f (/ u)))
      by (rewrite HprP; apply (proj2_sig prP)).
    assert (Hcomp : derivable_pt_lim (fun u => - Phi (/ u)) u (f (/ u) * / (u * u))).
    { pose proof (derivable_pt_lim_comp (fun x => / x) Phi u (- / (u * u)) (f (/ u))
                    (recip_deriv u Hupos) HdP) as Hc.
      apply (derivable_pt_lim_opp (comp Phi (fun x => / x)) u (f (/ u) * (- / (u * u)))) in Hc.
      apply (derivable_pt_lim_ext (opp_fct (comp Phi (fun x => / x))) (fun u => - Phi (/ u))).
      - intro z; unfold opp_fct, comp; reflexivity.
      - replace (f (/ u) * / (u * u)) with (- (f (/ u) * (- / (u * u)))) by ring; exact Hc. }
    exists (exist (fun l => derivable_pt_lim (fun u => - Phi (/ u)) u l)
              (f (/ u) * / (u * u)) Hcomp); reflexivity. }
  rewrite (FTC_antideriv (fun u => f (/ u) * / (u * u)) (fun u => - Phi (/ u)) 1 B HB
             Hcont prL Hanti).
  rewrite Rinv_1; ring.
Qed.

(* --- Rpower of a reciprocal base --- *)

Lemma Rpower_inv_base : forall u a, 0 < u -> Rpower (/ u) a = Rpower u (- a).
Proof. intros u a Hu; unfold Rpower; rewrite ln_Rinv by exact Hu; f_equal; ring. Qed.

(* --- the k-th reciprocal term of hker --- *)

Definition rk (s : R) (k : nat) (u : R) : R :=
  theta_term (/ clamp u) k * Rpower (clamp u) (- (s / 2) - 1).

Lemma cont_theta_term_recip : forall k w, 0 < w -> continuity_pt (fun w => theta_term (/ w) k) w.
Proof.
  intros k w Hw; unfold theta_term.
  apply (continuity_pt_comp (fun w => - (PI * INR (S k) ^ 2 * / w)) exp w).
  - apply continuity_pt_opp; apply (continuity_pt_scal (fun w => / w) (PI * INR (S k) ^ 2) w).
    apply (continuity_pt_inv (fun w => w) w);
      [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id | apply Rgt_not_eq; exact Hw ].
  - apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

Lemma cont_rk : forall s k, continuity (rk s k).
Proof.
  intros s k u; unfold rk; apply continuity_pt_mult.
  - apply (continuity_pt_comp clamp (fun w => theta_term (/ w) k) u);
      [ apply cont_clamp | apply cont_theta_term_recip; apply clamp_pos ].
  - apply (cont_eker (- (s / 2) - 1)).
Qed.

Lemma rk_int : forall s k x y, Riemann_integrable (rk s k) x y.
Proof.
  intros s k x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_rk ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros u _; apply cont_rk ].
Qed.

Lemma rk_nonneg : forall s k u, 0 <= rk s k u.
Proof.
  intros s k u; unfold rk; apply Rmult_le_pos;
    [ unfold theta_term; left; apply exp_pos | left; unfold Rpower; apply exp_pos ].
Qed.

(* --- the cov integrand match on [1,∞) --- *)

Lemma rk_key : forall u a, 0 < u -> Rpower (/ u) (a - 1) * / (u * u) = Rpower u (- a - 1).
Proof.
  intros u a Hu; unfold Rpower; rewrite ln_Rinv by exact Hu.
  assert (Huu : u * u = exp (2 * ln u))
    by (replace (2 * ln u) with (ln u + ln u) by ring;
        rewrite exp_plus, exp_ln by exact Hu; reflexivity).
  rewrite Huu, <- exp_Ropp, <- exp_plus; f_equal; ring.
Qed.

Lemma rk_eq_pt : forall s k u, 1 <= u ->
  rk s k u = gnk (s / 2) (PI * INR (S k) ^ 2) (/ u) * / (u * u).
Proof.
  intros s k u Hu; assert (Hu0 : 0 < u) by lra.
  unfold rk, gnk; rewrite (clamp_id u Hu); unfold theta_term.
  rewrite <- (rk_key u (s / 2) Hu0); ring.
Qed.

(* --- the per-B identity  ∫_1^B rk = ∫_{1/B}^1 gnk_k  --- *)

Lemma rk_pint_eq : forall s k B, 1 <= B -> 0 < s ->
  pint1 (rk s k) (rk_int s k) B
  = rint01 (gnk (s / 2) (PI * INR (S k) ^ 2)) (Hf_near (s / 2) (PI * INR (S k) ^ 2)) (/ B).
Proof.
  intros s k B HB Hs; unfold pint1.
  assert (HinvB0 : 0 < / B) by (apply Rinv_0_lt_compat; lra).
  assert (HinvB1 : / B <= 1) by (apply inv_le_1; exact HB).
  set (c := PI * INR (S k) ^ 2).
  assert (prL : Riemann_integrable (fun u => gnk (s / 2) c (/ u) * / (u * u)) 1 B).
  { apply continuity_implies_RiemannInt; [ exact HB | intros u [Hu1 HuB]; apply cont_recip_integrand;
      [ lra | apply cont_gnk; apply Rinv_0_lt_compat; lra ] ]. }
  assert (Hcf : forall x, / B <= x <= 1 -> continuity_pt (gnk (s / 2) c) x)
    by (intros x [Hx1 Hx2]; apply cont_gnk; lra).
  pose proof (cov_recip (gnk (s / 2) c) B HB Hcf prL (Hf_near (s / 2) c (/ B) 1 HinvB0 HinvB1)) as Hcov.
  rewrite (rint01_val (gnk (s / 2) c) (Hf_near (s / 2) c) (/ B) HinvB0 HinvB1), <- Hcov.
  apply RiemannInt_P18; [ exact HB | intros u [Hu1 HuB]; unfold c; apply rk_eq_pt; lra ].
Qed.

(* --- the bridge:  ∫₁^∞ rk = gnear (s/2)(π(k+1)²) --- *)

Theorem recip_eq_gnear : forall s k (Hs2 : 0 < s / 2) (Hc : 0 < PI * INR (S k) ^ 2),
  ImproperCv1 (rk s k) (rk_int s k) (gnear (s / 2) (PI * INR (S k) ^ 2) Hs2 Hc).
Proof.
  intros s k Hs2 Hc.
  assert (Hs : 0 < s) by lra.
  apply (improper_welldef1 (rk s k) (rk_int s k) (fun x _ => rk_nonneg s k x)
           (fun n => 1 + INR n) (gnear (s / 2) (PI * INR (S k) ^ 2) Hs2 Hc)).
  - intro n; pose proof (pos_INR n); lra.
  - apply cv_infty_1_INR.
  - apply (Un_cv_ext (fun n => rint01 (gnk (s / 2) (PI * INR (S k) ^ 2))
                              (Hf_near (s / 2) (PI * INR (S k) ^ 2)) (/ (1 + INR n)))).
    + intro n; symmetry; apply rk_pint_eq; [ pose proof (pos_INR n); lra | exact Hs ].
    + unfold gnear; exact (proj2_sig (gnear_sig (s / 2) (PI * INR (S k) ^ 2) Hs2 Hc)
        (fun n => / (1 + INR n))
        (fun n => Rinv_0_lt_compat (1 + INR n) ltac:(pose proof (pos_INR n); lra))
        (fun n => inv_le_1 (1 + INR n) ltac:(pose proof (pos_INR n); lra))
        (Un_cv_recip_0 (fun n => 1 + INR n)
           (fun n => ltac:(pose proof (pos_INR n); lra) : 0 < 1 + INR n) cv_infty_1_INR)).
Qed.

Print Assumptions recip_eq_gnear.

(* ================================================================= *)
(*  END MellinCoV.v.  ∫₁^∞ rk = gnear (s/2)(π(k+1)²).                 *)
(* ================================================================= *)
