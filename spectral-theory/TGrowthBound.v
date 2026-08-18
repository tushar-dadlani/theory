(* ================================================================= *)
(*  TGrowthBound.v  —  Hadamard Stage A (part 2): the T(sigma) estimate. *)
(*                                                                    *)
(*  The order-1 growth of XiC reduces (via XiGrowthBound.TC_mod_le) to  *)
(*  bounding the real Mellin tail  T(sigma) = int_1^inf u^{sigma/2-1}    *)
(*  Psi(u) du  by exp(O(sigma ln sigma)).  Core inequality (this part):  *)
(*                                                                    *)
(*    pow_exp_max : u^m . e^{-a u} <= (m/a)^m . e^{-m}   (u,m,a > 0)     *)
(*                                                                    *)
(*  the maximum of u^m e^{-a u}, from ln t <= t-1 (itself exp_ineq1_le). *)
(*  With a = pi/2 this gives u^{sigma/2-1} e^{-pi u} <= B . e^{-pi u/2},  *)
(*  B = (2m/pi)^m e^{-m} = exp(O(sigma ln sigma)); integrating the       *)
(*  residual e^{-pi u/2} yields the T(sigma) bound (next).              *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ThetaTailBounds RiemannPsi MellinTail MellinElem
        ImproperCv1 CImproperIntegral ContinuousCoV LogGeomSeries.
Open Scope R_scope.

(* ln t <= t - 1  (t > 0), i.e. the tangent-line bound, from 1+s <= exp s *)
Lemma ln_le_sub1 : forall t, 0 < t -> ln t <= t - 1.
Proof.
  intros t Ht.
  assert (Ht' : t <= exp (t - 1)) by (pose proof (exp_ineq1_le (t - 1)); lra).
  apply Rle_trans with (ln (exp (t - 1))); [ | rewrite ln_exp; lra ].
  destruct Ht' as [Hlt | Heq].
  - left; apply ln_increasing; [ exact Ht | exact Hlt ].
  - rewrite <- Heq; apply Rle_refl.
Qed.

(* the maximum of u^m e^{-a u} over u>0 is at u=m/a, value (m/a)^m e^{-m} *)
Lemma pow_exp_max : forall a m u, 0 < a -> 0 < m -> 0 < u ->
  Rpower u m * exp (- (a * u)) <= Rpower (m / a) m * exp (- m).
Proof.
  intros a m u Ha Hm Hu.
  assert (Hma : 0 < m / a) by (apply Rdiv_lt_0_compat; lra).
  unfold Rpower. rewrite <- !exp_plus. apply exp_le_mono.
  set (t := a * u / m).
  assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; [ nra | exact Hm ]).
  pose proof (ln_le_sub1 t Ht) as Hln.
  assert (Hu_eq : u = t * (m / a)) by (unfold t; field; lra).
  assert (Hlnu : ln u = ln t + ln (m / a))
    by (rewrite Hu_eq, ln_mult; [ reflexivity | exact Ht | exact Hma ]).
  assert (Hau : a * u = t * m) by (unfold t; field; lra).
  rewrite Hlnu, Hau. nra.
Qed.

Print Assumptions pow_exp_max.

(* ===== parametric exponential tail integral, rate r>0 ===== *)
Definition edkr (r u : R) : R := exp (- (r * u)).

Lemma edkr_deriv : forall r x, 0 < r ->
  derivable_pt_lim (fun y => - / r * exp (- (r * y))) x (edkr r x).
Proof.
  intros r x Hr.
  assert (Hin : derivable_pt_lim (fun y => - (r * y)) x (- r)).
  { replace (- r) with (- (r * 1)) by ring.
    apply derivable_pt_lim_opp.
    apply (derivable_pt_lim_scal (fun y => y) r x 1 (derivable_pt_lim_id x)). }
  assert (Hexp : derivable_pt_lim (fun y => exp (- (r * y))) x (exp (- (r * x)) * (- r))).
  { apply (derivable_pt_lim_comp (fun y => - (r * y)) exp x (- r) (exp (- (r * x))));
      [ exact Hin | apply derivable_pt_lim_exp ]. }
  apply (derivable_pt_lim_scal (fun y => exp (- (r * y))) (- / r) x
           (exp (- (r * x)) * (- r))) in Hexp.
  replace (edkr r x) with (- / r * (exp (- (r * x)) * - r))
    by (unfold edkr; field; lra).
  exact Hexp.
Qed.

Lemma edkr_deriv_self : forall r x, derivable_pt_lim (edkr r) x (edkr r x * - r).
Proof.
  intros r x. unfold edkr.
  assert (Hin : derivable_pt_lim (fun y => - (r * y)) x (- r)).
  { replace (- r) with (- (r * 1)) by ring.
    apply derivable_pt_lim_opp.
    apply (derivable_pt_lim_scal (fun y => y) r x 1 (derivable_pt_lim_id x)). }
  apply (derivable_pt_lim_comp (fun y => - (r * y)) exp x (- r) (exp (- (r * x))));
    [ exact Hin | apply derivable_pt_lim_exp ].
Qed.

Lemma cont_edkr : forall r, continuity (edkr r).
Proof.
  intros r x. apply (derivable_continuous_pt (edkr r) x).
  exists (edkr r x * - r). apply edkr_deriv_self.
Qed.

Lemma edkr_int : forall r x y, Riemann_integrable (edkr r) x y.
Proof.
  intros r x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_edkr ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_edkr ].
Qed.

Lemma edkr_pint : forall r A, 0 < r -> 1 <= A ->
  pint1 (edkr r) (edkr_int r) A
  = (- / r * exp (- (r * A))) - (- / r * exp (- (r * 1))).
Proof.
  intros r A Hr HA; unfold pint1.
  set (F := fun x => - / r * exp (- (r * x))).
  assert (Hanti : antiderivative (edkr r) F 1 A).
  { split; [ | exact HA ]. intros x [Hx1 HxA].
    exists (exist (fun l => derivable_pt_lim F x l) (edkr r x) (edkr_deriv r x Hr)).
    reflexivity. }
  rewrite (FTC_antideriv (edkr r) F 1 A HA (fun x _ => cont_edkr r x) (edkr_int r 1 A) Hanti).
  unfold F; reflexivity.
Qed.

Lemma exp_neg_pow_r : forall r n, exp (- (r * INR n)) = (exp (- r)) ^ n.
Proof.
  intros r n. induction n as [| n IH].
  - simpl; rewrite Rmult_0_r, Ropp_0, exp_0; reflexivity.
  - rewrite S_INR.
    replace (- (r * (INR n + 1))) with ((- (r * INR n)) + (- r)) by ring.
    rewrite exp_plus, IH; simpl; ring.
Qed.

Lemma edkr_seq_cv0 : forall r, 0 < r -> Un_cv (fun k => exp (- (r * INR (S k)))) 0.
Proof.
  intros r Hr. apply (Un_cv_ext (fun k => exp (- r) * (exp (- r)) ^ k)).
  - intro k; rewrite exp_neg_pow_r; simpl; ring.
  - replace 0 with (exp (- r) * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | ].
    apply pow_cv0. rewrite Rabs_right;
      [ | apply Rle_ge; apply Rlt_le; apply exp_pos ].
    rewrite <- exp_0. apply exp_increasing. lra.
Qed.

Theorem edkr_improper : forall r, 0 < r ->
  ImproperCv1 (edkr r) (edkr_int r) (exp (- r) / r).
Proof.
  intros r Hr.
  apply (improper_welldef1 (edkr r) (edkr_int r)
           (fun x _ => Rlt_le _ _ (exp_pos _)) (fun k => INR (S k)) (exp (- r) / r)).
  - intro k; rewrite S_INR; pose proof (pos_INR k); lra.
  - apply cv_infty_Sn.
  - apply (Un_cv_ext (fun k => (- / r * exp (- (r * INR (S k))))
                             - (- / r * exp (- (r * 1))))).
    + intro k; symmetry; apply edkr_pint; [ exact Hr | rewrite S_INR; pose proof (pos_INR k); lra ].
    + replace (exp (- r) / r) with (- / r * 0 - (- / r * exp (- (r * 1))))
        by (rewrite Rmult_1_r; field; lra).
      apply CV_minus; [ | apply Un_cv_const ].
      apply (CV_mult (fun _ => - / r) (fun k => exp (- (r * INR (S k)))) (- / r) 0);
        [ apply Un_cv_const | apply edkr_seq_cv0; exact Hr ].
Qed.

Print Assumptions edkr_improper.

(* Rpower is monotone in the exponent for base >= 1 *)
Lemma Rpower_exp_le : forall u a b, 1 <= u -> a <= b -> Rpower u a <= Rpower u b.
Proof.
  intros u a b Hu Hab. unfold Rpower. apply exp_le_mono.
  assert (Hln : 0 <= ln u).
  { rewrite <- ln_1. destruct Hu as [Hlt | Heq].
    - left; apply ln_increasing; lra.
    - subst u; apply Rle_refl. }
  nra.
Qed.

(* the pointwise domination of the Mellin integrand by a const times e^{-pi u/2} *)
Lemma wker_dom : forall s u, 1/2 <= s -> 1 <= u ->
  wker s u
  <= / (1 - exp (- PI)) * (Rpower (s / PI) (s / 2) * exp (- (s / 2))) * edkr (PI / 2) u.
Proof.
  intros s u Hs Hu. pose proof PI_RGT_0 as HPI.
  assert (Hden : 0 < 1 - exp (- PI))
    by (assert (exp (- PI) < 1) by (rewrite <- exp_0; apply exp_increasing; lra); lra).
  assert (Hu0 : 0 < u) by lra.
  unfold wker. rewrite (clamp_id u Hu). unfold edkr.
  set (m1 := s / 2 - 1). set (m := s / 2).
  replace (/ (1 - exp (- PI)) * (Rpower (s / PI) m * exp (- m)) * exp (- (PI / 2 * u)))
    with (/ (1 - exp (- PI)) * ((Rpower (s / PI) m * exp (- m)) * exp (- (PI / 2 * u))))
    by ring.
  assert (HRnn : 0 <= Rpower u m1) by (unfold Rpower; left; apply exp_pos).
  apply Rle_trans with (Rpower u m1 * (exp (- (PI * u)) / (1 - exp (- PI)))).
  { apply Rmult_le_compat_l; [ exact HRnn | apply Psi_upper1; exact Hu ]. }
  apply Rle_trans with (Rpower u m * (exp (- (PI * u)) / (1 - exp (- PI)))).
  { apply Rmult_le_compat_r.
    - unfold Rdiv; apply Rmult_le_pos;
        [ left; apply exp_pos | left; apply Rinv_0_lt_compat; exact Hden ].
    - apply Rpower_exp_le; [ exact Hu | unfold m1, m; lra ]. }
  replace (Rpower u m * (exp (- (PI * u)) / (1 - exp (- PI))))
    with (/ (1 - exp (- PI)) * (Rpower u m * exp (- (PI * u)))) by (field; lra).
  assert (Hsplit : exp (- (PI * u)) = exp (- (PI / 2 * u)) * exp (- (PI / 2 * u)))
    by (rewrite <- exp_plus; f_equal; field).
  rewrite Hsplit.
  apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; exact Hden | ].
  replace (Rpower u m * (exp (- (PI / 2 * u)) * exp (- (PI / 2 * u))))
    with ((Rpower u m * exp (- (PI / 2 * u))) * exp (- (PI / 2 * u))) by ring.
  apply Rmult_le_compat_r; [ left; apply exp_pos | ].
  replace (s / PI) with (m / (PI / 2)) by (unfold m; field; lra).
  apply pow_exp_max; [ lra | unfold m; lra | exact Hu0 ].
Qed.

(* THE T(sigma) GROWTH BOUND *)
Theorem T_growth : forall s, 1/2 <= s ->
  T s <= / (1 - exp (- PI)) * (Rpower (s / PI) (s / 2) * exp (- (s / 2)))
         * (exp (- (PI / 2)) / (PI / 2)).
Proof.
  intros s Hs. pose proof PI_RGT_0 as HPI.
  set (C := / (1 - exp (- PI)) * (Rpower (s / PI) (s / 2) * exp (- (s / 2)))).
  apply (improper_mono (wker s) (fun u => C * edkr (PI / 2) u)
           (wker_int s)
           (fun x y => RI_scal (edkr (PI / 2)) C x y (edkr_int (PI / 2) x y))
           (T s) (C * (exp (- (PI / 2)) / (PI / 2)))).
  - intros x Hx. unfold C. apply wker_dom; [ exact Hs | exact Hx ].
  - exact (T_spec s).
  - apply (improper_scal (edkr (PI / 2)) C (edkr_int (PI / 2))
             (fun x y => RI_scal (edkr (PI / 2)) C x y (edkr_int (PI / 2) x y))
             (exp (- (PI / 2)) / (PI / 2))).
    apply edkr_improper; lra.
Qed.

Print Assumptions T_growth.
