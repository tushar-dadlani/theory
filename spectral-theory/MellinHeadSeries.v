(* ================================================================= *)
(*  MellinHeadSeries.v  —  Riemann FE milestone R3, file 3:          *)
(*  the head interchange  Hu s = Σ_k gnear (s/2)(π(k+1)²).           *)
(*                                                                    *)
(*  Harder than the tail: on the reciprocal side the θ-rate is         *)
(*  e^{−π/u} → 1, so NO pointwise M-null dominating function exists.  *)
(*  Instead: Σ_k gnl_k is monotone and bounded above by Hu s (a       *)
(*  comparison of improper values), hence converges to some L; and    *)
(*  each pint1(hker)(A) ≤ L via a FINITE [1,A] interchange (RInt_sum + *)
(*  a geom_tail_est bound at the A-local rate e^{−π/A} < 1), forcing   *)
(*  Hu s = lim pint1(hker) ≤ L.  With L ≤ Hu s, L = Hu s.             *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import JacobiTheta RiemannPsi RiemannPsiCont MellinElem GammaReal
        MellinCoV MellinHead MellinTailSeries ImproperCv1
        GaussPeriodSum GaussPeriodDeriv.
Open Scope R_scope.

(* --- comparison of two improper values --- *)

Lemma improper_le1 : forall f g Hf Hg If Ig,
  ImproperCv1 f Hf If -> ImproperCv1 g Hg Ig ->
  (forall x, 1 <= x -> f x <= g x) -> If <= Ig.
Proof.
  intros f g Hf Hg If Ig HF HG Hle.
  set (b := fun n => 1 + INR n).
  assert (Hb1 : forall n, 1 <= b n) by (intro n; unfold b; pose proof (pos_INR n); lra).
  assert (Hbinf : cv_infty b) by (unfold b; apply cv_infty_1_INR).
  apply (Un_cv_le (fun n => pint1 f Hf (b n)) (fun n => pint1 g Hg (b n)) If Ig);
    [ | apply HF; assumption | apply HG; assumption ].
  intro n; unfold pint1; apply RiemannInt_P19; [ apply Hb1 | intros x Hx; apply Hle; lra ].
Qed.

(* --- the k-th head value and the partial-sum integrand --- *)

Section Head.
Variable s : R.
Hypothesis Hs2 : 0 < s / 2.

Definition gnl (k : nat) : R := gnear (s / 2) (PI * INR (S k) ^ 2) Hs2 (PIn2_pos k).

Definition Hpartial (M : nat) (u : R) : R := sum_f_R0 (fun k => rk s k u) M.

Lemma cont_Hpartial : forall M, continuity (Hpartial M).
Proof. intro M; apply (cont_sum (fun k u => rk s k u) M); intro k; apply cont_rk. Qed.

Lemma Hpartial_int : forall M x y, Riemann_integrable (Hpartial M) x y.
Proof.
  intros M x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_Hpartial ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros u _; apply cont_Hpartial ].
Qed.

Lemma Hpartial_eq : forall M u,
  Hpartial M u = Rpower (clamp u) (- (s / 2) - 1) * theta_partial (/ clamp u) M.
Proof.
  intros M u; unfold Hpartial, theta_partial; induction M; cbn [sum_f_R0].
  - unfold rk; ring.
  - rewrite IHM; unfold rk; ring.
Qed.

Lemma Hpartial_le_hker : forall M u, Hpartial M u <= hker s u.
Proof.
  intros M u; unfold Hpartial.
  assert (Heq : hker s u = sum_f_R0 (fun k => rk s k u) M
                          + (Rpower (clamp u) (- (s / 2) - 1)
                             * (Psi (/ clamp u) - theta_partial (/ clamp u) M))).
  { unfold hker.
    assert (HH : sum_f_R0 (fun k => rk s k u) M
                 = Rpower (clamp u) (- (s / 2) - 1) * theta_partial (/ clamp u) M).
    { unfold theta_partial; induction M; cbn [sum_f_R0].
      - unfold rk; ring.
      - rewrite IHM; unfold rk; ring. }
    rewrite HH; ring. }
  rewrite Heq.
  assert (0 <= Rpower (clamp u) (- (s / 2) - 1) * (Psi (/ clamp u) - theta_partial (/ clamp u) M)).
  { apply Rmult_le_pos; [ left; unfold Rpower; apply exp_pos | ].
    assert (Hcu : 0 < / clamp u) by (apply Rinv_0_lt_compat; apply clamp_pos).
    rewrite (Psi_eq_proj (/ clamp u) Hcu).
    assert (theta_partial (/ clamp u) M <= proj1_sig (theta_half_converges (/ clamp u) Hcu)).
    { apply (growing_ineq (theta_partial (/ clamp u)));
        [ apply theta_partial_growing | exact (proj2_sig (theta_half_converges (/ clamp u) Hcu)) ]. }
    lra. }
  lra.
Qed.

(* Σ_{k≤M} gnl_k is the improper value of Hpartial M. *)
Lemma Hcv : forall M, ImproperCv1 (Hpartial M) (Hpartial_int M) (sum_f_R0 gnl M).
Proof.
  intros M b Hb1 Hbinf.
  apply (Un_cv_ext (fun n => sum_f_R0 (fun k =>
           pint1 (rk s k) (rk_int s k) (b n)) M)).
  - intro n; unfold pint1; symmetry.
    apply (RInt_sum (fun k => rk s k) 1 (b n) (fun k => cont_rk s k) (Hb1 n) M
             (Hpartial_int M 1 (b n)) (fun k => rk_int s k 1 (b n))).
  - apply Un_cv_sum_f_R0; intro k; unfold gnl.
    exact (recip_eq_gnear s k Hs2 (PIn2_pos k) b Hb1 Hbinf).
Qed.

Lemma Hu_ge_partial : forall M, 1 < s -> sum_f_R0 gnl M <= Hu s.
Proof.
  intros M Hs.
  apply (improper_le1 (Hpartial M) (hker s) (Hpartial_int M) (hker_int s)
           (sum_f_R0 gnl M) (Hu s) (Hcv M) (Hu_spec s Hs)).
  intros x _; apply Hpartial_le_hker.
Qed.

Lemma gnl_nonneg : forall k, 0 <= gnl k.
Proof. intro k; unfold gnl; apply gnear_pos. Qed.

Lemma gnl_conv : forall (Hs : 1 < s), { L : R | Un_cv (sum_f_R0 gnl) L }.
Proof.
  intro Hs; apply growing_cv.
  - intro n; cbn [sum_f_R0]; pose proof (gnl_nonneg (S n)); lra.
  - unfold has_ub, EUn, bound, is_upper_bound; exists (Hu s);
      intros r [n ->]; apply Hu_ge_partial; exact Hs.
Qed.

(* --- the A-local geometric tail --- *)

Definition DA (A : R) (M : nat) : R :=
  exp (- (PI * / A)) ^ (S (S M)) / (1 - exp (- (PI * / A))).

Lemma head_tail_bound : forall A M u, 1 <= u -> u <= A ->
  Psi (/ u) - theta_partial (/ u) M <= DA A M.
Proof.
  intros A M u Hu HuA; assert (HApos : 0 < A) by lra; assert (Hupos : 0 < u) by lra.
  assert (Hiu : 0 < / u) by (apply Rinv_0_lt_compat; exact Hupos).
  assert (HiA : 0 < / A) by (apply Rinv_0_lt_compat; exact HApos).
  set (w := exp (- (PI * / u))).
  assert (Hw0 : 0 <= w) by (unfold w; left; apply exp_pos).
  assert (Hw1 : w < 1) by (unfold w; apply theta_ratio_lt1; exact Hiu).
  assert (HL : Un_cv (sum_f_R0 (theta_term (/ u))) (Psi (/ u)))
    by (rewrite (Psi_eq_proj (/ u) Hiu); exact (proj2_sig (theta_half_converges (/ u) Hiu))).
  assert (Hdom : forall k, Rabs (theta_term (/ u) k) <= w * w ^ k).
  { intro k; rewrite Rabs_right by (apply Rle_ge; unfold theta_term; left; apply exp_pos).
    change (w * w ^ k) with (w ^ (S k)); apply theta_term_le'; exact Hiu. }
  pose proof (geom_tail_est (theta_term (/ u)) (Psi (/ u)) w w Hw0 Hw1 Hw0 HL Hdom M) as Hg.
  assert (Hpos : theta_partial (/ u) M <= Psi (/ u)).
  { rewrite (Psi_eq_proj (/ u) Hiu); apply (growing_ineq (theta_partial (/ u)));
      [ apply theta_partial_growing | exact (proj2_sig (theta_half_converges (/ u) Hiu)) ]. }
  unfold theta_partial in Hpos.
  rewrite Rabs_right in Hg by (apply Rle_ge; lra).
  eapply Rle_trans; [ exact Hg | ].
  (* w * w^(S M) / (1-w) <= DA A M, using w <= exp(-(PI*/A)) *)
  set (v := exp (- (PI * / A))).
  assert (Hwv : w <= v).
  { unfold w, v; apply exp_le_compat; apply Ropp_le_contravar; apply Rmult_le_compat_l;
      [ pose proof PI_RGT_0; lra | apply Rinv_le_contravar; [ exact Hupos | exact HuA ] ]. }
  assert (Hv1 : v < 1) by (unfold v; apply theta_ratio_lt1; exact HiA).
  assert (Hv0 : 0 <= v) by (unfold v; left; apply exp_pos).
  unfold DA; fold v; change (w * w ^ (S M)) with (w ^ (S (S M))).
  apply Rle_trans with (v ^ (S (S M)) / (1 - w)).
  - unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra
                                          | apply pow_incr; split; [ exact Hw0 | exact Hwv ] ].
  - unfold Rdiv; apply Rmult_le_compat_l; [ apply pow_le; exact Hv0 | ].
    apply Rinv_le_contravar; lra.
Qed.

Lemma DA_cv : forall A, 1 <= A -> Un_cv (fun M => DA A M) 0.
Proof.
  intros A HA; assert (HApos : 0 < A) by lra.
  assert (HiA : 0 < / A) by (apply Rinv_0_lt_compat; exact HApos).
  assert (Hd : 0 < 1 - exp (- (PI * / A))) by (pose proof (theta_ratio_lt1 (/ A) HiA); lra).
  unfold DA.
  apply (Un_cv_ext (fun M => / (1 - exp (- (PI * / A))) * exp (- (PI * / A)) ^ (S (S M)))).
  - intro M; unfold Rdiv; ring.
  - replace 0 with (/ (1 - exp (- (PI * / A))) * 0) by ring.
    apply (CV_mult (fun _ => / (1 - exp (- (PI * / A))))
             (fun M => exp (- (PI * / A)) ^ (S (S M)))
             (/ (1 - exp (- (PI * / A)))) 0); [ apply Un_cv_const | ].
    intros eps He.
    assert (Hab : Rabs (exp (- (PI * / A))) < 1)
      by (rewrite Rabs_right by (apply Rle_ge; left; apply exp_pos);
          apply theta_ratio_lt1; exact HiA).
    destruct (pow_lt_1_zero (exp (- (PI * / A))) Hab eps He) as [N HN]; exists N; intros n Hn.
    unfold R_dist; rewrite Rminus_0_r; apply HN; lia.
Qed.

(* --- the finite [1,A] interchange --- *)

Lemma head_finite : forall A, 1 <= A -> 1 < s ->
  Un_cv (fun M => pint1 (Hpartial M) (Hpartial_int M) A) (pint1 (hker s) (hker_int s) A).
Proof.
  intros A HA Hs eps Heps.
  set (KA := pint1 (eker (- (s / 2) - 1)) (eker_int (- (s / 2) - 1)) A).
  assert (HKA : 0 <= KA).
  { unfold KA, pint1; apply Rle_trans with (RiemannInt (RiemannInt_P14 1 A 0)).
    - rewrite (RiemannInt_P15 (RiemannInt_P14 1 A 0)); ring_simplify; apply Rle_refl.
    - apply RiemannInt_P19; [ exact HA | intros x _; unfold fct_cte; left; apply eker_pos ]. }
  destruct (DA_cv A HA eps ltac:(lra)) as [N0 _].
  assert (Hcv0 : Un_cv (fun M => DA A M * KA) 0).
  { replace 0 with (0 * KA) by ring; apply (CV_mult (fun M => DA A M) (fun _ => KA) 0 KA);
      [ apply DA_cv; exact HA | apply Un_cv_const ]. }
  destruct (Hcv0 eps Heps) as [N HN]; exists N; intros M HM.
  specialize (HN M HM); unfold R_dist in HN |- *; rewrite Rminus_0_r in HN.
  assert (HbdInt : Riemann_integrable
            (fun u => Hpartial M u + DA A M * eker (- (s / 2) - 1) u) 1 A).
  { apply continuity_implies_RiemannInt; [ exact HA | intros u _; apply continuity_pt_plus;
      [ apply cont_Hpartial | apply continuity_pt_scal; apply cont_eker ] ]. }
  assert (Hle : pint1 (hker s) (hker_int s) A <= RiemannInt HbdInt).
  { unfold pint1; apply RiemannInt_P19; [ exact HA | intros u [Hu1 HuA] ].
    rewrite (Hpartial_eq M u); unfold hker, eker; rewrite !(clamp_id u) by lra.
    set (R := Rpower u (- (s / 2) - 1)).
    assert (HR : 0 <= R) by (unfold R; left; unfold Rpower; apply exp_pos).
    pose proof (head_tail_bound A M u ltac:(lra) ltac:(lra)) as Ht.
    apply Rle_trans with ((theta_partial (/ u) M + DA A M) * R).
    - apply Rmult_le_compat_r; [ exact HR | lra ].
    - apply Req_le; ring. }
  assert (Hval : RiemannInt HbdInt
                 = pint1 (Hpartial M) (Hpartial_int M) A + DA A M * KA).
  { unfold pint1, KA; apply (RiemannInt_P13 (Hpartial_int M 1 A) (eker_int (- (s / 2) - 1) 1 A)). }
  assert (Hlo : pint1 (Hpartial M) (Hpartial_int M) A <= pint1 (hker s) (hker_int s) A).
  { unfold pint1; apply RiemannInt_P19; [ exact HA | intros u _; apply Hpartial_le_hker ]. }
  rewrite Rabs_left1 by lra.
  rewrite Hval in Hle.
  apply Rle_lt_trans with (DA A M * KA); [ lra | ].
  rewrite Rabs_right in HN by (apply Rle_ge; apply Rmult_le_pos;
    [ unfold DA; apply Rle_mult_inv_pos; [ apply pow_le; left; apply exp_pos |
      pose proof (theta_ratio_lt1 (/ A) (Rinv_0_lt_compat A ltac:(lra))); lra ] | exact HKA ]).
  exact HN.
Qed.

(* --- pint1(hker)(A) ≤ Σ gnl --- *)

Lemma pint_hker_le : forall A (Hs : 1 < s), 1 <= A ->
  pint1 (hker s) (hker_int s) A <= proj1_sig (gnl_conv Hs).
Proof.
  intros A Hs HA.
  destruct (gnl_conv Hs) as [L HL]; simpl.
  apply (Un_cv_le_const (fun M => pint1 (Hpartial M) (Hpartial_int M) A)
           (pint1 (hker s) (hker_int s) A) L); [ | apply head_finite; assumption ].
  intro M.
  (* pint1(Hpartial M)(A) = Σ_{k≤M} pint1(rk_k)(A) ≤ Σ_{k≤M} gnl_k ≤ L *)
  assert (Heq : pint1 (Hpartial M) (Hpartial_int M) A
                = sum_f_R0 (fun k => pint1 (rk s k) (rk_int s k) A) M).
  { unfold pint1;
      apply (RInt_sum (fun k => rk s k) 1 A (fun k => cont_rk s k) HA M
               (Hpartial_int M 1 A) (fun k => rk_int s k 1 A)). }
  rewrite Heq.
  apply Rle_trans with (sum_f_R0 gnl M).
  - apply sum_f_R0_le; intro k; unfold gnl.
    apply (pint1_le_improper (rk s k) (rk_int s k)
             (gnear (s / 2) (PI * INR (S k) ^ 2) Hs2 (PIn2_pos k)));
      [ apply recip_eq_gnear | intros x _; apply rk_nonneg | exact HA ].
  - apply (growing_ineq (sum_f_R0 gnl));
      [ intro n; cbn [sum_f_R0]; pose proof (gnl_nonneg (S n)); lra | exact HL ].
Qed.

(* --- the head interchange --- *)

Theorem head_series : forall (Hs : 1 < s), Un_cv (sum_f_R0 gnl) (Hu s).
Proof.
  intro Hs; destruct (gnl_conv Hs) as [L HL] eqn:E.
  assert (HLe : L <= Hu s)
    by (apply (Un_cv_le_const (sum_f_R0 gnl) L (Hu s));
        [ intro M; apply Hu_ge_partial; exact Hs | exact HL ]).
  assert (HGe : Hu s <= L).
  { set (b := fun n => 1 + INR n).
    assert (Hb1 : forall n, 1 <= b n) by (intro n; unfold b; pose proof (pos_INR n); lra).
    assert (Hbinf : cv_infty b) by (unfold b; apply cv_infty_1_INR).
    apply (Un_cv_le_const (fun n => pint1 (hker s) (hker_int s) (b n)) (Hu s) L).
    - intro n; pose proof (pint_hker_le (b n) Hs (Hb1 n)) as Hp; rewrite E in Hp; exact Hp.
    - apply Hu_spec; assumption. }
  assert (L = Hu s) by lra.
  rewrite <- H; exact HL.
Qed.

End Head.

Print Assumptions head_series.

(* ================================================================= *)
(*  END MellinHeadSeries.v.  Hu s = Σ_k gnear (s/2)(π(k+1)²).         *)
(* ================================================================= *)
