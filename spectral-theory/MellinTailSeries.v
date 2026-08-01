(* ================================================================= *)
(*  MellinTailSeries.v  —  Riemann FE milestone R3, file 2:          *)
(*  the tail interchange  T s = Σ_k gtail (s/2)(π(k+1)²).            *)
(*                                                                    *)
(*  On [1,∞) the θ-decay rate e^{−πu} ≤ e^{−π} < 1 is uniform, so the  *)
(*  M-tail ψ(t)−θ_M(t) is dominated pointwise by E_M·e^{−πt} with     *)
(*  E_M → 0 (geom_tail_est).  The finite partial sum's improper       *)
(*  integral is Σ_{k≤M} gtail_k (RInt_sum), and the difference        *)
(*  T s − Σ_{k≤M} gtail_k is squeezed into [0, E_M·gtail(s/2)π] via a  *)
(*  per-[1,A] RiemannInt_P19 bound (mirroring MellinTail.T_exists).   *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import JacobiTheta RiemannPsi RiemannPsiCont MellinTail MellinElem
        GammaReal ImproperCv1 MellinKernel GaussPeriodSum GaussPeriodDeriv.
Open Scope R_scope.

Lemma PIn2_pos : forall k, 0 < PI * INR (S k) ^ 2.
Proof.
  intro k; apply Rmult_lt_0_compat; [ apply PI_RGT_0 | apply pow_lt; apply lt_0_INR; lia ].
Qed.

Definition gtl (s : R) (k : nat) : R := gtail (s / 2) (PI * INR (S k) ^ 2) (PIn2_pos k).

(* --- Un_cv of a finite sum of convergent sequences --- *)

Lemma Un_cv_sum_f_R0 : forall (a : nat -> nat -> R) (L : nat -> R) M,
  (forall k, Un_cv (fun n => a k n) (L k)) ->
  Un_cv (fun n => sum_f_R0 (fun k => a k n) M) (sum_f_R0 L M).
Proof.
  intros a L M Ha; induction M; simpl.
  - apply Ha.
  - apply CV_plus; [ exact IHM | apply Ha ].
Qed.

(* --- the uniform M-tail factor --- *)

Definition Em (M : nat) : R := exp (- PI) ^ (S M) / (1 - exp (- PI)).

Lemma one_minus_pos : 0 < 1 - exp (- PI).
Proof.
  pose proof (theta_ratio_lt1 1 Rlt_0_1) as H; replace (PI * 1) with PI in H by ring; lra.
Qed.

Lemma Em_cv : Un_cv Em 0.
Proof.
  unfold Em.
  apply (Un_cv_ext (fun M => / (1 - exp (- PI)) * exp (- PI) ^ (S M))).
  - intro M; unfold Rdiv; ring.
  - replace 0 with (/ (1 - exp (- PI)) * 0) by ring.
    apply (CV_mult (fun _ => / (1 - exp (- PI))) (fun M => exp (- PI) ^ (S M))
             (/ (1 - exp (- PI))) 0); [ apply Un_cv_const | ].
    intros eps He; pose proof one_minus_pos.
    assert (Hab : Rabs (exp (- PI)) < 1)
      by (rewrite Rabs_right by (apply Rle_ge; left; apply exp_pos);
          pose proof (theta_ratio_lt1 1 Rlt_0_1) as Hr; replace (PI * 1) with PI in Hr by ring; lra).
    destruct (pow_lt_1_zero (exp (- PI)) Hab eps He) as [N HN]; exists N; intros n Hn.
    unfold R_dist; rewrite Rminus_0_r; apply HN; lia.
Qed.

Lemma theta_tail_factor : forall M t, 1 <= t ->
  Psi t - theta_partial t M <= Em M * exp (- (PI * t)).
Proof.
  intros M t Ht; assert (Ht0 : 0 < t) by lra.
  set (w := exp (- (PI * t))).
  assert (Hw0 : 0 <= w) by (unfold w; left; apply exp_pos).
  assert (Hw1 : w < 1) by (unfold w; apply theta_ratio_lt1; exact Ht0).
  assert (HL : Un_cv (sum_f_R0 (theta_term t)) (Psi t)).
  { rewrite (Psi_eq_proj t Ht0); exact (proj2_sig (theta_half_converges t Ht0)). }
  assert (Hdom : forall k, Rabs (theta_term t k) <= w * w ^ k).
  { intro k; rewrite Rabs_right by (apply Rle_ge; unfold theta_term; left; apply exp_pos).
    change (w * w ^ k) with (w ^ (S k)); apply theta_term_le'; exact Ht0. }
  pose proof (geom_tail_est (theta_term t) (Psi t) w w Hw0 Hw1 Hw0 HL Hdom M) as Hg.
  assert (Hpos : theta_partial t M <= Psi t).
  { rewrite (Psi_eq_proj t Ht0).
    apply (growing_ineq (theta_partial t)); [ apply theta_partial_growing | ].
    exact (proj2_sig (theta_half_converges t Ht0)). }
  rewrite Rabs_right in Hg by (apply Rle_ge; unfold theta_partial in *; lra).
  eapply Rle_trans; [ exact Hg | ].
  (* w * w^(S M) / (1-w) <= Em M * w *)
  assert (Hwle : w <= exp (- PI))
    by (unfold w; apply exp_le_compat; apply Ropp_le_contravar;
        pose proof PI_RGT_0; rewrite <- (Rmult_1_r PI) at 1; apply Rmult_le_compat_l; lra).
  assert (HwM : w ^ (S M) <= exp (- PI) ^ (S M)) by (apply pow_incr; split; [ exact Hw0 | exact Hwle ]).
  assert (Hden : / (1 - w) <= / (1 - exp (- PI)))
    by (apply (Rinv_le_contravar (1 - exp (- PI)) (1 - w)); [ apply one_minus_pos | lra ]).
  unfold Em, Rdiv.
  replace (w * w ^ (S M) * / (1 - w)) with (w * (w ^ (S M) * / (1 - w))) by ring.
  replace (exp (- PI) ^ (S M) * / (1 - exp (- PI)) * w)
    with (w * (exp (- PI) ^ (S M) * / (1 - exp (- PI)))) by ring.
  apply Rmult_le_compat_l; [ exact Hw0 | ].
  apply Rmult_le_compat; [ apply pow_le; exact Hw0 | left; apply Rinv_0_lt_compat; lra
                         | exact HwM | exact Hden ].
Qed.

(* --- the finite partial-sum integrand and its improper value --- *)

Definition Wpartial (s : R) (M : nat) (u : R) : R :=
  sum_f_R0 (fun k => gtk (s / 2) (PI * INR (S k) ^ 2) u) M.

Lemma cont_Wpartial : forall s M, continuity (Wpartial s M).
Proof.
  intros s M; apply (cont_sum (fun k u => gtk (s / 2) (PI * INR (S k) ^ 2) u) M);
    intro k; apply cont_gtk.
Qed.

Lemma Wpartial_int : forall s M x y, Riemann_integrable (Wpartial s M) x y.
Proof.
  intros s M x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_Wpartial ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros u _; apply cont_Wpartial ].
Qed.

Lemma Wpartial_eq : forall s M u,
  Wpartial s M u = Rpower (clamp u) (s / 2 - 1) * theta_partial (clamp u) M.
Proof.
  intros s M u; unfold Wpartial, theta_partial; induction M; cbn [sum_f_R0].
  - unfold gtk, theta_term; ring.
  - rewrite IHM; unfold gtk, theta_term; ring.
Qed.

Lemma Wcv : forall s M, ImproperCv1 (Wpartial s M) (Wpartial_int s M) (sum_f_R0 (gtl s) M).
Proof.
  intros s M b Hb1 Hbinf.
  apply (Un_cv_ext (fun n => sum_f_R0 (fun k =>
           pint1 (gtk (s / 2) (PI * INR (S k) ^ 2)) (gtk_int (s / 2) (PI * INR (S k) ^ 2)) (b n)) M)).
  - intro n; unfold pint1; symmetry.
    apply (RInt_sum (fun k => gtk (s / 2) (PI * INR (S k) ^ 2)) 1 (b n)
             (fun k => cont_gtk (s / 2) (PI * INR (S k) ^ 2)) (Hb1 n) M
             (Wpartial_int s M 1 (b n))
             (fun k => gtk_int (s / 2) (PI * INR (S k) ^ 2) 1 (b n))).
  - apply Un_cv_sum_f_R0; intro k; unfold gtl.
    exact (proj2_sig (gtail_sig (s / 2) (PI * INR (S k) ^ 2) (PIn2_pos k)) b Hb1 Hbinf).
Qed.

(* --- the pointwise sandwich --- *)

Lemma wker_Wpartial_lo : forall s M u, Wpartial s M u <= wker s u.
Proof.
  intros s M u; rewrite Wpartial_eq; unfold wker.
  apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | ].
  rewrite (Psi_eq_proj (clamp u) (clamp_pos u)).
  apply (growing_ineq (theta_partial (clamp u)));
    [ apply theta_partial_growing | exact (proj2_sig (theta_half_converges (clamp u) (clamp_pos u))) ].
Qed.

Lemma wker_Wpartial_hi : forall s M u,
  wker s u <= Wpartial s M u + Em M * gtk (s / 2) PI u.
Proof.
  intros s M u; rewrite Wpartial_eq; unfold wker, gtk.
  set (R := Rpower (clamp u) (s / 2 - 1)).
  assert (HR : 0 <= R) by (unfold R; left; unfold Rpower; apply exp_pos).
  assert (Hcl : 1 <= clamp u) by apply clamp_ge1.
  pose proof (theta_tail_factor M (clamp u) Hcl) as Ht.
  (* Psi(clamp u) <= theta_partial(clamp u) M + Em M * exp(-(PI*clamp u)) *)
  apply Rle_trans with (R * (theta_partial (clamp u) M + Em M * exp (- (PI * clamp u)))).
  - apply Rmult_le_compat_l; [ exact HR | lra ].
  - apply Req_le; ring.
Qed.

(* --- the per-M sandwich on the improper value --- *)

Lemma bound_M : forall s M, 1 < s ->
  0 <= T s - sum_f_R0 (gtl s) M <= Em M * gtail (s / 2) PI PI_RGT_0.
Proof.
  intros s M Hs.
  set (b := fun n => 1 + INR n).
  assert (Hb1 : forall n, 1 <= b n) by (intro n; unfold b; pose proof (pos_INR n); lra).
  assert (Hbinf : cv_infty b) by (unfold b; apply cv_infty_1_INR).
  assert (HW : Un_cv (fun n => pint1 (Wpartial s M) (Wpartial_int s M) (b n)) (sum_f_R0 (gtl s) M))
    by (apply Wcv; assumption).
  assert (HT : Un_cv (fun n => pint1 (wker s) (wker_int s) (b n)) (T s))
    by (apply T_spec; assumption).
  assert (Hdiff : Un_cv (fun n => pint1 (wker s) (wker_int s) (b n)
                              - pint1 (Wpartial s M) (Wpartial_int s M) (b n))
                        (T s - sum_f_R0 (gtl s) M))
    by (apply CV_minus; assumption).
  assert (EM0 : 0 <= Em M) by
    (unfold Em; apply Rle_mult_inv_pos; [ apply pow_le; left; apply exp_pos | apply one_minus_pos ]).
  split.
  - apply (Un_cv_le (fun _ => 0)
             (fun n => pint1 (wker s) (wker_int s) (b n) - pint1 (Wpartial s M) (Wpartial_int s M) (b n))
             0 (T s - sum_f_R0 (gtl s) M)); [ | apply Un_cv_const | exact Hdiff ].
    intro n; unfold pint1; apply Rge_le; apply Rge_minus; apply Rle_ge; apply RiemannInt_P19;
      [ apply Hb1 | intros x _; apply wker_Wpartial_lo ].
  - apply (Un_cv_le
             (fun n => pint1 (wker s) (wker_int s) (b n) - pint1 (Wpartial s M) (Wpartial_int s M) (b n))
             (fun _ => Em M * gtail (s / 2) PI PI_RGT_0)
             (T s - sum_f_R0 (gtl s) M) (Em M * gtail (s / 2) PI PI_RGT_0));
      [ | exact Hdiff | apply Un_cv_const ].
    intro n; pose proof (Hb1 n) as HbN.
    (* pint1 wker (b n) <= pint1 Wpartial (b n) + Em M * pint1 gtk (b n) <= ... *)
    assert (Hsum_int : Riemann_integrable
              (fun u => Wpartial s M u + Em M * gtk (s / 2) PI u) 1 (b n)).
    { apply continuity_implies_RiemannInt; [ exact HbN | intros u _; apply continuity_pt_plus;
        [ apply cont_Wpartial | apply continuity_pt_scal; apply cont_gtk ] ]. }
    assert (H1 : pint1 (wker s) (wker_int s) (b n) <= RiemannInt Hsum_int).
    { unfold pint1; apply RiemannInt_P19; [ exact HbN | intros u _; apply wker_Wpartial_hi ]. }
    assert (H2 : RiemannInt Hsum_int
                 = pint1 (Wpartial s M) (Wpartial_int s M) (b n)
                   + Em M * pint1 (gtk (s / 2) PI) (gtk_int (s / 2) PI) (b n)).
    { unfold pint1; apply (RiemannInt_P13 (Wpartial_int s M 1 (b n)) (gtk_int (s / 2) PI 1 (b n))). }
    assert (H3 : pint1 (gtk (s / 2) PI) (gtk_int (s / 2) PI) (b n) <= gtail (s / 2) PI PI_RGT_0).
    { apply (pint1_le_improper (gtk (s / 2) PI) (gtk_int (s / 2) PI) (gtail (s / 2) PI PI_RGT_0));
        [ exact (proj2_sig (gtail_sig (s / 2) PI PI_RGT_0)) | intros x _; apply gtk_nonneg | exact HbN ]. }
    apply Rle_trans with (Em M * pint1 (gtk (s / 2) PI) (gtk_int (s / 2) PI) (b n)).
    + rewrite H2 in H1; lra.
    + apply Rmult_le_compat_l; [ exact EM0 | exact H3 ].
Qed.

(* --- the tail interchange --- *)

Theorem tail_series : forall s, 1 < s -> Un_cv (fun M => sum_f_R0 (gtl s) M) (T s).
Proof.
  intros s Hs eps Heps.
  assert (Hcv : Un_cv (fun M => Em M * gtail (s / 2) PI PI_RGT_0) 0).
  { replace 0 with (0 * gtail (s / 2) PI PI_RGT_0) by ring.
    apply (CV_mult Em (fun _ => gtail (s / 2) PI PI_RGT_0) 0 (gtail (s / 2) PI PI_RGT_0));
      [ exact Em_cv | apply Un_cv_const ]. }
  destruct (Hcv eps Heps) as [N HN]; exists N; intros M HM.
  specialize (HN M HM); unfold R_dist in HN |- *; rewrite Rminus_0_r in HN.
  pose proof (bound_M s M Hs) as [Hlo Hhi].
  rewrite Rabs_right in HN by (apply Rle_ge; apply Rle_trans with (T s - sum_f_R0 (gtl s) M); assumption).
  rewrite Rabs_left1 by lra.
  replace (- (sum_f_R0 (gtl s) M - T s)) with (T s - sum_f_R0 (gtl s) M) by ring.
  lra.
Qed.

Print Assumptions tail_series.

(* ================================================================= *)
(*  END MellinTailSeries.v.  T s = Σ_k gtail (s/2)(π(k+1)²).          *)
(* ================================================================= *)
