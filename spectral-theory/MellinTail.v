(* ================================================================= *)
(*  MellinTail.v  —  Riemann FE milestone R1, file 5:               *)
(*  the convergent tail integral  T(s) = ∫₁^∞ t^{s/2−1} ψ(t) dt.      *)
(*                                                                    *)
(*  ψ decays faster than any power: for any exponent N,               *)
(*     ψ(t) ≤ C · t^{−N}   (t ≥ 1)                                    *)
(*  (Psi_upper + a single term of the exp series, exp_lb2).  Choosing *)
(*  N > s/2 makes t^{s/2−1}ψ(t) ≤ C·t^{s/2−1−N} with exponent < −1,    *)
(*  so the partial integrals are bounded by the elementary            *)
(*  ∫₁^∞ (MellinElem) and T(s) exists (improper_bounded_cv).          *)
(*  Integrands are clamped (Rmax 1) for global integrability.         *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import RiemannPsi RiemannPsiCont MellinElem ImproperCv1
        ZetaContinuation JacobiTheta GammaFunction.
Open Scope R_scope.

(* --- a Type-level "some N with x < N" (avoids Prop-ex elimination) --- *)

Lemma nat_gt : forall x : R, { n : nat | x < INR (S n) }.
Proof.
  intro x; exists (Z.to_nat (up x)).
  destruct (archimed x) as [H1 _].
  rewrite S_INR, INR_IZR_INZ.
  assert (Hz : (Z.of_nat (Z.to_nat (up x)) >= up x)%Z) by lia.
  apply IZR_ge in Hz; lra.
Qed.

(* --- exponential-over-power decay of e^{−πt} --- *)

Lemma exp_decay_power : forall k t, 1 <= t ->
  exp (- (PI * t)) <= INR (S k) ^ (S k) / PI ^ (S k) * Rpower t (- INR (S k)).
Proof.
  intros k t Ht.
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (Htpos : 0 < t) by lra.
  assert (Hpt : 0 <= PI * t) by nra.
  pose proof (exp_lb2 k (PI * t) Hpt) as Hlb.
  set (Q := INR (S k) ^ (S k)).
  set (P := (PI * t) ^ (S k)).
  assert (HQ : 0 < Q) by (unfold Q; apply pow_lt; apply lt_0_INR; lia).
  assert (HP : 0 < P) by (unfold P; apply pow_lt; nra).
  assert (Hinv : / exp (PI * t) <= Q / P).
  { apply Rle_trans with (/ (P / Q)).
    - apply Rinv_le_contravar; [ apply Rdiv_lt_0_compat; [ exact HP | exact HQ ] | exact Hlb ].
    - unfold Rdiv; rewrite Rinv_mult, Rinv_inv; apply Req_le; ring. }
  assert (Heq : Q / P = INR (S k) ^ (S k) / PI ^ (S k) * Rpower t (- INR (S k))).
  { unfold Q, P; rewrite Rpow_mult_distr, Rpower_Ropp, (Rpower_pow (S k) t Htpos).
    field; split; [ apply Rgt_not_eq; apply pow_lt; exact Htpos
                  | apply Rgt_not_eq; apply pow_lt; exact HPI ]. }
  rewrite exp_Ropp; rewrite Heq in Hinv; exact Hinv.
Qed.

(* --- power domination of ψ --- *)

Lemma Psi_power_bound : forall k, { C : R | 0 <= C /\
  forall t, 1 <= t -> Psi t <= C * Rpower t (- INR (S k)) }.
Proof.
  intro k.
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (HD : 0 < 1 - exp (- PI)).
  { pose proof (theta_ratio_lt1 1 Rlt_0_1) as Hr; replace (PI * 1) with PI in Hr by ring; lra. }
  set (C0 := INR (S k) ^ (S k) / PI ^ (S k)).
  assert (HC0 : 0 <= C0)
    by (unfold C0; apply Rle_mult_inv_pos;
        [ apply pow_le; apply pos_INR | apply pow_lt; exact HPI ]).
  exists (C0 / (1 - exp (- PI))); split.
  - apply Rle_mult_inv_pos; [ exact HC0 | exact HD ].
  - intros t Ht.
    assert (Htpos : 0 < t) by lra.
    assert (Hde : exp (- (PI * t)) <= C0 * Rpower t (- INR (S k)))
      by (unfold C0; apply exp_decay_power; exact Ht).
    apply Rle_trans with (exp (- (PI * t)) / (1 - exp (- PI))).
    + apply Rle_trans with (exp (- (PI * t)) / (1 - exp (- (PI * t)))).
      * apply (Psi_upper t Htpos).
      * assert (Hmono : 1 - exp (- PI) <= 1 - exp (- (PI * t))).
        { assert (exp (- (PI * t)) <= exp (- PI)).
          { apply exp_le_compat; apply Ropp_le_contravar; nra. }
          lra. }
        assert (Hden : 0 < 1 - exp (- (PI * t)))
          by (pose proof (theta_ratio_lt1 t Htpos); lra).
        unfold Rdiv; apply Rmult_le_compat_l; [ left; apply exp_pos | ].
        apply Rinv_le_contravar; [ exact HD | exact Hmono ].
    + unfold Rdiv.
      replace (C0 * / (1 - exp (- PI)) * Rpower t (- INR (S k)))
        with (C0 * Rpower t (- INR (S k)) * / (1 - exp (- PI))) by ring.
      apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact HD | exact Hde ].
Qed.

(* --- the clamped tail integrand --- *)

Definition wker (s : R) (u : R) : R := Rpower (clamp u) (s / 2 - 1) * Psi (clamp u).

Lemma wker_nonneg : forall s u, 0 <= wker s u.
Proof.
  intros s u; unfold wker; apply Rmult_le_pos;
    [ left; unfold Rpower; apply exp_pos | apply Psi_nonneg ].
Qed.

Lemma cont_wker : forall s, continuity (wker s).
Proof.
  intros s u; unfold wker; apply continuity_pt_mult.
  - apply (cont_eker (s / 2 - 1)).
  - apply (continuity_pt_comp clamp Psi u); [ apply cont_clamp | apply Psi_cont; apply clamp_pos ].
Qed.

Lemma wker_int : forall s x y, Riemann_integrable (wker s) x y.
Proof.
  intros s x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_wker ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_wker ].
Qed.

(* --- the domination on [1,∞) --- *)

Lemma w_dom : forall s n C, 0 <= C ->
  (forall t, 1 <= t -> Psi t <= C * Rpower t (- INR (S n))) ->
  forall u, 1 <= u -> wker s u <= C * eker (s / 2 - 1 - INR (S n)) u.
Proof.
  intros s n C HC Hbound u Hu; unfold wker, eker; rewrite (clamp_id u Hu).
  apply Rle_trans with (Rpower u (s / 2 - 1) * (C * Rpower u (- INR (S n)))).
  - apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | apply Hbound; exact Hu ].
  - apply Req_le.
    replace (s / 2 - 1 - INR (S n)) with ((s / 2 - 1) + - INR (S n)) by ring.
    rewrite Rpower_plus; ring.
Qed.

(* --- the zero integrand's improper integral --- *)

Lemma improper_zero : ImproperCv1 (fct_cte 0) (fun a d => RiemannInt_P14 a d 0) 0.
Proof.
  intros b Hb1 Hbinf eps Heps; exists 0%nat; intros n _.
  unfold R_dist, pint1; cbv beta.
  rewrite (RiemannInt_P15 (RiemannInt_P14 1 (b n) 0)).
  replace (0 * (b n - 1) - 0) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

(* --- T(s) exists --- *)

Theorem T_exists : forall s, { I : R | ImproperCv1 (wker s) (wker_int s) I }.
Proof.
  intro s.
  destruct (nat_gt (s / 2)) as [n Hn].
  set (b := s / 2 - 1 - INR (S n)).
  assert (Hb : b < -1) by (unfold b; lra).
  assert (Hb1 : b + 1 <> 0) by lra.
  destruct (Psi_power_bound n) as [C [HC0 HCbound]].
  assert (Ddint : forall a d, Riemann_integrable (fun x => C * eker b x) a d).
  { intros a d; destruct (Rle_dec a d) as [H | H].
    - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply continuity_pt_scal; apply cont_eker ].
    - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
        [ lra | intros x _; apply continuity_pt_scal; apply cont_eker ]. }
  assert (D0int : forall a d, Riemann_integrable (fun x => fct_cte 0 x + C * eker b x) a d).
  { intros a d; destruct (Rle_dec a d) as [H | H].
    - apply continuity_implies_RiemannInt; [ exact H | intros x _;
        apply continuity_pt_plus; [ apply continuity_pt_const; intros p q; reflexivity
                                  | apply continuity_pt_scal; apply cont_eker ] ].
    - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
        [ lra | intros x _; apply continuity_pt_plus;
          [ apply continuity_pt_const; intros p q; reflexivity
          | apply continuity_pt_scal; apply cont_eker ] ]. }
  assert (HDcv : ImproperCv1 (fun x => C * eker b x) Ddint (C * (- / (b + 1)))).
  { apply (improper_ext (fun x => fct_cte 0 x + C * eker b x) (fun x => C * eker b x)
             D0int Ddint (C * (- / (b + 1)))); [ intros x _; unfold fct_cte; ring | ].
    replace (C * (- / (b + 1))) with (0 + C * (- / (b + 1))) by ring.
    apply (improper_linear (fct_cte 0) (eker b) C (fun a d => RiemannInt_P14 a d 0)
             (eker_int b) D0int 0 (- / (b + 1)));
      [ apply improper_zero | apply eker_improper; exact Hb ]. }
  apply (improper_bounded_cv (wker s) (wker_int s) (fun x _ => wker_nonneg s x)).
  exists (C * (- / (b + 1))); intros A HA.
  apply Rle_trans with (pint1 (fun x => C * eker b x) Ddint A).
  - unfold pint1; apply RiemannInt_P19; [ exact HA | intros x [Hx1 HxA] ].
    apply (w_dom s n C HC0 HCbound x); lra.
  - apply (pint1_le_improper (fun x => C * eker b x) Ddint (C * (- / (b + 1))) HDcv);
      [ intros x _; apply Rmult_le_pos; [ exact HC0 | left; apply eker_pos ] | exact HA ].
Qed.

Definition T (s : R) : R := proj1_sig (T_exists s).

Theorem T_spec : forall s, ImproperCv1 (wker s) (wker_int s) (T s).
Proof. intro s; exact (proj2_sig (T_exists s)). Qed.

Print Assumptions T_spec.

(* ================================================================= *)
(*  END MellinTail.v                                                 *)
(*  T(s) = ∫₁^∞ t^{s/2−1} ψ(t) dt, convergent for every real s.       *)
(* ================================================================= *)
