(* ================================================================= *)
(*  GammaReal.v  —  Riemann FE milestone R2a, file 3:               *)
(*  the real Gamma function and the two-parameter Mellin integral.   *)
(*                                                                    *)
(*     mellin a c := ∫₀^∞ t^{a-1} e^{-ct} dt   (a>0, c>0),            *)
(*     Gam a      := mellin a 1.                                      *)
(*  Split at t=1: the near-0 piece (∫₀^1, ImproperCv0) is bounded by  *)
(*  ∫_ε^1 t^{a-1} = (1-ε^a)/a ≤ 1/a — a bound UNIFORM in c; the tail  *)
(*  (∫₁^∞, ImproperCv1) converges because e^{-ct} beats any power     *)
(*  (exp_lb2, mirroring MellinTail).  Γ(s/2) will enter R3 only as an *)
(*  opaque factor, so no value of Γ is computed here.                *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import ImproperCv0 ImproperCv1 MellinElem MellinTail
        ZetaContinuation GammaFunction RpowerZero ContinuousCoV JacobiTheta.
Open Scope R_scope.

(* ================================================================= *)
(*  Near-0 piece:  ∫₀^1 t^{a-1} e^{-ct} dt.                          *)
(* ================================================================= *)

Definition gnk (a c : R) (t : R) : R := Rpower t (a - 1) * exp (- (c * t)).

Lemma cont_gnk : forall a c t, 0 < t -> continuity_pt (gnk a c) t.
Proof.
  intros a c t Ht; unfold gnk; apply continuity_pt_mult.
  - apply cont_Rpower_pos; exact Ht.
  - apply (continuity_pt_comp (fun t => - (c * t)) exp t).
    + apply continuity_pt_opp; apply (continuity_pt_scal (fun t => t) c t);
        apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
    + apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

Lemma Hf_near : forall a c, forall x y, 0 < x -> x <= y -> Riemann_integrable (gnk a c) x y.
Proof.
  intros a c x y Hx Hxy; apply continuity_implies_RiemannInt;
    [ exact Hxy | intros t Ht; apply cont_gnk; lra ].
Qed.

(* the pure power integrand on [x,1] and its exact integral (FTC) *)
Lemma rpow_ri : forall a x y, 0 < x -> x <= y ->
  Riemann_integrable (fun t => Rpower t (a - 1)) x y.
Proof.
  intros a x y Hx Hxy; apply continuity_implies_RiemannInt;
    [ exact Hxy | intros t Ht; apply cont_Rpower_pos; lra ].
Qed.

Lemma rpow_pint : forall a x (Hx : 0 < x) (Hx1 : x <= 1), a <> 0 ->
  RiemannInt (rpow_ri a x 1 Hx Hx1) = / a * Rpower 1 a - / a * Rpower x a.
Proof.
  intros a x Hx Hx1 Ha.
  set (F := fun t => / a * Rpower t a).
  assert (Hanti : antiderivative (fun t => Rpower t (a - 1)) F x 1).
  { split; [ | exact Hx1 ]. intros t [Ht1 HtA].
    assert (Htpos : 0 < t) by lra.
    assert (Hd : derivable_pt_lim F t (Rpower t (a - 1))).
    { unfold F; pose proof (Rpower_deriv a t Htpos) as Hrp.
      apply (derivable_pt_lim_scal (fun y => Rpower y a) (/ a) t (a * Rpower t (a - 1))) in Hrp.
      replace (Rpower t (a - 1)) with (/ a * (a * Rpower t (a - 1)));
        [ exact Hrp | field; exact Ha ]. }
    exists (exist (fun l => derivable_pt_lim F t l) (Rpower t (a - 1)) Hd); reflexivity. }
  rewrite (FTC_antideriv (fun t => Rpower t (a - 1)) F x 1 Hx1
             (fun t _ => cont_Rpower_pos (a - 1) t ltac:(lra)) (rpow_ri a x 1 Hx Hx1) Hanti).
  unfold F; reflexivity.
Qed.

Lemma gnear_bound : forall a c x (Hx : 0 < x) (Hx1 : x <= 1), 0 < a -> 0 < c ->
  rint01 (gnk a c) (Hf_near a c) x <= / a.
Proof.
  intros a c x Hx Hx1 Ha Hc.
  rewrite (rint01_val (gnk a c) (Hf_near a c) x Hx Hx1).
  apply Rle_trans with (RiemannInt (rpow_ri a x 1 Hx Hx1)).
  - apply RiemannInt_P19; [ exact Hx1 | intros t [Ht1 HtA]; unfold gnk ].
    rewrite <- (Rmult_1_r (Rpower t (a - 1))) at 2.
    apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | ].
    rewrite <- exp_0; apply Rlt_le, exp_increasing.
    assert (0 < t) by lra; nra.
  - rewrite (rpow_pint a x Hx Hx1 (Rgt_not_eq _ _ Ha)), Rpower_base1.
    assert (0 <= Rpower x a) by (left; unfold Rpower; apply exp_pos).
    assert (0 < / a) by (apply Rinv_0_lt_compat; exact Ha).
    nra.
Qed.

Lemma gnk_nonneg : forall a c t, 0 <= gnk a c t.
Proof.
  intros a c t; unfold gnk; apply Rmult_le_pos;
    [ left; unfold Rpower; apply exp_pos | left; apply exp_pos ].
Qed.

Definition gnear_sig (a c : R) (Ha : 0 < a) (Hc : 0 < c) :
  { I : R | ImproperCv0 (gnk a c) (Hf_near a c) I }.
Proof.
  apply (improper_bounded_cv0 (gnk a c) (Hf_near a c) (fun x _ _ => gnk_nonneg a c x)).
  exists (/ a); intros x Hx Hx1; apply gnear_bound; assumption.
Defined.

Definition gnear (a c : R) (Ha : 0 < a) (Hc : 0 < c) : R := proj1_sig (gnear_sig a c Ha Hc).

(* ================================================================= *)
(*  Tail piece:  ∫₁^∞ t^{a-1} e^{-ct} dt   (clamped, mirrors MellinTail). *)
(* ================================================================= *)

Lemma exp_c_decay_power : forall c k t, 0 < c -> 1 <= t ->
  exp (- (c * t)) <= INR (S k) ^ (S k) / c ^ (S k) * Rpower t (- INR (S k)).
Proof.
  intros c k t Hc Ht.
  assert (Htpos : 0 < t) by lra.
  assert (Hct : 0 <= c * t) by nra.
  pose proof (exp_lb2 k (c * t) Hct) as Hlb.
  set (Q := INR (S k) ^ (S k)).
  set (P := (c * t) ^ (S k)).
  assert (HQ : 0 < Q) by (unfold Q; apply pow_lt; apply lt_0_INR; lia).
  assert (HP : 0 < P) by (unfold P; apply pow_lt; nra).
  assert (Hinv : / exp (c * t) <= Q / P).
  { apply Rle_trans with (/ (P / Q)).
    - apply Rinv_le_contravar; [ apply Rdiv_lt_0_compat; [ exact HP | exact HQ ] | exact Hlb ].
    - unfold Rdiv; rewrite Rinv_mult, Rinv_inv; apply Req_le; ring. }
  assert (Heq : Q / P = INR (S k) ^ (S k) / c ^ (S k) * Rpower t (- INR (S k))).
  { unfold Q, P; rewrite Rpow_mult_distr, Rpower_Ropp, (Rpower_pow (S k) t Htpos).
    field; split; [ apply Rgt_not_eq; apply pow_lt; exact Htpos
                  | apply Rgt_not_eq; apply pow_lt; exact Hc ]. }
  rewrite exp_Ropp; rewrite Heq in Hinv; exact Hinv.
Qed.

Definition gtk (a c : R) (u : R) : R := Rpower (clamp u) (a - 1) * exp (- (c * clamp u)).

Lemma cont_gtk : forall a c, continuity (gtk a c).
Proof.
  intros a c u; unfold gtk; apply continuity_pt_mult.
  - apply (cont_eker (a - 1)).
  - apply (continuity_pt_comp clamp (fun w => exp (- (c * w))) u); [ apply cont_clamp | ].
    apply (continuity_pt_comp (fun w => - (c * w)) exp (clamp u)).
    + apply continuity_pt_opp; apply (continuity_pt_scal (fun w => w) c (clamp u));
        apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
    + apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

Lemma gtk_int : forall a c x y, Riemann_integrable (gtk a c) x y.
Proof.
  intros a c x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_gtk ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_gtk ].
Qed.

Lemma gtk_nonneg : forall a c u, 0 <= gtk a c u.
Proof.
  intros a c u; unfold gtk; apply Rmult_le_pos;
    [ left; unfold Rpower; apply exp_pos | left; apply exp_pos ].
Qed.

Lemma gtk_dom : forall a c n C, 0 <= C ->
  (forall t, 1 <= t -> exp (- (c * t)) <= C * Rpower t (- INR (S n))) ->
  forall u, 1 <= u -> gtk a c u <= C * eker (a - 1 - INR (S n)) u.
Proof.
  intros a c n C HC Hbound u Hu; unfold gtk, eker; rewrite (clamp_id u Hu).
  apply Rle_trans with (Rpower u (a - 1) * (C * Rpower u (- INR (S n)))).
  - apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | apply Hbound; exact Hu ].
  - apply Req_le.
    replace (a - 1 - INR (S n)) with ((a - 1) + - INR (S n)) by ring.
    rewrite Rpower_plus; ring.
Qed.

Definition gtail_sig (a c : R) (Hc : 0 < c) :
  { I : R | ImproperCv1 (gtk a c) (gtk_int a c) I }.
Proof.
  destruct (nat_gt a) as [n Hn].
  set (b := a - 1 - INR (S n)).
  assert (Hb : b < -1) by (unfold b; lra).
  set (C := INR (S n) ^ (S n) / c ^ (S n)).
  assert (HC0 : 0 <= C)
    by (unfold C; apply Rle_mult_inv_pos;
        [ apply pow_le; apply pos_INR | apply pow_lt; exact Hc ]).
  assert (Hbound : forall t, 1 <= t -> exp (- (c * t)) <= C * Rpower t (- INR (S n)))
    by (intros t Ht; unfold C; apply exp_c_decay_power; [ exact Hc | exact Ht ]).
  assert (Ddint : forall x y, Riemann_integrable (fun u => C * eker b u) x y).
  { intros x y; destruct (Rle_dec x y) as [H | H];
      [ apply continuity_implies_RiemannInt; [ exact H | intros z _; apply continuity_pt_scal; apply cont_eker ]
      | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros z _; apply continuity_pt_scal; apply cont_eker ] ]. }
  assert (D0int : forall x y, Riemann_integrable (fun u => fct_cte 0 u + C * eker b u) x y).
  { intros x y; destruct (Rle_dec x y) as [H | H];
      [ apply continuity_implies_RiemannInt; [ exact H | intros z _;
          apply continuity_pt_plus; [ apply continuity_pt_const; intros p q; reflexivity
                                    | apply continuity_pt_scal; apply cont_eker ] ]
      | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros z _;
          apply continuity_pt_plus; [ apply continuity_pt_const; intros p q; reflexivity
                                    | apply continuity_pt_scal; apply cont_eker ] ] ]. }
  assert (HDcv : ImproperCv1 (fun u => C * eker b u) Ddint (C * (- / (b + 1)))).
  { apply (improper_ext (fun u => fct_cte 0 u + C * eker b u) (fun u => C * eker b u)
             D0int Ddint (C * (- / (b + 1)))); [ intros x _; unfold fct_cte; ring | ].
    replace (C * (- / (b + 1))) with (0 + C * (- / (b + 1))) by ring.
    apply (improper_linear (fct_cte 0) (eker b) C (fun x y => RiemannInt_P14 x y 0)
             (eker_int b) D0int 0 (- / (b + 1)));
      [ apply improper_zero | apply eker_improper; exact Hb ]. }
  apply (improper_bounded_cv (gtk a c) (gtk_int a c) (fun x _ => gtk_nonneg a c x)).
  exists (C * (- / (b + 1))); intros A HA.
  apply Rle_trans with (pint1 (fun u => C * eker b u) Ddint A).
  - unfold pint1; apply RiemannInt_P19; [ exact HA | intros x [Hx1 HxA] ].
    apply (gtk_dom a c n C HC0 Hbound x); lra.
  - apply (pint1_le_improper (fun u => C * eker b u) Ddint (C * (- / (b + 1))) HDcv);
      [ intros x _; apply Rmult_le_pos; [ exact HC0 | left; apply eker_pos ] | exact HA ].
Qed.

Definition gtail (a c : R) (Hc : 0 < c) : R := proj1_sig (gtail_sig a c Hc).

(* ================================================================= *)
(*  Gamma and the two-parameter Mellin integral.                    *)
(* ================================================================= *)

Definition mellin (a c : R) (Ha : 0 < a) (Hc : 0 < c) : R := gnear a c Ha Hc + gtail a c Hc.

Definition Gam (a : R) (Ha : 0 < a) : R := mellin a 1 Ha Rlt_0_1.

Lemma gnear_pos : forall a c (Ha : 0 < a) (Hc : 0 < c), 0 <= gnear a c Ha Hc.
Proof.
  intros a c Ha Hc; unfold gnear.
  destruct (gnear_sig a c Ha Hc) as [I HI]; simpl.
  apply (Un_cv_le (fun _ => 0) (fun k => rint01 (gnk a c) (Hf_near a c) (/ (1 + INR k))) 0 I).
  - intro k; assert (Hk0 : 0 < / (1 + INR k))
      by (apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
    assert (Hk1 : / (1 + INR k) <= 1) by (apply inv_le_1; pose proof (pos_INR k); lra).
    rewrite (rint01_val (gnk a c) (Hf_near a c) _ Hk0 Hk1).
    pose proof (RiemannInt_P15 (RiemannInt_P14 (/ (1 + INR k)) 1 0)) as Hz.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 (/ (1 + INR k)) 1 0)).
    + rewrite Hz; ring_simplify; apply Rle_refl.
    + apply RiemannInt_P19; [ exact Hk1 | intros t _; unfold fct_cte; apply gnk_nonneg ].
  - intros eps He; exists 0%nat; intros n _; unfold R_dist;
      replace (0 - 0) with 0 by ring; rewrite Rabs_R0; exact He.
  - apply HI; [ intro k; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra
             | intro k; apply inv_le_1; pose proof (pos_INR k); lra
             | apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ] ].
Qed.

Lemma gtail_pos : forall a c (Hc : 0 < c), 0 <= gtail a c Hc.
Proof.
  intros a c Hc; unfold gtail.
  destruct (gtail_sig a c Hc) as [I HI]; simpl.
  apply (Un_cv_le (fun _ => 0) (fun k => pint1 (gtk a c) (gtk_int a c) (1 + INR k)) 0 I).
  - intro k; unfold pint1.
    pose proof (RiemannInt_P15 (RiemannInt_P14 1 (1 + INR k) 0)) as Hz.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 1 (1 + INR k) 0)).
    + rewrite Hz; ring_simplify; apply Rle_refl.
    + apply RiemannInt_P19; [ pose proof (pos_INR k); lra | intros t _; unfold fct_cte; apply gtk_nonneg ].
  - intros eps He; exists 0%nat; intros n _; unfold R_dist;
      replace (0 - 0) with 0 by ring; rewrite Rabs_R0; exact He.
  - apply HI; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ].
Qed.

Theorem Gam_nonneg : forall a (Ha : 0 < a), 0 <= Gam a Ha.
Proof.
  intros a Ha; unfold Gam, mellin.
  pose proof (gnear_pos a 1 Ha Rlt_0_1); pose proof (gtail_pos a 1 Rlt_0_1); lra.
Qed.

Print Assumptions Gam_nonneg.

(* ================================================================= *)
(*  END GammaReal.v  —  Gam a = ∫₀^∞ t^{a-1}e^{-t}dt ≥ 0  (a > 0).    *)
(* ================================================================= *)
