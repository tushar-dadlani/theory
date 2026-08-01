(* ================================================================= *)
(*  MellinElem.v  —  Riemann FE milestone R1, file 4:               *)
(*  the elementary power integral  ∫₁^∞ u^a du = −1/(a+1)  (a < −1).  *)
(*                                                                    *)
(*  Integrands are clamped by `Rmax 1` so they are globally continuous *)
(*  (the true u^a blows up at 0 for a<0); on [1,∞) the clamp is the    *)
(*  identity, so every ∫₁^A value is unchanged.  The antiderivative    *)
(*  u^{a+1}/(a+1) (Rpower_deriv + FTC_antideriv) gives the finite      *)
(*  integral, and Rpower_neg_cv0 sends the upper endpoint to 0.        *)
(*  Also `pint1_le_improper`: a nonnegative integrand's partial       *)
(*  integral never exceeds its improper value (monotone sup).         *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia FunctionalExtensionality.
Require Import ImproperCv1 ZetaContinuation ContinuousCoV JacobiTheta.
Open Scope R_scope.

(* --- the clamp  min-floored at 1 --- *)

Definition clamp (u : R) : R := Rmax 1 u.

Lemma clamp_ge1 : forall u, 1 <= clamp u. Proof. intro u; apply Rmax_l. Qed.
Lemma clamp_pos : forall u, 0 < clamp u. Proof. intro u; pose proof (clamp_ge1 u); lra. Qed.
Lemma clamp_id : forall u, 1 <= u -> clamp u = u. Proof. intros u H; apply Rmax_right; exact H. Qed.

Lemma Rmax1_eq : forall u, Rmax 1 u = (1 + u + Rabs (1 - u)) / 2.
Proof.
  intro u; unfold Rmax; destruct (Rle_dec 1 u) as [H | H];
    [ rewrite Rabs_left1 by lra | rewrite Rabs_right by lra ]; lra.
Qed.

Lemma cont_clamp : continuity clamp.
Proof.
  assert (Heq : clamp = fun u => (1 + u + Rabs (1 - u)) / 2)
    by (apply functional_extensionality; intro u; apply Rmax1_eq).
  rewrite Heq; intro u.
  apply (continuity_pt_mult (fun u => 1 + u + Rabs (1 - u)) (fun _ => / 2) u).
  - apply continuity_pt_plus.
    + apply continuity_pt_plus.
      * apply continuity_pt_const; intros p q; reflexivity.
      * apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
    + apply (continuity_pt_comp (fun u => 1 - u) Rabs u).
      * apply continuity_pt_minus;
          [ apply continuity_pt_const; intros p q; reflexivity
          | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
      * apply Rcontinuity_abs.
  - apply continuity_pt_const; intros p q; reflexivity.
Qed.

(* --- the clamped power integrand --- *)

Definition eker (a : R) (u : R) : R := Rpower (clamp u) a.

Lemma eker_pos : forall a u, 0 < eker a u.
Proof. intros a u; unfold eker, Rpower; apply exp_pos. Qed.

Lemma cont_Rpower_pos : forall a w, 0 < w -> continuity_pt (fun w => Rpower w a) w.
Proof.
  intros a w Hw; apply derivable_continuous_pt; exists (a * Rpower w (a - 1));
    apply Rpower_deriv; exact Hw.
Qed.

Lemma cont_eker : forall a, continuity (eker a).
Proof.
  intros a u; unfold eker; apply (continuity_pt_comp clamp (fun w => Rpower w a) u);
    [ apply cont_clamp | apply cont_Rpower_pos; apply clamp_pos ].
Qed.

Lemma eker_int : forall a x y, Riemann_integrable (eker a) x y.
Proof.
  intros a x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_eker ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_eker ].
Qed.

(* --- the finite integral via FTC --- *)

Lemma eker_pint : forall a A, 1 <= A -> a + 1 <> 0 ->
  pint1 (eker a) (eker_int a) A
  = / (a + 1) * Rpower A (a + 1) - / (a + 1) * Rpower 1 (a + 1).
Proof.
  intros a A HA Ha1; unfold pint1.
  set (F := fun x => / (a + 1) * Rpower x (a + 1)).
  assert (Hanti : antiderivative (eker a) F 1 A).
  { split; [ | exact HA ]. intros x [Hx1 HxA].
    assert (Hxpos : 0 < x) by lra.
    assert (Hd : derivable_pt_lim F x (Rpower x a)).
    { unfold F; pose proof (Rpower_deriv (a + 1) x Hxpos) as Hrp.
      apply (derivable_pt_lim_scal (fun y => Rpower y (a + 1)) (/ (a + 1)) x
               ((a + 1) * Rpower x (a + 1 - 1))) in Hrp.
      replace (Rpower x a) with (/ (a + 1) * ((a + 1) * Rpower x (a + 1 - 1)));
        [ exact Hrp | replace (a + 1 - 1) with a by ring; field; exact Ha1 ]. }
    exists (exist (fun l => derivable_pt_lim F x l) (Rpower x a) Hd).
    unfold eker; rewrite (clamp_id x Hx1); reflexivity. }
  rewrite (FTC_antideriv (eker a) F 1 A HA (fun x _ => cont_eker a x) (eker_int a 1 A) Hanti).
  unfold F; reflexivity.
Qed.

(* --- the improper value --- *)

Lemma cv_infty_Sn : cv_infty (fun k => INR (S k)).
Proof.
  intro M; destruct (INR_unbounded M) as [N HN]; exists N; intros n Hn;
    rewrite S_INR; pose proof (le_INR N n Hn); lra.
Qed.

Theorem eker_improper : forall a, a < -1 -> ImproperCv1 (eker a) (eker_int a) (- / (a + 1)).
Proof.
  intros a Ha.
  assert (Ha1 : a + 1 <> 0) by lra.
  assert (Ha1neg : a + 1 < 0) by lra.
  apply (improper_welldef1 (eker a) (eker_int a) (fun x _ => Rlt_le _ _ (eker_pos a x))
           (fun k => INR (S k)) (- / (a + 1))).
  - intro k; rewrite S_INR; pose proof (pos_INR k); lra.
  - apply cv_infty_Sn.
  - apply (Un_cv_ext (fun k => / (a + 1) * Rpower (INR (S k)) (a + 1)
                             - / (a + 1) * Rpower 1 (a + 1))).
    + intro k; symmetry; apply eker_pint;
        [ rewrite S_INR; pose proof (pos_INR k); lra | exact Ha1 ].
    + rewrite Rpower_base1.
      replace (- / (a + 1)) with (/ (a + 1) * 0 - / (a + 1) * 1) by (field; exact Ha1).
      apply CV_minus.
      * apply (CV_mult (fun _ => / (a + 1)) (fun k => Rpower (INR (S k)) (a + 1))
                 (/ (a + 1)) 0); [ apply Un_cv_const | apply Rpower_neg_cv0; exact Ha1neg ].
      * apply Un_cv_const.
Qed.

(* --- partial integral never exceeds the improper value --- *)

Theorem pint1_le_improper : forall f Hf I, ImproperCv1 f Hf I ->
  (forall x, 1 <= x -> 0 <= f x) -> forall A, 1 <= A -> pint1 f Hf A <= I.
Proof.
  intros f Hf I HI Hpos A HA.
  set (c := fun k => A + INR k).
  assert (Hc1 : forall k, 1 <= c k) by (intro k; unfold c; pose proof (pos_INR k); lra).
  assert (Hcinf : cv_infty c).
  { intro M; destruct (INR_unbounded (M - A)) as [N HN]; exists N; intros n Hn;
      unfold c; pose proof (le_INR N n Hn); lra. }
  apply (Un_cv_le (fun _ => pint1 f Hf A) (fun k => pint1 f Hf (c k)) (pint1 f Hf A) I).
  - intro k; apply (pint1_mono f Hf Hpos A (c k) HA); unfold c; pose proof (pos_INR k); lra.
  - apply Un_cv_const.
  - apply HI; [ exact Hc1 | exact Hcinf ].
Qed.

Print Assumptions eker_improper.

(* ================================================================= *)
(*  END MellinElem.v                                                 *)
(*  ∫₁^∞ u^a du = −1/(a+1)  (a < −1);  ∫₁^A f ≤ ∫₁^∞ f  for f ≥ 0.     *)
(* ================================================================= *)
