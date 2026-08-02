(* ================================================================= *)
(*  CexpRemainder.v  —  the quadratic remainder bound for Cexpf.       *)
(*                                                                    *)
(*  |Cexpf w - 1 - w| <= 3 * |w|^2 * exp |w|.                          *)
(*  The make-or-break estimate for the difference-quotient argument   *)
(*  that shows the theta-tail integral is holomorphic.  Proved by an  *)
(*  order-2 bound (double MVT) on the two real components.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField EulerFormula Cmodulus CexpFull.
Open Scope R_scope.

(* --- linear/derivative helpers --- *)

Lemma dts : forall s t, derivable_pt_lim (fun x => x * s) t s.
Proof.
  intros s t.
  assert (H : derivable_pt_lim (fun x => x * s) t (1 * s + t * 0))
    by (apply derivable_pt_lim_mult; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]).
  assert (Heq : 1 * s + t * 0 = s) by ring; rewrite Heq in H; exact H.
Qed.

Lemma dexpts : forall s t, derivable_pt_lim (fun x => exp (x * s)) t (exp (t * s) * s).
Proof.
  intros s t.
  apply (derivable_pt_lim_comp (fun x => x * s) exp t s (exp (t * s)));
    [ apply dts | apply derivable_pt_lim_exp ].
Qed.

Lemma dcosts : forall r t, derivable_pt_lim (fun x => cos (x * r)) t (- sin (t * r) * r).
Proof.
  intros r t.
  apply (derivable_pt_lim_comp (fun x => x * r) cos t r (- sin (t * r)));
    [ apply dts | apply derivable_pt_lim_cos ].
Qed.

Lemma dsints : forall r t, derivable_pt_lim (fun x => sin (x * r)) t (cos (t * r) * r).
Proof.
  intros r t.
  apply (derivable_pt_lim_comp (fun x => x * r) sin t r (cos (t * r)));
    [ apply dts | apply derivable_pt_lim_sin ].
Qed.

Lemma sqrt2_bound : sqrt 2 <= 3 / 2.
Proof.
  replace (3 / 2) with (sqrt (Rsqr (3 / 2))) by (rewrite sqrt_Rsqr by lra; reflexivity).
  apply sqrt_le_1_alt. unfold Rsqr; lra.
Qed.

(* --- order-2 bound via double MVT --- *)

Lemma order2_bound : forall (f df ddf : R -> R) (M : R), 0 <= M ->
  (forall t, 0 <= t <= 1 -> derivable_pt_lim f t (df t)) ->
  (forall t, 0 <= t <= 1 -> derivable_pt_lim df t (ddf t)) ->
  (forall t, 0 <= t <= 1 -> Rabs (ddf t) <= M) ->
  Rabs (f 1 - f 0 - df 0) <= M.
Proof.
  intros f df ddf M HM Hf Hdf Hbd.
  set (g := fun t => f t - df 0 * t).
  set (dg := fun t => df t - df 0).
  assert (Hg : forall t, 0 <= t <= 1 -> derivable_pt_lim g t (dg t)).
  { intros t Ht. unfold g, dg.
    apply derivable_pt_lim_minus; [ apply Hf; exact Ht | ].
    assert (Hc : derivable_pt_lim (fun x => df 0 * x) t (df 0 * 1))
      by (apply (derivable_pt_lim_scal (fun x => x) (df 0) t 1); apply derivable_pt_lim_id).
    assert (Heq : df 0 * 1 = df 0) by ring; rewrite Heq in Hc; exact Hc. }
  destruct (MVT_cor2 g dg 0 1 Rlt_0_1 (fun c Hc => Hg c Hc)) as [c [Hgc Hc]].
  assert (Hc1 : c <= 1) by lra.
  assert (Hdf0c : forall d, 0 <= d <= c -> derivable_pt_lim df d (ddf d))
    by (intros d Hd; apply Hdf; lra).
  destruct (MVT_cor2 df ddf 0 c (proj1 Hc) Hdf0c) as [d [Hdfc Hd]].
  assert (H1 : f 1 - f 0 - df 0 = df c - df 0) by (unfold g, dg in Hgc; lra).
  assert (Heq : f 1 - f 0 - df 0 = ddf d * c) by (rewrite H1, Hdfc; ring).
  rewrite Heq, Rabs_mult, (Rabs_right c) by lra.
  apply Rle_trans with (M * c); [ apply Rmult_le_compat_r; [ lra | apply Hbd; lra ] | nra ].
Qed.

(* --- the two component functions and their derivatives --- *)

Section Remainder.
Variable w : C.
Let s := Re w.
Let r := Im w.
Let Rf := fun t => exp (t * s) * cos (t * r).
Let dRf := fun t => exp (t * s) * (s * cos (t * r) - r * sin (t * r)).
Let ddRf := fun t => exp (t * s) * ((s * s - r * r) * cos (t * r) - 2 * s * r * sin (t * r)).
Let If := fun t => exp (t * s) * sin (t * r).
Let dIf := fun t => exp (t * s) * (s * sin (t * r) + r * cos (t * r)).
Let ddIf := fun t => exp (t * s) * ((s * s - r * r) * sin (t * r) + 2 * s * r * cos (t * r)).

Lemma dRf_ok : forall t, derivable_pt_lim Rf t (dRf t).
Proof.
  intro t; unfold Rf, dRf.
  assert (H := derivable_pt_lim_mult _ _ _ _ _ (dexpts s t) (dcosts r t)).
  replace (exp (t * s) * (s * cos (t * r) - r * sin (t * r)))
    with (exp (t * s) * s * cos (t * r) + exp (t * s) * (- sin (t * r) * r)) by ring.
  exact H.
Qed.

Lemma ddRf_ok : forall t, derivable_pt_lim dRf t (ddRf t).
Proof.
  intro t; unfold dRf, ddRf.
  assert (Hin : derivable_pt_lim (fun x => s * cos (x * r) - r * sin (x * r)) t
                  (s * (- sin (t * r) * r) - r * (cos (t * r) * r))).
  { apply derivable_pt_lim_minus;
      [ apply (derivable_pt_lim_scal (fun x => cos (x * r)) s t); apply dcosts
      | apply (derivable_pt_lim_scal (fun x => sin (x * r)) r t); apply dsints ]. }
  assert (H := derivable_pt_lim_mult _ _ _ _ _ (dexpts s t) Hin).
  replace (exp (t * s) * ((s * s - r * r) * cos (t * r) - 2 * s * r * sin (t * r)))
    with (exp (t * s) * s * (s * cos (t * r) - r * sin (t * r))
          + exp (t * s) * (s * (- sin (t * r) * r) - r * (cos (t * r) * r))) by ring.
  exact H.
Qed.

Lemma dIf_ok : forall t, derivable_pt_lim If t (dIf t).
Proof.
  intro t; unfold If, dIf.
  assert (H := derivable_pt_lim_mult _ _ _ _ _ (dexpts s t) (dsints r t)).
  replace (exp (t * s) * (s * sin (t * r) + r * cos (t * r)))
    with (exp (t * s) * s * sin (t * r) + exp (t * s) * (cos (t * r) * r)) by ring.
  exact H.
Qed.

Lemma ddIf_ok : forall t, derivable_pt_lim dIf t (ddIf t).
Proof.
  intro t; unfold dIf, ddIf.
  assert (Hin : derivable_pt_lim (fun x => s * sin (x * r) + r * cos (x * r)) t
                  (s * (cos (t * r) * r) + r * (- sin (t * r) * r))).
  { apply derivable_pt_lim_plus;
      [ apply (derivable_pt_lim_scal (fun x => sin (x * r)) s t); apply dsints
      | apply (derivable_pt_lim_scal (fun x => cos (x * r)) r t); apply dcosts ]. }
  assert (H := derivable_pt_lim_mult _ _ _ _ _ (dexpts s t) Hin).
  replace (exp (t * s) * ((s * s - r * r) * sin (t * r) + 2 * s * r * cos (t * r)))
    with (exp (t * s) * s * (s * sin (t * r) + r * cos (t * r))
          + exp (t * s) * (s * (cos (t * r) * r) + r * (- sin (t * r) * r))) by ring.
  exact H.
Qed.

(* second-derivative bound M = 2 |w|^2 exp|w| *)
Let M := 2 * (Cmod w) ^ 2 * exp (Cmod w).

Lemma abs_s_le : Rabs s <= Cmod w.
Proof.
  unfold s. rewrite <- Cmod_RtoC. unfold Cmod, Cnorm2, RtoC; simpl.
  apply sqrt_le_1_alt. pose proof (Rle_0_sqr (Im w)); unfold Rsqr in *; nra.
Qed.

Lemma abs_r_le : Rabs r <= Cmod w.
Proof.
  unfold r. unfold Cmod, Cnorm2; simpl.
  rewrite <- (sqrt_Rsqr_abs (Im w)). apply sqrt_le_1_alt.
  pose proof (Rle_0_sqr (Re w)); unfold Rsqr in *; nra.
Qed.

Lemma trig_le1 : forall x, Rabs (cos x) <= 1 /\ Rabs (sin x) <= 1.
Proof.
  intro x; split;
    [ apply Rabs_le; destruct (COS_bound x); lra
    | apply Rabs_le; destruct (SIN_bound x); lra ].
Qed.

Lemma exp_ts_le : forall t, 0 <= t <= 1 -> exp (t * s) <= exp (Cmod w).
Proof.
  intros t Ht.
  assert (Hts : t * s <= Cmod w).
  { apply Rle_trans with (Rabs (t * s)); [ apply Rle_abs | ].
    rewrite Rabs_mult, (Rabs_right t) by lra.
    apply Rle_trans with (1 * Rabs s); [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | ].
    rewrite Rmult_1_l. apply abs_s_le. }
  destruct (Rle_lt_or_eq_dec _ _ Hts) as [Hlt | Heq];
    [ apply Rlt_le, exp_increasing; exact Hlt | rewrite Heq; right; reflexivity ].
Qed.

Lemma cmod_sq_sr : (Cmod w) ^ 2 = s * s + r * r.
Proof.
  assert (H : (Cmod w) ^ 2 = Rsqr (Cmod w)) by (unfold Rsqr; ring).
  rewrite H, Cmod_sqr. unfold Cnorm2, s, r; reflexivity.
Qed.

(* |(s^2-r^2) c - 2 s r d| <= 2|w|^2  and the sin-swapped version, for |c|,|d|<=1 *)
Lemma E_bound : forall c d, Rabs c <= 1 -> Rabs d <= 1 ->
  Rabs ((s * s - r * r) * c - 2 * s * r * d) <= 2 * (Cmod w) ^ 2.
Proof.
  intros c d Hc Hd. rewrite cmod_sq_sr.
  apply Rle_trans with (Rabs ((s * s - r * r) * c) + Rabs (2 * s * r * d)).
  { unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_Ropp. apply Rle_refl. }
  apply Rle_trans with ((s * s + r * r) + (s * s + r * r)); [ | lra ].
  apply Rplus_le_compat.
  - rewrite Rabs_mult. apply Rle_trans with (Rabs (s * s - r * r) * 1).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | assumption ].
    + rewrite Rmult_1_r. apply Rabs_le.
      pose proof (Rle_0_sqr s); pose proof (Rle_0_sqr r); unfold Rsqr in *; lra.
  - rewrite Rabs_mult. apply Rle_trans with (Rabs (2 * s * r) * 1).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | assumption ].
    + rewrite Rmult_1_r. apply Rabs_le.
      pose proof (Rle_0_sqr (s - r)); pose proof (Rle_0_sqr (s + r)); unfold Rsqr in *; split; nra.
Qed.

Lemma ddRf_bound : forall t, 0 <= t <= 1 -> Rabs (ddRf t) <= M.
Proof.
  intros t Ht; unfold ddRf, M.
  rewrite Rabs_mult, (Rabs_right (exp (t * s))) by (left; apply exp_pos).
  apply Rle_trans with (exp (Cmod w) * (2 * (Cmod w) ^ 2)).
  - apply Rmult_le_compat; try apply Rabs_pos; try (left; apply exp_pos).
    + apply exp_ts_le; exact Ht.
    + apply E_bound; [ apply (proj1 (trig_le1 (t * r))) | apply (proj2 (trig_le1 (t * r))) ].
  - apply Req_le; ring.
Qed.

Lemma ddIf_bound : forall t, 0 <= t <= 1 -> Rabs (ddIf t) <= M.
Proof.
  intros t Ht; unfold ddIf, M.
  rewrite Rabs_mult, (Rabs_right (exp (t * s))) by (left; apply exp_pos).
  apply Rle_trans with (exp (Cmod w) * (2 * (Cmod w) ^ 2)).
  - apply Rmult_le_compat; try apply Rabs_pos; try (left; apply exp_pos).
    + apply exp_ts_le; exact Ht.
    + replace ((s * s - r * r) * sin (t * r) + 2 * s * r * cos (t * r))
        with ((s * s - r * r) * sin (t * r) - 2 * s * r * (- cos (t * r))) by ring.
      apply E_bound; [ apply (proj2 (trig_le1 (t * r))) | rewrite Rabs_Ropp; apply (proj1 (trig_le1 (t * r))) ].
  - apply Req_le; ring.
Qed.

Lemma HM_nonneg : 0 <= M.
Proof.
  unfold M. apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | apply pow_le; apply Cmod_nonneg ] | left; apply exp_pos ].
Qed.

Lemma Re_diff_eq : Re (Cminus (Cminus (Cexpf w) C1) w) = Rf 1 - Rf 0 - dRf 0.
Proof.
  unfold Rf, dRf, Cexpf, Cexp, Cminus, Cmul, RtoC, C1; simpl.
  replace (1 * s) with s by ring; replace (1 * r) with r by ring;
    replace (0 * s) with 0 by ring; replace (0 * r) with 0 by ring.
  rewrite exp_0, cos_0, sin_0. unfold s, r; ring.
Qed.

Lemma Im_diff_eq : Im (Cminus (Cminus (Cexpf w) C1) w) = If 1 - If 0 - dIf 0.
Proof.
  unfold If, dIf, Cexpf, Cexp, Cminus, Cmul, RtoC, C1; simpl.
  replace (1 * s) with s by ring; replace (1 * r) with r by ring;
    replace (0 * s) with 0 by ring; replace (0 * r) with 0 by ring.
  rewrite exp_0, cos_0, sin_0. unfold s, r; ring.
Qed.

Theorem Cexpf_remainder_w : Cmod (Cminus (Cminus (Cexpf w) C1) w) <= 3 * (Cmod w) ^ 2 * exp (Cmod w).
Proof.
  assert (HR : Rabs (Rf 1 - Rf 0 - dRf 0) <= M)
    by (apply order2_bound with (ddf := ddRf);
        [ apply HM_nonneg | intros t _; apply dRf_ok | intros t _; apply ddRf_ok | apply ddRf_bound ]).
  assert (HI : Rabs (If 1 - If 0 - dIf 0) <= M)
    by (apply order2_bound with (ddf := ddIf);
        [ apply HM_nonneg | intros t _; apply dIf_ok | intros t _; apply ddIf_ok | apply ddIf_bound ]).
  rewrite <- Re_diff_eq in HR; rewrite <- Im_diff_eq in HI.
  unfold Cmod at 1.
  apply Rle_trans with (sqrt (2 * M ^ 2)).
  - apply sqrt_le_1_alt. unfold Cnorm2.
    pose proof (Rsqr_le_abs_1 (Re (Cminus (Cminus (Cexpf w) C1) w)) M) as HAR.
    pose proof (Rsqr_le_abs_1 (Im (Cminus (Cminus (Cexpf w) C1) w)) M) as HAI.
    pose proof HM_nonneg as HMn.
    rewrite (Rabs_right M) in HAR, HAI by lra.
    unfold Rsqr in HAR, HAI.
    apply Rle_trans with (M * M + M * M); [ | nra ].
    apply Rplus_le_compat; [ apply HAR; exact HR | apply HAI; exact HI ].
  - replace (2 * M ^ 2) with (2 * (M * M)) by ring.
    rewrite sqrt_mult_alt by lra.
    replace (M * M) with (Rsqr M) by (unfold Rsqr; ring).
    rewrite sqrt_Rsqr by apply HM_nonneg. unfold M.
    set (C := (Cmod w) ^ 2 * exp (Cmod w)).
    assert (HC : 0 <= C)
      by (unfold C; apply Rmult_le_pos; [ apply pow_le; apply Cmod_nonneg | left; apply exp_pos ]).
    replace (2 * (Cmod w) ^ 2 * exp (Cmod w)) with (2 * C) by (unfold C; ring).
    replace (3 * (Cmod w) ^ 2 * exp (Cmod w)) with (3 * C) by (unfold C; ring).
    clearbody C.
    assert (H23 : 2 * sqrt 2 <= 3).
    { apply Rsqr_incr_0_var; [ rewrite Rsqr_mult, Rsqr_sqrt by lra; unfold Rsqr; lra | lra ]. }
    replace (sqrt 2 * (2 * C)) with (2 * sqrt 2 * C) by ring.
    apply Rmult_le_compat_r; [ exact HC | exact H23 ].
Qed.

End Remainder.

Lemma Cexpf_remainder : forall w,
  Cmod (Cminus (Cminus (Cexpf w) C1) w) <= 3 * (Cmod w) ^ 2 * exp (Cmod w).
Proof. exact Cexpf_remainder_w. Qed.

Print Assumptions Cexpf_remainder.

(* ================================================================= *)
(*  END CexpRemainder.v.                                              *)
(* ================================================================= *)
