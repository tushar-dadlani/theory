(* ================================================================= *)
(*  LeibnizInterval.v  —  the shared bounded-interval parameter-       *)
(*  Leibniz rule (differentiation under a compact integral).          *)
(*                                                                    *)
(*  Generalising GaussLeibniz.leibniz_bounded (which baked in the      *)
(*  Gaussian cos-Taylor bound), this abstracts over the integrand      *)
(*  phi(v,·), its parameter-derivative dphi(w,·), and a supplied       *)
(*  SECOND-ORDER remainder bound                                       *)
(*     |phi(w+h,x) − phi(w,x) − h·dphi(w,x)| ≤ h²·B(x)   on [a,b].     *)
(*  Then                                                              *)
(*     d/dv (∫_a^b phi(v,x) dx)|_{v=w} = ∫_a^b dphi(w,x) dx.           *)
(*                                                                    *)
(*  Proof (identical spine to leibniz_bounded): the difference         *)
(*  quotient minus the target is (1/t)∫ dq with                        *)
(*  dq x = phi(w+t,x) − phi(w,x) − t·dphi(w,x); the remainder bound     *)
(*  gives |∫dq| ≤ t²·M, M = ∫B, so the error is ≤ M|t| → 0.  The       *)
(*  integral linearity is two RiemannInt_P13's.                       *)
(*                                                                    *)
(*  Reused by FourierSincC1 (sinc via ∫₀¹cos(ws)ds) and FourierHadamard *)
(*  (the smooth localiser factor).  No new axioms (classical Reals).   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussFull GaussPiValue.
Open Scope R_scope.

Theorem leibniz_interval :
  forall (phi dphi : R -> R -> R) (B : R -> R) (a b w : R),
  a <= b ->
  (forall v, continuity (phi v)) ->
  continuity (dphi w) ->
  continuity B ->
  (forall h x, a <= x <= b ->
     Rabs (phi (w + h) x - phi w x - h * dphi w x) <= h ^ 2 * B x) ->
  forall (prP : forall v, Riemann_integrable (phi v) a b)
         (prD : Riemann_integrable (dphi w) a b),
  derivable_pt_lim (fun v => RiemannInt (prP v)) w (RiemannInt prD).
Proof.
  intros phi dphi B a b w Hab Cphi Cdphi CB Hrem prP prD.
  set (l := RiemannInt prD).
  assert (prM : Riemann_integrable B a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply CB ]).
  set (M := RiemannInt prM).
  assert (HM0 : 0 <= M).
  { unfold M; apply (nonneg_int B a b prM); [ exact Hab | intros x Hx ].
    apply Rle_trans with (Rabs (phi (w + 1) x - phi w x - 1 * dphi w x)); [ apply Rabs_pos | ].
    replace (B x) with (1 ^ 2 * B x) by ring; apply Hrem; exact Hx. }
  intros eps He.
  assert (Hd0 : 0 < eps / (M + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (mkposreal (eps / (M + 1)) Hd0).
  intros t Ht0 Htd; simpl in Htd; cbv beta.
  set (Fp := RiemannInt (prP (w + t))).
  set (Fm := RiemannInt (prP w)).
  set (dq := fun x => phi (w + t) x - phi w x - t * dphi w x).
  assert (contdq : continuity dq).
  { intro x; unfold dq; apply continuity_pt_minus;
      [ apply continuity_pt_minus; [ apply Cphi | apply Cphi ] | ].
    apply (continuity_pt_scal (dphi w) t x); apply Cdphi. }
  assert (prdq : Riemann_integrable dq a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply contdq ]).
  assert (Hpt : forall x, a <= x <= b -> Rabs (dq x) <= t ^ 2 * B x)
    by (intros x Hx; unfold dq; apply Hrem; exact Hx).
  assert (prTM : Riemann_integrable (fun x => t ^ 2 * B x) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
        apply (continuity_pt_scal B (t ^ 2) x); apply CB ]).
  assert (Hdq_bound : Rabs (RiemannInt prdq) <= t ^ 2 * M).
  { apply Rle_trans with (RiemannInt (RiemannInt_P16 prdq)); [ apply RiemannInt_P17; exact Hab | ].
    apply Rle_trans with (RiemannInt prTM).
    - apply RiemannInt_P19; [ exact Hab | intros x Hx; apply Hpt; lra ].
    - rewrite (RInt_scal_cont B (t ^ 2) a b Hab CB prM prTM); apply Rle_refl. }
  assert (Hdq_val : RiemannInt prdq = Fp - Fm - t * l).
  { assert (prg1 : Riemann_integrable (fun x => phi (w + t) x + (-1) * phi w x) a b).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_plus;
        [ apply Cphi | apply (continuity_pt_scal (phi w) (-1) x); apply Cphi ] ]. }
    assert (prg2 : Riemann_integrable
                     (fun x => (fun y => phi (w + t) y + (-1) * phi w y) x + (- t) * dphi w x) a b).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_plus;
        [ apply continuity_pt_plus; [ apply Cphi | apply (continuity_pt_scal (phi w) (-1) x); apply Cphi ]
        | apply (continuity_pt_scal (dphi w) (- t) x); apply Cdphi ] ]. }
    pose proof (RiemannInt_P13 (prP (w + t)) (prP w) prg1) as HP1.
    pose proof (RiemannInt_P13 prg1 prD prg2) as HP2.
    assert (Hdg2 : RiemannInt prdq = RiemannInt prg2)
      by (apply RiemannInt_P18; [ exact Hab | intros x _; unfold dq; ring ]).
    unfold Fp, Fm, l; rewrite Hdg2, HP2, HP1; ring. }
  assert (Hq : (Fp - Fm) / t - l = RiemannInt prdq / t)
    by (rewrite Hdq_val; field; exact Ht0).
  rewrite Hq.
  apply Rle_lt_trans with (Rabs t * M).
  - apply Rmult_le_reg_r with (Rabs t); [ apply Rabs_pos_lt; exact Ht0 | ].
    rewrite <- Rabs_mult.
    replace (RiemannInt prdq / t * t) with (RiemannInt prdq) by (field; exact Ht0).
    apply Rle_trans with (t ^ 2 * M); [ exact Hdq_bound | ].
    apply Req_le; replace (t ^ 2) with (Rabs t * Rabs t)
      by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring); ring.
  - apply Rle_lt_trans with (Rabs t * (M + 1)).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | lra ].
    + pose proof (Rmult_lt_compat_r (M + 1) (Rabs t) (eps / (M + 1)) ltac:(lra) Htd) as Hmm.
      replace (eps / (M + 1) * (M + 1)) with eps in Hmm by (field; lra); exact Hmm.
Qed.

Print Assumptions leibniz_interval.

(* ----------------------------------------------------------------- *)
(*  Local variant: the remainder bound is needed only for |h| < r.   *)
(*  (derivable_pt_lim is local, so a bounded-h Taylor bound suffices —  *)
(*  the case where B comes from a Lipschitz f'' on a bounded range.)   *)
(* ----------------------------------------------------------------- *)

Theorem leibniz_interval_local :
  forall (phi dphi : R -> R -> R) (B : R -> R) (a b w : R) (r : posreal),
  a <= b ->
  (forall v, continuity (phi v)) ->
  continuity (dphi w) ->
  continuity B ->
  (forall x, a <= x <= b -> 0 <= B x) ->
  (forall h x, Rabs h < r -> a <= x <= b ->
     Rabs (phi (w + h) x - phi w x - h * dphi w x) <= h ^ 2 * B x) ->
  forall (prP : forall v, Riemann_integrable (phi v) a b)
         (prD : Riemann_integrable (dphi w) a b),
  derivable_pt_lim (fun v => RiemannInt (prP v)) w (RiemannInt prD).
Proof.
  intros phi dphi B a b w r Hab Cphi Cdphi CB HBnn Hrem prP prD.
  set (l := RiemannInt prD).
  assert (prM : Riemann_integrable B a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply CB ]).
  set (M := RiemannInt prM).
  assert (HM0 : 0 <= M)
    by (unfold M; apply (nonneg_int B a b prM); [ exact Hab | exact HBnn ]).
  intros eps He.
  assert (Hd0 : 0 < eps / (M + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (mkposreal (Rmin (eps / (M + 1)) (pos r)) (Rmin_pos _ _ Hd0 (cond_pos r))).
  intros t Ht0 Htd; simpl in Htd; cbv beta.
  assert (Htde : Rabs t < eps / (M + 1))
    by (eapply Rlt_le_trans; [ exact Htd | apply Rmin_l ]).
  assert (Htdr : Rabs t < r)
    by (eapply Rlt_le_trans; [ exact Htd | apply Rmin_r ]).
  set (Fp := RiemannInt (prP (w + t))).
  set (Fm := RiemannInt (prP w)).
  set (dq := fun x => phi (w + t) x - phi w x - t * dphi w x).
  assert (contdq : continuity dq).
  { intro x; unfold dq; apply continuity_pt_minus;
      [ apply continuity_pt_minus; [ apply Cphi | apply Cphi ] | ].
    apply (continuity_pt_scal (dphi w) t x); apply Cdphi. }
  assert (prdq : Riemann_integrable dq a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply contdq ]).
  assert (Hpt : forall x, a <= x <= b -> Rabs (dq x) <= t ^ 2 * B x)
    by (intros x Hx; unfold dq; apply Hrem; [ exact Htdr | exact Hx ]).
  assert (prTM : Riemann_integrable (fun x => t ^ 2 * B x) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
        apply (continuity_pt_scal B (t ^ 2) x); apply CB ]).
  assert (Hdq_bound : Rabs (RiemannInt prdq) <= t ^ 2 * M).
  { apply Rle_trans with (RiemannInt (RiemannInt_P16 prdq)); [ apply RiemannInt_P17; exact Hab | ].
    apply Rle_trans with (RiemannInt prTM).
    - apply RiemannInt_P19; [ exact Hab | intros x Hx; apply Hpt; lra ].
    - rewrite (RInt_scal_cont B (t ^ 2) a b Hab CB prM prTM); apply Rle_refl. }
  assert (Hdq_val : RiemannInt prdq = Fp - Fm - t * l).
  { assert (prg1 : Riemann_integrable (fun x => phi (w + t) x + (-1) * phi w x) a b).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_plus;
        [ apply Cphi | apply (continuity_pt_scal (phi w) (-1) x); apply Cphi ] ]. }
    assert (prg2 : Riemann_integrable
                     (fun x => (fun y => phi (w + t) y + (-1) * phi w y) x + (- t) * dphi w x) a b).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_plus;
        [ apply continuity_pt_plus; [ apply Cphi | apply (continuity_pt_scal (phi w) (-1) x); apply Cphi ]
        | apply (continuity_pt_scal (dphi w) (- t) x); apply Cdphi ] ]. }
    pose proof (RiemannInt_P13 (prP (w + t)) (prP w) prg1) as HP1.
    pose proof (RiemannInt_P13 prg1 prD prg2) as HP2.
    assert (Hdg2 : RiemannInt prdq = RiemannInt prg2)
      by (apply RiemannInt_P18; [ exact Hab | intros x _; unfold dq; ring ]).
    unfold Fp, Fm, l; rewrite Hdg2, HP2, HP1; ring. }
  assert (Hq : (Fp - Fm) / t - l = RiemannInt prdq / t)
    by (rewrite Hdq_val; field; exact Ht0).
  rewrite Hq.
  apply Rle_lt_trans with (Rabs t * M).
  - apply Rmult_le_reg_r with (Rabs t); [ apply Rabs_pos_lt; exact Ht0 | ].
    rewrite <- Rabs_mult.
    replace (RiemannInt prdq / t * t) with (RiemannInt prdq) by (field; exact Ht0).
    apply Rle_trans with (t ^ 2 * M); [ exact Hdq_bound | ].
    apply Req_le; replace (t ^ 2) with (Rabs t * Rabs t)
      by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring); ring.
  - apply Rle_lt_trans with (Rabs t * (M + 1)).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | lra ].
    + pose proof (Rmult_lt_compat_r (M + 1) (Rabs t) (eps / (M + 1)) ltac:(lra) Htde) as Hmm.
      replace (eps / (M + 1) * (M + 1)) with eps in Hmm by (field; lra); exact Hmm.
Qed.

Print Assumptions leibniz_interval_local.

(* ================================================================= *)
(*  END LeibnizInterval.v                                            *)
(*  d/dv ∫_a^b phi(v,x) dx = ∫_a^b dphi(w,x) dx at v=w, given a         *)
(*  second-order remainder bound |Δ²phi| ≤ h²·B.  The reusable engine  *)
(*  for the removable-singularity localiser (sinc and Hadamard factor).*)
(* ================================================================= *)
