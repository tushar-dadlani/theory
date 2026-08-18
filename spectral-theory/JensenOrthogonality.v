(* ================================================================= *)
(*  JensenOrthogonality.v  —  Hadamard Stage B, brick 1.                *)
(*                                                                    *)
(*  Toward Jensen's formula (zero-counting for the order-1 XiC), the     *)
(*  keystone integral  int_0^{2pi} ln|1 - w e^{i th}| d th = 0  (|w|<1)  *)
(*  is proved by the Fourier expansion of ln|1-w e^{i th}| whose modes   *)
(*  integrate to zero.  This brick supplies that orthogonality:          *)
(*                                                                    *)
(*    cos_int_2PI : int_0^{2pi} cos(n th) d th = 0   (n >= 1)           *)
(*    sin_int_2PI : int_0^{2pi} sin(n th) d th = 0   (n >= 1)           *)
(*                                                                    *)
(*  via FTC (antiderivatives sin(n th)/n, -cos(n th)/n) and the 2pi-     *)
(*  periodicity of sin/cos.  Axiom-clean.                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV.
Open Scope R_scope.

Lemma dsin_scaled : forall c x, derivable_pt_lim (fun t => sin (c * t)) x (c * cos (c * x)).
Proof.
  intros c x.
  pose proof (derivable_pt_lim_comp (fun t => c * t) sin x (c * 1) (cos (c * x))
    (derivable_pt_lim_scal (fun t => t) c x 1 (derivable_pt_lim_id x))
    (derivable_pt_lim_sin (c * x))) as H.
  replace (c * cos (c * x)) with (cos (c * x) * (c * 1)) by ring.
  exact H.
Qed.

Lemma dcos_scaled : forall c x, derivable_pt_lim (fun t => cos (c * t)) x (- (c * sin (c * x))).
Proof.
  intros c x.
  pose proof (derivable_pt_lim_comp (fun t => c * t) cos x (c * 1) (- sin (c * x))
    (derivable_pt_lim_scal (fun t => t) c x 1 (derivable_pt_lim_id x))
    (derivable_pt_lim_cos (c * x))) as H.
  replace (- (c * sin (c * x))) with (- sin (c * x) * (c * 1)) by ring.
  exact H.
Qed.

Lemma cont_cos_scaled : forall c, continuity (fun t => cos (c * t)).
Proof.
  intros c x. apply derivable_continuous_pt.
  exists (- (c * sin (c * x))). apply dcos_scaled.
Qed.

Lemma cont_sin_scaled : forall c, continuity (fun t => sin (c * t)).
Proof.
  intros c x. apply derivable_continuous_pt.
  exists (c * cos (c * x)). apply dsin_scaled.
Qed.

Lemma cos_scaled_int : forall c a b, Riemann_integrable (fun t => cos (c * t)) a b.
Proof.
  intros c a b. destruct (Rle_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_cos_scaled ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_cos_scaled ].
Qed.

Lemma sin_scaled_int : forall c a b, Riemann_integrable (fun t => sin (c * t)) a b.
Proof.
  intros c a b. destruct (Rle_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_sin_scaled ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_sin_scaled ].
Qed.

Lemma cos_int_2PI : forall n, (1 <= n)%nat ->
  RiemannInt (cos_scaled_int (INR n) 0 (2 * PI)) = 0.
Proof.
  intros n Hn. pose proof PI_RGT_0 as HPI.
  assert (Hn0 : INR n <> 0) by (apply not_0_INR; lia).
  assert (H2pi : 0 <= 2 * PI) by lra.
  set (G := fun t => / INR n * sin (INR n * t)).
  assert (Hanti : antiderivative (fun t => cos (INR n * t)) G 0 (2 * PI)).
  { split; [ | exact H2pi ]. intros x _.
    assert (HG : derivable_pt_lim G x (cos (INR n * x))).
    { unfold G. pose proof (dsin_scaled (INR n) x) as Hs.
      apply (derivable_pt_lim_scal (fun t => sin (INR n * t)) (/ INR n) x
               (INR n * cos (INR n * x))) in Hs.
      replace (cos (INR n * x)) with (/ INR n * (INR n * cos (INR n * x)))
        by (field; exact Hn0).
      exact Hs. }
    exists (exist (fun l => derivable_pt_lim G x l) (cos (INR n * x)) HG). reflexivity. }
  rewrite (FTC_antideriv (fun t => cos (INR n * t)) G 0 (2 * PI) H2pi
             (fun x _ => cont_cos_scaled (INR n) x) (cos_scaled_int (INR n) 0 (2 * PI)) Hanti).
  unfold G.
  replace (INR n * (2 * PI)) with (0 + 2 * INR n * PI) by ring.
  rewrite sin_period, sin_0.
  replace (INR n * 0) with 0 by ring. rewrite sin_0. field; exact Hn0.
Qed.

Lemma sin_int_2PI : forall n, (1 <= n)%nat ->
  RiemannInt (sin_scaled_int (INR n) 0 (2 * PI)) = 0.
Proof.
  intros n Hn. pose proof PI_RGT_0 as HPI.
  assert (Hn0 : INR n <> 0) by (apply not_0_INR; lia).
  assert (H2pi : 0 <= 2 * PI) by lra.
  set (G := fun t => - / INR n * cos (INR n * t)).
  assert (Hanti : antiderivative (fun t => sin (INR n * t)) G 0 (2 * PI)).
  { split; [ | exact H2pi ]. intros x _.
    assert (HG : derivable_pt_lim G x (sin (INR n * x))).
    { unfold G. pose proof (dcos_scaled (INR n) x) as Hs.
      apply (derivable_pt_lim_scal (fun t => cos (INR n * t)) (- / INR n) x
               (- (INR n * sin (INR n * x)))) in Hs.
      replace (sin (INR n * x)) with (- / INR n * - (INR n * sin (INR n * x)))
        by (field; exact Hn0).
      exact Hs. }
    exists (exist (fun l => derivable_pt_lim G x l) (sin (INR n * x)) HG). reflexivity. }
  rewrite (FTC_antideriv (fun t => sin (INR n * t)) G 0 (2 * PI) H2pi
             (fun x _ => cont_sin_scaled (INR n) x) (sin_scaled_int (INR n) 0 (2 * PI)) Hanti).
  unfold G.
  replace (INR n * (2 * PI)) with (0 + 2 * INR n * PI) by ring.
  rewrite cos_period, cos_0.
  replace (INR n * 0) with 0 by ring. rewrite cos_0. field; exact Hn0.
Qed.

Print Assumptions cos_int_2PI.
Print Assumptions sin_int_2PI.
