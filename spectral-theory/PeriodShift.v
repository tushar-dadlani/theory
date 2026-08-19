(* ================================================================= *)
(*  PeriodShift.v  —  Hadamard keystone, brick 4 enabler (rotation):    *)
(*  the integral of a 2PI-periodic function over one period is          *)
(*  invariant under a shift of the variable.                            *)
(*                                                                    *)
(*    int_period_shift : f continuous, f(x+2PI)=f(x) ==>               *)
(*      INT_0^{2PI} f(t + c) dt = INT_0^{2PI} f(t) dt.                  *)
(*                                                                    *)
(*  This is the rotation-invariance that lets the single-zero Jensen    *)
(*  factor (JensenZeroFactor.jensen_zero_factor, proved for a REAL      *)
(*  zero a) extend to a COMPLEX zero w: writing w = |w| e^{i phi},      *)
(*    ln|Rr e^{it} - w| = ln|Rr e^{i(t-phi)} - |w||,                    *)
(*  so the integral over a full period equals the real case (a=|w|).    *)
(*  Needed for the zero-count n(r)=O(r), whose zeros (of xi) are        *)
(*  complex.                                                           *)
(*                                                                    *)
(*  Proof: with P the primitive of f on a large interval [A,B]          *)
(*  (RiemannInt_P28), both integrals are P-differences (FTC_antideriv); *)
(*  Q(x) = P(x+2PI) - P(x) has derivative f(x+2PI)-f(x) = 0, hence is    *)
(*  constant (null_derivative_loc), giving the two differences equal.   *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ContinuousCoV.
Open Scope R_scope.

Lemma int_period_shift : forall (f : R -> R) (c : R),
  (forall x, continuity_pt f x) ->
  (forall x, f (x + 2 * PI) = f x) ->
  forall (pr1 : Riemann_integrable (fun t => f (t + c)) 0 (2 * PI))
         (pr2 : Riemann_integrable f 0 (2 * PI)),
  RiemannInt pr1 = RiemannInt pr2.
Proof.
  intros f c Hcont Hper pr1 pr2.
  pose proof PI_RGT_0 as Hpi. pose proof (Rabs_pos c) as Hac. pose proof (Rle_abs c) as Hca.
  assert (Hca2 : - Rabs c <= c) by (pose proof (Rabs_Ropp c); pose proof (Rle_abs (- c)); lra).
  set (A := - Rabs c - 1). set (B := 2 * PI + Rabs c + 1).
  assert (HAB : A <= B) by (unfold A, B; lra).
  assert (C0 : forall x, A <= x <= B -> continuity_pt f x) by (intros; apply Hcont).
  set (P := primitive HAB (FTC_P1 HAB C0)).
  assert (HP' : forall x, A <= x <= B -> derivable_pt_lim P x (f x))
    by (intros x Hx; exact (RiemannInt_P28 HAB C0 Hx)).
  assert (H0le : (0:R) <= 2 * PI) by lra.
  (* derivative of a shifted P:  d/dx P(x + s) = f(x + s) *)
  assert (Hshift : forall s x, A <= x + s <= B ->
                   derivable_pt_lim (fun u => P (u + s)) x (f (x + s))).
  { intros s x Hx. replace (f (x + s)) with (f (x + s) * 1) by ring.
    apply (derivable_pt_lim_comp (fun u => u + s) P x 1 (f (x + s))).
    - replace 1 with (1 + 0) by ring.
      apply derivable_pt_lim_plus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
    - apply HP'; exact Hx. }
  (* INT_0^{2PI} f = P(2PI) - P(0) *)
  assert (Cc2 : forall x, 0 <= x <= 2 * PI -> continuity_pt f x) by (intros; apply Hcont).
  assert (Hanti2 : antiderivative f P 0 (2 * PI)).
  { split; [ intros x Hx | lra ].
    assert (Hxab : A <= x <= B) by (unfold A, B; lra).
    exists (exist _ (f x) (HP' x Hxab)). reflexivity. }
  assert (H2 : RiemannInt pr2 = P (2 * PI) - P 0)
    by exact (FTC_antideriv f P 0 (2 * PI) H0le Cc2 pr2 Hanti2).
  (* INT_0^{2PI} f(t+c) = P(2PI+c) - P(c) *)
  assert (Cc1 : forall x, 0 <= x <= 2 * PI -> continuity_pt (fun t => f (t + c)) x).
  { intros x _. apply (continuity_pt_comp (fun t => t + c) f); [ reg | apply Hcont ]. }
  assert (Hanti1 : antiderivative (fun t => f (t + c)) (fun t => P (t + c)) 0 (2 * PI)).
  { split; [ intros x Hx | lra ].
    assert (Hxab : A <= x + c <= B) by (unfold A, B; lra).
    exists (exist _ (f (x + c)) (Hshift c x Hxab)). reflexivity. }
  assert (H1 : RiemannInt pr1 = P (2 * PI + c) - P (0 + c))
    by exact (FTC_antideriv (fun t => f (t + c)) (fun t => P (t + c)) 0 (2 * PI)
                H0le Cc1 pr1 Hanti1).
  (* Q(x) = P(x+2PI) - P(x) is constant on [A, B-2PI] *)
  set (Q := fun x => P (x + 2 * PI) - P x).
  assert (HAB' : A <= B - 2 * PI) by (unfold A, B; lra).
  assert (HQlim : forall x, A <= x <= B - 2 * PI -> derivable_pt_lim Q x 0).
  { intros x Hx.
    assert (Hx2 : A <= x + 2 * PI <= B) by (unfold A, B in *; lra).
    assert (HxB : A <= x <= B) by (unfold A, B in *; lra).
    replace 0 with (f (x + 2 * PI) - f x) by (rewrite Hper; ring).
    apply derivable_pt_lim_minus; [ apply (Hshift (2 * PI) x Hx2) | apply HP'; exact HxB ]. }
  assert (HQcont : forall x, A <= x <= B - 2 * PI -> continuity_pt Q x)
    by (intros x Hx; apply derivable_continuous_pt; exists 0; apply HQlim; exact Hx).
  assert (HQder : forall x, A < x < B - 2 * PI -> derivable_pt Q x)
    by (intros x Hx; exists 0; apply HQlim; lra).
  assert (HQd0 : forall x (Px : A < x < B - 2 * PI), derive_pt Q x (HQder x Px) = 0)
    by (intros x Px; apply derive_pt_eq_0; apply HQlim; lra).
  pose proof (null_derivative_loc Q A (B - 2 * PI) HQder HQcont HQd0) as Hconst.
  unfold constant_D_eq in Hconst.
  assert (HQ0 : Q 0 = Q A) by (apply Hconst; unfold A, B; lra).
  assert (HQc : Q c = Q A) by (apply Hconst; unfold A, B; lra).
  assert (HQ0c : Q 0 = Q c) by (rewrite HQ0, HQc; reflexivity).
  unfold Q in HQ0c.
  replace (P (0 + 2 * PI)) with (P (2 * PI)) in HQ0c by (f_equal; ring).
  rewrite H1, H2.
  replace (2 * PI + c) with (c + 2 * PI) by ring.
  replace (0 + c) with c by ring.
  symmetry; exact HQ0c.
Qed.

Print Assumptions int_period_shift.
