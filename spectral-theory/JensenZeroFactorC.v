(* ================================================================= *)
(*  JensenZeroFactorC.v  —  Hadamard keystone, brick 4 (step 4c):       *)
(*  the Jensen zero factor for a COMPLEX zero.                          *)
(*                                                                    *)
(*    INT_0^{2PI} ln|Rr e^{it} - w| dt = 2 PI ln Rr   (|w| < Rr, w:C)   *)
(*                                                                    *)
(*  Generalizes JensenZeroFactor.jensen_zero_factor (real zero a) to a  *)
(*  complex zero w = |w| e^{i phi}, via the rotation-invariance of the  *)
(*  period integral (PeriodShift.int_period_shift):                     *)
(*    ln|Rr e^{it} - w| = zfk Rr |w| (t - phi),                        *)
(*  so the integral equals the real case at a = |w|.  Axiom-clean.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CSeries CPathIntegral CSegInt
        JensenZeroFactor ChebyshevPrime PeriodShift.
Open Scope R_scope.

(* every (p,q) is |.|.(cos phi, sin phi) for some angle phi *)
Lemma polar_exists : forall p q : R,
  exists phi, p = Cmod (mkC p q) * cos phi /\ q = Cmod (mkC p q) * sin phi.
Proof.
  intros p q. set (r := Cmod (mkC p q)).
  assert (Hr2 : r * r = p * p + q * q).
  { unfold r, Cmod, Cnorm2; simpl. rewrite sqrt_sqrt; [ ring | nra ]. }
  assert (Hr0 : 0 <= r) by (unfold r; apply Cmod_nonneg).
  destruct (Rle_lt_dec r 0) as [Hle | Hpos].
  - assert (Hr00 : r = 0) by lra.
    assert (Hpp : p * p = 0) by nra.
    assert (Hqq : q * q = 0) by nra.
    exists 0. rewrite Hr00. split; rewrite Rmult_0_l.
    + apply Rsqr_0_uniq; unfold Rsqr; exact Hpp.
    + apply Rsqr_0_uniq; unfold Rsqr; exact Hqq.
  - assert (Hple : Rabs p <= r)
      by (unfold r; pose proof (Cmod_Re_le (mkC p q)) as H; simpl in H; exact H).
    assert (Hpp : - r <= p <= r).
    { pose proof (Rle_abs p) as H1. pose proof (Rle_abs (- p)) as H2.
      rewrite Rabs_Ropp in H2. lra. }
    assert (Hrne : r <> 0) by lra.
    assert (Hpr : -1 <= p / r <= 1).
    { split; apply Rmult_le_reg_r with r; try exact Hpos;
        replace (p / r * r) with p by (field; lra); lra. }
    set (phi0 := acos (p / r)).
    assert (Hcos : cos phi0 = p / r) by (unfold phi0; apply cos_acos; exact Hpr).
    assert (Hsin : sin phi0 = sqrt (1 - (p / r)²)) by (unfold phi0; apply sin_acos; exact Hpr).
    assert (Hsq : 1 - (p / r)² = (q / r)²).
    { unfold Rsqr, Rdiv.
      replace (p * / r * (p * / r)) with (p * p * (/ r * / r)) by ring.
      replace (q * / r * (q * / r)) with (q * q * (/ r * / r)) by ring.
      rewrite <- Rinv_mult, Hr2. field. nra. }
    assert (Hsin2 : sin phi0 = Rabs (q / r)) by (rewrite Hsin, Hsq, sqrt_Rsqr_abs; reflexivity).
    destruct (Rle_lt_dec 0 q) as [Hq | Hq].
    + exists phi0. split.
      * rewrite Hcos; field; lra.
      * rewrite Hsin2, (Rabs_right (q / r)); [ field; lra | ].
        apply Rle_ge; unfold Rdiv; apply Rmult_le_pos;
          [ exact Hq | left; apply Rinv_0_lt_compat; exact Hpos ].
    + exists (- phi0). split.
      * rewrite cos_neg, Hcos; field; lra.
      * rewrite sin_neg, Hsin2, (Rabs_left (q / r)); [ field; lra | ].
        replace 0 with (0 * / r) by ring. unfold Rdiv.
        apply Rmult_lt_compat_r; [ apply Rinv_0_lt_compat; exact Hpos | exact Hq ].
Qed.

(* the Jensen contribution of a single COMPLEX zero w (|w| < Rr) *)
Theorem jensen_zero_factor_C : forall (Rr : R) (w : C),
  0 < Rr -> Cmod w < Rr ->
  forall (pr : Riemann_integrable (fun t => ln (Cmod (Cminus (arc Rr t) w))) 0 (2 * PI)),
  RiemannInt pr = 2 * PI * ln Rr.
Proof.
  intros Rr [p q] HR Hlt pr.
  set (a := Cmod (mkC p q)).
  assert (Ha : 0 <= a < Rr) by (unfold a; split; [ apply Cmod_nonneg | exact Hlt ]).
  destruct (polar_exists p q) as [phi [Hp Hq]].
  fold a in Hp, Hq.
  assert (Ha2 : a * a = p * p + q * q)
    by (unfold a, Cmod, Cnorm2; simpl; rewrite sqrt_sqrt; [ ring | nra ]).
  assert (Hzcont : forall x, continuity_pt (zfk Rr a) x)
    by (intro x; apply zfk_cont; [ exact HR | exact Ha ]).
  assert (Hzper : forall x, zfk Rr a (x + 2 * PI) = zfk Rr a x).
  { intro x. unfold zfk.
    replace (cos (x + 2 * PI)) with (cos x); [ reflexivity | ].
    replace (2 * PI) with (2 * INR 1 * PI) by (simpl; ring).
    symmetry; apply cos_period. }
  (* pointwise:  ln|Rr e^{it} - w| = zfk Rr a (t + (- phi)) *)
  assert (Hpt : forall t, ln (Cmod (Cminus (arc Rr t) (mkC p q))) = zfk Rr a (t + - phi)).
  { intro t.
    assert (Hnorm : Cnorm2 (Cminus (arc Rr t) (mkC p q))
                    = Rr ^ 2 - 2 * Rr * a * cos (t - phi) + a ^ 2).
    { unfold Cnorm2, Cminus, arc, Re, Im; simpl.
      rewrite cos_minus, Hp, Hq.
      pose proof (sin2_cos2 t) as HPt; unfold Rsqr in HPt.
      pose proof (sin2_cos2 phi) as HPp; unfold Rsqr in HPp.
      assert (Et : Rr * Rr * (cos t * cos t + sin t * sin t) = Rr * Rr)
        by (replace (cos t * cos t + sin t * sin t) with 1 by lra; ring).
      assert (Ep : a * a * (cos phi * cos phi + sin phi * sin phi) = a * a)
        by (replace (cos phi * cos phi + sin phi * sin phi) with 1 by lra; ring).
      transitivity (Rr * Rr * (cos t * cos t + sin t * sin t)
                    - 2 * Rr * a * (cos t * cos phi + sin t * sin phi)
                    + a * a * (cos phi * cos phi + sin phi * sin phi));
        [ ring | rewrite Et, Ep; ring ]. }
    assert (HnormPos : 0 < Cnorm2 (Cminus (arc Rr t) (mkC p q)))
      by (rewrite Hnorm; apply zfk_pos; [ exact HR | exact Ha ]).
    unfold Cmod. rewrite ln_sqrt_half by exact HnormPos.
    rewrite Hnorm. unfold zfk.
    replace (cos (t + - phi)) with (cos (t - phi)) by (f_equal; ring). reflexivity. }
  (* rotation-invariance assembly *)
  assert (Hab : (0:R) <= 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (prshift : Riemann_integrable (fun t => zfk Rr a (t + - phi)) 0 (2 * PI)).
  { apply continuity_implies_RiemannInt; [ exact Hab | ].
    intros t _. apply (continuity_pt_comp (fun s => s + - phi) (zfk Rr a));
      [ reg | apply Hzcont ]. }
  pose (przfk := zfk_int Rr a HR Ha).
  assert (Hext : forall x, 0 < x < 2 * PI ->
             ln (Cmod (Cminus (arc Rr x) (mkC p q))) = zfk Rr a (x + - phi))
    by (intros x _; apply Hpt).
  assert (Hsplit : RiemannInt pr = RiemannInt prshift)
    by (apply RiemannInt_P18; [ exact Hab | exact Hext ]).
  rewrite Hsplit, (int_period_shift (zfk Rr a) (- phi) Hzcont Hzper prshift przfk).
  exact (jensen_zero_factor Rr a HR Ha przfk).
Qed.

Print Assumptions jensen_zero_factor_C.
