(* ================================================================= *)
(*  JensenOneZero.v  —  Hadamard keystone, brick 4 (first step):        *)
(*  Jensen's formula for an entire function with ONE (real) zero.       *)
(*                                                                    *)
(*  For F(z) = (z - a) . G(z) with G entire and zero-free, 0 < a < Rr:  *)
(*                                                                    *)
(*    (1/2PI) INT_0^{2PI} ln|F(Rr e^{it})| dt = ln|F(0)| + ln(Rr/a).    *)
(*                                                                    *)
(*  This COMBINES the two proved halves of Jensen's formula:           *)
(*   * JensenZeroFactor.jensen_zero_factor  (the zero factor (z-a):     *)
(*       INT ln|Rr e^{it} - a| dt = 2PI.ln Rr);                        *)
(*   * ZeroFreeMVP.zero_free_MVP  (the zero-free part G:                *)
(*       INT ln|G(Rr e^{it})| dt = 2PI.ln|G(0)|).                      *)
(*                                                                    *)
(*  ln|F| = ln|Rr e^{it}-a| + ln|G| pointwise (Cmod_mul + ln_mult),     *)
(*  and ln|Rr e^{it}-a| = (1/2)ln(Rr^2 - 2 Rr a cos t + a^2) = zfk       *)
(*  (Cmod = sqrt Cnorm2, ln_sqrt_half, sin2_cos2); RiemannInt split by   *)
(*  P10/P13/P18.  This is the n=1 case of Jensen -- the building block   *)
(*  of the zero-count n(r)=O(r) (each zero in |z|<r/2 contributes        *)
(*  >= ln 2 to the left side).  Axiom-clean.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral CSegInt
        JensenZeroFactor ZeroFreeMVP ChebyshevPrime.
Open Scope R_scope.

Theorem jensen_one_zero : forall (G Gp : C -> C) (a Rr : R),
  (forall z, is_Cderiv G z (Gp z)) ->
  (forall z, exists d, is_Cderiv Gp z d) ->
  (forall z, G z <> C0) ->
  CcontC (fun w => Cmul (Gp w) (Cinv (G w))) ->
  0 < a < Rr ->
  forall (prG : Riemann_integrable (fun t => ln (Cmod (G (arc Rr t)))) 0 (2 * PI))
         (prF : Riemann_integrable
                  (fun t => ln (Cmod (Cmul (Cminus (arc Rr t) (RtoC a)) (G (arc Rr t)))))
                  0 (2 * PI)),
  RiemannInt prF
  = 2 * PI * (ln (Cmod (Cmul (Cminus C0 (RtoC a)) (G C0))) + ln (Rr / a)).
Proof.
  intros G Gp a Rr HGhol HGphol HGne0 HcontG Ha0 prG prF.
  assert (HR : 0 < Rr) by lra.
  assert (Ha : 0 <= a < Rr) by lra.
  (* Cnorm2 of the zero factor at arc Rr t *)
  assert (Hnorm : forall t, Cnorm2 (Cminus (arc Rr t) (RtoC a))
                            = Rr ^ 2 - 2 * Rr * a * cos t + a ^ 2).
  { intro t. unfold Cnorm2, Cminus, arc, RtoC, Re, Im.
    pose proof (sin2_cos2 t) as HP; unfold Rsqr in HP.
    assert (HP2 : Rr * Rr * (sin t * sin t) + Rr * Rr * (cos t * cos t) = Rr * Rr).
    { replace (Rr * Rr * (sin t * sin t) + Rr * Rr * (cos t * cos t))
         with (Rr * Rr * (sin t * sin t + cos t * cos t)) by ring.
      rewrite HP. ring. }
    nra. }
  assert (HnormPos : forall t, 0 < Cnorm2 (Cminus (arc Rr t) (RtoC a))).
  { intro t. rewrite Hnorm. pose proof (COS_bound t) as HC.
    assert (Hprod : 0 <= Rr * a * (1 - cos t))
      by (apply Rmult_le_pos; [ apply Rmult_le_pos; lra | lra ]).
    assert (H1 : (Rr - a) ^ 2 <= Rr ^ 2 - 2 * Rr * a * cos t + a ^ 2) by nra.
    assert (H2 : 0 < (Rr - a) ^ 2) by nra. lra. }
  (* ln|Rr e^{it} - a| = zfk *)
  assert (HlnX : forall t, ln (Cmod (Cminus (arc Rr t) (RtoC a))) = zfk Rr a t).
  { intro t. unfold Cmod. rewrite ln_sqrt_half by apply HnormPos.
    rewrite Hnorm. unfold zfk. reflexivity. }
  (* Cmod positivity of the two factors *)
  assert (HcmXpos : forall t, 0 < Cmod (Cminus (arc Rr t) (RtoC a)))
    by (intro t; unfold Cmod; apply sqrt_lt_R0; apply HnormPos).
  assert (HcmGpos : forall z, 0 < Cmod (G z)).
  { intro z. destruct (Cmod_nonneg (G z)) as [Hlt | Heq]; [ exact Hlt | ].
    exfalso. apply (HGne0 z). apply (proj1 (Cmod0 (G z))). symmetry; exact Heq. }
  (* pointwise:  ln|F| = zfk + ln|G| *)
  assert (Hpt : forall t, ln (Cmod (Cmul (Cminus (arc Rr t) (RtoC a)) (G (arc Rr t))))
                          = zfk Rr a t + ln (Cmod (G (arc Rr t)))).
  { intro t. rewrite Cmod_mul, ln_mult by (try apply HcmXpos; apply HcmGpos).
    rewrite HlnX. reflexivity. }
  (* the two Jensen halves *)
  pose (prZ := zfk_int Rr a HR Ha).
  assert (HjZ : RiemannInt prZ = 2 * PI * ln Rr)
    by exact (jensen_zero_factor Rr a HR Ha prZ).
  assert (HjG : RiemannInt prG = 2 * PI * ln (Cmod (G C0)))
    by exact (zero_free_MVP G Gp Rr HGhol HGphol HGne0 HcontG HR prG).
  (* split the F-integral *)
  pose (prsum := RiemannInt_P10 1 prZ prG).
  assert (Hab : (0:R) <= 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hext : forall x, 0 < x < 2 * PI ->
             ln (Cmod (Cmul (Cminus (arc Rr x) (RtoC a)) (G (arc Rr x))))
             = zfk Rr a x + 1 * ln (Cmod (G (arc Rr x))))
    by (intros x _; rewrite Hpt; ring).
  assert (Hsplit : RiemannInt prF = RiemannInt prsum)
    by (apply RiemannInt_P18; [ exact Hab | exact Hext ]).
  assert (H13 : RiemannInt prsum = RiemannInt prZ + 1 * RiemannInt prG)
    by apply RiemannInt_P13.
  (* the F(0) side *)
  assert (HcmA : Cmod (Cminus C0 (RtoC a)) = a).
  { unfold Cmod, Cnorm2, Cminus, C0, RtoC, Re, Im.
    replace ((0 - a) * (0 - a) + (0 - 0) * (0 - 0)) with (a ^ 2) by ring.
    apply sqrt_pow2; lra. }
  assert (HRHS : ln (Cmod (Cmul (Cminus C0 (RtoC a)) (G C0))) = ln a + ln (Cmod (G C0))).
  { rewrite Cmod_mul, HcmA. rewrite ln_mult by (try lra; apply HcmGpos). reflexivity. }
  assert (Hlndiv : ln (Rr / a) = ln Rr - ln a).
  { unfold Rdiv. rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
    rewrite ln_Rinv by lra. ring. }
  rewrite Hsplit, H13, HjZ, HjG, HRHS, Hlndiv. ring.
Qed.

Print Assumptions jensen_one_zero.
