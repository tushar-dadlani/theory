(* ================================================================= *)
(*  JensenZeroFactor.v  —  Hadamard keystone, brick 3 (zeros-side):     *)
(*  the mean value of the log of a zero factor.                         *)
(*                                                                    *)
(*    int_0^{2pi} ln|Rr e^{i theta} - a| d theta = 2 pi ln Rr  (0<=a<Rr)*)
(*                                                                    *)
(*  This is the contribution of ONE zero  a  (|a|<Rr) to Jensen's       *)
(*  formula.  It follows from brick 2 (JensenIntegral.                  *)
(*  jensen_log_kernel_integral) by factoring out Rr^2:                  *)
(*    |Rr e^{i theta} - a|^2 = Rr^2 (1 - 2(a/Rr)cos + (a/Rr)^2),       *)
(*  so ln|Rr e^{i th} - a| = ln Rr + (1/2)ln(1 - 2(a/Rr)cos+(a/Rr)^2),  *)
(*  and the second term integrates to 0 (brick 2 at r = a/Rr < 1).     *)
(*                                                                    *)
(*  HONEST STATUS: this is the ZEROS-SIDE of Jensen's formula only.     *)
(*  The full formula also needs the ZERO-FREE mean value property       *)
(*    ln|F(0)| = (1/2pi) int_0^{2pi} ln|F(Rr e^{i theta})|             *)
(*  for a zero-free holomorphic F, which requires a HOLOMORPHIC COMPLEX *)
(*  LOGARITHM (Log F, so ln|F| = Re(Log F) is harmonic) -- absent in    *)
(*  the repo.  So brick 3 is NOT closed; this is its zeros-side.        *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import JensenIntegral.
Open Scope R_scope.

Definition zfk (Rr a θ : R) : R := (/ 2) * ln (Rr ^ 2 - 2 * Rr * a * cos θ + a ^ 2).

Lemma zfk_pos : forall Rr a θ, 0 < Rr -> 0 <= a < Rr ->
  0 < Rr ^ 2 - 2 * Rr * a * cos θ + a ^ 2.
Proof.
  intros Rr a θ HR Ha. assert (Hc : -1 <= cos θ <= 1) by apply COS_bound.
  replace (Rr ^ 2 - 2 * Rr * a * cos θ + a ^ 2)
     with ((Rr - a) * (Rr - a) + 2 * Rr * a * (1 - cos θ)) by ring.
  assert (H1 : 0 < (Rr - a) * (Rr - a)) by (apply Rmult_lt_0_compat; lra).
  assert (H2 : 0 <= 2 * Rr * a * (1 - cos θ)) by (repeat apply Rmult_le_pos; lra).
  lra.
Qed.

Lemma zfk_cont : forall Rr a θ, 0 < Rr -> 0 <= a < Rr -> continuity_pt (zfk Rr a) θ.
Proof.
  intros Rr a θ HR Ha. unfold zfk. apply continuity_pt_scal.
  apply (continuity_pt_comp (fun t => Rr ^ 2 - 2 * Rr * a * cos t + a ^ 2) ln).
  - reg.
  - apply derivable_continuous_pt.
    exists (/ (Rr ^ 2 - 2 * Rr * a * cos θ + a ^ 2)).
    apply derivable_pt_lim_ln. apply zfk_pos; assumption.
Qed.

Definition zfk_int (Rr a : R) (HR : 0 < Rr) (Ha : 0 <= a < Rr) :
  Riemann_integrable (zfk Rr a) 0 (2 * PI) :=
  continuity_implies_RiemannInt (Rlt_le _ _ (Rmult_lt_0_compat 2 PI Rlt_0_2 PI_RGT_0))
    (fun θ _ => zfk_cont Rr a θ HR Ha).

(* the Jensen contribution of a single zero a (|a| < Rr) *)
Theorem jensen_zero_factor : forall Rr a (HR : 0 < Rr) (Ha : 0 <= a < Rr)
    (pr : Riemann_integrable (zfk Rr a) 0 (2 * PI)),
  RiemannInt pr = 2 * PI * ln Rr.
Proof.
  intros Rr a HR Ha pr.
  assert (HarR : 0 <= a / Rr < 1).
  { split.
    - unfold Rdiv; apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
    - apply Rmult_lt_reg_r with Rr; [ lra | ].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra. lra. }
  pose (prc := RiemannInt_P14 0 (2 * PI) (ln Rr)).
  pose (prg := logker_int (a / Rr) HarR).
  pose (prcomb := RiemannInt_P10 (-1) prc prg).
  assert (Heq : RiemannInt pr = RiemannInt prcomb).
  { apply RiemannInt_P18; [ pose proof PI_RGT_0; lra | ].
    intros θ _. unfold zfk, prcomb, prg, prc, fct_cte. cbv beta.
    assert (HX : 0 < 1 - 2 * (a / Rr) * cos θ + (a / Rr) ^ 2) by (apply kernel_pos; exact HarR).
    assert (HR2 : 0 < Rr ^ 2) by nra.
    assert (HRsq : Rr ^ 2 - 2 * Rr * a * cos θ + a ^ 2
                   = Rr ^ 2 * (1 - 2 * (a / Rr) * cos θ + (a / Rr) ^ 2)) by (field; lra).
    rewrite HRsq, (ln_mult (Rr ^ 2) _ HR2 HX).
    replace (ln (Rr ^ 2)) with (2 * ln Rr).
    2:{ replace (Rr ^ 2) with (Rr * Rr) by ring. rewrite (ln_mult Rr Rr HR HR). ring. }
    lra. }
  rewrite Heq. unfold prcomb.
  rewrite (RiemannInt_P13 prc prg (RiemannInt_P10 (-1) prc prg)).
  rewrite (RiemannInt_P15 prc).
  replace (RiemannInt prg) with 0 by (unfold prg; symmetry; apply jensen_log_kernel_integral).
  ring.
Qed.

Print Assumptions jensen_zero_factor.
