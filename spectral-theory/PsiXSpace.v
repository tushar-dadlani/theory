(* ================================================================= *)
(*  PsiXSpace.v  --  Psi with a RATIONAL tail constant.                *)
(*                                                                    *)
(*    Psi_simple : 1 <= u ->                                          *)
(*      e^{-pi u} + e^{-4 pi u}                                        *)
(*        <= Psi u <=                                                  *)
(*      e^{-pi u} + e^{-4 pi u} + 2 e^{-9 pi u}                        *)
(*                                                                    *)
(*  Stage 4c groundwork.  ThetaTailSharp.Psi_sharp is sharp but its    *)
(*  upper bound carries the factor 1/(1 - e^{-pi u}), which an         *)
(*  interval evaluation cannot form: IntervalArith has +, -, * and     *)
(*  (through IntervalArithFun / IntervalCos / IntervalLn) exp, cos and *)
(*  ln, but NO reciprocal.  Rather than build Iinv for one use, the    *)
(*  factor is replaced by the constant 2.                              *)
(*                                                                    *)
(*  That costs nothing.  On u >= 1 the true factor is 1.0451, so the   *)
(*  bound loses a factor 2 on a term that is already e^{-9 pi u}       *)
(*  -- at u = 1 that term is 5e-13 against a value of 4e-2, so the     *)
(*  enclosure is still ~1e-11 relative, eight orders better than the   *)
(*  2e-3 the sign change needs.                                        *)
(*                                                                    *)
(*  The chain avoiding any decimal arithmetic on e: pi >= 3 from       *)
(*  CertifiedPi.PI_lower, so e^{-pi u} <= e^{-3}; and e >= 2 from      *)
(*  exp_ineq1_le, so e^{-3} <= 1/8 < 1/2, whence 1/(1-e^{-pi u}) <= 2. *)
(*  No numerical bound on e itself is needed anywhere.  Axiom-clean.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import JacobiTheta RiemannPsi ThetaTailBounds ThetaTailSharp CertifiedPi.
Open Scope R_scope.

Lemma exp_ge_2 : 2 <= exp 1.
Proof. pose proof (exp_ineq1_le 1); lra. Qed.

Lemma exp_3_ge_8 : 8 <= exp 3.
Proof.
  replace 3 with (1 + (1 + 1)) by ring.
  rewrite exp_plus, exp_plus.
  pose proof exp_ge_2 as H. pose proof (exp_pos 1).
  assert (H2 : 2 * 2 <= exp 1 * exp 1) by nra.
  nra.
Qed.

Lemma exp_neg_pi_small : forall u, 1 <= u -> exp (- (PI * u)) <= / 8.
Proof.
  intros u Hu.
  assert (HPI : 3 <= PI) by (pose proof PI_lower; lra).
  assert (Hle : - (PI * u) <= -3) by nra.
  eapply Rle_trans; [ apply exp_le_mono; exact Hle | ].
  assert (E : exp (-3) * exp 3 = 1)
    by (rewrite <- exp_plus; replace (-3 + 3) with 0 by ring; apply exp_0).
  pose proof exp_3_ge_8 as H8. pose proof (exp_pos (-3)) as Hn.
  nra.
Qed.

Corollary Psi_simple : forall u, 1 <= u ->
  exp (- (PI * u)) + exp (- (PI * 4 * u)) <= Psi u
  <= exp (- (PI * u)) + exp (- (PI * 4 * u)) + 2 * exp (- (9 * (PI * u))).
Proof.
  intros u Hu.
  assert (Hu0 : 0 < u) by lra.
  destruct (Psi_sharp u Hu0) as [Hlo Hhi].
  split; [ exact Hlo | ].
  eapply Rle_trans; [ exact Hhi | ].
  apply Rplus_le_compat_l.
  (* e^{-9 pi u}/(1 - e^{-pi u}) <= 2 e^{-9 pi u} *)
  assert (Hsm : exp (- (PI * u)) <= / 8) by (apply exp_neg_pi_small; exact Hu).
  assert (Hden : / 2 <= 1 - exp (- (PI * u))) by lra.
  assert (Hden0 : 0 < 1 - exp (- (PI * u))) by lra.
  assert (Hnum : 0 < exp (- (9 * (PI * u)))) by apply exp_pos.
  apply (Rmult_le_reg_r (1 - exp (- (PI * u)))); [ exact Hden0 | ].
  unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
  nra.
Qed.

(* the form stage 4c consumes, at u = e^x with x >= 0 *)
Corollary Psi_xspace : forall x, 0 <= x ->
  exp (- (PI * exp x)) + exp (- (PI * 4 * exp x)) <= Psi (exp x)
  <= exp (- (PI * exp x)) + exp (- (PI * 4 * exp x))
     + 2 * exp (- (9 * (PI * exp x))).
Proof.
  intros x Hx. apply Psi_simple.
  rewrite <- exp_0. apply exp_le_mono; exact Hx.
Qed.

Print Assumptions exp_neg_pi_small.
Print Assumptions Psi_simple.
Print Assumptions Psi_xspace.
