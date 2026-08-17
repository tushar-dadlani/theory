(* ================================================================= *)
(*  ThetaTailBounds.v  —  two-sided exponential enclosure of Psi.        *)
(*                                                                    *)
(*  Stage 1 of the verified-quadrature program to EXHIBIT the first     *)
(*  nontrivial zeta zero (discharge the sign-change hypothesis of       *)
(*  CritLineZeroCollapse.crit_sign_change_gives_zero_collapse).         *)
(*                                                                    *)
(*  Everything downstream -- the tail-truncation bound on               *)
(*  Re TC(1/2+it) = integral_1^inf Psi(x) x^{-3/4} cos((t/2) ln x) dx,  *)
(*  and the quadrature error control -- needs a tight rigorous          *)
(*  enclosure of the theta tail  Psi(x) = sum_{n>=1} e^{-pi n^2 x}.     *)
(*  We pin it between its first term and a geometric upper bound:       *)
(*                                                                    *)
(*    Psi_lower  :  e^{-pi t}              <= Psi t        (t > 0)      *)
(*    Psi_upper1 :  Psi t <= e^{-pi t} / (1 - e^{-pi})     (t >= 1)     *)
(*                                                                    *)
(*  So on x >= 1,  Psi(x) = e^{-pi x} . (1 + O(e^{-3 pi x})), enclosed  *)
(*  in [e^{-pi x}, 1.046 e^{-pi x}].  (Psi_upper, JacobiTheta, already  *)
(*  give the geometric bound e^{-pi t}/(1-e^{-pi t}); here we replace   *)
(*  the t-dependent denominator by the constant 1 - e^{-pi} valid for   *)
(*  t >= 1, and add the matching lower bound from the first term.)      *)
(*                                                                    *)
(*  HONEST STATUS.  This is a reusable numeric FOUNDATION, not the zero *)
(*  itself: it bounds the integrand of Re TC.  The verified quadrature  *)
(*  of that oscillatory integral (the piece that actually pins the sign *)
(*  of x_ir near t ~ 14.13) is the large remaining work.               *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import JacobiTheta RiemannPsi.
Open Scope R_scope.

(* monotonicity of exp in <= form (Stdlib exposes only the strict version) *)
Lemma exp_le_mono : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H. destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - right; rewrite Heq; reflexivity.
Qed.

(* lower bound: Psi t >= its first series term e^{-pi t} *)
Lemma Psi_lower : forall t (Ht : 0 < t), exp (- (PI * t)) <= Psi t.
Proof.
  intros t Ht. rewrite (Psi_val t Ht). unfold theta.
  destruct (theta_half_converges t Ht) as [L HL]; simpl.
  assert (Hle : theta_partial t 0 <= L)
    by (apply (growing_ineq (theta_partial t)); [ apply theta_partial_growing | exact HL ]).
  assert (Heq : theta_partial t 0 = exp (- (PI * t))).
  { unfold theta_partial, theta_term; cbn [sum_f_R0]; f_equal; simpl INR; ring. }
  lra.
Qed.

(* upper bound with a CONSTANT denominator, valid for t >= 1 *)
Lemma Psi_upper1 : forall t, 1 <= t -> Psi t <= exp (- (PI * t)) / (1 - exp (- PI)).
Proof.
  intros t Ht1. assert (Ht : 0 < t) by lra.
  eapply Rle_trans; [ apply (Psi_upper t Ht) | ].
  pose proof PI_RGT_0 as HPI.
  assert (Hq : exp (- (PI * t)) <= exp (- PI)) by (apply exp_le_mono; nra).
  assert (Hpi : exp (- PI) < 1)
    by (rewrite <- exp_0; apply exp_increasing; lra).
  assert (Hden : 0 < 1 - exp (- PI)) by lra.
  unfold Rdiv. apply Rmult_le_compat_l; [ apply Rlt_le, exp_pos | ].
  apply Rinv_le_contravar; [ exact Hden | lra ].
Qed.

(* the enclosure, packaged: on x >= 1, Psi x is trapped between e^{-pi x}
   and 1.046... e^{-pi x} (the constant is 1/(1 - e^{-pi})). *)
Theorem Psi_enclosure : forall t, 1 <= t ->
  exp (- (PI * t)) <= Psi t <= exp (- (PI * t)) / (1 - exp (- PI)).
Proof.
  intros t Ht1. split.
  - apply Psi_lower; lra.
  - apply Psi_upper1; exact Ht1.
Qed.

Print Assumptions Psi_lower.
Print Assumptions Psi_upper1.
Print Assumptions Psi_enclosure.
