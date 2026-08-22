(* ================================================================= *)
(*  ThetaDerivMajorant.v  --  the Weierstrass majorant for Psi'.       *)
(*                                                                    *)
(*    dtheta_term_bound : 1/2 <= u ->                                 *)
(*      pi (n+1)^2 e^{-pi (n+1)^2 u}  <=  4 (e^{-pi/4})^n              *)
(*                                                                    *)
(*  Stage 4c.  midpoint_single needs the integrand's derivative, and   *)
(*  the integrand contains Psi(e^x) = sum_{n>=1} e^{-pi n^2 e^x}.      *)
(*  Differentiating that termwise is not free: Psi is an infinite sum, *)
(*  so it needs derivable_pt_lim_CVU (Ranalysis5), whose load-bearing  *)
(*  hypothesis is UNIFORM convergence of the differentiated partials.  *)
(*  This file supplies the majorant that gives it, by the M-test.      *)
(*                                                                    *)
(*  The bound is not the naive one.  The n-th derivative term carries  *)
(*  a factor pi (n+1)^2 that GROWS, so it cannot simply be dominated   *)
(*  by the corresponding term of Psi (as JacobiTheta.theta_term_le     *)
(*  does for Psi itself).  The factor is absorbed by splitting the     *)
(*  exponential in half and spending one half on it:                   *)
(*                                                                    *)
(*    a e^{-a u} = (a u/2 . e^{-a u/2}) . (2/u) . e^{-a u/2}           *)
(*               <= 1 . 4 . e^{-a u/2}     (u >= 1/2)                  *)
(*                                                                    *)
(*  using v e^{-v} <= 1, which is exp_ineq1_le again -- the same trick *)
(*  that gave ln u <= u^d/(d e) in RPowerLogTail.  What remains,       *)
(*  e^{-pi (n+1)^2 u/2}, is then geometric in n because (n+1)^2 >= n+1. *)
(*                                                                    *)
(*  The ratio is e^{-pi/4} = 0.456, so the majorant series converges   *)
(*  fast and the M-test applies on any half-line u >= 1/2 -- which     *)
(*  covers u = e^x for x >= 0 with room.  Axiom-clean.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ExpEnclosure ThetaTailBounds.
Open Scope R_scope.

(* v e^{-v} <= 1 : exp_ineq1_le, one more time *)
Lemma v_exp_neg_v : forall v, 0 <= v -> v * exp (- v) <= 1.
Proof.
  intros v Hv.
  assert (Hle : 1 + v <= exp v) by apply exp_ineq1_le.
  assert (Hpos : 0 < exp v) by apply exp_pos.
  assert (Hinv : exp (- v) * exp v = 1)
    by (rewrite <- exp_plus; replace (- v + v) with 0 by ring; apply exp_0).
  assert (Hv2 : v <= exp v) by lra.
  apply (Rmult_le_reg_r (exp v)); [ exact Hpos | ].
  rewrite Rmult_assoc, Hinv, Rmult_1_r. lra.
Qed.

(* the derivative term, dominated by a geometric series *)
Theorem dtheta_term_bound : forall u n, / 2 <= u ->
  PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2 * u))
  <= 4 * exp (- (PI / 4)) ^ n.
Proof.
  intros u n Hu.
  pose proof PI_RGT_0 as HPI.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 0 < a) by (unfold a; nra).
  (* absorb the growing factor into half the exponential *)
  assert (Hv : (a * u / 2) * exp (- (a * u / 2)) <= 1)
    by (apply v_exp_neg_v; nra).
  assert (Hsplit : exp (- (a * u)) = exp (- (a * u / 2)) * exp (- (a * u / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hstep : a * exp (- (a * u)) <= 4 * exp (- (a * u / 2))).
  { rewrite Hsplit.
    assert (He : 0 < exp (- (a * u / 2))) by apply exp_pos.
    assert (E1 : a * exp (- (a * u / 2))
               = (2 / u) * (a * u / 2 * exp (- (a * u / 2)))) by (field; lra).
    assert (H2u : 0 < 2 / u) by (apply Rdiv_lt_0_compat; lra).
    assert (Hkey : a * exp (- (a * u / 2)) <= 2 / u)
      by (rewrite E1; nra).
    assert (Hu2 : 2 / u <= 4).
    { apply (Rmult_le_reg_r u); [ lra | ].
      assert (E2 : 2 / u * u = 2) by (field; lra).
      rewrite E2. lra. }
    nra. }
  (* and the remaining half is geometric, since (n+1)^2 >= n+1 *)
  assert (Hgeo : exp (- (a * u / 2)) <= exp (- (PI / 4)) ^ n).
  { assert (Hsq : k <= k ^ 2) by nra.
    assert (Hchain : - (a * u / 2) <= - (PI * k * u / 2)).
    { unfold a.
      assert (Hd : PI * k ^ 2 * u / 2 - PI * k * u / 2
                 = (PI * u / 2) * (k ^ 2 - k)) by field.
      assert (Hpu : 0 < PI * u / 2) by (apply Rdiv_lt_0_compat; nra).
      assert (Hprod : 0 <= (PI * u / 2) * (k ^ 2 - k))
        by (apply Rmult_le_pos; lra).
      lra. }
    eapply Rle_trans; [ apply exp_le_mono; exact Hchain | ].
    assert (Hkn : INR n + 1 = k) by (unfold k; rewrite S_INR; ring).
    assert (E : - (PI * k * u / 2) = INR n * (- (PI * u / 2)) + (- (PI * u / 2)))
      by (rewrite <- Hkn; field).
    rewrite E, exp_plus, <- exp_INR_pow, <- exp_plus.
    apply exp_le_mono.
    assert (Hn : 0 <= INR n) by apply pos_INR.
    assert (Hp1 : 0 <= INR n * (u / 2 - / 4)) by (apply Rmult_le_pos; lra).
    assert (Hp2 : 0 <= PI * (INR n * (u / 2 - / 4) + u / 2))
      by (apply Rmult_le_pos; lra).
    assert (Hexp : PI * (INR n * (u / 2 - / 4) + u / 2)
                 = INR n * - (PI / 4)
                   - (INR n * - (PI * u / 2) + - (PI * u / 2))) by field.
    lra. }
  lra.
Qed.

(* the ratio is genuinely below 1, so the majorant series converges *)
Corollary dtheta_ratio_lt1 : exp (- (PI / 4)) < 1.
Proof.
  rewrite <- exp_0. apply exp_increasing. pose proof PI_RGT_0. lra.
Qed.

Print Assumptions v_exp_neg_v.
Print Assumptions dtheta_term_bound.
