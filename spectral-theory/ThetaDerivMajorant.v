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
Require Import ExpEnclosure ThetaTailBounds CertifiedPi.
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

(* ----------------------------------------------------------------- *)
(*  The geometric half, isolated for reuse: what survives after the    *)
(*  growing factor has been absorbed.  Used at both orders.            *)
(* ----------------------------------------------------------------- *)
Lemma exp_half_geo : forall u n, / 2 <= u ->
  exp (- (PI * INR (S n) ^ 2 * u / 2)) <= exp (- (PI / 4)) ^ n.
Proof.
  intros u n Hu. pose proof PI_RGT_0 as HPI.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : k <= k ^ 2) by nra.
  assert (Hchain : - (PI * k ^ 2 * u / 2) <= - (PI * k * u / 2)).
  { assert (Hd : PI * k ^ 2 * u / 2 - PI * k * u / 2
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
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Second order.  midpoint_single wants a LIPSCHITZ bound on Psi',    *)
(*  i.e. a bound on the twice-differentiated series, whose terms       *)
(*  carry pi^2 n^4.  Same absorption, one notch harder: the split is   *)
(*  into QUARTERS and v e^{-v} <= 1 is applied and then SQUARED.       *)
(* ----------------------------------------------------------------- *)
Theorem dtheta2_term_bound : forall u n, / 2 <= u ->
  PI ^ 2 * INR (S n) ^ 4 * exp (- (PI * INR (S n) ^ 2 * u))
  <= 64 * exp (- (PI / 4)) ^ n.
Proof.
  intros u n Hu. pose proof PI_RGT_0 as HPI.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 0 < a) by (unfold a; nra).
  assert (Hsq4 : PI ^ 2 * k ^ 4 = a ^ 2) by (unfold a; ring).
  assert (Hv : (a * u / 4) * exp (- (a * u / 4)) <= 1)
    by (apply v_exp_neg_v; nra).
  assert (Hpos1 : 0 <= a * u / 4) by nra.
  assert (Hpos2 : 0 < exp (- (a * u / 4))) by apply exp_pos.
  assert (Hsq : (a * u / 4) ^ 2 * exp (- (a * u / 2)) <= 1).
  { assert (E : exp (- (a * u / 2)) = exp (- (a * u / 4)) * exp (- (a * u / 4)))
      by (rewrite <- exp_plus; f_equal; lra).
    rewrite E.
    assert (Hxy : 0 <= a * u / 4 * exp (- (a * u / 4)))
      by (apply Rmult_le_pos; lra).
    assert (Hsq2 : (a * u / 4 * exp (- (a * u / 4))) ^ 2 <= 1) by nra.
    assert (Eexp : (a * u / 4 * exp (- (a * u / 4))) ^ 2
                 = (a * u / 4) ^ 2 * (exp (- (a * u / 4)) * exp (- (a * u / 4))))
      by ring.
    lra. }
  assert (Hu2 : a ^ 2 * exp (- (a * u / 2)) <= 64).
  { assert (E : (a * u / 4) ^ 2 * exp (- (a * u / 2))
              = u ^ 2 / 16 * (a ^ 2 * exp (- (a * u / 2)))) by field.
    rewrite E in Hsq.
    assert (Hu16 : / 64 <= u ^ 2 / 16) by nra.
    assert (Hnn : 0 <= a ^ 2 * exp (- (a * u / 2)))
      by (apply Rmult_le_pos; [ nra | left; apply exp_pos ]).
    nra. }
  assert (Hsplit : exp (- (a * u)) = exp (- (a * u / 2)) * exp (- (a * u / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hgeo : exp (- (a * u / 2)) <= exp (- (PI / 4)) ^ n)
    by (unfold a; apply exp_half_geo; exact Hu).
  assert (He : 0 < exp (- (a * u / 2))) by apply exp_pos.
  rewrite Hsq4, Hsplit. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  X-SPACE.  The quadrature runs in x with u = e^x, so what the       *)
(*  error term actually needs is a bound on the x-derivatives of       *)
(*  Psi(e^x), i.e. on  u Psi'(u)  and  u^2 Psi''(u) - u Psi'(u).       *)
(*                                                                    *)
(*  Bounding those by combining the u-space bounds with u <= e^L is    *)
(*  catastrophically lossy: it multiplies the worst case of Psi'' (at  *)
(*  u = 1/2) by e^{2L} = 25 (at u = 5), where Psi'' is ~10^{-6}.  For  *)
(*  the sign change at t = 16 that route costs a factor 2200 in the    *)
(*  quadrature constant -- 44000 nodes instead of 940.                 *)
(*                                                                    *)
(*  Bounding a u . e^{-a u} directly costs nothing extra: the same     *)
(*  half-split applies, and u simply rides along inside v = a u.       *)
(* ----------------------------------------------------------------- *)
Theorem xterm_bound : forall u n, 1 <= u ->
  PI * INR (S n) ^ 2 * u * exp (- (PI * INR (S n) ^ 2 * u))
  <= 2 * exp (- (PI / 4)) ^ n.
Proof.
  intros u n Hu. pose proof PI_RGT_0 as HPI.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 0 < a) by (unfold a; nra).
  assert (Hv : a * u / 2 * exp (- (a * u / 2)) <= 1)
    by (apply v_exp_neg_v; nra).
  assert (He : 0 < exp (- (a * u / 2))) by apply exp_pos.
  assert (Hone : a * u * exp (- (a * u / 2)) <= 2) by lra.
  assert (Hsplit : exp (- (a * u)) = exp (- (a * u / 2)) * exp (- (a * u / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hgeo : exp (- (a * u / 2)) <= exp (- (PI / 4)) ^ n)
    by (unfold a; apply exp_half_geo; lra).
  rewrite Hsplit. nra.
Qed.

Theorem xterm2_bound : forall u n, 1 <= u ->
  ((PI * INR (S n) ^ 2 * u) ^ 2 + PI * INR (S n) ^ 2 * u)
    * exp (- (PI * INR (S n) ^ 2 * u))
  <= 18 * exp (- (PI / 4)) ^ n.
Proof.
  intros u n Hu. pose proof PI_RGT_0 as HPI.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 0 < a) by (unfold a; nra).
  assert (He : 0 < exp (- (a * u / 2))) by apply exp_pos.
  (* linear part, via the half split *)
  assert (Hv2 : a * u / 2 * exp (- (a * u / 2)) <= 1)
    by (apply v_exp_neg_v; nra).
  assert (Hlin : a * u * exp (- (a * u / 2)) <= 2) by lra.
  (* quadratic part, via the quarter split squared *)
  assert (Hv4 : a * u / 4 * exp (- (a * u / 4)) <= 1)
    by (apply v_exp_neg_v; nra).
  assert (Hp1 : 0 <= a * u / 4) by nra.
  assert (Hp2 : 0 < exp (- (a * u / 4))) by apply exp_pos.
  assert (Hquad : (a * u) ^ 2 * exp (- (a * u / 2)) <= 16).
  { assert (E4 : exp (- (a * u / 2)) = exp (- (a * u / 4)) * exp (- (a * u / 4)))
      by (rewrite <- exp_plus; f_equal; lra).
    assert (Hxy : 0 <= a * u / 4 * exp (- (a * u / 4)))
      by (apply Rmult_le_pos; lra).
    assert (Hsq2 : (a * u / 4 * exp (- (a * u / 4))) ^ 2 <= 1) by nra.
    assert (Eexp : (a * u / 4 * exp (- (a * u / 4))) ^ 2
                 = (a * u) ^ 2 / 16
                   * (exp (- (a * u / 4)) * exp (- (a * u / 4)))) by field.
    rewrite E4. lra. }
  assert (Hsplit : exp (- (a * u)) = exp (- (a * u / 2)) * exp (- (a * u / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hgeo : exp (- (a * u / 2)) <= exp (- (PI / 4)) ^ n)
    by (unfold a; apply exp_half_geo; lra).
  rewrite Hsplit. nra.
Qed.

(* ================================================================= *)
(*  SHARP BOUNDS.  The geometric majorants above are uniform in n but  *)
(*  badly slack at the FIRST term: 2 q^0 = 2 against a true value of   *)
(*  pi e^{-pi} = 0.136, a factor 15, and 18 q^0 = 18 against 0.562, a  *)
(*  factor 32.  Since the first term dominates the sum, that slack is  *)
(*  the whole error constant, and it propagates straight into the      *)
(*  quadrature node count as its square root.                          *)
(*                                                                    *)
(*  Same fix as ThetaTailSharp used for Psi itself: evaluate k = 1, 2  *)
(*  EXACTLY and majorize only k >= 3.  It works for the same reason --  *)
(*  the exponents are QUADRATIC, so the first neglected term is        *)
(*  e^{-9 pi} rather than a constant factor down.                      *)
(*                                                                    *)
(*  Two ingredients.  First, every term is maximised at u = 1, because *)
(*  z e^{-z} and z^2 e^{-z} are antitone past z = 1 and z = 2 and the  *)
(*  smallest exponent here is pi.  Second, past k = 3 the same         *)
(*  half-split as above still applies, now with room to spare.         *)
(* ================================================================= *)

(* z e^{-cz} is antitone once cz >= 1 -- the only monotonicity needed, *)
(* used at c = 1 for the first-order terms and c = 1/2 for the second  *)
(* (where z^2 e^{-z} = (z e^{-z/2})^2 makes it the same statement).    *)
Lemma vexp_antitone : forall c v w, 0 < c -> 1 <= c * v -> v <= w ->
  w * exp (- (c * w)) <= v * exp (- (c * v)).
Proof.
  intros c v w Hc Hcv Hvw.
  assert (Hv : 0 < v) by nra.
  assert (H1 : w <= v * (1 + c * (w - v))).
  { assert (E : v * (1 + c * (w - v)) - w = (w - v) * (c * v - 1)) by ring. nra. }
  assert (H2 : 1 + c * (w - v) <= exp (c * (w - v))) by apply exp_ineq1_le.
  assert (H3 : w <= v * exp (c * (w - v))) by nra.
  assert (E2 : exp (c * (w - v)) * exp (- (c * w)) = exp (- (c * v)))
    by (rewrite <- exp_plus; f_equal; ring).
  assert (H4 : w * exp (- (c * w)) <= v * exp (c * (w - v)) * exp (- (c * w)))
    by (apply Rmult_le_compat_r; [ left; apply exp_pos | exact H3 ]).
  rewrite Rmult_assoc, E2 in H4. exact H4.
Qed.

(* every term is largest at u = 1 *)
Lemma xterm_at1 : forall u n, 1 <= u ->
  PI * INR (S n) ^ 2 * u * exp (- (PI * INR (S n) ^ 2 * u))
  <= PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2)).
Proof.
  intros u n Hu. pose proof PI_lower as HP3.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 1 <= a) by (unfold a; nra).
  assert (Haw : a <= a * u) by nra.
  pose proof (vexp_antitone 1 a (a * u) ltac:(lra) ltac:(lra) Haw) as H.
  replace (1 * (a * u)) with (a * u) in H by ring.
  replace (1 * a) with a in H by ring.
  unfold a in H. exact H.
Qed.

Lemma xterm2_at1 : forall u n, 1 <= u ->
  (PI * INR (S n) ^ 2 * u) ^ 2 * exp (- (PI * INR (S n) ^ 2 * u))
  <= (PI * INR (S n) ^ 2) ^ 2 * exp (- (PI * INR (S n) ^ 2)).
Proof.
  intros u n Hu. pose proof PI_lower as HP3.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 2 <= a) by (unfold a; nra).
  assert (Haw : a <= a * u) by nra.
  pose proof (vexp_antitone (/ 2) a (a * u) ltac:(lra) ltac:(lra) Haw) as H.
  (* square both sides; both are nonnegative *)
  assert (Hl : 0 <= a * u * exp (- (/ 2 * (a * u))))
    by (apply Rmult_le_pos; [ nra | left; apply exp_pos ]).
  assert (Hsq : (a * u * exp (- (/ 2 * (a * u)))) ^ 2
             <= (a * exp (- (/ 2 * a))) ^ 2)
    by (apply pow_incr; lra).
  assert (E1 : (a * u * exp (- (/ 2 * (a * u)))) ^ 2
             = (a * u) ^ 2 * exp (- (a * u))).
  { assert (Ee : exp (- (/ 2 * (a * u))) * exp (- (/ 2 * (a * u)))
               = exp (- (a * u))) by (rewrite <- exp_plus; f_equal; field).
    simpl. rewrite <- Ee. ring. }
  assert (E2 : (a * exp (- (/ 2 * a))) ^ 2 = a ^ 2 * exp (- a)).
  { assert (Ee : exp (- (/ 2 * a)) * exp (- (/ 2 * a)) = exp (- a))
      by (rewrite <- exp_plus; f_equal; field).
    simpl. rewrite <- Ee. ring. }
  rewrite E1, E2 in Hsq. unfold a in Hsq. exact Hsq.
Qed.

(* past k = 3 the half-split still applies, geometrically in j = k - 3 *)
Lemma sharp_tail1 : forall j : nat,
  PI * (INR j + 3) ^ 2 * exp (- (PI * (INR j + 3) ^ 2))
  <= 2 * exp (- (9 * PI / 2)) * exp (- PI) ^ j.
Proof.
  intro j. pose proof PI_RGT_0 as HPI. pose proof (pos_INR j) as Hj.
  set (a := PI * (INR j + 3) ^ 2).
  assert (Ha : 0 < a) by (unfold a; nra).
  assert (Hv : a / 2 * exp (- (a / 2)) <= 1) by (apply v_exp_neg_v; lra).
  assert (He : 0 < exp (- (a / 2))) by apply exp_pos.
  assert (Hsplit : exp (- a) = exp (- (a / 2)) * exp (- (a / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hstep : a * exp (- a) <= 2 * exp (- (a / 2))) by (rewrite Hsplit; nra).
  assert (Hgeo : exp (- (a / 2)) <= exp (- (9 * PI / 2)) * exp (- PI) ^ j).
  { rewrite <- exp_INR_pow, <- exp_plus. apply exp_le_mono.
    assert (Hq : 0 <= PI * (INR j ^ 2 + 4 * INR j) / 2)
      by (apply Rmult_le_pos; [ nra | lra ]).
    assert (E : PI * (INR j ^ 2 + 4 * INR j) / 2
              = (- (9 * PI / 2) + INR j * - PI) - (- (a / 2)))
      by (unfold a; field).
    lra. }
  unfold a in Hstep. nra.
Qed.

Lemma sharp_tail2 : forall j : nat,
  ((PI * (INR j + 3) ^ 2) ^ 2 + PI * (INR j + 3) ^ 2)
    * exp (- (PI * (INR j + 3) ^ 2))
  <= 18 * exp (- (9 * PI / 2)) * exp (- PI) ^ j.
Proof.
  intro j. pose proof PI_RGT_0 as HPI. pose proof (pos_INR j) as Hj.
  set (a := PI * (INR j + 3) ^ 2).
  assert (Ha : 0 < a) by (unfold a; nra).
  assert (He2 : 0 < exp (- (a / 2))) by apply exp_pos.
  assert (He4 : 0 < exp (- (a / 4))) by apply exp_pos.
  assert (Hsplit : exp (- a) = exp (- (a / 2)) * exp (- (a / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  (* linear part *)
  assert (Hv2 : a / 2 * exp (- (a / 2)) <= 1) by (apply v_exp_neg_v; lra).
  assert (Hlin : a * exp (- a) <= 2 * exp (- (a / 2))) by (rewrite Hsplit; nra).
  (* quadratic part, quarter split squared *)
  assert (Hv4 : a / 4 * exp (- (a / 4)) <= 1) by (apply v_exp_neg_v; lra).
  assert (Hp : 0 <= a / 4 * exp (- (a / 4))) by nra.
  assert (Hsq : (a / 4 * exp (- (a / 4))) ^ 2 <= 1) by nra.
  assert (Equ : (a / 4 * exp (- (a / 4))) ^ 2
              = a ^ 2 / 16 * exp (- (a / 2))).
  { assert (Ee : exp (- (a / 4)) * exp (- (a / 4)) = exp (- (a / 2)))
      by (rewrite <- exp_plus; f_equal; field).
    simpl. rewrite <- Ee. field. }
  rewrite Equ in Hsq.
  assert (Hquad : a ^ 2 * exp (- a) <= 16 * exp (- (a / 2)))
    by (rewrite Hsplit; nra).
  assert (Hgeo : exp (- (a / 2)) <= exp (- (9 * PI / 2)) * exp (- PI) ^ j).
  { rewrite <- exp_INR_pow, <- exp_plus. apply exp_le_mono.
    assert (Hq : 0 <= PI * (INR j ^ 2 + 4 * INR j) / 2)
      by (apply Rmult_le_pos; [ nra | lra ]).
    assert (E : PI * (INR j ^ 2 + 4 * INR j) / 2
              = (- (9 * PI / 2) + INR j * - PI) - (- (a / 2)))
      by (unfold a; field).
    lra. }
  unfold a in Hlin, Hquad. nra.
Qed.

(* the ratio is genuinely below 1, so the majorant series converges *)
Corollary dtheta_ratio_lt1 : exp (- (PI / 4)) < 1.
Proof.
  rewrite <- exp_0. apply exp_increasing. pose proof PI_RGT_0. lra.
Qed.

Print Assumptions v_exp_neg_v.
Print Assumptions dtheta_term_bound.
Print Assumptions dtheta2_term_bound.
Print Assumptions xterm_bound.
Print Assumptions xterm2_bound.
Print Assumptions vexp_antitone.
Print Assumptions xterm_at1.
Print Assumptions sharp_tail1.
Print Assumptions sharp_tail2.
