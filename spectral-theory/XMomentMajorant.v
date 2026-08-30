(* ================================================================= *)
(*  XMomentMajorant.v  --  majorants for the x-space moment sums.      *)
(*                                                                    *)
(*  Simpson needs the THIRD x-derivative of Psi(e^x) to exist and to   *)
(*  be Lipschitz.  Differentiating in u and composing is hopeless:     *)
(*  the chain rule produces D3Psi(e^x) e^{3x} + 3 D2Psi(e^x) e^{2x}    *)
(*  + DPsi(e^x) e^x, and bounding e^{3x} by e^{3L} costs a factor 134. *)
(*  PsiXDeriv already paid a factor 1.5 of this at order 1 and had to  *)
(*  undo it with joint bounds.                                        *)
(*                                                                    *)
(*  In x-space it costs nothing.  Writing w = a e^x with a = pi k^2,   *)
(*  we have d/dx = w d/dw, so every derivative order is a POLYNOMIAL   *)
(*  IN w TIMES e^{-w}:                                                *)
(*                                                                    *)
(*    P0 = 1   P1 = -w   P2 = w^2 - w   P3 = -w^3 + 3w^2 - w           *)
(*    P4 = w^4 - 6w^3 + 7w^2 - w                                       *)
(*                                                                    *)
(*  (|coefficient of w^j in Pn| is the Stirling number S(n,j) -- row 4 *)
(*  is 1,7,6,1 -- which is a free correctness oracle at every order.)  *)
(*                                                                    *)
(*  So the ONLY object that ever needs majorizing is the single family *)
(*  w^i e^{-w}.  This file bounds it, in the two ways needed:          *)
(*    - uniformly in u >= 1/2 and geometrically in k, for the M-test   *)
(*      that makes the termwise differentiation legal;                 *)
(*    - sharply at its maximum, jointly with the e^{x/4} weight of the *)
(*      integrand, for the error constant.                            *)
(*                                                                    *)
(*  The tail constants are deliberately CRUDE ((2i)^i rather than the  *)
(*  sharp (2i)^i e^{-i}).  They multiply Ktail <= 5e-6 against a head  *)
(*  of order 1, so sharpening them moves the final constant by under   *)
(*  0.05% and would only cost lemmas.  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ExpEnclosure ThetaTailBounds CertifiedPi ThetaDerivMajorant.
Open Scope R_scope.

(* (2i)^i : the maximum of w^i e^{-w/2} is (2i)^i e^{-i}; we drop e^{-i}. *)
Definition Cm (i : nat) : R :=
  match i with
  | 0%nat => 1 | 1%nat => 2 | 2%nat => 16 | 3%nat => 216 | _ => 4096
  end.

Lemma Cm_pos : forall i, 0 < Cm i.
Proof. intro i. destruct i as [|[|[|[|i]]]]; simpl; lra. Qed.

(* the one absorption: v e^{-v} <= 1, raised to the i-th power, with    *)
(* v = w/(2i) so that i copies of e^{-v} make exactly e^{-w/2}.         *)
Lemma wpow_half_gen : forall (i : nat) (w : R), (1 <= i)%nat -> 0 <= w ->
  w ^ i * exp (- (w / 2)) <= (2 * INR i) ^ i.
Proof.
  intros i w Hi Hw.
  assert (Hi0 : 0 < INR i) by (apply lt_0_INR; lia).
  set (v := w / (2 * INR i)).
  assert (Hv : 0 <= v) by (unfold v; apply Rle_mult_inv_pos; lra).
  assert (H1 : v * exp (- v) <= 1) by (apply v_exp_neg_v; exact Hv).
  assert (H0 : 0 <= v * exp (- v))
    by (apply Rmult_le_pos; [ exact Hv | left; apply exp_pos ]).
  assert (Hpow : (v * exp (- v)) ^ i <= 1).
  { replace 1 with (1 ^ i) by (apply pow1). apply pow_incr. lra. }
  assert (Eexp : (exp (- v)) ^ i = exp (- (w / 2))).
  { rewrite <- exp_INR_pow. f_equal. unfold v. field. lra. }
  assert (Esplit : (v * exp (- v)) ^ i = v ^ i * exp (- (w / 2)))
    by (rewrite Rpow_mult_distr, Eexp; reflexivity).
  rewrite Esplit in Hpow.
  assert (Ev : w ^ i = (2 * INR i) ^ i * v ^ i).
  { unfold v. rewrite <- Rpow_mult_distr. f_equal. field. lra. }
  rewrite Ev.
  assert (Hc : 0 < (2 * INR i) ^ i) by (apply pow_lt; lra).
  nra.
Qed.

Theorem wpow_half : forall (i : nat) (w : R), (i <= 4)%nat -> 0 <= w ->
  w ^ i * exp (- (w / 2)) <= Cm i.
Proof.
  intros i w Hi Hw.
  destruct i as [|[|[|[|[|i]]]]]; simpl Cm.
  - simpl. rewrite Rmult_1_l.
    rewrite <- exp_0. apply exp_le_mono. lra.
  - eapply Rle_trans; [ apply (wpow_half_gen 1 w ltac:(lia) Hw) | ].
    simpl. lra.
  - eapply Rle_trans; [ apply (wpow_half_gen 2 w ltac:(lia) Hw) | ].
    simpl. lra.
  - eapply Rle_trans; [ apply (wpow_half_gen 3 w ltac:(lia) Hw) | ].
    simpl. lra.
  - eapply Rle_trans; [ apply (wpow_half_gen 4 w ltac:(lia) Hw) | ].
    simpl. lra.
  - exfalso; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the M-test input: uniform in u >= 1/2, geometric in k          *)
(*                                                                    *)
(*  Half the exponential absorbs the polynomial, the other half is     *)
(*  exp_half_geo -- already proved for the first-order case, and it    *)
(*  never mentioned the power, so it is reused verbatim.               *)
(* ----------------------------------------------------------------- *)
Theorem mterm_geo_bound : forall (i : nat) (u : R) (n : nat),
  (i <= 4)%nat -> / 2 <= u ->
  (PI * INR (S n) ^ 2 * u) ^ i * exp (- (PI * INR (S n) ^ 2 * u))
  <= Cm i * exp (- (PI / 4)) ^ n.
Proof.
  intros i u n Hi Hu. pose proof PI_RGT_0 as HPI.
  set (w := PI * INR (S n) ^ 2 * u).
  assert (Hk : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= INR (S n) ^ 2) by nra.
  assert (Hw : 0 <= w).
  { unfold w. apply Rmult_le_pos; [ | lra ].
    apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ]. }
  assert (Hsplit : exp (- w) = exp (- (w / 2)) * exp (- (w / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hpoly : w ^ i * exp (- (w / 2)) <= Cm i)
    by (apply wpow_half; assumption).
  assert (Hgeo : exp (- (w / 2)) <= exp (- (PI / 4)) ^ n)
    by (unfold w; apply exp_half_geo; exact Hu).
  assert (He : 0 < exp (- (w / 2))) by apply exp_pos.
  assert (Hq : 0 <= exp (- (PI / 4)) ^ n)
    by (apply pow_le; left; apply exp_pos).
  assert (Hwi : 0 <= w ^ i) by (apply pow_le; exact Hw).
  rewrite Hsplit.
  replace (w ^ i * (exp (- (w / 2)) * exp (- (w / 2))))
    with ((w ^ i * exp (- (w / 2))) * exp (- (w / 2))) by ring.
  apply Rle_trans with (Cm i * exp (- (w / 2))).
  - apply Rmult_le_compat_r; [ lra | exact Hpoly ].
  - apply Rmult_le_compat_l; [ left; apply Cm_pos | exact Hgeo ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the joint absorption of the integrand's e^{x/4} weight        *)
(*                                                                    *)
(*  With w = a e^x, the term TIMES the weight is                       *)
(*     w^i e^{-w} e^{x/4} = a^i exp((i + 1/4) x - a (e^x - 1)) e^{-a}, *)
(*  so it is largest at x = 0 exactly when (i + 1/4) x <= a (e^x - 1). *)
(*  Since e^x - 1 >= x that holds as soon as i + 1/4 <= a.             *)
(*                                                                    *)
(*  The threshold is i + 1/4, NOT i: the weight shifts it.  The        *)
(*  smallest a occurring is pi = 3.1416, so the clean bound covers     *)
(*  i <= 2 and already FAILS at i = 3 (by 0.108).  Rather than fall    *)
(*  back to the global maximum i^i e^{-i} -- which discards the e^{-a} *)
(*  and costs a factor e^{pi-i} -- the shortfall is absorbed by a      *)
(*  slack factor e^s, using the sharper e^x >= (1 + x/2)^2.  Completing *)
(*  the square gives s = (b-a)^2/a: s = 1/100 at i = 3 and 1/2 at      *)
(*  i = 4.  Cost in the final constant: about 0.05%.                   *)
(* ----------------------------------------------------------------- *)
Lemma joint_shift : forall a b x, 0 <= x -> 0 <= b -> b <= a ->
  b * x <= a * (exp x - 1).
Proof.
  intros a b x Hx Hb Hba.
  assert (Hex : 1 + x <= exp x) by apply exp_ineq1_le.
  assert (H1 : b * x <= a * x) by nra.
  assert (H2 : a * x <= a * (exp x - 1)) by nra.
  lra.
Qed.

Lemma exp_quad_lb : forall x, 0 <= x -> 1 + x + x ^ 2 / 4 <= exp x.
Proof.
  intros x Hx.
  assert (Hh : 1 + x / 2 <= exp (x / 2)) by apply exp_ineq1_le.
  assert (Hp : 0 <= 1 + x / 2) by lra.
  assert (Hsq : (1 + x / 2) ^ 2 <= (exp (x / 2)) ^ 2) by (apply pow_incr; lra).
  assert (E : (exp (x / 2)) ^ 2 = exp x)
    by (simpl; rewrite Rmult_1_r, <- exp_plus; f_equal; field).
  rewrite E in Hsq. nra.
Qed.

Lemma joint_shift_slack : forall a b s x, 0 < a -> 0 <= x -> 0 <= s ->
  (b - a) ^ 2 <= a * s -> b * x - a * (exp x - 1) <= s.
Proof.
  intros a b s x Ha Hx Hs Hbas.
  assert (Hex : 1 + x + x ^ 2 / 4 <= exp x) by (apply exp_quad_lb; exact Hx).
  (* b x - a(x + x^2/4) = -(a/4)(x - 2(b-a)/a)^2 + (b-a)^2/a *)
  assert (Hsq : 0 <= (a * x - 2 * (b - a)) ^ 2) by (apply pow2_ge_0).
  assert (Ekey : (b * x - a * (x + x ^ 2 / 4)) * (4 * a)
               = 4 * (b - a) ^ 2 - (a * x - 2 * (b - a)) ^ 2) by field.
  assert (Hstep : (b * x - a * (x + x ^ 2 / 4)) * (4 * a) <= 4 * (a * s))
    by (rewrite Ekey; nra).
  assert (Hdiv : b * x - a * (x + x ^ 2 / 4) <= s)
    by (apply (Rmult_le_reg_r (4 * a)); [ lra | nra ]).
  nra.
Qed.

(* the term, times the weight, at its maximum -- with a slack factor   *)
(* e^s that is 1 whenever i + 1/4 <= a                                 *)
Theorem mterm_joint_at0 : forall (i : nat) (a s x : R),
  0 <= x -> 0 < a -> 0 <= s -> (INR i + / 4 - a) ^ 2 <= a * s ->
  (a * exp x) ^ i * exp (- (a * exp x)) * exp (/ 4 * x)
  <= a ^ i * exp (- a) * exp s.
Proof.
  intros i a s x Hx Ha Hs Hslack.
  (* (a e^x)^i = a^i e^{i x} *)
  assert (Epow : (a * exp x) ^ i = a ^ i * exp (INR i * x)).
  { rewrite Rpow_mult_distr. f_equal. symmetry. apply exp_INR_pow. }
  rewrite Epow.
  (* collect the three exponentials *)
  assert (Ecoll : exp (INR i * x) * exp (- (a * exp x)) * exp (/ 4 * x)
                = exp ((INR i + / 4) * x - a * exp x))
    by (rewrite <- !exp_plus; f_equal; field).
  assert (Ereg : a ^ i * exp (INR i * x) * exp (- (a * exp x)) * exp (/ 4 * x)
               = a ^ i * (exp (INR i * x) * exp (- (a * exp x)) * exp (/ 4 * x)))
    by ring.
  rewrite Ereg, Ecoll.
  assert (Eexp : exp (- a) * exp s = exp (- a + s)) by (rewrite exp_plus; ring).
  assert (Etgt2 : a ^ i * exp (- a) * exp s = a ^ i * exp (- a + s))
    by (rewrite <- Eexp; ring).
  rewrite Etgt2.
  assert (Hai : 0 <= a ^ i) by (apply pow_le; lra).
  apply Rmult_le_compat_l; [ exact Hai | ].
  apply exp_le_mono.
  pose proof (joint_shift_slack a (INR i + / 4) s x Ha Hx Hs Hslack) as H.
  lra.
Qed.

(* the clean case: no slack needed once i + 1/4 <= a.  Same collection *)
(* of exponentials, closed by joint_shift instead of its slack form.   *)
Corollary mterm_joint_at0_clean : forall (i : nat) (a x : R),
  0 <= x -> 0 < a -> INR i + / 4 <= a ->
  (a * exp x) ^ i * exp (- (a * exp x)) * exp (/ 4 * x) <= a ^ i * exp (- a).
Proof.
  intros i a x Hx Ha Hle.
  assert (Hi : 0 <= INR i) by apply pos_INR.
  assert (Epow : (a * exp x) ^ i = a ^ i * exp (INR i * x)).
  { rewrite Rpow_mult_distr. f_equal. symmetry. apply exp_INR_pow. }
  rewrite Epow.
  assert (Ecoll : exp (INR i * x) * exp (- (a * exp x)) * exp (/ 4 * x)
                = exp ((INR i + / 4) * x - a * exp x))
    by (rewrite <- !exp_plus; f_equal; field).
  assert (Ereg : a ^ i * exp (INR i * x) * exp (- (a * exp x)) * exp (/ 4 * x)
               = a ^ i * (exp (INR i * x) * exp (- (a * exp x)) * exp (/ 4 * x)))
    by ring.
  rewrite Ereg, Ecoll.
  assert (Hai : 0 <= a ^ i) by (apply pow_le; lra).
  apply Rmult_le_compat_l; [ exact Hai | ].
  apply exp_le_mono.
  pose proof (joint_shift a (INR i + / 4) x Hx ltac:(lra) Hle) as H.
  lra.
Qed.

Print Assumptions wpow_half.
Print Assumptions mterm_geo_bound.
Print Assumptions joint_shift_slack.
Print Assumptions mterm_joint_at0.
