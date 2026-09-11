(* ================================================================= *)
(*  XiRealGrowth.v  --  xi grows like a FACTORIAL on the real axis.    *)
(*                                                                    *)
(*    xi_real_growth : for M >= 1,                                    *)
(*      ln(N(2N-1)) - N ln pi + (M ln M - M + 1)                      *)
(*        <= ln (Cmod (XiC (RtoC (2N))))       where N = M+1          *)
(*                                                                    *)
(*  i.e. ln |xi(2N)| grows at least like N ln N.                      *)
(*                                                                    *)
(*  WHY THIS IS THE MISSING DIRECTION.  XiGrowthBound.XiC_growth       *)
(*  bounds |xi| ABOVE by /2 + (|z|+1)^2 Tgb(|z|+1) with               *)
(*  Tgb s = C (s/pi)^{s/2} e^{-s/2} -- the Stirling shape.  Every      *)
(*  zero-counting theorem in the repo consumes that upper bound and    *)
(*  concludes the count is SMALL.  Nothing anywhere bounds |xi| from   *)
(*  BELOW, and without that no zero count can be bounded below --      *)
(*  in particular "xi has infinitely many zeros" is unreachable.       *)
(*  This file supplies the lower bound, in the one place it is easy:   *)
(*  the real axis at even integers, where every factor of the          *)
(*  completed zeta is positive and Gamma is a factorial.               *)
(*                                                                    *)
(*  The geometry it feeds: Jensen's formula says the circle average    *)
(*  of ln|xi| equals ln|xi(0)| plus sum over zeros of ln(r/|rho|).     *)
(*  Finitely many zeros can pay for at most O(ln r) of growth.  A      *)
(*  factorial is r ln r.  The zeros are the only account that can be   *)
(*  debited, so there must be infinitely many of them.                 *)
(*                                                                    *)
(*  Everything here is assembly.  The one identity that makes it easy  *)
(*  is ZetaXiLink.XiC_is_completed_zeta, which is already stated with  *)
(*  a PURELY REAL right-hand side -- no Gamma/zeta bridge is needed.   *)
(*  Gam at a natural argument (Gam_nat below) was the only genuinely   *)
(*  missing lemma.                                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Factorial.
Require Import ComplexField Cmodulus RiemannXiEntire GammaReal GammaOne
        GammaRecur GammaExtend Ell2ZetaCont CEulerProductZeta ZetaXiLink
        Chebyshev StirlingSharp.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- Gamma at a natural argument is a factorial.              *)
(* ----------------------------------------------------------------- *)

Lemma INR_S_pos : forall N : nat, 0 < INR (S N).
Proof. intro N. apply lt_0_INR. lia. Qed.

Lemma Gam_nat : forall N (H : 0 < INR (S N)), Gam (INR (S N)) H = INR (fact N).
Proof.
  induction N as [| N IH]; intro H.
  - assert (H1 : (0:R) < 1) by lra.
    assert (Heq1 : INR (S 0) = 1) by reflexivity.
    rewrite (Gam_arg_eq (INR (S 0)) 1 H H1 Heq1), (Gam_1 H1).
    replace (fact 0) with 1%nat by reflexivity. reflexivity.
  - pose proof (INR_S_pos N) as Hp.
    assert (Hb : 0 < INR (S N) + 1) by lra.
    assert (Heq : INR (S (S N)) = INR (S N) + 1) by (rewrite (S_INR (S N)); reflexivity).
    rewrite (Gam_arg_eq (INR (S (S N))) (INR (S N) + 1) H Hb Heq).
    rewrite (Gam_recur (INR (S N)) Hp Hb), (IH Hp).
    rewrite fact_simpl, mult_INR. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the value of xi at an even integer, in closed form.      *)
(* ----------------------------------------------------------------- *)

Section AtEven.
Variable M : nat.
Hypothesis HM : (1 <= M)%nat.

Let N := S M.
Let s := 2 * INR N.

Lemma N_ge2 : 2 <= INR N.
Proof. unfold N. replace 2 with (INR 2) by reflexivity. apply le_INR. lia. Qed.

Lemma s_gt1 : 1 < s.
Proof. unfold s. pose proof N_ge2. lra. Qed.

Lemma s_pos : 0 < s.
Proof. pose proof s_gt1. lra. Qed.

Lemma s_ne1 : s <> 1.
Proof. pose proof s_gt1. lra. Qed.

Lemma shalf_pos : 0 < s / 2.
Proof. pose proof s_pos. lra. Qed.

Lemma shalf_eq : s / 2 = INR (S M).
Proof. unfold s, N. field. Qed.

Lemma Pfac_pos : 0 < Rpower PI (- (s / 2)).
Proof. unfold Rpower. apply exp_pos. Qed.

Lemma Gfac_pos : 0 < INR (fact M).
Proof. apply lt_0_INR. apply lt_O_fact. Qed.

Lemma Zfac_ge1 : 1 <= zeta_cont s s_pos s_ne1.
Proof. apply zeta_cont_ge1. exact s_gt1. Qed.

Lemma head_pos : 0 < INR N * (2 * INR N - 1).
Proof. pose proof N_ge2. nra. Qed.

Lemma xi_even_value :
  Cmod (XiC (RtoC s))
  = INR N * (2 * INR N - 1) * Rpower PI (- (s / 2)) * INR (fact M)
    * zeta_cont s s_pos s_ne1.
Proof.
  pose proof head_pos as Hh. pose proof Pfac_pos as Hp.
  pose proof Gfac_pos as Hg. pose proof Zfac_ge1 as Hz.
  pose proof N_ge2 as HN.
  rewrite (XiC_is_completed_zeta s s_pos s_ne1 shalf_pos s_gt1), Cmod_RtoC.
  assert (HG : Gam (s / 2) shalf_pos = INR (fact M)).
  { assert (Hpp : 0 < INR (S M)) by apply INR_S_pos.
    rewrite (Gam_arg_eq (s / 2) (INR (S M)) shalf_pos Hpp shalf_eq).
    apply Gam_nat. }
  rewrite HG, Rabs_pos_eq.
  - unfold s. field.
  - assert (Hs4 : 4 <= s) by (unfold s; lra).
    assert (HPGZ : 0 < Rpower PI (- (s / 2)) * INR (fact M)
                       * zeta_cont s s_pos s_ne1)
      by (repeat apply Rmult_lt_0_compat; lra).
    assert (Hrest : 0 < (s - 1) * (Rpower PI (- (s / 2)) * INR (fact M)
                                   * zeta_cont s s_pos s_ne1))
      by (apply Rmult_lt_0_compat; lra).
    nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the logarithm, bounded below by Stirling.                *)
(* ----------------------------------------------------------------- *)

Theorem xi_real_growth :
  ln (INR N * (2 * INR N - 1)) - INR N * ln PI + (INR M * ln (INR M) - INR M + 1)
  <= ln (Cmod (XiC (RtoC s))).
Proof.
  pose proof head_pos as Hh. pose proof Pfac_pos as Hp.
  pose proof Gfac_pos as Hg. pose proof Zfac_ge1 as Hz.
  assert (Hzp : 0 < zeta_cont s s_pos s_ne1) by lra.
  assert (H1 : 0 < INR N * (2 * INR N - 1) * Rpower PI (- (s / 2)))
    by (apply Rmult_lt_0_compat; assumption).
  assert (H2 : 0 < INR N * (2 * INR N - 1) * Rpower PI (- (s / 2)) * INR (fact M))
    by (apply Rmult_lt_0_compat; assumption).
  rewrite xi_even_value.
  rewrite (ln_mult (INR N * (2 * INR N - 1) * Rpower PI (- (s / 2)) * INR (fact M))
                   (zeta_cont s s_pos s_ne1)) by assumption.
  rewrite (ln_mult (INR N * (2 * INR N - 1) * Rpower PI (- (s / 2)))
                   (INR (fact M))) by assumption.
  rewrite (ln_mult (INR N * (2 * INR N - 1)) (Rpower PI (- (s / 2)))) by assumption.
  assert (HlnP : ln (Rpower PI (- (s / 2))) = - INR N * ln PI).
  { unfold Rpower. rewrite ln_exp, shalf_eq. unfold N. ring. }
  rewrite HlnP.
  assert (HlnG : INR M * ln (INR M) - INR M + 1 <= ln (INR (fact M))).
  { rewrite <- Tlog_eq_ln_fact. exact (proj1 (Tlog_sharp M HM)). }
  assert (HlnZ : 0 <= ln (zeta_cont s s_pos s_ne1)).
  { destruct (Rle_lt_or_eq_dec 1 (zeta_cont s s_pos s_ne1) Hz) as [Hlt | Heq].
    - left. rewrite <- ln_1. apply ln_increasing; lra.
    - rewrite <- Heq, ln_1. lra. }
  lra.
Qed.

End AtEven.

Print Assumptions xi_real_growth.

(* ================================================================= *)
(*  END XiRealGrowth.v                                                *)
(* ================================================================= *)
