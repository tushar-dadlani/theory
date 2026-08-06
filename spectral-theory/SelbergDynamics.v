(* ================================================================= *)
(*  SelbergDynamics.v  —  the robust dynamical bricks of the S2 wall.   *)
(*                                                                    *)
(*  The elementary-PNT self-improvement (alpha = 0) is the one genuine  *)
(*  gap.  Its robust, NON-PNT-hard ingredients -- which unlike          *)
(*  avg_below / S1 are sound and provable from psi monotone alone --    *)
(*  are isolated here:                                                  *)
(*                                                                    *)
(*   Rem_step  : Rem(N+1) = Rem N + Lam(N+1) - 1   -- the exact         *)
(*     discrete sigma-dynamics (dR/dt = Lambda - 1): Rem drifts DOWN by *)
(*     1 between prime powers and jumps up by Lam at prime powers.      *)
(*   Rem_gap / Rem_drift_lb : the interval form (Rem falls by at most   *)
(*     M-N over [N,M], exactly M-N with no prime power).                *)
(*   plateau_pos / plateau_neg : an excursion to +/-b at y forces       *)
(*     Vsig >= b' (resp <= b') over the whole multiplicative interval   *)
(*     t <= y*(1+b)/(1+b') -- excursions have positive width.           *)
(*                                                                    *)
(*  These reduce S2 to the single hard estimate: bounding the COLLECTIVE *)
(*  up-jump mass against the down-drift over an interval (Erdos density, *)
(*  elementary from Chebyshev), which forces a positive log-fraction    *)
(*  with |Vsig| < alpha - c and hence the contraction alpha <= (1-c)alpha.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import Chebyshev ChebyshevBound SelbergEndgame SelbergAverageSigned
        VonMangoldtGlobal.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  The exact discrete dynamics of the error Rem = psi - N.        *)
(* ================================================================= *)

(* dR/dt = Lambda - 1: between prime powers Rem falls by 1; at a prime  *)
(* power N it jumps up by Lam N.                                        *)
Lemma Rem_step : forall N, Rem (S N) = Rem N + Lam (S N) - 1.
Proof. intro N; unfold Rem; rewrite psi_succ, S_INR; ring. Qed.

Lemma Rem_gap : forall N M, Rem M - Rem N = (psi M - psi N) - (INR M - INR N).
Proof. intros N M; unfold Rem; ring. Qed.

(* psi monotone => Rem cannot fall faster than the trivial slope -1 *)
Lemma Rem_drift_lb : forall N M, (N <= M)%nat -> Rem N - (INR M - INR N) <= Rem M.
Proof.
  intros N M HNM; pose proof (psi_mono N M HNM) as Hp;
    pose proof (Rem_gap N M) as Hg; lra.
Qed.

(* with no prime power in (N,M] (psi M = psi N), Rem falls by exactly M-N *)
Lemma Rem_drift_eq : forall N M, psi M = psi N -> Rem M = Rem N - (INR M - INR N).
Proof. intros N M Hpsi; pose proof (Rem_gap N M) as Hg; lra. Qed.

(* ================================================================= *)
(*  2.  The plateau lemmas: excursions have positive multiplicative    *)
(*  width (from psi monotone alone).                                   *)
(* ================================================================= *)

(* A near-peak Vsig y >= b forces Vsig t >= b' for every later t with   *)
(* t*(1+b') <= y*(1+b), i.e. t <= y*(1+b)/(1+b').                       *)
Theorem plateau_pos : forall (y t : nat) (b b' : R),
  (1 <= y)%nat -> (y <= t)%nat ->
  b <= Vsig y -> INR t * (1 + b') <= INR y * (1 + b) -> b' <= Vsig t.
Proof.
  intros y t b b' Hy Hyt Hb Hcond.
  assert (Hy0 : 0 < INR y) by (apply lt_0_INR; lia).
  assert (Ht0 : 0 < INR t) by (apply lt_0_INR; lia).
  (* Vsig y >= b  =>  psi y >= (1+b) * INR y *)
  assert (Hpsiy : (1 + b) * INR y <= psi y).
  { pose proof (Rmult_le_compat_r (INR y) b ((psi y - INR y) / INR y)
                 (Rlt_le _ _ Hy0) ltac:(unfold Vsig, Rem in Hb; exact Hb)) as HbY.
    replace ((psi y - INR y) / INR y * INR y) with (psi y - INR y) in HbY by (field; lra).
    lra. }
  pose proof (psi_mono y t Hyt) as Hmono.
  assert (HRemt : (1 + b) * INR y - INR t <= Rem t) by (unfold Rem; lra).
  unfold Vsig, Rdiv; apply Rmult_le_reg_r with (INR t); [ exact Ht0 | ].
  replace (Rem t * / INR t * INR t) with (Rem t) by (field; lra).
  assert (Hkey : (1 + b') * INR t <= (1 + b) * INR y)
    by (rewrite (Rmult_comm (1 + b') (INR t)), (Rmult_comm (1 + b) (INR y)); exact Hcond).
  assert (Hbt : b' * INR t = (1 + b') * INR t - INR t) by ring; lra.
Qed.

(* Symmetrically, a near-trough Vsig y <= b forces Vsig t <= b' for     *)
(* every earlier t with y*(1+b) <= t*(1+b').                            *)
Theorem plateau_neg : forall (y t : nat) (b b' : R),
  (1 <= t)%nat -> (t <= y)%nat ->
  Vsig y <= b -> INR y * (1 + b) <= INR t * (1 + b') -> Vsig t <= b'.
Proof.
  intros y t b b' Ht Hty Hb Hcond.
  assert (Hy0 : 0 < INR y) by (apply lt_0_INR; lia).
  assert (Ht0 : 0 < INR t) by (apply lt_0_INR; lia).
  assert (Hpsiy : psi y <= (1 + b) * INR y).
  { pose proof (Rmult_le_compat_r (INR y) ((psi y - INR y) / INR y) b
                 (Rlt_le _ _ Hy0) ltac:(unfold Vsig, Rem in Hb; exact Hb)) as HbY.
    replace ((psi y - INR y) / INR y * INR y) with (psi y - INR y) in HbY by (field; lra).
    lra. }
  pose proof (psi_mono t y Hty) as Hmono.
  assert (HRemt : Rem t <= (1 + b) * INR y - INR t) by (unfold Rem; lra).
  unfold Vsig, Rdiv; apply Rmult_le_reg_r with (INR t); [ exact Ht0 | ].
  replace (Rem t * / INR t * INR t) with (Rem t) by (field; lra).
  assert (Hkey : (1 + b) * INR y <= (1 + b') * INR t)
    by (rewrite (Rmult_comm (1 + b) (INR y)), (Rmult_comm (1 + b') (INR t)); exact Hcond).
  assert (Hbt : b' * INR t = (1 + b') * INR t - INR t) by ring; lra.
Qed.

Print Assumptions Rem_step.
Print Assumptions plateau_pos.

(* ================================================================= *)
(*  END SelbergDynamics.v  —  the sound, non-PNT-hard core of S2:       *)
(*  Rem_step (dynamics) + plateau_pos/neg (excursions have width).     *)
(*  Remaining: the collective jump-vs-drift estimate (Erdos density).   *)
(* ================================================================= *)
