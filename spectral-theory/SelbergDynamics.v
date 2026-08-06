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

(* ================================================================= *)
(*  3.  BAND OCCUPANCY (the sound core): during a downward crossing     *)
(*  Rem cannot skip a level, so it visits EVERY level it crosses.       *)
(* ================================================================= *)

(* Rem drops by at most 1 per step (the down-drift is -1, jumps are up). *)
Lemma Rem_no_big_drop : forall N, Rem N - 1 <= Rem (S N).
Proof. intro N; pose proof (Rem_step N); pose proof (Lam_nonneg (S N)); lra. Qed.

(* Interval version of the no-skip crossing. *)
Lemma crossing_band_d : forall d N L,
  Rem N >= L -> Rem (N + d)%nat < L ->
  exists k, (N < k <= N + d)%nat /\ L - 1 <= Rem k /\ Rem k < L.
Proof.
  induction d as [|d IH]; intros N L H0 Hd.
  - rewrite Nat.add_0_r in Hd; exfalso; lra.
  - destruct (Rle_lt_dec L (Rem (S N))) as [Hge | Hlt].
    + assert (Hd' : Rem (S N + d)%nat < L)
        by (replace (S N + d)%nat with (N + S d)%nat by lia; exact Hd).
      destruct (IH (S N) L (Rle_ge _ _ Hge) Hd') as [k [Hk [Hk1 Hk2]]].
      exists k; split; [ lia | split; assumption ].
    + exists (S N); split; [ lia | ].
      pose proof (Rem_no_big_drop N); split; [ lra | exact Hlt ].
Qed.

(* No downward skip: between a point with Rem >= L and a later point     *)
(* with Rem < L there is a point INSIDE the unit band [L-1, L).  Applied *)
(* at every integer level L in (A,B] this gives >= B-A DISTINCT points   *)
(* with Rem in [A,B) (disjoint unit bands => distinct points): the band  *)
(* [A,B) is occupied at >= (B-A) indices during any crossing of it --    *)
(* the elementary heart of band occupancy (no jump control needed).      *)
Theorem crossing_band : forall N M L, (N <= M)%nat ->
  Rem N >= L -> Rem M < L ->
  exists k, (N < k <= M)%nat /\ L - 1 <= Rem k /\ Rem k < L.
Proof.
  intros N M L HNM H0 HM.
  assert (Hd : Rem (N + (M - N))%nat < L)
    by (replace (N + (M - N))%nat with M by lia; exact HM).
  destruct (crossing_band_d (M - N) N L H0 Hd) as [k [Hk Hr]].
  exists k; split; [ replace (N + (M - N))%nat with M in Hk by lia; lia | exact Hr ].
Qed.

Print Assumptions Rem_step.
Print Assumptions plateau_pos.
Print Assumptions crossing_band.

(* ================================================================= *)
(*  END SelbergDynamics.v  —  the sound, non-PNT-hard core of S2:       *)
(*  Rem_step (dynamics) + plateau_pos/neg (excursions have width).     *)
(*  Remaining: the collective jump-vs-drift estimate (Erdos density).   *)
(* ================================================================= *)
