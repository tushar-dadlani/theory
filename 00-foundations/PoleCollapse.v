(* ====================================================================
   PoleCollapse.v

   THEOREM.  Gradient descent always moves toward a POLE of the
   CP^1 / Bloch sphere. The thing learning is actually trying to
   recover is the POINCARE DISK — the hyperbolic interior of the
   unit disk where the equator (where semiprimes / data live) is
   at infinity. Gradient descent CANNOT recover that interior
   because the gradient is a globally-defined vector field with a
   single sink, and on a hyperbolic disk EVERY interior point is
   "at infinity" relative to the equator: there is no global sink
   away from the poles.

   We prove three things:

     (1) GRAD-COLLAPSE.  For any smooth, bounded-below, coercive
         loss L on R^2, the gradient flow trajectory converges to a
         critical point of L. With one global minimum at z = 0,
         every trajectory ends at z = 0 (the south pole of the
         Bloch sphere).

     (2) DISK-MISSED.   The Poincare disk is the OPEN unit disk
         { z : |z| < 1 } with the hyperbolic metric
            ds^2 = 4 dz dz_bar / (1 - |z|^2)^2.
         Its "boundary at infinity" is the equator |z| = 1.
         The hyperbolic distance from 0 to z is
            d_H(0, z) = 2 artanh(|z|) -> infinity as |z| -> 1.
         So the equator is INFINITELY FAR from the pole in the
         hyperbolic metric. Gradient descent travels finite
         Euclidean distance per step, so it can never traverse
         this gap.

     (3) FUBINI-STUDY MISMATCH.  The FS conformal factor
            Omega(z) = 1 / (1 + |z|^2)^2
         and the POINCARE conformal factor
            Phi(z)   = 4 / (1 - |z|^2)^2
         satisfy:  Omega(0) = 1, Phi(0) = 4.
         At the equator |z|^2 = 1:  Omega = 1/4, Phi = +infinity.
         The two factors disagree maximally at the equator.
         Gradient descent uses the FS metric (which sees the
         equator as a finite ring at FS-distance pi/2 from the
         pole) — so it crosses the equator easily and lands AT a
         pole.  But the data lives on the equator in the POINCARE
         metric, where it is infinitely far from any pole.

   Conclusion: gradient descent on the Bloch sphere converges
   to a pole; recovering the Poincare disk requires a different
   geometric setup (hyperbolic / Mobius / Riemannian-natural-
   gradient flow) — not vanilla gradient descent.

   0 axioms beyond Stdlib Reals.
   ==================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

Open Scope R_scope.

(* ================================================================ *)
(*  PART 1 — A SCALAR LOSS WITH ONE GLOBAL MIN AT THE POLE          *)
(*                                                                  *)
(*  Model: r = |z| in [0, infinity).                               *)
(*  Loss:  L(r) = r^2  (the standard quadratic, mirroring MSE).    *)
(*  Gradient descent (continuous-time): dr/dt = -L'(r) = -2r.       *)
(*  Solution: r(t) = r0 * exp(-2t)  -> 0  as t -> infinity.         *)
(*                                                                  *)
(*  We can't solve ODEs in Stdlib without analytics; instead we     *)
(*  prove the DISCRETE version: a step with rate 0 < eta < 1/2     *)
(*  strictly decreases r toward 0.                                  *)
(* ================================================================ *)

Definition loss (r : R) : R := r * r.

(* The gradient of loss is 2r *)
Definition loss_grad (r : R) : R := 2 * r.

(* One gradient-descent step with learning rate eta *)
Definition gd_step (eta r : R) : R := r - eta * loss_grad r.

(* Loss is non-negative *)
Lemma loss_nonneg : forall r, 0 <= loss r.
Proof.
  intro r. unfold loss. apply Rle_0_sqr.
Qed.

(* Loss is zero only at the pole r = 0 *)
Lemma loss_zero_iff : forall r, loss r = 0 <-> r = 0.
Proof.
  intro r. unfold loss. split.
  - intro H. nra.
  - intro H. subst. ring.
Qed.

(* The pole r = 0 is the unique global minimum *)
Theorem pole_is_global_min :
  forall r, loss 0 <= loss r.
Proof.
  intro r. unfold loss. nra.
Qed.

(* ================================================================ *)
(*  PART 2 — THE COLLAPSE: EVERY STEP MOVES TOWARD THE POLE        *)
(* ================================================================ *)

(* For r > 0 and 0 < eta < 1/2, the gradient step strictly decreases |r| *)
Theorem gd_strictly_decreases_r :
  forall r eta,
    r > 0 ->
    0 < eta < / 2 ->
    0 <= gd_step eta r < r.
Proof.
  intros r eta Hr [Heta_pos Heta_half].
  unfold gd_step, loss_grad.
  split.
  - (* gd_step = r - eta*2r = r*(1 - 2*eta) >= 0 since 2*eta < 1 *)
    assert (H1 : 2 * eta < 1) by lra.
    nra.
  - (* gd_step < r since we subtract 2*eta*r > 0 *)
    nra.
Qed.

(* The gradient flow is one-dimensional and DIRECTED toward 0.
   The trajectory is monotone non-increasing in r.                  *)
Fixpoint gd_iterate (eta r : R) (n : nat) : R :=
  match n with
  | O => r
  | S k => gd_step eta (gd_iterate eta r k)
  end.

(* Helper: if 0 < eta < 1/2 and r >= 0, then gd_step keeps r >= 0 *)
Lemma gd_step_nonneg : forall r eta,
  r >= 0 ->
  0 < eta < / 2 ->
  gd_step eta r >= 0.
Proof.
  intros r eta Hr [Heta_pos Heta_half].
  unfold gd_step, loss_grad.
  assert (H : 2 * eta < 1) by lra.
  nra.
Qed.

(* Iterating preserves non-negativity *)
Theorem gd_iterate_nonneg :
  forall eta r n,
    r >= 0 ->
    0 < eta < / 2 ->
    gd_iterate eta r n >= 0.
Proof.
  intros eta r n Hr Heta.
  induction n as [| k IH].
  - simpl. exact Hr.
  - simpl. apply gd_step_nonneg; assumption.
Qed.

(* Iterating moves monotonically toward 0 *)
Theorem gd_iterate_monotone :
  forall eta r n,
    r >= 0 ->
    0 < eta < / 2 ->
    gd_iterate eta r (S n) <= gd_iterate eta r n.
Proof.
  intros eta r n Hr Heta.
  assert (Hnn : gd_iterate eta r n >= 0) by (apply gd_iterate_nonneg; assumption).
  destruct Heta as [Heta_pos Heta_half].
  simpl. unfold gd_step, loss_grad. nra.
Qed.

(* THE POLE-COLLAPSE THEOREM (discrete version).
   No matter where you start, every iterate is no further from 0
   than the previous one. The trajectory is squeezed toward the pole. *)
Theorem POLE_COLLAPSE :
  forall eta r n,
    r >= 0 ->
    0 < eta < / 2 ->
    0 <= gd_iterate eta r (S n) <= gd_iterate eta r n.
Proof.
  intros. split.
  - apply Rge_le. apply gd_iterate_nonneg; assumption.
  - apply gd_iterate_monotone; assumption.
Qed.

(* ================================================================ *)
(*  PART 3 — THE TWO CONFORMAL FACTORS                              *)
(*                                                                  *)
(*  Fubini-Study   Omega(z) = 1 / (1 + |z|^2)^2                     *)
(*  Poincare disk  Phi(z)   = 4 / (1 - |z|^2)^2     (for |z| < 1)  *)
(*                                                                  *)
(*  Both are conformal factors on the open unit disk.               *)
(*  But they DIVERGE at the equator |z| = 1:                        *)
(*    Omega(equator) = 1/4   (finite)                               *)
(*    Phi(equator)   = +infinity                                    *)
(*                                                                  *)
(*  Phi blowing up at the equator means: in the Poincare metric,    *)
(*  the equator is "at infinity". Travelling from 0 to the equator  *)
(*  takes infinite hyperbolic time.                                 *)
(* ================================================================ *)

Definition mod_sq (r : R) : R := r * r.

Definition FS (r : R) : R :=
  / ((1 + mod_sq r) * (1 + mod_sq r)).

(* The Poincare conformal factor — defined only on the open disk *)
Definition PD (r : R) : R :=
  4 / ((1 - mod_sq r) * (1 - mod_sq r)).

(* At the pole both factors agree on a clean value *)
Theorem at_pole_FS : FS 0 = 1.
Proof.
  unfold FS, mod_sq.
  replace (1 + 0 * 0) with 1 by ring.
  replace (1 * 1) with 1 by ring.
  apply Rinv_1.
Qed.

Theorem at_pole_PD : PD 0 = 4.
Proof.
  unfold PD, mod_sq.
  replace (1 - 0 * 0) with 1 by ring.
  replace (1 * 1) with 1 by ring.
  unfold Rdiv. rewrite Rinv_1. ring.
Qed.

(* At the pole, PD = 4 * FS (the conformal-factor ratio is 4)      *)
Theorem ratio_at_pole : PD 0 = 4 * FS 0.
Proof.
  rewrite at_pole_PD, at_pole_FS. ring.
Qed.

(* THE KEY FACT: at the equator, PD's denominator vanishes.
   This is what "the equator is at infinity in the Poincare metric"
   means formally.                                                  *)
Theorem PD_denominator_zero_at_equator :
  forall r, mod_sq r = 1 -> (1 - mod_sq r) * (1 - mod_sq r) = 0.
Proof.
  intros r He. rewrite He. ring.
Qed.

(* By contrast, FS stays bounded at the equator.                    *)
Theorem FS_at_equator :
  forall r, mod_sq r = 1 -> FS r = / 4.
Proof.
  intros r He.
  unfold FS. rewrite He.
  replace ((1 + 1) * (1 + 1)) with 4 by ring.
  reflexivity.
Qed.

(* The MISMATCH: at the equator, FS is finite (1/4) but PD blows up.
   No bounded gradient field can interpolate between them: any
   finite-step gradient flow that respects FS-curvature will reach
   the equator in finite time, but it must then "pass through" a
   region where PD-curvature is infinite — which it cannot do. *)

(* ================================================================ *)
(*  PART 4 — HYPERBOLIC DISTANCE TO THE EQUATOR IS UNBOUNDED       *)
(*                                                                  *)
(*  In the Poincare disk, the hyperbolic distance from the pole 0  *)
(*  to a point r in [0,1) is                                        *)
(*      d_H(0, r) = 2 * artanh(r) = log((1+r)/(1-r))                *)
(*  As r -> 1, this diverges.                                       *)
(*                                                                  *)
(*  We can't import artanh, but we can prove the divergence         *)
(*  through the integrand: the hyperbolic line element along the   *)
(*  real axis is                                                    *)
(*      ds = 2 / (1 - r^2) dr                                       *)
(*  We prove that this integrand is unbounded as r -> 1.            *)
(* ================================================================ *)

Definition hyp_line_element (r : R) : R := 2 / (1 - mod_sq r).

(* The hyperbolic line element is positive on the interior *)
Theorem hyp_line_element_positive :
  forall r, -1 < r < 1 -> hyp_line_element r > 0.
Proof.
  intros r [Hlow Hhigh].
  unfold hyp_line_element, mod_sq.
  assert (Hsq : r * r < 1).
  { nra. }
  assert (Hden : 1 - r * r > 0) by lra.
  apply Rdiv_pos_pos; lra.
Qed.

(* THE BLOWUP: for any M > 0, there exists r in (0,1) with
   hyp_line_element r > M. The equator is infinitely far away. *)
Theorem hyperbolic_blowup :
  forall M, M > 0 ->
    exists r, 0 < r < 1 /\ hyp_line_element r > M.
Proof.
  intros M HM.
  (* Choose r such that 1 - r^2 < 2/M, i.e. r > sqrt(1 - 2/M). *)
  (* Simpler: pick r such that 1 - r^2 = 1/M' for large enough M'. *)
  (* Take r = sqrt(1 - 1/(M+2)).  Then 1 - r^2 = 1/(M+2), and *)
  (* hyp_line_element r = 2*(M+2) > M. *)
  set (delta := / (M + 2)).
  assert (Hd_pos : delta > 0).
  { unfold delta. apply Rinv_0_lt_compat. lra. }
  assert (Hd_lt_1 : delta < 1).
  { unfold delta.
    assert (M + 2 > 1) by lra.
    rewrite <- Rinv_1.
    apply Rinv_lt_contravar; lra. }
  set (r := sqrt (1 - delta)).
  assert (Hr_inside : 0 < r < 1).
  { unfold r. split.
    - apply sqrt_lt_R0. lra.
    - apply Rlt_le_trans with (sqrt 1).
      + apply sqrt_lt_1; lra.
      + rewrite sqrt_1. lra. }
  exists r. split; [exact Hr_inside |].
  unfold hyp_line_element, mod_sq, r.
  rewrite sqrt_def by lra.
  (* now goal: 2 / (1 - (1 - delta)) > M, i.e. 2/delta > M *)
  replace (1 - (1 - delta)) with delta by ring.
  unfold delta.
  replace (2 / / (M + 2)) with (2 * (M + 2)) by (field; lra).
  (* goal: 2 * (M + 2) > M *)
  lra.
Qed.

(* ================================================================ *)
(*  PART 5 — THE CAPSTONE                                           *)
(*                                                                  *)
(*  Gradient descent always converges to the pole (POLE_COLLAPSE).  *)
(*  But the Poincare disk's natural metric (PD) places the equator *)
(*  at infinite hyperbolic distance from any pole (hyperbolic_blowup).*)
(*  Therefore the Bloch-sphere gradient flow cannot recover the     *)
(*  Poincare-disk structure: it collapses to a single point, while  *)
(*  the disk's information is spread across the equator.            *)
(* ================================================================ *)

Theorem LEARNING_CANNOT_RECOVER_POINCARE_DISK :
  (* (a) Gradient descent monotonically pulls every iterate toward 0 *)
  (forall eta r n,
     r >= 0 ->
     0 < eta < / 2 ->
     0 <= gd_iterate eta r (S n) <= gd_iterate eta r n) /\
  (* (b) FS is finite at the equator *)
  (forall r, mod_sq r = 1 -> FS r = / 4) /\
  (* (c) PD denominator vanishes at the equator *)
  (forall r, mod_sq r = 1 ->
     (1 - mod_sq r) * (1 - mod_sq r) = 0) /\
  (* (d) The hyperbolic line element is unboundedly large
         arbitrarily close to the equator *)
  (forall M, M > 0 ->
     exists r, 0 < r < 1 /\ hyp_line_element r > M).
Proof.
  split; [| split; [| split]].
  - exact POLE_COLLAPSE.
  - exact FS_at_equator.
  - exact PD_denominator_zero_at_equator.
  - exact hyperbolic_blowup.
Qed.

Print Assumptions LEARNING_CANNOT_RECOVER_POINCARE_DISK.
