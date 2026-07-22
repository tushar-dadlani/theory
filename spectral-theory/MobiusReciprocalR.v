(* ================================================================= *)
(*  MobiusReciprocalR.v                                               *)
(*                                                                    *)
(*  The analytic reciprocal (archimedean, over R): the Mobius series   *)
(*  (1 - x) is the exact multiplicative INVERSE of the Euler factor     *)
(*  1/(1 - x), so  zeta * mu = delta  per mode, analytically.          *)
(*                                                                    *)
(*  MobiusReciprocal.v proved (over Q) that mumode = 1 - x is the       *)
(*  per-mode Mobius series and that mumode * psum = 1 - x^K.            *)
(*  EulerFactorR.geom_limit proved that the zeta series converges,      *)
(*  sum_k x^k -> 1/(1-x).  Here the two meet: (1 - x) * (1/(1-x)) = 1,  *)
(*  so the Mobius factor inverts the Euler factor exactly -- the        *)
(*  analytic Dirichlet-convolution identity zeta * mu = delta.          *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, like EulerFactorR.v);*)
(*  the Q core stays Closed under the global context.                  *)
(* ================================================================= *)

Require Import EulerFactorR.
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the Mobius factor (1 - x) is the multiplicative inverse of the       *)
(* Euler factor 1/(1 - x) *)
Theorem mu_inverse : forall x, x <> 1 -> (1 - x) * (/ (1 - x)) = 1.
Proof.
  intros x Hx; apply Rinv_r; intro H; apply Hx; lra.
Qed.

(* the analytic Mobius inversion zeta * mu = delta per mode:            *)
(* the zeta series converges to 1/(1-x), and the Mobius factor (1-x)    *)
(* is its exact reciprocal.                                            *)
Theorem mobius_zeta_delta : forall x, Rabs x < 1 ->
  infinite_sum (fun k => x ^ k) (/ (1 - x))
  /\ (1 - x) * (/ (1 - x)) = 1.
Proof.
  intros x Hx; split.
  - apply geom_limit; exact Hx.
  - apply mu_inverse; intro H; subst x; rewrite Rabs_R1 in Hx; lra.
Qed.

Print Assumptions mobius_zeta_delta.

(* ================================================================= *)
(*  END MobiusReciprocalR.v                                           *)
(*  The Mobius factor (1-x) inverts the Euler factor 1/(1-x): the       *)
(*  analytic zeta * mu = delta per mode.  Uses the classical Reals      *)
(*  axioms (quarantined); the Q core stays Closed under the global      *)
(*  context.                                                           *)
(* ================================================================= *)
