(* ================================================================= *)
(*  TGrowthBound.v  —  Hadamard Stage A (part 2): the T(sigma) estimate. *)
(*                                                                    *)
(*  The order-1 growth of XiC reduces (via XiGrowthBound.TC_mod_le) to  *)
(*  bounding the real Mellin tail  T(sigma) = int_1^inf u^{sigma/2-1}    *)
(*  Psi(u) du  by exp(O(sigma ln sigma)).  Core inequality (this part):  *)
(*                                                                    *)
(*    pow_exp_max : u^m . e^{-a u} <= (m/a)^m . e^{-m}   (u,m,a > 0)     *)
(*                                                                    *)
(*  the maximum of u^m e^{-a u}, from ln t <= t-1 (itself exp_ineq1_le). *)
(*  With a = pi/2 this gives u^{sigma/2-1} e^{-pi u} <= B . e^{-pi u/2},  *)
(*  B = (2m/pi)^m e^{-m} = exp(O(sigma ln sigma)); integrating the       *)
(*  residual e^{-pi u/2} yields the T(sigma) bound (next).              *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ThetaTailBounds.
Open Scope R_scope.

(* ln t <= t - 1  (t > 0), i.e. the tangent-line bound, from 1+s <= exp s *)
Lemma ln_le_sub1 : forall t, 0 < t -> ln t <= t - 1.
Proof.
  intros t Ht.
  assert (Ht' : t <= exp (t - 1)) by (pose proof (exp_ineq1_le (t - 1)); lra).
  apply Rle_trans with (ln (exp (t - 1))); [ | rewrite ln_exp; lra ].
  destruct Ht' as [Hlt | Heq].
  - left; apply ln_increasing; [ exact Ht | exact Hlt ].
  - rewrite <- Heq; apply Rle_refl.
Qed.

(* the maximum of u^m e^{-a u} over u>0 is at u=m/a, value (m/a)^m e^{-m} *)
Lemma pow_exp_max : forall a m u, 0 < a -> 0 < m -> 0 < u ->
  Rpower u m * exp (- (a * u)) <= Rpower (m / a) m * exp (- m).
Proof.
  intros a m u Ha Hm Hu.
  assert (Hma : 0 < m / a) by (apply Rdiv_lt_0_compat; lra).
  unfold Rpower. rewrite <- !exp_plus. apply exp_le_mono.
  set (t := a * u / m).
  assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; [ nra | exact Hm ]).
  pose proof (ln_le_sub1 t Ht) as Hln.
  assert (Hu_eq : u = t * (m / a)) by (unfold t; field; lra).
  assert (Hlnu : ln u = ln t + ln (m / a))
    by (rewrite Hu_eq, ln_mult; [ reflexivity | exact Ht | exact Hma ]).
  assert (Hau : a * u = t * m) by (unfold t; field; lra).
  rewrite Hlnu, Hau. nra.
Qed.

Print Assumptions pow_exp_max.
