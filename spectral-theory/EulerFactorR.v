(* ================================================================= *)
(*  EulerFactorR.v                                                    *)
(*                                                                    *)
(*  THE ANALYTIC LAYER (archimedean, over R): the single Euler        *)
(*  factor as a genuine convergent series,                            *)
(*                                                                    *)
(*     sum_{k=0}^infinity  p^{-k s}  =  1 / (1 - p^{-s}).              *)
(*                                                                    *)
(*  This completes PrimonGas.v's FINITE Euler product by taking the    *)
(*  K -> infinity limit of one mode.  Our axiom-free Q result          *)
(*  geom_closed,  (1 - x) * psum x K = 1 - x^K,  is exactly the        *)
(*  finite geometric closed form; over R stdlib already proves it as   *)
(*  `tech3`, and `GP_infinite` supplies the limit  x^K -> 0  for        *)
(*  |x| < 1.  So the bridge is: keep the finite/algebraic identity     *)
(*  (proved axiom-free over Q), then attach the stdlib limit over R.   *)
(*                                                                    *)
(*  NOTE ON AXIOMS: this file is the QUARANTINED analytic layer.  It   *)
(*  uses the classical Reals axioms (as `Print Assumptions` reports),  *)
(*  exactly like LandauerBound.v.  The core Q files (PrimonGas,        *)
(*  LadderOps, FreeDivMeet, ...) remain Closed under the global        *)
(*  context; nothing already built loses its purity.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  THE FINITE GEOMETRIC CLOSED FORM  (= geom_closed, over R)     *)
(* ================================================================= *)

(* The R mirror of PrimonGas.geom_closed:  the (K+1)-term partial sum  *)
(* of the geometric series has the closed form (1 - x^{S N})/(1 - x).  *)
(* stdlib already proves this as `tech3`.                              *)
Lemma psumR_closed : forall x N,
  x <> 1 -> sum_f_R0 (fun k => x ^ k) N = (1 - x ^ (S N)) / (1 - x).
Proof. intros x N Hx; apply tech3; exact Hx. Qed.

(* ================================================================= *)
(*  2.  THE GEOMETRIC LIMIT  (K -> infinity)                          *)
(* ================================================================= *)

(* For |x| < 1 the partial sums converge to 1/(1 - x): the analytic    *)
(* completion of the finite closed form above.  This is stdlib's        *)
(* GP_infinite, with the trivial coefficient 1 stripped off.           *)
Theorem geom_limit : forall x,
  Rabs x < 1 -> infinite_sum (fun k => x ^ k) (/ (1 - x)).
Proof.
  intros x Hx.
  assert (H := GP_infinite x Hx); unfold Pser in H.
  intros eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  rewrite (sum_eq (fun k => x ^ k) (fun m => 1 * x ^ m) n) by (intros i _; ring).
  apply HN; exact Hn.
Qed.

(* ================================================================= *)
(*  3.  THE EULER FACTOR  sum_k (p^{-s})^k = 1/(1 - p^{-s})           *)
(* ================================================================= *)

(* With base p > 1 and exponent s > 0 the fugacity x = p^{-s} lies in   *)
(* (0,1), so the primon-gas single-mode partition function converges    *)
(* to the Euler factor 1/(1 - p^{-s}).  (Here (Rpower p (-s))^k =        *)
(* p^{-k s} is the Boltzmann weight of occupation k at energy log p.)    *)
Theorem euler_factor : forall p s,
  1 < p -> 0 < s ->
  infinite_sum (fun k => (Rpower p (- s)) ^ k) (/ (1 - Rpower p (- s))).
Proof.
  intros p s Hp Hs; apply geom_limit.
  assert (Hpos : 0 < Rpower p (- s)) by (unfold Rpower; apply exp_pos).
  rewrite Rabs_pos_eq by lra.
  unfold Rpower; rewrite <- exp_0; apply exp_increasing.
  assert (Hln : 0 < ln p) by (rewrite <- ln_1; apply ln_increasing; lra).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the analytic Euler factor (uses Reals axioms)    *)
(* ----------------------------------------------------------------- *)

Theorem euler_factor_analytic :
  (* finite closed form (= geom_closed over R) *)
  (forall x N, x <> 1 -> sum_f_R0 (fun k => x ^ k) N = (1 - x ^ (S N)) / (1 - x))
  (* the geometric limit *)
  /\ (forall x, Rabs x < 1 -> infinite_sum (fun k => x ^ k) (/ (1 - x)))
  (* the Euler factor as a convergent series *)
  /\ (forall p s, 1 < p -> 0 < s ->
        infinite_sum (fun k => (Rpower p (- s)) ^ k) (/ (1 - Rpower p (- s)))).
Proof.
  split; [ exact psumR_closed | ].
  split; [ exact geom_limit | exact euler_factor ].
Qed.

Print Assumptions euler_factor_analytic.

(* ================================================================= *)
(*  END EulerFactorR.v                                                *)
(*  The archimedean analytic layer: PrimonGas's finite Euler product   *)
(*  completed to the genuine convergent Euler factor over R.           *)
(*  Uses the classical Reals axioms (quarantined here); the Q core     *)
(*  stays Closed under the global context.                             *)
(* ================================================================= *)
