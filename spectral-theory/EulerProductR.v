(* ================================================================= *)
(*  EulerProductR.v                                                   *)
(*                                                                    *)
(*  GAP-FILL: the FINITE EULER PRODUCT over R -- lifting EulerFactorR   *)
(*  from a single prime factor to a product over any finite set of      *)
(*  primes, as an identity of convergent series.                       *)
(*                                                                    *)
(*  For a finite list of fugacities xs (each |x| < 1), the product of    *)
(*  the truncated geometric partial sums converges to the product of    *)
(*  the Euler factors:                                                 *)
(*                                                                    *)
(*     prod_{x in xs} ( sum_{k<=N} x^k )  -->  prod_{x in xs} 1/(1-x)   *)
(*                                                                    *)
(*  i.e. the FINITE Euler product  prod_p (1 - p^{-s})^{-1}  as N -> oo. *)
(*  Proof: each factor converges (EulerFactorR.geom_limit) and a finite  *)
(*  product of convergent sequences converges to the product of the     *)
(*  limits (stdlib CV_mult), by induction on the list.                 *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, like EulerFactorR).   *)
(*  Still per-FINITE-set of primes; the full infinite product / zeta     *)
(*  remains out of scope (see LEDGER.md).                              *)
(* ================================================================= *)

Require Import EulerFactorR.
From Stdlib Require Import Reals Lra List.
Import ListNotations.
Open Scope R_scope.

(* the product over xs of the N-th geometric partial sums *)
Definition Zpartial (xs : list R) (N : nat) : R :=
  fold_right Rmult 1 (map (fun x => sum_f_R0 (fun k => x ^ k) N) xs).

(* the product over xs of the Euler factors 1/(1-x) *)
Definition Zfactor (xs : list R) : R :=
  fold_right Rmult 1 (map (fun x => / (1 - x)) xs).

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists O; intros n _; unfold R_dist.
  replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

(* the finite Euler product converges to the product of Euler factors *)
Theorem euler_product_R : forall xs,
  Forall (fun x => Rabs x < 1) xs ->
  Un_cv (Zpartial xs) (Zfactor xs).
Proof.
  induction xs as [|x xs IH]; intro Hall.
  - unfold Zpartial, Zfactor; simpl; apply Un_cv_const.
  - pose proof (Forall_inv Hall) as Hx.
    pose proof (Forall_inv_tail Hall) as Hxs.
    unfold Zpartial, Zfactor; simpl.
    apply CV_mult.
    + exact (geom_limit x Hx).
    + apply IH; exact Hxs.
Qed.

Print Assumptions euler_product_R.

(* ================================================================= *)
(*  END EulerProductR.v                                               *)
(*  The finite Euler product over R: a product over any finite prime    *)
(*  set of geometric partial sums converges to the product of Euler      *)
(*  factors.  Uses the classical Reals axioms (quarantined).           *)
(* ================================================================= *)
