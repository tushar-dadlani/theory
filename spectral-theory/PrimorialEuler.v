(* ================================================================= *)
(*  PrimorialEuler.v                                                  *)
(*                                                                    *)
(*  RELATIVIZING THE EULER PRODUCT TO PRIMORIALS.                     *)
(*                                                                    *)
(*  The Euler product over ALL primes is intractable as a single       *)
(*  infinite product.  We relativize it to the PRIMORIAL TOWER: for     *)
(*  each n, the FINITE Euler product over the first n primes (the       *)
(*  primes dividing the n-th primorial),                               *)
(*                                                                    *)
(*     EP n = prod_{i<n} 1/(1 - p_i^{-s})   (here s = 2, so p^{-s}=1/p^2)*)
(*                                                                    *)
(*  Each EP n is a genuine finite Euler product (EulerProductR): it is   *)
(*  the K->oo limit of the products of truncated geometric sums, i.e.    *)
(*  the primon-gas partition function RESTRICTED to the first n primes.  *)
(*  The tower is MONOTONE increasing in n (adjoining a prime multiplies  *)
(*  by a factor >= 1), exactly mirroring the primorial primor n growing  *)
(*  by the factor P n.  The full Euler product over all primes is the    *)
(*  LIMIT of this primorial-indexed tower.                             *)
(*                                                                    *)
(*  We fix an abstract prime enumeration P : nat -> R with P i >= 2      *)
(*  (instantiate with the actual primes, e.g. INR o kth_prime, to get    *)
(*  the genuine primorial).  Uses the classical Reals axioms.          *)
(*                                                                    *)
(*  HONEST SCOPE: the tower is built and proved monotone, and each rung  *)
(*  is a finite Euler product / restricted partition function.  Its      *)
(*  CONVERGENCE to zeta(s) (the top of the tower) needs a uniform bound  *)
(*  on the smooth partial sums and remains out of scope (LEDGER.md).     *)
(* ================================================================= *)

Require Import EulerFactorR EulerProductR.
From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Open Scope R_scope.

Lemma fold_mult_app : forall l a,
  fold_right Rmult 1 (l ++ [a]) = fold_right Rmult 1 l * a.
Proof. induction l as [|x l IH]; intro a; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma Zfactor_app : forall xs y, Zfactor (xs ++ [y]) = Zfactor xs * / (1 - y).
Proof. intros xs y; unfold Zfactor; rewrite map_app; cbn [map]; apply fold_mult_app. Qed.

Section PrimEuler.

Variable P : nat -> R.               (* the prime enumeration (P i = i-th prime) *)
Hypothesis HP : forall i, 2 <= P i.  (* each is >= 2 *)

(* fugacity of the i-th prime at s = 2:  p_i^{-2} = 1/p_i^2 *)
Definition fug (i : nat) : R := / (P i) ^ 2.

Lemma fug_pos : forall i, 0 < fug i.
Proof. intro i; unfold fug; apply Rinv_0_lt_compat, pow_lt; pose proof (HP i); lra. Qed.

Lemma fug_lt1 : forall i, fug i < 1.
Proof.
  intro i; unfold fug; pose proof (HP i).
  apply Rle_lt_trans with (/ 4); [ apply Rinv_le_contravar; nra | lra ].
Qed.

(* the first n prime fugacities, and the primorial-relativized Euler product *)
Definition pfugs (n : nat) : list R := map fug (seq 0 n).
Definition EP (n : nat) : R := Zfactor (pfugs n).

(* and the primorial itself: product of the first n primes *)
Definition primor (n : nat) : R := fold_right Rmult 1 (map P (seq 0 n)).

Lemma pfugs_ok : forall n, Forall (fun x => Rabs x < 1) (pfugs n).
Proof.
  intro n; unfold pfugs; apply Forall_forall; intros x Hx.
  apply in_map_iff in Hx; destruct Hx as [i [Heq _]]; subst x.
  rewrite Rabs_pos_eq by (apply Rlt_le, fug_pos); apply fug_lt1.
Qed.

Lemma pfugs_S : forall n, pfugs (S n) = pfugs n ++ [fug n].
Proof.
  intro n; unfold pfugs; rewrite seq_S, map_app; cbn [map];
    rewrite Nat.add_0_l; reflexivity.
Qed.

(* each rung adjoins one prime factor 1/(1 - p_n^{-2}) *)
Lemma EP_rec : forall n, EP (S n) = EP n * / (1 - fug n).
Proof. intro n; unfold EP; rewrite pfugs_S; apply Zfactor_app. Qed.

(* the primorial grows by the factor P n at the same rung *)
Lemma primor_rec : forall n, primor (S n) = primor n * P n.
Proof.
  intro n; unfold primor; rewrite seq_S, map_app; cbn [map];
    rewrite Nat.add_0_l; apply fold_mult_app.
Qed.

Lemma EP_pos : forall n, 0 < EP n.
Proof.
  induction n as [|n IH].
  - unfold EP, pfugs, Zfactor; simpl; lra.
  - rewrite EP_rec; apply Rmult_lt_0_compat;
      [ exact IH | apply Rinv_0_lt_compat; pose proof (fug_lt1 n); lra ].
Qed.

(* each rung is a genuine finite Euler product: the K->oo limit of the *)
(* products of truncated geometric sums over the first n primes *)
Theorem EP_is_limit : forall n, Un_cv (Zpartial (pfugs n)) (EP n).
Proof. intro n; unfold EP; apply euler_product_R, pfugs_ok. Qed.

(* the primorial tower is MONOTONE increasing *)
Theorem EP_monotone : forall n, EP n <= EP (S n).
Proof.
  intro n; rewrite EP_rec.
  pose proof (EP_pos n); pose proof (fug_pos n); pose proof (fug_lt1 n).
  assert (Hge1 : 1 <= / (1 - fug n))
    by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the primorial-relativized Euler product         *)
(* ----------------------------------------------------------------- *)

Theorem primorial_euler :
  (* each rung adjoins the prime factor, mirroring the primorial's growth *)
  (forall n, EP (S n) = EP n * / (1 - fug n))
  /\ (forall n, primor (S n) = primor n * P n)
  (* each rung is a finite Euler product (restricted partition function) *)
  /\ (forall n, Un_cv (Zpartial (pfugs n)) (EP n))
  (* the tower is positive and monotone increasing in n *)
  /\ (forall n, 0 < EP n)
  /\ (forall n, EP n <= EP (S n)).
Proof.
  split; [ exact EP_rec | ].
  split; [ exact primor_rec | ].
  split; [ exact EP_is_limit | ].
  split; [ exact EP_pos | exact EP_monotone ].
Qed.

End PrimEuler.

Print Assumptions primorial_euler.

(* ================================================================= *)
(*  END PrimorialEuler.v                                              *)
(*  The Euler product relativized to the primorial tower: EP n = the   *)
(*  finite Euler product over the first n primes (dividing primor n),   *)
(*  a monotone tower of restricted partition functions whose limit is   *)
(*  the Euler product over all primes.  Uses the classical Reals axioms.*)
(* ================================================================= *)
