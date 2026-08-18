(* ================================================================= *)
(*  SieveDensity.v  —  sieving = the inverse of the Euler product.       *)
(*                                                                    *)
(*  The primorial primorial(k) = prod_{i<k} p_i is the SIEVE MODULUS:     *)
(*  sieving out multiples of the first k primes is periodic with period   *)
(*  primorial(k), and in one period the survivors (coprime to all k       *)
(*  primes) number phi(primorial) = prod(p_i - 1) = denom(k).  Hence the  *)
(*  SIEVE DENSITY (fraction surviving) is                                 *)
(*                                                                    *)
(*    sieve_density k = prod_{i<k}(1 - 1/p_i) = denom k / primorial k     *)
(*                    = phi(primorial)/primorial.                        *)
(*                                                                    *)
(*  Each prime keeps (1 - 1/p) and sieves out 1/p (the n=1 rung of        *)
(*  (1/prime)^inf).  The load-bearing fact tying sieving to the Euler     *)
(*  product zeta = prod_p 1/(1-p^{-s}) is that SIEVING-OUT is the exact    *)
(*  multiplicative INVERSE of the Euler factor's COUNTING-IN:             *)
(*                                                                    *)
(*    sieve_density k . euler_prod k = 1        (prod(1-1/p) . prod 1/(1-1/p) = 1) *)
(*                                                                    *)
(*  i.e. the Euler factor is the "un-sieve"; and prod(1-p^{-s}) = 1/zeta  *)
(*  = Sum mu(n) n^{-s} is the sieve's Mobius inclusion-exclusion.         *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

Section Sieve.
Variable P : nat -> R.                 (* abstract prime enumeration *)
Hypothesis HP : forall i, 2 <= P i.    (* each prime is >= 2 *)

Fixpoint primorial (k : nat) : R :=
  match k with 0 => 1 | S k' => primorial k' * P k' end.           (* sieve modulus *)

Fixpoint denom (k : nat) : R :=
  match k with 0 => 1 | S k' => denom k' * (P k' - 1) end.         (* phi(primorial) = survivors *)

Fixpoint sieve_density (k : nat) : R :=
  match k with 0 => 1 | S k' => sieve_density k' * (1 - / P k') end. (* fraction surviving *)

Fixpoint euler_prod (k : nat) : R :=
  match k with 0 => 1 | S k' => euler_prod k' * (P k' / (P k' - 1)) end. (* count-in (Euler product) *)

Lemma primorial_pos : forall k, 0 < primorial k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rmult_lt_0_compat; [ exact IH | pose proof (HP k); lra ].
Qed.

(* each new prime keeps the fraction (1 - 1/p) and sieves out 1/p *)
Lemma sieve_density_rec : forall k, sieve_density (S k) = sieve_density k * (1 - / P k).
Proof. reflexivity. Qed.

(* the survivor density = phi(primorial)/primorial = denom/primorial *)
Theorem sieve_density_eq : forall k, sieve_density k = denom k / primorial k.
Proof.
  induction k as [| k IH]; [ simpl; field | ].
  cbn [sieve_density denom primorial]. rewrite IH.
  assert (Hp : P k <> 0) by (pose proof (HP k); lra).
  assert (Hpk : 0 < primorial k) by apply primorial_pos.
  field; split; lra.
Qed.

(* THE load-bearing fact: sieving-out is the inverse of counting-in *)
Theorem sieve_counting_inverse : forall k, sieve_density k * euler_prod k = 1.
Proof.
  induction k as [| k IH]; [ simpl; ring | ].
  cbn [sieve_density euler_prod].
  assert (Hk : P k - 1 <> 0) by (pose proof (HP k); lra).
  assert (Hp : P k <> 0) by (pose proof (HP k); lra).
  replace (sieve_density k * (1 - / P k) * (euler_prod k * (P k / (P k - 1))))
    with ((sieve_density k * euler_prod k) * ((1 - / P k) * (P k / (P k - 1))))
    by ring.
  rewrite IH.
  replace ((1 - / P k) * (P k / (P k - 1))) with 1 by (field; split; lra).
  ring.
Qed.

(* ===== the sieve picture, bundled ===== *)
Theorem sieve_picture :
  (forall k, sieve_density (S k) = sieve_density k * (1 - / P k))  (* each prime sieves out 1/p, keeps (1-1/p) *)
  /\ (forall k, sieve_density k = denom k / primorial k)          (* density = phi(primorial)/primorial *)
  /\ (forall k, sieve_density k * euler_prod k = 1).              (* sieving-out = inverse of Euler counting-in *)
Proof.
  split; [ exact sieve_density_rec | ].
  split; [ exact sieve_density_eq | exact sieve_counting_inverse ].
Qed.

End Sieve.

Print Assumptions sieve_density_eq.
Print Assumptions sieve_counting_inverse.
Print Assumptions sieve_picture.
