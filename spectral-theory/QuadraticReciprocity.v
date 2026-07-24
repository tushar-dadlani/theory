(* ================================================================= *)
(*  QuadraticReciprocity.v                                           *)
(*                                                                    *)
(*  THE LAW OF QUADRATIC RECIPROCITY:  for distinct odd primes p, q,  *)
(*                                                                    *)
(*      (q/p) * (p/q) = (-1)^( ((p-1)/2) * ((q-1)/2) ).              *)
(*                                                                    *)
(*  Assembled from Eisenstein's refinement (a/p) = (-1)^(sum          *)
(*  floor(k*a/p)) applied in both directions, and the lattice-point   *)
(*  count sum floor(k*q/p) + sum floor(k*p/q) = ((p-1)/2)((q-1)/2).   *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Require Import LegendreSymbol EisensteinLemma ReciprocityCount.
Open Scope nat_scope.

(* distinct primes do not divide each other *)
Lemma distinct_primes_ndvd : forall p q,
  prime (Z.of_nat p) -> prime (Z.of_nat q) -> p <> q -> ~ Nat.divide p q.
Proof.
  intros p q Hp Hq Hpq Hd.
  pose proof (prime_ge_2 _ Hp); pose proof (prime_ge_2 _ Hq).
  apply Hpq; apply Nat2Z.inj.
  assert (Hdz : (Z.of_nat p | Z.of_nat q))
    by (destruct Hd as [c Hc]; exists (Z.of_nat c); rewrite Hc, Nat2Z.inj_mul; ring).
  destruct (prime_divisors (Z.of_nat q) Hq (Z.of_nat p) Hdz) as [E|[E|[E|E]]]; lia.
Qed.

(* ================================================================= *)
(*  THE MAIN THEOREM                                                 *)
(* ================================================================= *)

Theorem quadratic_reciprocity : forall p q,
  prime (Z.of_nat p) -> prime (Z.of_nat q) -> p <> q ->
  p mod 2 = 1 -> q mod 2 = 1 ->
  (legendre p q * legendre q p)%Z = ((-1) ^ Z.of_nat (hlf p * hlf q))%Z.
Proof.
  intros p q Hp Hq Hpq Hpo Hqo.
  assert (Hnpq : ~ Nat.divide p q) by (apply distinct_primes_ndvd; assumption).
  assert (Hnqp : ~ Nat.divide q p)
    by (apply distinct_primes_ndvd; [ exact Hq | exact Hp | intro E; apply Hpq; symmetry; exact E ]).
  rewrite (legendre_eisenstein p q Hp Hpo Hnpq Hqo).
  rewrite (legendre_eisenstein q p Hq Hqo Hnqp Hpo).
  (* Tsum p q = fsum p q  (definitionally) *)
  change (Tsum p q) with (fsum p q); change (Tsum q p) with (fsum q p).
  rewrite <- Z.pow_add_r by lia.
  rewrite <- Nat2Z.inj_add, (reciprocity_count p q Hp Hq Hpq Hpo Hqo).
  reflexivity.
Qed.

Print Assumptions quadratic_reciprocity.

(* ================================================================= *)
(*  END QuadraticReciprocity.v                                       *)
(*  (q/p)*(p/q) = (-1)^(((p-1)/2)((q-1)/2)) for distinct odd primes,  *)
(*  from Eisenstein's refinement + the lattice-point count.          *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
