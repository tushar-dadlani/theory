(* ================================================================= *)
(*  EuclidPrimes.v                                                   *)
(*                                                                    *)
(*  EUCLID'S THEOREM: there are infinitely many primes.              *)
(*                                                                    *)
(*      for every m, there is a prime p with m < p.                  *)
(*                                                                    *)
(*  Proof: m! + 1 has a prime divisor p (has_prime_divisor); if       *)
(*  p <= m then p | m!, so p | 1, absurd.  Hence p > m.  This is the  *)
(*  foundation for the arithmetic-progression results.  AXIOM-FREE.  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Factorial.
Require Import PrimeFactorizationExists.
Open Scope nat_scope.

(* every k in [1,n] divides n! *)
Lemma divide_fact : forall n k, 1 <= k <= n -> Nat.divide k (fact n).
Proof.
  induction n as [|n IH]; intros k Hk; [ lia | ].
  cbn [fact].
  destruct (Nat.eq_dec k (S n)) as [->|Hne].
  - exists (fact n); ring.
  - apply Nat.divide_mul_r; apply IH; lia.
Qed.

(* nat / Z divisibility bridge *)
Lemma Zdiv_nat : forall a b, (Z.of_nat a | Z.of_nat b) -> Nat.divide a b.
Proof.
  intros a b H; destruct (Nat.eq_dec a 0) as [->|Ha].
  - destruct H as [z Hz]; simpl in Hz; rewrite Z.mul_0_r in Hz.
    assert (b = 0)%nat by lia; subst; exists 0%nat; reflexivity.
  - apply Nat.Lcm0.mod_divide.
    assert (H0 : (Z.of_nat a <> 0)%Z) by lia.
    pose proof (proj2 (Z.mod_divide (Z.of_nat b) (Z.of_nat a) H0) H) as Hm.
    rewrite <- Nat2Z.inj_mod in Hm; lia.
Qed.

(* a nat prime divisor of any n >= 2 *)
Lemma nat_prime_divisor : forall n, 2 <= n ->
  exists p, prime (Z.of_nat p) /\ Nat.divide p n.
Proof.
  intros n Hn.
  destruct (has_prime_divisor (Z.of_nat n) ltac:(lia)) as [q [Hq Hqn]].
  pose proof (prime_ge_2 _ Hq).
  exists (Z.to_nat q); split.
  - rewrite Z2Nat.id by lia; exact Hq.
  - apply Zdiv_nat; rewrite Z2Nat.id by lia; exact Hqn.
Qed.

(* ================================================================= *)
(*  EUCLID: infinitely many primes                                  *)
(* ================================================================= *)

Theorem euclid_primes : forall m, exists p, prime (Z.of_nat p) /\ m < p.
Proof.
  intro m.
  assert (Hfge : 1 <= fact m) by (pose proof (lt_O_fact m); lia).
  destruct (nat_prime_divisor (fact m + 1) ltac:(lia)) as [p [Hp Hpd]].
  pose proof (prime_ge_2 _ Hp) as Hp2.
  exists p; split; [ exact Hp | ].
  destruct (Nat.le_gt_cases p m) as [Hle | Hgt]; [ exfalso | exact Hgt ].
  (* p <= m : then p | m!, and p | m!+1, so p | 1 *)
  assert (Hpf : Nat.divide p (fact m)) by (apply divide_fact; lia).
  assert (Hp1 : Nat.divide p 1).
  { replace 1 with (fact m + 1 - fact m) by lia.
    apply Nat.divide_sub_r; assumption. }
  apply Nat.divide_1_r in Hp1; lia.
Qed.

Print Assumptions euclid_primes.

(* ================================================================= *)
(*  END EuclidPrimes.v                                              *)
(*  Euclid's theorem: for every m there is a prime p > m, via a       *)
(*  prime divisor of m! + 1.  Closed under the global context        *)
(*  (axiom-free).                                                    *)
(* ================================================================= *)
