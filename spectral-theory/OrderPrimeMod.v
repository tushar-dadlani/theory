(* ================================================================= *)
(*  OrderPrimeMod.v                                                  *)
(*                                                                    *)
(*  THE ORDER LEMMA behind primes in arithmetic progressions:        *)
(*                                                                    *)
(*    if a prime q divides a^n - 1 but divides NO a^d - 1 for a       *)
(*    proper divisor d of n, then the multiplicative order of a mod q *)
(*    is exactly n, hence n | q - 1, i.e.  q ≡ 1 (mod n).            *)
(*                                                                    *)
(*  This is the arithmetic core of "infinitely many primes ≡ 1       *)
(*  (mod n)".  Reuses the order machinery (ord, ord_period,          *)
(*  ord_divides, ord_div_pm1).  AXIOM-FREE.                          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import ZmodOrder ZmodPStar LegendreSymbol.
Open Scope nat_scope.

(* q | (x-1)  <->  x ≡ 1 (mod q),  for q >= 2 and x >= 1 *)
Lemma dvd_pred_iff : forall q x, 2 <= q -> 1 <= x ->
  (Nat.divide q (x - 1) <-> x mod q = 1).
Proof.
  intros q x Hq Hx; split.
  - intros [c Hc].
    replace x with (1 + c * q) by lia.
    rewrite Nat.Div0.mod_add, (Nat.mod_small 1 q) by lia; reflexivity.
  - intro Hm; exists (x / q).
    pose proof (Nat.div_mod_eq x q); lia.
Qed.

(* pw q (a mod q) k = a^k mod q  (the residue power is base-invariant) *)
Lemma pw_a_pow : forall q a k, pw q (a mod q) k = a ^ k mod q.
Proof. intros q a k; unfold pw; apply pow_mod_base. Qed.

(* ================================================================= *)
(*  THE ORDER LEMMA                                                 *)
(* ================================================================= *)

Theorem order_prime_mod : forall q a n,
  prime (Z.of_nat q) -> ~ Nat.divide q a -> 1 <= n ->
  Nat.divide q (a ^ n - 1) ->
  (forall d, Nat.divide d n -> d < n -> ~ Nat.divide q (a ^ d - 1)) ->
  Nat.divide n (q - 1).
Proof.
  intros q a n Hq Hnd Hn Hdvd Hprim.
  assert (Hq2 : 2 <= q) by (pose proof (prime_ge_2 _ Hq); lia).
  assert (Ha1 : 1 <= a)
    by (destruct (Nat.eq_dec a 0) as [->|Hne]; [ exfalso; apply Hnd; exists 0; reflexivity | lia ]).
  assert (Hage : forall k, 1 <= a ^ k)
    by (intro k; rewrite <- (Nat.pow_1_l k); apply Nat.pow_le_mono_l; exact Ha1).
  set (r := a mod q).
  assert (Hr : 1 <= r <= q - 1).
  { unfold r; pose proof (Nat.mod_upper_bound a q ltac:(lia)).
    assert (a mod q <> 0) by (intro E; apply Hnd, Nat.Lcm0.mod_divide; exact E); lia. }
  (* q | a^n - 1  =>  pw q r n = 1 *)
  assert (HpwN : pw q r n = 1).
  { unfold r; rewrite pw_a_pow; apply (dvd_pred_iff q (a ^ n) Hq2 (Hage n)); exact Hdvd. }
  (* the order divides n, and is exactly n (no proper divisor works) *)
  assert (Hordn : Nat.divide (ord q r) n) by (apply ord_divides; assumption).
  assert (Hordeq : ord q r = n).
  { destruct (Nat.lt_ge_cases (ord q r) n) as [Hlt | Hge].
    - exfalso.
      apply (Hprim (ord q r) Hordn Hlt).
      apply (dvd_pred_iff q (a ^ (ord q r)) Hq2 (Hage _)).
      unfold r; rewrite <- pw_a_pow; apply ord_period; assumption.
    - pose proof (Nat.divide_pos_le (ord q r) n ltac:(lia) Hordn); lia. }
  rewrite <- Hordeq; apply ord_div_pm1; assumption.
Qed.

Print Assumptions order_prime_mod.

(* ================================================================= *)
(*  END OrderPrimeMod.v                                              *)
(*  If prime q | a^n-1 but q ∤ a^d-1 for every proper divisor d of n, *)
(*  then ord_q(a) = n, so n | q-1, i.e. q ≡ 1 (mod n).  Closed under  *)
(*  the global context (axiom-free).                                 *)
(* ================================================================= *)
