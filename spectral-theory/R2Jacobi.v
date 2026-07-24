(* ================================================================= *)
(*  R2Jacobi.v                                                       *)
(*                                                                    *)
(*  JACOBI'S TWO-SQUARE FORMULA, in full:                            *)
(*                                                                    *)
(*      r2(n) = 4 * (d1(n) - d3(n)) = 4 * sum_{d|n} chi4(d),  n >= 1. *)
(*                                                                    *)
(*  The multiplicative-agreement assembly.  Both r2/4 and S =         *)
(*  sum chi4 are multiplicative on coprimes (r2_mult, S_mult) with    *)
(*  MATCHING prime-power values (r2_ppow_eq_4S: r2(p^k) = 4*S(p^k)).  *)
(*  Two such functions agreeing on prime powers agree everywhere, by  *)
(*  strong induction peeling one prime power p^v || n (nat_padic):    *)
(*      4*r2(n) = r2(p^v)*r2(m') = 16*S(p^v)*S(m') = 16*S(n),         *)
(*  so r2(n) = 4*S(n).  AXIOM-FREE.                                   *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Wf_nat.
Require Import JacobiRHS R2Multiplicative R2PrimePower R2PrimePowerSplit R2Count
        GaussianCoprime PrimeFactorizationExists TwoSquaresFull.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  a nat prime divisor and prime-power peeling                  *)
(* ================================================================= *)

Lemma gcd_1_l : forall m, Nat.gcd 1 m = 1%nat.
Proof. intro m; apply Nat.divide_1_r, Nat.gcd_divide_l. Qed.

Lemma coprime_mul_l : forall a b m,
  Nat.gcd a m = 1%nat -> Nat.gcd b m = 1%nat -> Nat.gcd (a * b) m = 1%nat.
Proof.
  intros a b m Ha Hb.
  destruct (Nat.eq_dec (Nat.gcd (a * b) m) 1) as [E | E]; [ exact E | exfalso ].
  set (g := Nat.gcd (a * b) m).
  assert (Hgm : Nat.divide g m) by apply Nat.gcd_divide_r.
  assert (Hgab : Nat.divide g (a * b)) by apply Nat.gcd_divide_l.
  assert (Hga : Nat.gcd g a = 1%nat).
  { apply Nat.divide_1_r; rewrite <- Ha; apply Nat.gcd_greatest;
      [ apply Nat.gcd_divide_r
      | apply (Nat.divide_trans _ g); [ apply Nat.gcd_divide_l | exact Hgm ] ]. }
  assert (Hgb : Nat.divide g b) by (apply (Nat.gauss g a b); [ exact Hgab | exact Hga ]).
  apply E, Nat.divide_1_r; rewrite <- Hb; apply Nat.gcd_greatest; [ exact Hgb | exact Hgm ].
Qed.

Lemma gcd_pow_coprime : forall v p m, Nat.gcd p m = 1%nat -> Nat.gcd (p ^ v) m = 1%nat.
Proof.
  induction v as [|v IH]; intros p m Hpm;
    [ apply gcd_1_l | simpl; apply coprime_mul_l; [ exact Hpm | apply IH; exact Hpm ] ].
Qed.

Lemma nat_prime_divisor : forall n, (2 <= n)%nat ->
  exists p, prime (Z.of_nat p) /\ Nat.divide p n.
Proof.
  intros n Hn.
  destruct (has_prime_divisor (Z.of_nat n) ltac:(lia)) as [q [Hq Hqn]].
  pose proof (prime_ge_2 _ Hq).
  exists (Z.to_nat q); split.
  - rewrite Z2Nat.id by lia; exact Hq.
  - apply Zdiv_nat; rewrite Z2Nat.id by lia; exact Hqn.
Qed.

Lemma nat_padic : forall p, prime (Z.of_nat p) -> forall n, (1 <= n)%nat ->
  exists v m', n = (p ^ v * m')%nat /\ ~ Nat.divide p m' /\ (1 <= m')%nat.
Proof.
  intros p Hp; assert (Hp2 : (2 <= p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
  intro n; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  destruct (Nat.eq_dec (n mod p) 0) as [Hdiv | Hndiv].
  - assert (Hpn : Nat.divide p n) by (apply Nat.Lcm0.mod_divide; exact Hdiv).
    destruct Hpn as [n1 Hn1].
    assert (Hn1pos : (1 <= n1)%nat) by nia.
    assert (Hn1lt : (n1 < n)%nat) by nia.
    destruct (IH n1 Hn1lt Hn1pos) as [v [m' [Hdec [Hpm Hm'1]]]].
    exists (S v), m'; repeat split; [ | exact Hpm | exact Hm'1 ].
    rewrite Hn1, Hdec; simpl; ring.
  - exists 0%nat, n; repeat split; [ simpl; lia | | exact Hn ].
    intro Hpn; apply Hndiv, Nat.Lcm0.mod_divide; exact Hpn.
Qed.

(* ================================================================= *)
(*  §2  r2 and 4*S agree on prime powers                            *)
(* ================================================================= *)

Lemma r2_ppow_eq_4S : forall p k, prime (Z.of_nat p) ->
  Z.of_nat (r2 ((Z.of_nat p) ^ (Z.of_nat k))) = 4 * Sfun (p ^ k).
Proof.
  intros p k Hp; destruct (prime_mod4 p Hp) as [Hp2 | [Hp1 | Hp3]].
  - subst p; rewrite S_prime_pow_2.
    replace (Z.of_nat 2) with 2 by reflexivity.
    rewrite r2_2pow; reflexivity.
  - rewrite (r2_1pow p k Hp Hp1), (S_prime_pow_1 p k Hp Hp1); lia.
  - rewrite (r2_3pow p k Hp Hp3), (S_prime_pow_3 p k Hp Hp3).
    destruct (Nat.even k); reflexivity.
Qed.

(* ================================================================= *)
(*  §3  the assembly:  r2(n) = 4*S(n)  for n >= 1                    *)
(* ================================================================= *)

Lemma jacobi_full : forall n, (1 <= n)%nat ->
  Z.of_nat (r2 (Z.of_nat n)) = 4 * Sfun n.
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  destruct (Nat.eq_dec n 1) as [-> | Hn1].
  - vm_compute; reflexivity.
  - assert (Hn2 : (2 <= n)%nat) by lia.
    destruct (nat_prime_divisor n Hn2) as [p [Hp Hpn]].
    destruct (nat_padic p Hp n ltac:(lia)) as [v [m' [Hdec [Hpm Hm'1]]]].
    (* v >= 1, else p would not divide n *)
    assert (Hv1 : (1 <= v)%nat).
    { destruct v as [|v]; [ | lia ].
      exfalso; apply Hpm; rewrite Nat.pow_0_r, Nat.mul_1_l in Hdec; rewrite <- Hdec; exact Hpn. }
    (* gcd(p, m') = 1 : divisor of prime p is 1 or p, and p does not divide m' *)
    assert (Hpm'1 : Nat.gcd p m' = 1%nat).
    { pose proof (Nat.gcd_divide_l p m') as Hgp; pose proof (Nat.gcd_divide_r p m') as Hgm.
      destruct (nat_prime_divisors p (Nat.gcd p m') Hp Hgp) as [E | E];
        [ exact E | exfalso; apply Hpm; rewrite <- E; exact Hgm ]. }
    assert (Hcop : Nat.gcd (p ^ v) m' = 1%nat) by (apply gcd_pow_coprime; exact Hpm'1).
    assert (Hpv2 : (2 <= p ^ v)%nat).
    { assert (Hp2 : (1 < p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
      pose proof (Nat.pow_gt_1 p v Hp2 ltac:(lia)); lia. }
    assert (Hm'lt : (m' < n)%nat) by nia.
    (* the three ingredients *)
    pose proof (r2_mult (p ^ v) m' Hcop ltac:(nia) Hm'1) as Hmul.
    assert (HA : Z.of_nat (r2 (Z.of_nat (p ^ v))) = 4 * Sfun (p ^ v)).
    { rewrite Nat2Z.inj_pow; apply r2_ppow_eq_4S; exact Hp. }
    assert (HB : Z.of_nat (r2 (Z.of_nat m')) = 4 * Sfun m') by (apply IH; [ lia | exact Hm'1 ]).
    assert (HS : Sfun n = Sfun (p ^ v) * Sfun m').
    { rewrite Hdec; apply S_mult; [ exact Hcop | nia | exact Hm'1 ]. }
    (* convert r2_mult to Z and combine *)
    assert (Hnat : (r2 (Z.of_nat (p ^ v)) * r2 (Z.of_nat m') = 4 * r2 (Z.of_nat n))%nat).
    { rewrite Hmul; f_equal; f_equal.
      rewrite <- Nat2Z.inj_mul; f_equal; symmetry; exact Hdec. }
    assert (HmulZ : Z.of_nat (r2 (Z.of_nat (p ^ v))) * Z.of_nat (r2 (Z.of_nat m'))
                    = 4 * Z.of_nat (r2 (Z.of_nat n))).
    { rewrite <- Nat2Z.inj_mul, Hnat, Nat2Z.inj_mul; reflexivity. }
    rewrite HA, HB in HmulZ; rewrite HS; nia.
Qed.

(* ================================================================= *)
(*  §4  MASTER: Jacobi's two-square formula                         *)
(* ================================================================= *)

Theorem jacobi_two_squares : forall n, (1 <= n)%nat ->
  Z.of_nat (r2 (Z.of_nat n)) = 4 * (Z.of_nat (d1 n) - Z.of_nat (d3 n)).
Proof. intros n Hn; rewrite (jacobi_full n Hn), S_as_d1d3; reflexivity. Qed.

Print Assumptions jacobi_two_squares.

(* ================================================================= *)
(*  END R2Jacobi.v                                                   *)
(*  Jacobi's formula r2(n) = 4*(d1(n) - d3(n)) for n >= 1, assembled  *)
(*  from the two multiplicativities (r2_mult, S_mult) + matching      *)
(*  prime-power values (r2_ppow_eq_4S) by prime-power peeling.        *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
