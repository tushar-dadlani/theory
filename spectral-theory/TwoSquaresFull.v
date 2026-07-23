(* ================================================================= *)
(*  TwoSquaresFull.v                                                 *)
(*                                                                    *)
(*  THE FULL SUM-OF-TWO-SQUARES CHARACTERISATION (Fermat-Euler):      *)
(*                                                                    *)
(*     for n > 0,  n = a^2 + b^2  <->  every prime q = 3 (mod 4)       *)
(*                                     divides n to an EVEN power.     *)
(*                                                                    *)
(*  This completes the converse thread: SumTwoSquaresConverse gave     *)
(*  the obstruction/descent engine (prime3_descent) and the           *)
(*  sufficiency blocks; here we assemble the global iff by two         *)
(*  strong inductions over Z.lt_wf.                                   *)
(*                                                                    *)
(*  Uses only PER-PRIME facts (Euclid prime_mult, not_div_pow,         *)
(*  cancellation, decomposition-existence padic_val) -- NOT a general  *)
(*  valuation-additivity theorem.  Axiom-free.                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import SumTwoSquares FermatTwoSquares SumTwoSquaresConverse
        ZmodOrder ZmodPStar PrimeFactorizationExists.
Open Scope Z_scope.

(* "every prime q = 3 (mod 4) divides n to an even power" *)
Definition q3even (n : Z) : Prop :=
  forall q, prime (Z.of_nat q) -> (q mod 4 = 3)%nat ->
  forall v (m : Z), n = (Z.of_nat q) ^ (Z.of_nat v) * m -> ~ (Z.of_nat q | m) -> Nat.Even v.

(* ================================================================= *)
(*  §1  small per-prime / arithmetic helpers                         *)
(* ================================================================= *)

Lemma sum2_pow : forall a k, sum2 k -> sum2 (k ^ Z.of_nat a).
Proof.
  intros a k Hk; induction a as [|a IH]; [ rewrite Z.pow_0_r; exact sum2_1 | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by (apply Zle_0_nat); apply sum2_mul; assumption.
Qed.

Lemma prime_ndvd_pow : forall a q b, prime (Z.of_nat q) -> ~ (Z.of_nat q | b) ->
  ~ (Z.of_nat q | b ^ Z.of_nat a).
Proof.
  intros a q b Hq Hb; induction a as [|a IH].
  - rewrite Z.pow_0_r; intro Hd.
    pose proof (prime_ge_2 _ Hq); pose proof (Z.divide_pos_le _ 1 ltac:(lia) Hd); lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by (apply Zle_0_nat); intro Hd.
    destruct (prime_mult _ Hq _ _ Hd); [ apply Hb | apply IH ]; assumption.
Qed.

Lemma distinct_prime_ndvd : forall q r, prime (Z.of_nat q) -> prime (Z.of_nat r) ->
  q <> r -> ~ (Z.of_nat q | Z.of_nat r).
Proof.
  intros q r Hq Hr Hne Hd.
  pose proof (prime_ge_2 _ Hq); pose proof (prime_ge_2 _ Hr).
  destruct (prime_divisors (Z.of_nat r) Hr (Z.of_nat q) Hd) as [E|[E|[E|E]]];
    [ lia | lia | apply Hne; apply Nat2Z.inj; exact E | lia ].
Qed.

Lemma pow_split2 : forall q v, (2 <= v)%nat ->
  (Z.of_nat q) ^ (Z.of_nat v) = (Z.of_nat q * Z.of_nat q) * (Z.of_nat q) ^ (Z.of_nat (v - 2)).
Proof.
  intros q v Hv.
  replace (Z.of_nat v) with (2 + Z.of_nat (v - 2)) by lia.
  rewrite Z.pow_add_r by lia; rewrite Z.pow_2_r; reflexivity.
Qed.

Lemma even_prime_2 : forall q, prime (Z.of_nat q) -> Nat.divide 2 q -> q = 2%nat.
Proof.
  intros q Hq Hd.
  assert (HdZ : (Z.of_nat 2 | Z.of_nat q))
    by (destruct Hd as [k Hk]; exists (Z.of_nat k); rewrite Hk, Nat2Z.inj_mul; reflexivity).
  pose proof (prime_ge_2 _ Hq).
  destruct (prime_divisors (Z.of_nat q) Hq (Z.of_nat 2) HdZ) as [E|[E|[E|E]]]; lia.
Qed.

Lemma prime_mod4 : forall q, prime (Z.of_nat q) ->
  q = 2%nat \/ (q mod 4 = 1)%nat \/ (q mod 4 = 3)%nat.
Proof.
  intros q Hq.
  destruct (Nat.eq_dec q 2) as [->|Hne]; [ left; reflexivity | right ].
  assert (Hnd2 : ~ Nat.divide 2 q) by (intro Hd; apply Hne; exact (even_prime_2 q Hq Hd)).
  pose proof (Nat.div_mod_eq q 4) as Hdm.
  pose proof (Nat.mod_upper_bound q 4 ltac:(lia)) as Hub.
  destruct (Nat.eq_dec (q mod 4) 0) as [E0|E0].
  { exfalso; apply Hnd2; exists (2 * (q / 4))%nat; lia. }
  destruct (Nat.eq_dec (q mod 4) 2) as [E2|E2].
  { exfalso; apply Hnd2; exists (2 * (q / 4) + 1)%nat; lia. }
  lia.
Qed.

Lemma even_shift2 : forall v, (2 <= v)%nat -> Nat.Even (v - 2) -> Nat.Even v.
Proof. intros v Hv [c Hc]; exists (c + 1)%nat; lia. Qed.

(* ================================================================= *)
(*  §2  NECESSITY:  sum2 n -> q3even n                                *)
(* ================================================================= *)

Lemma two_squares_nec : forall n, 0 < n -> sum2 n -> q3even n.
Proof.
  intro n; pattern n; revert n.
  apply (well_founded_induction (Z.lt_wf 0)); intros n IH Hn Hsum q Hq Hmod v m Hdec Hqm.
  destruct (Zdivide_dec (Z.of_nat q) n) as [Hqn | Hqn].
  - (* q | n : descend *)
    destruct (prime3_descent q n Hq Hmod Hn Hqn Hsum) as [Hq2 Hs2].
    pose proof (prime_ge_2 _ Hq) as Hqge.
    assert (Hqq : Z.of_nat q * Z.of_nat q <> 0) by nia.
    assert (Hq0 : Z.of_nat q <> 0) by lia.
    remember (n / (Z.of_nat q * Z.of_nat q)) as n2 eqn:Hn2def.
    destruct Hq2 as [c Hc].
    assert (Hn2c : n2 = c) by (rewrite Hn2def, Hc, Z.div_mul by exact Hqq; reflexivity).
    assert (Hnn2 : n = Z.of_nat q * Z.of_nat q * n2) by (rewrite Hn2c, Hc; ring).
    assert (Hv2 : (2 <= v)%nat).
    { destruct v as [|[|v]]; [ exfalso | exfalso | lia ].
      - rewrite Z.pow_0_r, Z.mul_1_l in Hdec; rewrite Hdec in Hnn2.
        apply Hqm; exists (Z.of_nat q * n2); rewrite Hnn2; ring.
      - rewrite Z.pow_1_r in Hdec.
        apply Hqm; exists n2; apply (Z.mul_reg_l m (n2 * Z.of_nat q) (Z.of_nat q) Hq0).
        rewrite <- Hdec, Hnn2; ring. }
    assert (Hn2eq : n2 = (Z.of_nat q) ^ (Z.of_nat (v - 2)) * m).
    { apply (Z.mul_reg_l n2 ((Z.of_nat q) ^ (Z.of_nat (v - 2)) * m) (Z.of_nat q * Z.of_nat q) Hqq).
      rewrite <- Hnn2, Hdec, (pow_split2 q v Hv2); ring. }
    assert (Hn2pos : 0 < n2) by nia.
    assert (Hn2lt : n2 < n) by nia.
    pose proof (IH n2 ltac:(lia) Hn2pos Hs2) as Hq3n2.
    exact (even_shift2 v Hv2 (Hq3n2 q Hq Hmod (v - 2)%nat m Hn2eq Hqm)).
  - (* ~ q | n : v = 0 *)
    assert (v = 0)%nat.
    { destruct v as [|v]; [ reflexivity | exfalso ].
      apply Hqn; rewrite Hdec, Nat2Z.inj_succ, Z.pow_succ_r by (apply Zle_0_nat).
      exists ((Z.of_nat q) ^ (Z.of_nat v) * m); ring. }
    subst v; exists 0%nat; reflexivity.
Qed.

(* ================================================================= *)
(*  §3  TRANSFER:  q3even (q0^a * m') -> q0 prime, q0 ∤ m' -> q3even m'*)
(* ================================================================= *)

Lemma q3even_transfer : forall q0 a m',
  prime (Z.of_nat q0) -> ~ (Z.of_nat q0 | m') ->
  q3even ((Z.of_nat q0) ^ (Z.of_nat a) * m') -> q3even m'.
Proof.
  intros q0 a m' Hq0 Hnd Hq3 q Hq Hmod v s Hdec Hqs.
  destruct (Nat.eq_dec q q0) as [->|Hne].
  - (* q = q0 : q0 ∤ m' forces v = 0 *)
    assert (v = 0)%nat.
    { destruct v as [|v]; [ reflexivity | exfalso; apply Hnd ].
      rewrite Hdec, Nat2Z.inj_succ, Z.pow_succ_r by (apply Zle_0_nat).
      exists ((Z.of_nat q0) ^ (Z.of_nat v) * s); ring. }
    subst v; exists 0%nat; reflexivity.
  - (* q <> q0 : lift the q-decomposition of m' to one of q0^a*m' *)
    apply (Hq3 q Hq Hmod v ((Z.of_nat q0) ^ (Z.of_nat a) * s)).
    + rewrite Hdec; ring.
    + intro Hd; destruct (prime_mult (Z.of_nat q) Hq _ _ Hd) as [H|H].
      * exact (prime_ndvd_pow a q (Z.of_nat q0) Hq (distinct_prime_ndvd q q0 Hq Hq0 Hne) H).
      * exact (Hqs H).
Qed.

(* ================================================================= *)
(*  §4  SUFFICIENCY:  q3even n -> sum2 n                              *)
(* ================================================================= *)

Lemma two_squares_suf : forall n, 0 < n -> q3even n -> sum2 n.
Proof.
  intro n; pattern n; revert n.
  apply (well_founded_induction (Z.lt_wf 0)); intros n IH Hn Hq3.
  destruct (Z.eq_dec n 1) as [->|Hn1]; [ exact sum2_1 | ].
  assert (H1n : 1 < n) by lia.
  destruct (has_prime_divisor n H1n) as [q0 [Hq0p Hq0n]].
  assert (Hq02 : 2 <= q0) by (apply prime_ge_2; exact Hq0p).
  set (q0n := Z.to_nat q0).
  assert (Hq0eq : Z.of_nat q0n = q0) by (unfold q0n; apply Z2Nat.id; lia).
  assert (Hq0np : prime (Z.of_nat q0n)) by (rewrite Hq0eq; exact Hq0p).
  destruct (padic_val q0 Hq02 n Hn) as [a [m' [Hdec [Hndm Hm'pos]]]].
  assert (Ha1 : (1 <= a)%nat).
  { destruct a as [|a]; [ exfalso | lia ].
    rewrite Z.pow_0_r, Z.mul_1_l in Hdec; rewrite Hdec in Hq0n; exact (Hndm Hq0n). }
  assert (Hpow2 : 2 <= q0 ^ Z.of_nat a).
  { destruct a as [|a']; [ lia | ].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by (apply Zle_0_nat).
    assert (0 < q0 ^ Z.of_nat a') by (apply Z.pow_pos_nonneg; [ lia | apply Zle_0_nat ]); nia. }
  assert (Hm'lt : m' < n) by (rewrite Hdec; nia).
  assert (Hq3m' : q3even m').
  { apply (q3even_transfer q0n a m'); [ exact Hq0np | rewrite Hq0eq; exact Hndm
                                       | rewrite Hq0eq, <- Hdec; exact Hq3 ]. }
  assert (Hm'sum : sum2 m') by (apply (IH m' ltac:(lia) Hm'pos Hq3m')).
  assert (Hpow_sum : sum2 (q0 ^ Z.of_nat a)).
  { destruct (prime_mod4 q0n Hq0np) as [E2 | [E1 | E3]].
    - rewrite <- Hq0eq, E2; apply sum2_pow; exact sum2_2.
    - rewrite <- Hq0eq; apply sum2_pow, sum2_prime1; assumption.
    - assert (Heven : Nat.Even a)
        by (apply (Hq3 q0n Hq0np E3 a m'); [ rewrite Hq0eq; exact Hdec | rewrite Hq0eq; exact Hndm ]).
      destruct Heven as [c Hc].
      replace (Z.of_nat a) with (Z.of_nat c + Z.of_nat c) by lia.
      rewrite Z.pow_add_r by (apply Zle_0_nat); apply sum2_sq. }
  rewrite Hdec; apply sum2_mul; [ exact Hpow_sum | exact Hm'sum ].
Qed.

(* ================================================================= *)
(*  §5  MASTER                                                       *)
(* ================================================================= *)

Theorem two_squares_iff : forall n, 0 < n -> (sum2 n <-> q3even n).
Proof.
  intros n Hn; split; [ apply two_squares_nec; exact Hn | apply two_squares_suf; exact Hn ].
Qed.

Print Assumptions two_squares_iff.

(* ================================================================= *)
(*  END TwoSquaresFull.v                                             *)
(*  The full Fermat-Euler characterisation: for n>0, n is a sum of     *)
(*  two squares iff every prime q = 3 (mod 4) divides n to an even     *)
(*  power.  Both directions by strong induction on Z.lt_wf, on the     *)
(*  descent engine (prime3_descent) + Fermat (sum2_prime1) +           *)
(*  factorisation-existence (padic_val), using only per-prime facts.   *)
(*  Closed under the global context.                                  *)
(* ================================================================= *)
