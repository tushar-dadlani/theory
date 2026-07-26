(* ================================================================= *)
(*  DirichletPeel.v                                                  *)
(*                                                                    *)
(*  PRIME-POWER PEELING over ℕ, and the induction principle it        *)
(*  supplies for multiplicative-function proofs.                      *)
(*                                                                    *)
(*    nat_ppow_peel : every n ≥ 2 splits as n = p^v · m with p prime, *)
(*                    v ≥ 1, p ∤ m, m ≥ 1, and m < n.                 *)
(*    mult_ind      : to prove P n for all n ≥ 1, handle P 1 and the  *)
(*                    step P m ⟹ P (p^v · m) (p prime, p ∤ m).        *)
(*                                                                    *)
(*  Built by bridging PrimeFactorizationExists.padic_val (over ℤ) to  *)
(*  ℕ via has_prime_divisor.  This is the infrastructure the general   *)
(*  von Mangoldt identity (and any "reduce to prime powers" proof)     *)
(*  needs.  AXIOM-FREE.                                               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Wf_nat.
Require Import PrimeFactorizationExists.
Open Scope Z_scope.

Lemma dvd_nat_Z : forall x y, Nat.divide x y -> (Z.of_nat x | Z.of_nat y).
Proof. intros x y [k Hk]; exists (Z.of_nat k); rewrite Hk, Nat2Z.inj_mul; reflexivity. Qed.

(* ================================================================= *)
(*  Peel the least prime factor:  n = p^v · m,  p ∤ m,  m < n         *)
(* ================================================================= *)
Theorem nat_ppow_peel : forall n, (2 <= n)%nat -> exists p v m,
  prime (Z.of_nat p) /\ (n = p ^ v * m)%nat /\ ~ Nat.divide p m /\
  (1 <= v)%nat /\ (1 <= m)%nat /\ (m < n)%nat.
Proof.
  intros n Hn.
  assert (Hn1 : 1 < Z.of_nat n) by lia.
  destruct (has_prime_divisor (Z.of_nat n) Hn1) as [q [Hq Hqn]].
  pose proof (prime_ge_2 _ Hq) as Hq2.
  assert (Hn0 : 0 < Z.of_nat n) by lia.
  destruct (padic_val q Hq2 (Z.of_nat n) Hn0) as [v [m' [Heq [Hnd Hm'pos]]]].
  set (pn := Z.to_nat q). set (mn := Z.to_nat m').
  assert (Hqp : Z.of_nat pn = q) by (unfold pn; apply Z2Nat.id; lia).
  assert (Hmp : Z.of_nat mn = m') by (unfold mn; apply Z2Nat.id; lia).
  assert (Heqn : (n = pn ^ v * mn)%nat).
  { apply Nat2Z.inj; rewrite Nat2Z.inj_mul, Nat2Z.inj_pow, Hqp, Hmp; exact Heq. }
  assert (Hmn1 : (1 <= mn)%nat)
    by (assert (0 < Z.of_nat mn) by (rewrite Hmp; exact Hm'pos); lia).
  assert (Hv1 : (1 <= v)%nat).
  { destruct (Nat.eq_dec v 0) as [->|Hv]; [ | lia ].
    exfalso; apply Hnd; change (Z.of_nat 0) with 0%Z in Heq;
      rewrite Z.pow_0_r, Z.mul_1_l in Heq; rewrite <- Heq; exact Hqn. }
  assert (Hpn2 : (2 <= pn)%nat) by (assert (2 <= Z.of_nat pn) by (rewrite Hqp; exact Hq2); lia).
  assert (Hpv : (2 <= pn ^ v)%nat).
  { apply Nat.le_trans with (pn ^ 1)%nat;
      [ rewrite Nat.pow_1_r; exact Hpn2 | apply Nat.pow_le_mono_r; lia ]. }
  exists pn, v, mn.
  split; [ rewrite Hqp; exact Hq | ].
  split; [ exact Heqn | ].
  split; [ intro Hd; apply Hnd; rewrite <- Hqp, <- Hmp; apply dvd_nat_Z; exact Hd | ].
  split; [ exact Hv1 | ].
  split; [ exact Hmn1 | ].
  nia.
Qed.

(* ================================================================= *)
(*  Induction principle: reduce any n ≥ 1 to 1 and prime-power steps  *)
(* ================================================================= *)
Theorem mult_ind : forall (P : nat -> Prop),
  P 1%nat ->
  (forall p v m, prime (Z.of_nat p) -> ~ Nat.divide p m ->
     (1 <= v)%nat -> (1 <= m)%nat -> P m -> P (p ^ v * m)%nat) ->
  forall n, (1 <= n)%nat -> P n.
Proof.
  intros P P1 Pstep n; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  destruct (Nat.eq_dec n 1) as [->|Hn1]; [ exact P1 | ].
  destruct (nat_ppow_peel n ltac:(lia)) as [p [v [m [Hp [Heq [Hnd [Hv [Hm Hmn]]]]]]]].
  rewrite Heq; apply (Pstep p v m Hp Hnd Hv Hm); apply IH; [ exact Hmn | exact Hm ].
Qed.

Print Assumptions nat_ppow_peel.
Print Assumptions mult_ind.

(* ================================================================= *)
(*  END DirichletPeel.v                                              *)
(*  Prime-power peeling and the reduce-to-prime-powers induction      *)
(*  principle over ℕ.  Closed under the global context (axiom-free).  *)
(* ================================================================= *)
