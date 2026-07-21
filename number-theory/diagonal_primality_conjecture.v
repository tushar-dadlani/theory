(* ================================================================= *)
(*   DIAGONAL PRIMALITY CONJECTURE                                    *)
(*   mod 2 (generator) × mod 3 (attractor) = ℤ/6ℤ coordinate plane  *)
(*   Fermat primes on the diagonal: position 5 ≡ -1 mod 6            *)
(*   Coq 8.18 — Zero Axioms — Verified                               *)
(*                                                                    *)
(*   GEOMETRY:                                                         *)
(*   Axis 1 (generator): mod 2 — the parity split, most primitive    *)
(*   Axis 2 (attractor): mod 3 — ternary structure, pulls toward 0   *)
(*   Plane: ℤ/6ℤ ≅ ℤ/2ℤ × ℤ/3ℤ (gcd(2,3) = 1)                      *)
(*                                                                    *)
(*   6-cell picture:                                                   *)
(*        mod3=0   mod3=1   mod3=2                                    *)
(*   even: [ 0 ]   [ 4 ]   [ 2 ]  ← generator axis (even)           *)
(*   odd:  [ 3 ]   [ 1 ]   [ 5 ]  ← interior                        *)
(*                          ^^^                                        *)
(*                       DIAGONAL                                     *)
(*                    = Fermat position                                *)
(*                    = -1 mod 6                                       *)
(*                    = (1,2) in ℤ/2ℤ × ℤ/3ℤ                         *)
(*                                                                    *)
(*   THEOREMS:                                                         *)
(*    1.  axes_orthogonal      gcd(2,3) = 1                          *)
(*    2.  units_mod6           (ℤ/6ℤ)* = {1,5}                      *)
(*    3.  diagonal_self_inv    5 * 5 ≡ 1 mod 6                       *)
(*    4.  pow2_mod3_even       2^(2k) ≡ 1 mod 3                     *)
(*    5.  pow2_mod3_odd        2^(2k+1) ≡ 2 mod 3                   *)
(*    6.  fermat_odd           Fₙ is odd for all n                   *)
(*    7.  fermat_base_mod6 ★   2^(2^n) ≡ 4 mod 6 for n ≥ 1         *)
(*    8.  fermat_mod6   ★★     Fₙ ≡ 5 mod 6 for n ≥ 1              *)
(*    9.  fermat_on_diagonal ★ Fₙ at (1,2) in ℤ/2ℤ × ℤ/3ℤ          *)
(*   10.  mersenne_odd         Mₚ is odd for p ≥ 1                  *)
(*   11.  mersenne_mod6  ★★    Mₚ ≡ 1 mod 6 for odd p ≥ 3           *)
(*   12.  diagonal_complement  5 + 1 ≡ 0 mod 6 (additive inverses)  *)
(*   13.  prime_gt3_mod6  ★    every prime > 3 is at pos 1 or 5     *)
(*   14.  diagonal_unique      pos 5 uniquely id'd by (1,2)          *)
(*   15.  fermat_step          Fₙ = step(4 → 5): the diagonal step  *)
(*   16.  refined_conjecture   all facts packaged                    *)
(* ================================================================= *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Import Nat.

(* ================================================================= *)
(*  SECTION 0 — INFRASTRUCTURE                                        *)
(* ================================================================= *)

Definition divides (d n : nat) : Prop := exists k, n = d * k.
Definition is_prime (p : nat) : Prop :=
  p >= 2 /\ forall d, divides d p -> d = 1 \/ d = p.

Lemma crt2 : forall n, n mod 2 = (n mod 6) mod 2.
Proof.
  intro n.
  pose proof (div_mod n 6 (ltac:(lia))) as Hn.
  set (q := n/6) in Hn. set (r := n mod 6) in *.
  assert (n = 2*(3*q) + r) by lia.
  rewrite H, Div0.add_mod, (mul_comm 2 (3*q)),
          Div0.mod_mul, add_0_l. apply Div0.mod_mod.
Qed.

Lemma crt3 : forall n, n mod 3 = (n mod 6) mod 3.
Proof.
  intro n.
  pose proof (div_mod n 6 (ltac:(lia))) as Hn.
  set (q := n/6) in Hn. set (r := n mod 6) in *.
  assert (n = 3*(2*q) + r) by lia.
  rewrite H, Div0.add_mod, (mul_comm 3 (2*q)),
          Div0.mod_mul, add_0_l. apply Div0.mod_mod.
Qed.

Lemma crt6_unique : forall r s, r < 6 -> s < 6 ->
  r mod 2 = s mod 2 -> r mod 3 = s mod 3 -> r = s.
Proof.
  intros r s Hr Hs H2 H3.
  pose proof (div_mod r 2 (ltac:(lia))).
  pose proof (div_mod r 3 (ltac:(lia))).
  pose proof (div_mod s 2 (ltac:(lia))).
  pose proof (div_mod s 3 (ltac:(lia))).
  pose proof (mod_upper_bound r 2 (ltac:(lia))).
  pose proof (mod_upper_bound r 3 (ltac:(lia))).
  pose proof (mod_upper_bound s 2 (ltac:(lia))).
  pose proof (mod_upper_bound s 3 (ltac:(lia))).
  assert (r/2 < 3) by (apply Div0.div_lt_upper_bound; lia).
  assert (r/3 < 2) by (apply Div0.div_lt_upper_bound; lia).
  assert (s/2 < 3) by (apply Div0.div_lt_upper_bound; lia).
  assert (s/3 < 2) by (apply Div0.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma crt6_compute : forall x r, r < 6 ->
  x mod 2 = r mod 2 -> x mod 3 = r mod 3 -> x mod 6 = r.
Proof.
  intros x r Hr H2 H3.
  apply crt6_unique;
    [apply mod_upper_bound; lia | exact Hr |
     rewrite <- crt2; exact H2 | rewrite <- crt3; exact H3].
Qed.

(* ================================================================= *)
(*  SECTION 1 — THE ORTHOGONAL AXES                                   *)
(* ================================================================= *)

Theorem axes_orthogonal : Nat.gcd 2 3 = 1.
Proof. reflexivity. Qed.

Theorem field_plane_factorizes : 6 = 2 * 3.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  SECTION 2 — THE UNITS AND THE DIAGONAL                            *)
(*                                                                    *)
(*  (ℤ/6ℤ)* = {1, 5}: the two invertible elements                    *)
(*  5 ≡ -1 mod 6: the reflection element, the diagonal               *)
(*  1 ≡  1 mod 6: the identity element, the Mersenne position        *)
(* ================================================================= *)

Theorem units_mod6 : forall r, r < 6 ->
  (exists s, s < 6 /\ (r * s) mod 6 = 1) <-> (r = 1 \/ r = 5).
Proof.
  intros r Hr. split.
  - intros [s [Hs Hmul]].
    assert (H2 : (r * s) mod 2 = 1).
    { assert (Hc : (r*s) mod 6 mod 2 = 1 mod 2) by (rewrite Hmul; reflexivity).
      rewrite <- crt2 in Hc. exact Hc. }
    assert (H3 : (r * s) mod 3 = 1).
    { assert (Hc : (r*s) mod 6 mod 3 = 1 mod 3) by (rewrite Hmul; reflexivity).
      rewrite <- crt3 in Hc. exact Hc. }
    assert (Hr2 : r mod 2 = 1).
    { rewrite Div0.mul_mod in H2.
      pose proof (mod_upper_bound r 2 (ltac:(lia))).
      pose proof (mod_upper_bound s 2 (ltac:(lia))).
      destruct (r mod 2); [simpl in H2; lia | lia]. }
    assert (Hr3 : r mod 3 <> 0).
    { intro H. rewrite Div0.mul_mod in H3.
      rewrite H in H3. simpl in H3. lia. }
    pose proof (mod_upper_bound r 3 (ltac:(lia))).
    pose proof (div_mod r 2 (ltac:(lia))).
    pose proof (div_mod r 3 (ltac:(lia))).
    assert (r/2 < 3) by (apply Div0.div_lt_upper_bound; lia).
    assert (r/3 < 2) by (apply Div0.div_lt_upper_bound; lia).
    lia.
  - intros [H|H]; subst.
    + exists 1. split; [lia | reflexivity].
    + exists 5. split; [lia | reflexivity].
Qed.

(* 5 is the unique non-trivial unit: 5 ≡ -1 mod 6 *)
Theorem diagonal_is_neg1 : (5 + 1) mod 6 = 0.
Proof. reflexivity. Qed.

(* 5 is self-inverse: 5 * 5 ≡ 1 mod 6 *)
Theorem diagonal_self_inv : (5 * 5) mod 6 = 1.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  SECTION 3 — POWERS OF 2 MODULO 3                                 *)
(* ================================================================= *)

Lemma pow2_mod3_even : forall k, (2^(2*k)) mod 3 = 1.
Proof.
  intro k. induction k as [|k IHk].
  - reflexivity.
  - replace (2*(S k)) with (2*k+2) by lia.
    rewrite pow_add_r, Div0.mul_mod, IHk. reflexivity.
Qed.

Lemma pow2_mod3_odd : forall k, (2^(2*k+1)) mod 3 = 2.
Proof.
  intro k. induction k as [|k IHk].
  - reflexivity.
  - replace (2*(S k)+1) with (2*k+1+2) by lia.
    rewrite pow_add_r, Div0.mul_mod, IHk. reflexivity.
Qed.

(* ================================================================= *)
(*  SECTION 4 — FERMAT NUMBERS ON THE DIAGONAL                        *)
(* ================================================================= *)

Lemma pow2_even : forall n, n >= 1 -> exists k, 2^n = 2*k.
Proof.
  intros n Hn. exists (2^(n-1)).
  rewrite <- pow_succ_r; [f_equal; lia | lia].
Qed.

Lemma two_pow_ge1 : forall n, 2^n >= 1.
Proof. intro n. induction n; simpl; lia. Qed.

Lemma pow2_pow2_even : forall n, exists k, 2^(2^n) = 2*k.
Proof.
  intro n. exists (2^(2^n - 1)).
  assert (Hge : 2^n >= 1) by apply two_pow_ge1.
  rewrite <- pow_succ_r; [f_equal; lia | lia].
Qed.

(* Fₙ is always odd *)
Theorem fermat_odd : forall n, (2^(2^n) + 1) mod 2 = 1.
Proof.
  intro n.
  destruct (pow2_pow2_even n) as [k Hk].
  rewrite Hk, Div0.add_mod, (mul_comm 2 k), Div0.mod_mul.
  reflexivity.
Qed.

(* ★ 2^(2^n) ≡ 1 mod 3 for n ≥ 1 → Fₙ ≡ 2 mod 3 *)
Theorem fermat_mod3 : forall n, n >= 1 ->
  (2^(2^n) + 1) mod 3 = 2.
Proof.
  intros n Hn.
  destruct (pow2_even n Hn) as [k Hk].
  rewrite Hk, Div0.add_mod, pow2_mod3_even. reflexivity.
Qed.

(* ★ 2^(2^n) ≡ 4 mod 6 for n ≥ 1: the pre-step position *)
Theorem fermat_base_mod6 : forall n, n >= 1 ->
  (2^(2^n)) mod 6 = 4.
Proof.
  intros n Hn.
  apply crt6_compute; [lia | | ].
  - destruct (pow2_pow2_even n) as [k Hk].
    rewrite Hk, (mul_comm 2 k). apply Div0.mod_mul.
  - destruct (pow2_even n Hn) as [k Hk].
    rewrite Hk. apply pow2_mod3_even.
Qed.

(* ★★ Fₙ ≡ 5 mod 6: Fermat numbers lie on the diagonal *)
Theorem fermat_mod6 : forall n, n >= 1 ->
  (2^(2^n) + 1) mod 6 = 5.
Proof.
  intros n Hn.
  apply crt6_compute; [lia | apply fermat_odd | apply fermat_mod3; exact Hn].
Qed.

(* ★ Fₙ at the diagonal coordinate (1,2) in ℤ/2ℤ × ℤ/3ℤ *)
Theorem fermat_on_diagonal : forall n, n >= 1 ->
  ((2^(2^n)+1) mod 2, (2^(2^n)+1) mod 3) = (1, 2).
Proof.
  intros n Hn.
  rewrite fermat_odd, fermat_mod3; [reflexivity | exact Hn].
Qed.

(* The diagonal step: 2^(2^n) is at 4, Fₙ = +1 steps to 5 *)
Theorem fermat_step : forall n, n >= 1 ->
  (2^(2^n) + 1) mod 6 = (4 + 1) mod 6.
Proof.
  intros n Hn.
  rewrite Div0.add_mod, fermat_base_mod6; [reflexivity | exact Hn].
Qed.

(* ================================================================= *)
(*  SECTION 5 — MERSENNE NUMBERS AT THE DUAL POSITION                *)
(* ================================================================= *)

Lemma pow2_ge2 : forall p, p >= 1 -> 2^p >= 2.
Proof.
  intros p Hp. induction p as [|p IHp].
  - lia.
  - simpl. destruct p; [simpl; lia |
    assert (2^(S p) >= 2) by (apply IHp; lia); lia].
Qed.

Lemma sub1_mod3 : forall x, x >= 2 -> x mod 3 = 2 -> (x-1) mod 3 = 1.
Proof.
  intros x Hx H.
  assert (exists q, x = 3*q+2) by
    (exists (x/3); rewrite (div_mod x 3) at 1; lia).
  destruct H0 as [q ->].
  assert (3*q+2-1 = 3*q+1) by lia.
  rewrite H0, Div0.add_mod, (mul_comm 3 q), Div0.mod_mul. reflexivity.
Qed.

(* Mₚ is odd for p ≥ 1 *)
Theorem mersenne_odd : forall p, p >= 1 -> (2^p - 1) mod 2 = 1.
Proof.
  intros p Hp.
  destruct (pow2_even p Hp) as [k Hk].
  assert (Hbig : 2^p >= 2) by (apply pow2_ge2; exact Hp).
  rewrite Hk.
  assert (2*k - 1 = 2*(k-1) + 1) by lia.
  rewrite H, Div0.add_mod, (mul_comm 2 (k-1)), Div0.mod_mul.
  reflexivity.
Qed.

(* ★★ Mₚ ≡ 1 mod 6 for odd p ≥ 3 *)
Theorem mersenne_mod6 : forall p,
  p >= 3 -> p mod 2 = 1 -> (2^p - 1) mod 6 = 1.
Proof.
  intros p Hp Hodd.
  assert (Hbig : 2^p >= 8).
  { apply Nat.le_trans with (2^3); [reflexivity |
    apply Nat.pow_le_mono_r; lia]. }
  assert (exists k, p = 2*k+1) by
    (exists (p/2); pose proof (div_mod p 2 (ltac:(lia))); lia).
  destruct H as [k ->].
  apply crt6_compute; [lia | | ].
  - apply mersenne_odd. lia.
  - apply sub1_mod3; [lia | apply pow2_mod3_odd].
Qed.

(* ================================================================= *)
(*  SECTION 6 — THE DIAGONAL COMPLEMENT RELATIONSHIP                  *)
(*                                                                    *)
(*  Fermat at 5 ≡ -1 mod 6                                           *)
(*  Mersenne at 1 ≡  1 mod 6                                         *)
(*  Together: 5 + 1 = 6 ≡ 0 — they span the full unit group         *)
(* ================================================================= *)

Theorem diagonal_complement : (5 + 1) mod 6 = 0 /\ (1 + 5) mod 6 = 0.
Proof. split; reflexivity. Qed.

Theorem fermat_mersenne_sum_zero : forall n p,
  n >= 1 -> p >= 3 -> p mod 2 = 1 ->
  ((2^(2^n)+1) mod 6 + (2^p-1) mod 6) mod 6 = 0.
Proof.
  intros n p Hn Hp Hodd.
  rewrite fermat_mod6, mersenne_mod6; [reflexivity | exact Hp | exact Hodd | exact Hn].
Qed.

(* ================================================================= *)
(*  SECTION 7 — PRIMALITY LIVES OFF THE AXES                         *)
(*                                                                    *)
(*  Generator axis (mod 2 = 0): {0, 2, 4} — even numbers            *)
(*  Attractor axis (mod 3 = 0): {0, 3}    — multiples of 3          *)
(*  Every prime > 3 avoids both: lives in {1, 5} mod 6              *)
(* ================================================================= *)

(* ★ Every prime > 3 is at position 1 or 5 mod 6 *)
Theorem prime_gt3_mod6 : forall p,
  is_prime p -> p > 3 -> p mod 6 = 1 \/ p mod 6 = 5.
Proof.
  intros p [Hge Hdvd] Hgt.
  assert (Hodd : p mod 2 = 1).
  { pose proof (mod_upper_bound p 2 (ltac:(lia))).
    remember (p mod 2) as r.
    destruct r as [|[|r]]; try lia.
    exfalso.
    assert (Hd : divides 2 p).
    { exists (p/2). rewrite (div_mod p 2 (ltac:(lia))) at 1. lia. }
    destruct (Hdvd 2 Hd); lia. }
  assert (Hnot3 : p mod 3 <> 0).
  { intro H0.
    assert (Hd : divides 3 p).
    { exists (p/3). rewrite (div_mod p 3 (ltac:(lia))) at 1. lia. }
    destruct (Hdvd 3 Hd); lia. }
  pose proof (mod_upper_bound p 6 (ltac:(lia))) as H6.
  assert (Hp6_2 : p mod 6 mod 2 = 1) by (rewrite <- crt2; exact Hodd).
  assert (Hp6_3 : p mod 6 mod 3 <> 0) by (rewrite <- crt3; exact Hnot3).
  set (r := p mod 6) in *.
  pose proof (mod_upper_bound r 2 (ltac:(lia))).
  pose proof (mod_upper_bound r 3 (ltac:(lia))).
  pose proof (div_mod r 2 (ltac:(lia))).
  pose proof (div_mod r 3 (ltac:(lia))).
  assert (r/2 < 3) by (apply Div0.div_lt_upper_bound; lia).
  assert (r/3 < 2) by (apply Div0.div_lt_upper_bound; lia).
  lia.
Qed.

(* The diagonal position 5 is uniquely identified by mod 3 = 2
   among positions off both axes *)
Theorem diagonal_unique : forall r, r < 6 ->
  r mod 2 <> 0 -> r mod 3 <> 0 -> r mod 3 = 2 -> r = 5.
Proof.
  intros r Hr H2 H3 Hmod3.
  pose proof (mod_upper_bound r 2 (ltac:(lia))).
  pose proof (mod_upper_bound r 3 (ltac:(lia))).
  pose proof (div_mod r 2 (ltac:(lia))).
  pose proof (div_mod r 3 (ltac:(lia))).
  assert (r/2 < 3) by (apply Div0.div_lt_upper_bound; lia).
  assert (r/3 < 2) by (apply Div0.div_lt_upper_bound; lia).
  lia.
Qed.

(* ================================================================= *)
(*  SECTION 8 — THE REFINED DIAGONAL CONJECTURE                       *)
(* ================================================================= *)

Theorem refined_diagonal_conjecture :
  (* 1. Axes are orthogonal *)
  Nat.gcd 2 3 = 1 /\
  (* 2. Plane factorizes *)
  6 = 2 * 3 /\
  (* 3. Units are {1, 5}: the diagonal positions *)
  (forall r, r < 6 ->
    (exists s, s < 6 /\ (r*s) mod 6 = 1) <-> (r = 1 \/ r = 5)) /\
  (* 4. Diagonal is self-inverse: 5 * 5 ≡ 1 mod 6 *)
  (5 * 5) mod 6 = 1 /\
  (* 5. Fermat numbers on the diagonal: Fₙ ≡ 5 mod 6 *)
  (forall n, n >= 1 -> (2^(2^n)+1) mod 6 = 5) /\
  (* 6. Fermat base at 4, +1 steps to diagonal *)
  (forall n, n >= 1 -> (2^(2^n)) mod 6 = 4) /\
  (* 7. Mersenne at dual position: Mₚ ≡ 1 mod 6 *)
  (forall p, p >= 3 -> p mod 2 = 1 -> (2^p-1) mod 6 = 1) /\
  (* 8. Fermat + Mersenne = 0 mod 6: additive inverses *)
  (5 + 1) mod 6 = 0 /\
  (* 9. Every prime > 3 is at position 1 or 5 *)
  (forall p, is_prime p -> p > 3 -> p mod 6 = 1 \/ p mod 6 = 5) /\
  (* 10. Position 5 uniquely identified by (mod2=1, mod3=2) *)
  (forall r, r < 6 -> r mod 2 <> 0 -> r mod 3 <> 0 ->
    r mod 3 = 2 -> r = 5).
Proof.
  refine (conj axes_orthogonal
         (conj field_plane_factorizes
         (conj units_mod6
         (conj diagonal_self_inv
         (conj fermat_mod6
         (conj fermat_base_mod6
         (conj mersenne_mod6
         (conj _ (conj prime_gt3_mod6 diagonal_unique))))))))).
  reflexivity.
Qed.

(* ================================================================= *)
(*  SECTION 9 — PRINT ASSUMPTIONS (zero axioms)                      *)
(* ================================================================= *)

Print Assumptions fermat_mod6.
Print Assumptions mersenne_mod6.
Print Assumptions fermat_on_diagonal.
Print Assumptions prime_gt3_mod6.
Print Assumptions units_mod6.
Print Assumptions refined_diagonal_conjecture.

