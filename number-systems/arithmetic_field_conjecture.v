(* ================================================================= *)
(*   THE ARITHMETIC FIELD CONJECTURE                                  *)
(*   Constructive Coq Formalization — Zero Axioms                    *)
(*   Coq 8.18 — verified                                             *)
(*                                                                   *)
(*   THEOREMS:                                                        *)
(*    1.  vacuum_total            every n is in some vacuum sector    *)
(*    2.  vacuum_exclusive        sectors are disjoint                *)
(*    3.  squares_in_vacuum       n^2 ≡ 0 or 1 (mod 4)              *)
(*    4.  two_self_annihilates    2*2 ≡ 0 (mod 4)                   *)
(*    5.  attractor_total         every n is in some attractor fiber  *)
(*    6.  attractor_no_inverse    ℕ has no additive inverses         *)
(*    7.  attractor_has_inv       ℤ/3ℤ has multiplicative inverses   *)
(*    8.  stable_iff_mod12        stable ↔ mod12 ∈ {1,5,7,11}       *)
(*    9.  field_factorizes        12 = 4 × 3                         *)
(*   10.  V1_mul_V1               V1 × V1 = V1                       *)
(*   11.  V3_mul_V3               V3 × V3 = V1                       *)
(*   12.  V1_mul_V3               V1 × V3 = V3                       *)
(*   13.  mod3_integral_domain    ℤ/3ℤ has no zero divisors          *)
(*   14.  stable_mul_closed       stable × stable = stable           *)
(*   15.  AFC_I ★                 every prime > 3 is stable          *)
(*   16.  product_of_primes       products of stable primes stable   *)
(*   17.  two_not_stable          2 generates the vacuum             *)
(*   18.  three_not_stable        3 generates the attractor          *)
(*   19.  stable_no_even_factor   stable ⟹ not divisible by 2      *)
(*   20.  stable_no_3_factor      stable ⟹ not divisible by 3      *)
(*   21.  stable_pow              powers of stable are stable        *)
(*   22.  stable_prime_factor_gt3 prime factors of stable are > 3   *)
(* ================================================================= *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.ArithRing.

Import Nat.

(* Helper: k*n mod n = 0 *)
Lemma mod_multiple : forall k n, (k * n) mod n = 0.
Proof. intros k n. apply Div0.mod_mul. Qed.

(* ================================================================= *)
(*  SECTION 1 — VACUUM STATE (ℤ/4ℤ)                                  *)
(* ================================================================= *)

Definition in_V0 (n : nat) : Prop := n mod 4 = 0.
Definition in_V1 (n : nat) : Prop := n mod 4 = 1.
Definition in_V2 (n : nat) : Prop := n mod 4 = 2.
Definition in_V3 (n : nat) : Prop := n mod 4 = 3.

Theorem vacuum_total : forall n,
  in_V0 n \/ in_V1 n \/ in_V2 n \/ in_V3 n.
Proof.
  intro n. unfold in_V0, in_V1, in_V2, in_V3.
  pose proof (mod_upper_bound n 4 (ltac:(lia))). lia.
Qed.

Theorem vacuum_exclusive : forall n,
  ~ (in_V0 n /\ in_V1 n) /\ ~ (in_V0 n /\ in_V2 n) /\
  ~ (in_V0 n /\ in_V3 n) /\ ~ (in_V1 n /\ in_V2 n) /\
  ~ (in_V1 n /\ in_V3 n) /\ ~ (in_V2 n /\ in_V3 n).
Proof.
  intro n. unfold in_V0, in_V1, in_V2, in_V3. repeat split; lia.
Qed.

(* ================================================================= *)
(*  SECTION 2 — VACUUM GROUND STATE: n^2 ≡ 0 or 1 (mod 4)           *)
(* ================================================================= *)

Lemma square_mod4 : forall n, (n * n) mod 4 = 0 \/ (n * n) mod 4 = 1.
Proof.
  intro n.
  pose proof (div_mod n 4 (ltac:(lia))) as Hn.
  pose proof (mod_upper_bound n 4 (ltac:(lia))) as Hr.
  set (q := n/4) in Hn.
  set (r := n mod 4) in *.
  assert (Hrv : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  destruct Hrv as [Hr0|[Hr1|[Hr2|Hr3]]].
  - left.
    assert (Hn0 : n = 4*q) by lia. rewrite Hn0.
    assert (H : 4*q*(4*q) = (4*q*q)*4) by ring.
    rewrite H. apply mod_multiple.
  - right.
    assert (Hn1 : n = 4*q+1) by lia. rewrite Hn1.
    assert (H : (4*q+1)*(4*q+1) = (4*q*q+2*q)*4 + 1) by ring.
    rewrite H, Div0.add_mod, mod_multiple. reflexivity.
  - left.
    assert (Hn2 : n = 4*q+2) by lia. rewrite Hn2.
    assert (H : (4*q+2)*(4*q+2) = (4*q*q+4*q+1)*4) by ring.
    rewrite H. apply mod_multiple.
  - right.
    assert (Hn3 : n = 4*q+3) by lia. rewrite Hn3.
    assert (H : (4*q+3)*(4*q+3) = (4*q*q+6*q+2)*4 + 1) by ring.
    rewrite H, Div0.add_mod, mod_multiple. reflexivity.
Qed.

Theorem squares_in_vacuum : forall n,
  in_V0 (n * n) \/ in_V1 (n * n).
Proof. intro n. exact (square_mod4 n). Qed.

Theorem two_self_annihilates : in_V0 (2 * 2).
Proof. unfold in_V0. reflexivity. Qed.

(* ================================================================= *)
(*  SECTION 3 — ATTRACTOR FIELD (ℤ/3ℤ)                               *)
(* ================================================================= *)

Definition in_A0 (n : nat) : Prop := n mod 3 = 0.
Definition in_A1 (n : nat) : Prop := n mod 3 = 1.
Definition in_A2 (n : nat) : Prop := n mod 3 = 2.

Theorem attractor_total : forall n,
  in_A0 n \/ in_A1 n \/ in_A2 n.
Proof.
  intro n. unfold in_A0, in_A1, in_A2.
  pose proof (mod_upper_bound n 3 (ltac:(lia))). lia.
Qed.

(* ℕ cannot realize additive inverses — the attractor cannot close  *)
Theorem attractor_no_inverse : ~ exists n : nat, 1 + n = 0.
Proof. intros [n Hn]. lia. Qed.

(* ℤ/3ℤ has multiplicative inverses — it wants to be a field        *)
Theorem attractor_has_inv :
  (1 * 1) mod 3 = 1 /\ (2 * 2) mod 3 = 1.
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(*  SECTION 4 — STABLE EXCITATION                                    *)
(*                                                                   *)
(*  is_stable n  ⟺  n mod 3 ≠ 0  ∧  n mod 4 ∈ {1,3}              *)
(*              ⟺  n mod 12 ∈ {1, 5, 7, 11}                        *)
(* ================================================================= *)

Definition is_stable (n : nat) : Prop :=
  n mod 3 <> 0 /\ (n mod 4 = 1 \/ n mod 4 = 3).

Definition is_stable_bool (n : nat) : bool :=
  negb (Nat.eqb (n mod 3) 0) &&
  (Nat.eqb (n mod 4) 1 || Nat.eqb (n mod 4) 3).

Lemma stable_bool_spec : forall n,
  is_stable_bool n = true <-> is_stable n.
Proof.
  intro n. unfold is_stable_bool, is_stable.
  rewrite andb_true_iff, negb_true_iff, orb_true_iff.
  rewrite Nat.eqb_neq. repeat rewrite Nat.eqb_eq. tauto.
Qed.

(* ================================================================= *)
(*  SECTION 5 — CRT: ℤ/12ℤ ≅ ℤ/3ℤ × ℤ/4ℤ                          *)
(* ================================================================= *)

Lemma mod12_mod3 : forall n, n mod 3 = (n mod 12) mod 3.
Proof.
  intro n.
  pose proof (div_mod n 12 (ltac:(lia))) as Hn.
  set (q := n/12) in Hn. set (r := n mod 12) in *.
  assert (Hq : n = 3*(4*q) + r) by lia.
  rewrite Hq, Div0.add_mod, (mul_comm 3 (4*q)), Div0.mod_mul, add_0_l.
  apply Div0.mod_mod.
Qed.

Lemma mod12_mod4 : forall n, n mod 4 = (n mod 12) mod 4.
Proof.
  intro n.
  pose proof (div_mod n 12 (ltac:(lia))) as Hn.
  set (q := n/12) in Hn. set (r := n mod 12) in *.
  assert (Hq : n = 4*(3*q) + r) by lia.
  rewrite Hq, Div0.add_mod, (mul_comm 4 (3*q)), Div0.mod_mul, add_0_l.
  apply Div0.mod_mod.
Qed.

Theorem field_factorizes : 12 = 4 * 3.
Proof. reflexivity. Qed.

(* Forward direction helper *)
Lemma stable_small_fwd : forall r, r < 12 ->
  r mod 3 <> 0 -> (r mod 4 = 1 \/ r mod 4 = 3) ->
  r = 1 \/ r = 5 \/ r = 7 \/ r = 11.
Proof.
  intros r Hr H3 H4.
  pose proof (div_mod r 4 (ltac:(lia))) as Hr4.
  pose proof (div_mod r 3 (ltac:(lia))) as Hr3.
  assert (Hq4 : r / 4 < 3) by (apply Div0.div_lt_upper_bound; lia).
  assert (Hq3 : r / 3 < 4) by (apply Div0.div_lt_upper_bound; lia).
  assert (Hr3v : r mod 3 = 1 \/ r mod 3 = 2) by
    (pose proof (mod_upper_bound r 3 (ltac:(lia))); lia).
  destruct H4 as [H4|H4]; destruct Hr3v as [H|H].
  - left. lia.
  - right. left. lia.
  - right. right. left. lia.
  - right. right. right. lia.
Qed.

(* Backward direction helper *)
Lemma stable_small_bwd : forall r, r < 12 ->
  (r = 1 \/ r = 5 \/ r = 7 \/ r = 11) ->
  r mod 3 <> 0 /\ (r mod 4 = 1 \/ r mod 4 = 3).
Proof.
  intros r Hr Hin.
  destruct Hin as [H|[H|[H|H]]]; subst; simpl; split; lia.
Qed.

Theorem stable_iff_mod12 : forall n,
  is_stable n <->
  (n mod 12 = 1 \/ n mod 12 = 5 \/ n mod 12 = 7 \/ n mod 12 = 11).
Proof.
  intro n. unfold is_stable.
  rewrite mod12_mod3, mod12_mod4.
  split.
  - intros [H3 H4].
    apply stable_small_fwd.
    + apply mod_upper_bound. lia.
    + exact H3.
    + exact H4.
  - intro H.
    apply stable_small_bwd.
    + apply mod_upper_bound. lia.
    + exact H.
Qed.

(* ================================================================= *)
(*  SECTION 6 — VACUUM MULTIPLICATION LAWS                           *)
(*                                                                   *)
(*  {V1, V3} is a group under multiplication ≅ ℤ/2ℤ                *)
(*  = the symmetry group of the vacuum state                         *)
(* ================================================================= *)

Lemma V1_mul_V1 : forall a b, in_V1 a -> in_V1 b -> in_V1 (a * b).
Proof.
  intros a b Ha Hb. unfold in_V1 in *.
  assert (exists j, a = 4*j+1) by
    (exists (a/4); pose proof (div_mod a 4 (ltac:(lia))); lia).
  assert (exists k, b = 4*k+1) by
    (exists (b/4); pose proof (div_mod b 4 (ltac:(lia))); lia).
  destruct H as [j ->]. destruct H0 as [k ->].
  assert (Hm : (4*j+1)*(4*k+1) = (4*j*k+j+k)*4 + 1) by ring.
  rewrite Hm, Div0.add_mod, mod_multiple. reflexivity.
Qed.

Lemma V3_mul_V3 : forall a b, in_V3 a -> in_V3 b -> in_V1 (a * b).
Proof.
  intros a b Ha Hb. unfold in_V1, in_V3 in *.
  assert (exists j, a = 4*j+3) by
    (exists (a/4); pose proof (div_mod a 4 (ltac:(lia))); lia).
  assert (exists k, b = 4*k+3) by
    (exists (b/4); pose proof (div_mod b 4 (ltac:(lia))); lia).
  destruct H as [j ->]. destruct H0 as [k ->].
  assert (Hm : (4*j+3)*(4*k+3) = (4*j*k+3*j+3*k+2)*4 + 1) by ring.
  rewrite Hm, Div0.add_mod, mod_multiple. reflexivity.
Qed.

Lemma V1_mul_V3 : forall a b, in_V1 a -> in_V3 b -> in_V3 (a * b).
Proof.
  intros a b Ha Hb. unfold in_V1, in_V3 in *.
  assert (exists j, a = 4*j+1) by
    (exists (a/4); pose proof (div_mod a 4 (ltac:(lia))); lia).
  assert (exists k, b = 4*k+3) by
    (exists (b/4); pose proof (div_mod b 4 (ltac:(lia))); lia).
  destruct H as [j ->]. destruct H0 as [k ->].
  assert (Hm : (4*j+1)*(4*k+3) = (4*j*k+3*j+k)*4 + 3) by ring.
  rewrite Hm, Div0.add_mod, mod_multiple. reflexivity.
Qed.

(* ================================================================= *)
(*  SECTION 7 — STABLE EXCITATIONS CLOSED UNDER MULTIPLICATION       *)
(* ================================================================= *)

Lemma mod3_integral_domain : forall a b,
  (a * b) mod 3 = 0 -> a mod 3 = 0 \/ b mod 3 = 0.
Proof.
  intros a b H.
  rewrite Div0.mul_mod in H.
  pose proof (mod_upper_bound a 3 (ltac:(lia))) as Ha.
  pose proof (mod_upper_bound b 3 (ltac:(lia))) as Hb.
  remember (a mod 3) as ra. remember (b mod 3) as rb.
  destruct ra as [|[|[|]]]; try lia;
  destruct rb as [|[|[|]]]; try lia;
  simpl in H; discriminate.
Qed.

Theorem stable_mul_closed : forall a b,
  is_stable a -> is_stable b -> is_stable (a * b).
Proof.
  intros a b [Ha3 Ha4] [Hb3 Hb4].
  unfold is_stable. split.
  - intro H. destruct (mod3_integral_domain a b H); contradiction.
  - destruct Ha4 as [Ha4|Ha4]; destruct Hb4 as [Hb4|Hb4].
    + left.  exact (V1_mul_V1 a b Ha4 Hb4).
    + right. exact (V1_mul_V3 a b Ha4 Hb4).
    + right. rewrite mul_comm. exact (V1_mul_V3 b a Hb4 Ha4).
    + left.  exact (V3_mul_V3 a b Ha4 Hb4).
Qed.

(* ================================================================= *)
(*  SECTION 8 — PRIMALITY                                            *)
(* ================================================================= *)

Definition divides (d n : nat) : Prop := exists k, n = d * k.

Definition is_prime (p : nat) : Prop :=
  p >= 2 /\ forall d, divides d p -> d = 1 \/ d = p.

Lemma prime_gt3_not_even : forall p,
  is_prime p -> p > 3 -> ~ divides 2 p.
Proof.
  intros p [_ Hd] Hgt [k Hk].
  destruct (Hd 2 (ex_intro _ k Hk)); lia.
Qed.

Lemma prime_gt3_not_div3 : forall p,
  is_prime p -> p > 3 -> ~ divides 3 p.
Proof.
  intros p [_ Hd] Hgt [k Hk].
  destruct (Hd 3 (ex_intro _ k Hk)); lia.
Qed.

Lemma prime_gt3_odd : forall p,
  is_prime p -> p > 3 -> p mod 4 = 1 \/ p mod 4 = 3.
Proof.
  intros p Hprime Hgt.
  pose proof (mod_upper_bound p 4 (ltac:(lia))) as Hb.
  pose proof (div_mod p 4 (ltac:(lia))) as Hp.
  set (r := p mod 4) in *.
  assert (Hr : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  destruct Hr as [Hr0|[Hr1|[Hr2|Hr3]]].
  - exfalso. apply (prime_gt3_not_even p Hprime Hgt).
    exists (p/4 * 2). lia.
  - left. exact Hr1.
  - exfalso. apply (prime_gt3_not_even p Hprime Hgt).
    exists (p/4 * 2 + 1). lia.
  - right. exact Hr3.
Qed.

Lemma prime_gt3_not_A0 : forall p,
  is_prime p -> p > 3 -> p mod 3 <> 0.
Proof.
  intros p Hprime Hgt H0.
  apply (prime_gt3_not_div3 p Hprime Hgt).
  exists (p/3). pose proof (div_mod p 3 (ltac:(lia))). lia.
Qed.

(* ================================================================= *)
(*  SECTION 9 ★ — AFC-I: MAIN THEOREM                               *)
(*                                                                   *)
(*  Every prime > 3 is a stable field excitation.                    *)
(*  Primes resist simultaneous annihilation by vacuum (mod 4)        *)
(*  and attractor (mod 3) — the two field generators.                *)
(* ================================================================= *)

Theorem AFC_I : forall p,
  is_prime p -> p > 3 -> is_stable p.
Proof.
  intros p Hprime Hgt.
  unfold is_stable. split.
  - exact (prime_gt3_not_A0 p Hprime Hgt).
  - exact (prime_gt3_odd p Hprime Hgt).
Qed.

(* ================================================================= *)
(*  SECTION 10 — COROLLARIES                                         *)
(* ================================================================= *)

Corollary product_of_primes : forall p q,
  is_prime p -> is_prime q -> p > 3 -> q > 3 ->
  is_stable (p * q).
Proof.
  intros p q Hp Hq Hp3 Hq3.
  apply stable_mul_closed.
  - exact (AFC_I p Hp Hp3).
  - exact (AFC_I q Hq Hq3).
Qed.

(* 2 and 3 are the field generators — not excitations above the field *)
Theorem two_not_stable : ~ is_stable 2.
Proof.
  unfold is_stable. intros [_ Hv].
  destruct Hv as [H|H]; discriminate.
Qed.

Theorem three_not_stable : ~ is_stable 3.
Proof.
  unfold is_stable. intros [H _]. apply H. reflexivity.
Qed.

Theorem stable_no_even_factor : forall n,
  is_stable n -> ~ divides 2 n.
Proof.
  intros n [_ Hn4] [k Hk]. subst.
  pose proof (mod_upper_bound k 2 (ltac:(lia))) as Hkb.
  assert (Hkr : k mod 2 = 0 \/ k mod 2 = 1) by lia.
  destruct Hkr as [He|Ho].
  - assert (Hm : exists m, k = 2*m) by (exists (k/2);
      pose proof (div_mod k 2 (ltac:(lia))); lia).
    destruct Hm as [m Hm]. subst k.
    assert (Hmod : (2*(2*m)) mod 4 = 0).
    { replace (2*(2*m)) with (m*4) by lia. apply Div0.mod_mul. }
    destruct Hn4 as [H|H]; lia.
  - assert (Hm : exists m, k = 2*m+1) by (exists (k/2);
      pose proof (div_mod k 2 (ltac:(lia))); lia).
    destruct Hm as [m Hm]. subst k.
    assert (Hmod : (2*(2*m+1)) mod 4 = 2).
    { replace (2*(2*m+1)) with (m*4+2) by lia.
      rewrite Div0.add_mod.
      assert (Hz : m*4 mod 4 = 0) by apply Div0.mod_mul.
      rewrite Hz. reflexivity. }
    destruct Hn4 as [H|H]; lia.
Qed.

Theorem stable_no_3_factor : forall n,
  is_stable n -> ~ divides 3 n.
Proof.
  intros n [Hn3 _] [k Hk]. apply Hn3. subst.
  rewrite (mul_comm 3 k). apply Div0.mod_mul.
Qed.

Theorem stable_pow : forall n k,
  is_stable n -> k >= 1 -> is_stable (n ^ k).
Proof.
  intros n k Hn Hk.
  induction k as [|k IHk].
  - lia.
  - simpl.
    destruct k as [|k].
    + simpl. rewrite mul_1_r. exact Hn.
    + apply stable_mul_closed.
      * exact Hn.
      * apply IHk. lia.
Qed.

Lemma stable_prime_factor_gt3 : forall n p,
  is_stable n -> is_prime p -> divides p n -> p > 3.
Proof.
  intros n p Hstable [Hge _] Hdvd.
  destruct (lt_trichotomy p 4) as [H|[H|H]]; try lia.
  - destruct p as [|[|[|[|p]]]]; try lia.
    + exfalso. exact (stable_no_even_factor n Hstable Hdvd).
    + exfalso. exact (stable_no_3_factor n Hstable Hdvd).
Qed.

(* ================================================================= *)
(*  SECTION 11 — PRINT ASSUMPTIONS                                   *)
(*  All theorems rest on CIC alone. Zero extra axioms.               *)
(* ================================================================= *)

Print Assumptions AFC_I.
Print Assumptions stable_mul_closed.
Print Assumptions squares_in_vacuum.
Print Assumptions attractor_no_inverse.
Print Assumptions stable_iff_mod12.
Print Assumptions product_of_primes.
Print Assumptions stable_pow.
Print Assumptions stable_prime_factor_gt3.

