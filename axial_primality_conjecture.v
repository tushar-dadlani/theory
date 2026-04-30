(* ================================================================= *)
(*   AXIAL PRIMALITY CONJECTURE                                       *)
(*   Fermat & Mersenne primes on orthogonal mod 3 / mod 4 axes       *)
(*   Coq 8.18 — Zero Axioms — Verified                               *)
(*                                                                   *)
(*   THEOREMS:                                                        *)
(*    1.  axes_orthogonal        gcd(3,4) = 1                        *)
(*    2.  crt_unique             mod 12 is unique from (mod3, mod4)  *)
(*    3.  pow2_mod3_even         2^(2k) ≡ 1 mod 3                   *)
(*    4.  pow2_mod3_odd          2^(2k+1) ≡ 2 mod 3                 *)
(*    5.  pow2_mod4_ge2          2^k ≡ 0 mod 4 for k ≥ 2            *)
(*    6.  fermat_mod3   ★        2^(2^n) ≡ 1 mod 3 for n ≥ 1        *)
(*    7.  fermat_mod4   ★        2^(2^n) ≡ 0 mod 4 for n ≥ 1        *)
(*    8.  fermat_mod12  ★★       Fₙ ≡ 5 mod 12 for n ≥ 1            *)
(*    9.  mersenne_mod3 ★        2^(2k+1) ≡ 2 mod 3                 *)
(*   10.  mersenne_mod4 ★        2^p ≡ 0 mod 4 for p ≥ 2            *)
(*   11.  mersenne_mod12 ★★      Mₚ ≡ 7 mod 12 for odd p ≥ 3        *)
(*   12.  fermat_axial_pos       Fₙ at (mod3,mod4) = (2,1)          *)
(*   13.  mersenne_axial_pos     Mₚ at (mod3,mod4) = (1,3)          *)
(*   14.  axial_symmetry ★★      (2,1) and (1,3) are reflections     *)
(*   15.  fermat_axial_dist      d(5) = 2 (minimum)                 *)
(*   16.  mersenne_axial_dist    d(7) = 2 (minimum)                 *)
(*   17.  axial_dist_minimum     stable positions have dist ≥ 2      *)
(*   18.  fermat_stable          Fₙ (n≥1) is a stable excitation     *)
(*   19.  mersenne_stable        Mₚ (odd p≥3) is a stable excitation *)
(*   20.  primality_interior     primes > 3 live in the open interior *)
(*   21.  fermat_mersenne_dual   Fₙ and Mₚ are field duals          *)
(*   22.  refined_conjecture     all facts in one theorem             *)
(* ================================================================= *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Import Nat.

(* ================================================================= *)
(*  SECTION 0 — SHARED INFRASTRUCTURE                                *)
(* ================================================================= *)

Definition is_stable (n : nat) : Prop :=
  n mod 3 <> 0 /\ (n mod 4 = 1 \/ n mod 4 = 3).

Definition divides (d n : nat) : Prop := exists k, n = d * k.

Definition is_prime (p : nat) : Prop :=
  p >= 2 /\ forall d, divides d p -> d = 1 \/ d = p.

(* ================================================================= *)
(*  SECTION 1 — THE ORTHOGONAL AXES                                   *)
(* ================================================================= *)

Theorem axes_orthogonal : Nat.gcd 3 4 = 1.
Proof. reflexivity. Qed.

(* CRT infrastructure: mod 12 encodes both mod 3 and mod 4 *)
Lemma crt3 : forall n, n mod 3 = (n mod 12) mod 3.
Proof.
  intro n.
  pose proof (div_mod n 12 (ltac:(lia))) as Hn.
  set (q := n/12) in Hn. set (r := n mod 12) in *.
  assert (n = 3*(4*q) + r) by lia.
  rewrite H, Div0.add_mod, (mul_comm 3 (4*q)),
          Div0.mod_mul, add_0_l. apply Div0.mod_mod.
Qed.

Lemma crt4 : forall n, n mod 4 = (n mod 12) mod 4.
Proof.
  intro n.
  pose proof (div_mod n 12 (ltac:(lia))) as Hn.
  set (q := n/12) in Hn. set (r := n mod 12) in *.
  assert (n = 4*(3*q) + r) by lia.
  rewrite H, Div0.add_mod, (mul_comm 4 (3*q)),
          Div0.mod_mul, add_0_l. apply Div0.mod_mod.
Qed.

Theorem crt_unique : forall r s, r < 12 -> s < 12 ->
  r mod 3 = s mod 3 -> r mod 4 = s mod 4 -> r = s.
Proof.
  intros r s Hr Hs H3 H4.
  pose proof (div_mod r 3 (ltac:(lia))).
  pose proof (div_mod r 4 (ltac:(lia))).
  pose proof (div_mod s 3 (ltac:(lia))).
  pose proof (div_mod s 4 (ltac:(lia))).
  pose proof (mod_upper_bound r 3 (ltac:(lia))).
  pose proof (mod_upper_bound r 4 (ltac:(lia))).
  pose proof (mod_upper_bound s 3 (ltac:(lia))).
  pose proof (mod_upper_bound s 4 (ltac:(lia))).
  assert (r/3 < 4) by (apply Div0.div_lt_upper_bound; lia).
  assert (r/4 < 3) by (apply Div0.div_lt_upper_bound; lia).
  assert (s/3 < 4) by (apply Div0.div_lt_upper_bound; lia).
  assert (s/4 < 3) by (apply Div0.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma crt_compute : forall x r, r < 12 ->
  x mod 3 = r mod 3 -> x mod 4 = r mod 4 -> x mod 12 = r.
Proof.
  intros x r Hr H3 H4.
  apply crt_unique;
    [apply mod_upper_bound; lia | exact Hr |
     rewrite <- crt3; exact H3 | rewrite <- crt4; exact H4].
Qed.

(* ================================================================= *)
(*  SECTION 2 — POWERS OF 2: MODULAR PERIODICITY                     *)
(*                                                                   *)
(*  2 ≡ -1 mod 3, so 2^k alternates: 1 if k even, 2 if k odd        *)
(*  2^k ≡ 0 mod 4 for k ≥ 2 (since 4 | 2^k)                         *)
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

Lemma pow2_mod4_ge2 : forall k, k >= 2 -> (2^k) mod 4 = 0.
Proof.
  intros k Hk.
  assert (exists j, k = j+2) by (exists (k-2); lia).
  destruct H as [j ->]. rewrite pow_add_r.
  assert (2^j * 2^2 = 2^j * 4) by (simpl; lia).
  rewrite H. apply Div0.mod_mul.
Qed.

(* ================================================================= *)
(*  SECTION 3 — HELPER LEMMAS FOR SUBTRACTION MOD                    *)
(* ================================================================= *)

Lemma sub1_mod3 : forall x, x >= 2 -> x mod 3 = 2 -> (x-1) mod 3 = 1.
Proof.
  intros x Hx H.
  assert (exists q, x = 3*q+2) by
    (exists (x/3); rewrite (div_mod x 3) at 1; lia).
  destruct H0 as [q ->].
  assert (3*q+2-1 = 3*q+1) by lia.
  rewrite H0, Div0.add_mod, (mul_comm 3 q), Div0.mod_mul. reflexivity.
Qed.

Lemma sub1_mod4 : forall x, x >= 4 -> x mod 4 = 0 -> (x-1) mod 4 = 3.
Proof.
  intros x Hx H.
  assert (exists q, x = 4*q) by
    (exists (x/4); rewrite (div_mod x 4) at 1; lia).
  destruct H0 as [q ->].
  assert (Hq : q >= 1) by lia.
  assert (4*q-1 = 4*(q-1)+3) by lia.
  rewrite H0, Div0.add_mod, (mul_comm 4 (q-1)), Div0.mod_mul. reflexivity.
Qed.

(* ================================================================= *)
(*  SECTION 4 — FERMAT NUMBERS Fₙ = 2^(2^n) + 1                     *)
(* ================================================================= *)

Lemma pow2_even : forall n, n >= 1 -> exists k, 2^n = 2*k.
Proof.
  intros n Hn. exists (2^(n-1)).
  rewrite <- pow_succ_r; [f_equal; lia | lia].
Qed.

Lemma fermat_exp_ge2 : forall n, n >= 1 -> 2^n >= 2.
Proof.
  intros n Hn. induction n as [|n IHn].
  - lia.
  - simpl. destruct n.
    + simpl. lia.
    + assert (2^(S n) >= 2) by (apply IHn; lia). lia.
Qed.

(* ★ 2^(2^n) ≡ 1 mod 3 for n ≥ 1 *)
Theorem fermat_mod3 : forall n, n >= 1 -> (2^(2^n)) mod 3 = 1.
Proof.
  intros n Hn.
  destruct (pow2_even n Hn) as [k Hk].
  rewrite Hk. apply pow2_mod3_even.
Qed.

(* ★ 2^(2^n) ≡ 0 mod 4 for n ≥ 1 *)
Theorem fermat_mod4 : forall n, n >= 1 -> (2^(2^n)) mod 4 = 0.
Proof.
  intros n Hn. apply pow2_mod4_ge2. apply fermat_exp_ge2. exact Hn.
Qed.

(* ★★ Fₙ ≡ 5 mod 12 for n ≥ 1 *)
Theorem fermat_mod12 : forall n, n >= 1 -> (2^(2^n) + 1) mod 12 = 5.
Proof.
  intros n Hn.
  apply crt_compute; [lia | | ].
  - rewrite Div0.add_mod, fermat_mod3; [reflexivity | exact Hn].
  - rewrite Div0.add_mod, fermat_mod4; [reflexivity | exact Hn].
Qed.

(* ================================================================= *)
(*  SECTION 5 — MERSENNE NUMBERS Mₚ = 2^p - 1                       *)
(* ================================================================= *)

(* ★★ Mₚ ≡ 7 mod 12 for odd primes p ≥ 3 *)
Theorem mersenne_mod12 : forall p,
  p >= 3 -> p mod 2 = 1 -> (2^p - 1) mod 12 = 7.
Proof.
  intros p Hp Hodd.
  assert (Hbig : 2^p >= 8).
  { apply Nat.le_trans with (2^3); [reflexivity |
    apply Nat.pow_le_mono_r; lia]. }
  (* Express p = 2k+1 *)
  assert (exists k, p = 2*k+1) by
    (exists (p/2); pose proof (div_mod p 2 (ltac:(lia))); lia).
  destruct H as [k ->].
  assert (H3 : (2^(2*k+1)) mod 3 = 2) by apply pow2_mod3_odd.
  assert (H4 : (2^(2*k+1)) mod 4 = 0) by (apply pow2_mod4_ge2; lia).
  apply crt_compute; [lia | | ].
  - apply sub1_mod3; [lia | exact H3].
  - apply sub1_mod4; [lia | exact H4].
Qed.

(* ================================================================= *)
(*  SECTION 6 — AXIAL POSITIONS IN ℤ/3ℤ × ℤ/4ℤ                      *)
(* ================================================================= *)

Definition axial_pos (n : nat) : nat * nat := (n mod 3, n mod 4).

(* Fermat primes at (2,1) — attractor-negative, vacuum-stable *)
Theorem fermat_axial_pos : forall n, n >= 1 ->
  axial_pos (2^(2^n) + 1) = (2, 1).
Proof.
  intros n Hn. unfold axial_pos.
  assert (Hm3 : (2^(2^n)+1) mod 3 = 2).
  { rewrite Div0.add_mod, fermat_mod3; [reflexivity | exact Hn]. }
  assert (Hm4 : (2^(2^n)+1) mod 4 = 1).
  { rewrite Div0.add_mod, fermat_mod4; [reflexivity | exact Hn]. }
  rewrite Hm3, Hm4. reflexivity.
Qed.

(* Mersenne primes at (1,3) — attractor-positive, vacuum-charged *)
Theorem mersenne_axial_pos : forall p,
  p >= 3 -> p mod 2 = 1 ->
  axial_pos (2^p - 1) = (1, 3).
Proof.
  intros p Hp Hodd. unfold axial_pos.
  assert (Hbig : 2^p >= 8).
  { apply Nat.le_trans with (2^3); [reflexivity |
    apply Nat.pow_le_mono_r; lia]. }
  assert (exists k, p = 2*k+1) by
    (exists (p/2); pose proof (div_mod p 2 (ltac:(lia))); lia).
  destruct H as [k ->].
  assert (H3 : (2^(2*k+1)) mod 3 = 2) by apply pow2_mod3_odd.
  assert (H4 : (2^(2*k+1)) mod 4 = 0) by (apply pow2_mod4_ge2; lia).
  rewrite sub1_mod3, sub1_mod4; [reflexivity | lia | exact H4 | lia | exact H3].
Qed.

(* ================================================================= *)
(*  SECTION 7 — AXIAL SYMMETRY                                        *)
(*                                                                   *)
(*  The reflection σ : (a,b) ↦ ((3-a) mod 3, (4-b) mod 4)          *)
(*  maps the Fermat position (2,1) to the Mersenne position (1,3)    *)
(*  and vice versa. They are field duals.                             *)
(* ================================================================= *)

Definition reflect3 (a : nat) : nat := (3 - a mod 3) mod 3.
Definition reflect4 (b : nat) : nat := (4 - b mod 4) mod 4.

Theorem fermat_reflects_to_mersenne :
  (reflect3 2, reflect4 1) = (1, 3).
Proof. unfold reflect3, reflect4. reflexivity. Qed.

Theorem mersenne_reflects_to_fermat :
  (reflect3 1, reflect4 3) = (2, 1).
Proof. unfold reflect3, reflect4. reflexivity. Qed.

(* ★★ The two positions are exact reflections of each other *)
Theorem axial_symmetry :
  (reflect3 (fst (2,1)), reflect4 (snd (2,1))) = (1,3) /\
  (reflect3 (fst (1,3)), reflect4 (snd (1,3))) = (2,1).
Proof.
  simpl. unfold reflect3, reflect4. split; reflexivity.
Qed.

(* ================================================================= *)
(*  SECTION 8 — AXIAL DISTANCE AND MINIMALITY                        *)
(*                                                                   *)
(*  d(n) = circle-distance to attractor axis + circle-distance       *)
(*         to vacuum axis                                             *)
(*  d(5) = d(7) = 2: both positions achieve the minimum              *)
(* ================================================================= *)

Definition dist3 (n : nat) : nat :=
  let r := n mod 3 in if r <=? 1 then r else 3 - r.

Definition dist4 (n : nat) : nat :=
  let r := n mod 4 in if r <=? 2 then r else 4 - r.

Definition axial_distance (n : nat) : nat := dist3 n + dist4 n.

Theorem fermat_axial_dist : axial_distance 5 = 2.
Proof. unfold axial_distance, dist3, dist4. reflexivity. Qed.

Theorem mersenne_axial_dist : axial_distance 7 = 2.
Proof. unfold axial_distance, dist3, dist4. reflexivity. Qed.

(* All stable residues have axial distance ≥ 2 *)
Theorem axial_dist_minimum : forall r, r < 12 ->
  (r mod 3 <> 0 /\ (r mod 4 = 1 \/ r mod 4 = 3)) ->
  axial_distance r >= 2.
Proof.
  intros r Hr [H3 H4].
  unfold axial_distance, dist3, dist4.
  pose proof (mod_upper_bound r 3 (ltac:(lia))) as Ub3.
  pose proof (mod_upper_bound r 4 (ltac:(lia))) as Ub4.
  assert (Hm3v : r mod 3 = 1 \/ r mod 3 = 2) by lia.
  destruct H4 as [H4|H4]; destruct Hm3v as [Hv|Hv];
  rewrite Hv, H4; simpl; lia.
Qed.

(* ================================================================= *)
(*  SECTION 9 — STABILITY                                            *)
(* ================================================================= *)

Theorem fermat_stable : forall n, n >= 1 ->
  is_stable (2^(2^n) + 1).
Proof.
  intros n Hn.
  unfold is_stable.
  assert (Hm3 : (2^(2^n)+1) mod 3 = 2).
  { rewrite Div0.add_mod, fermat_mod3; [reflexivity | exact Hn]. }
  assert (Hm4 : (2^(2^n)+1) mod 4 = 1).
  { rewrite Div0.add_mod, fermat_mod4; [reflexivity | exact Hn]. }
  split.
  - rewrite Hm3. lia.
  - left. exact Hm4.
Qed.

Theorem mersenne_stable : forall p,
  p >= 3 -> p mod 2 = 1 -> is_stable (2^p - 1).
Proof.
  intros p Hp Hodd.
  assert (Hbig : 2^p >= 8).
  { apply Nat.le_trans with (2^3); [reflexivity |
    apply Nat.pow_le_mono_r; lia]. }
  assert (exists k, p = 2*k+1) by
    (exists (p/2); pose proof (div_mod p 2 (ltac:(lia))); lia).
  destruct H as [k ->].
  assert (H3 : (2^(2*k+1)) mod 3 = 2) by apply pow2_mod3_odd.
  assert (H4 : (2^(2*k+1)) mod 4 = 0) by (apply pow2_mod4_ge2; lia).
  unfold is_stable.
  split.
  - rewrite sub1_mod3; [lia | lia | exact H3].
  - right. apply sub1_mod4; [lia | exact H4].
Qed.

(* ================================================================= *)
(*  SECTION 10 — PRIMALITY LIVES IN THE INTERIOR                     *)
(* ================================================================= *)

Theorem primality_interior : forall p,
  is_prime p -> p > 3 ->
  p mod 3 <> 0 /\ (p mod 4 = 1 \/ p mod 4 = 3).
Proof.
  intros p [Hge Hdvd] Hgt.
  split.
  - intro H0.
    assert (Hdvd3 : divides 3 p).
    { exists (p/3). rewrite (div_mod p 3 (ltac:(lia))) at 1. lia. }
    destruct (Hdvd 3 Hdvd3); lia.
  - pose proof (mod_upper_bound p 4 (ltac:(lia))) as Hb4.
    remember (p mod 4) as r.
    assert (Hr : r=0\/r=1\/r=2\/r=3) by lia.
    destruct Hr as [H|[H|[H|H]]].
    + exfalso.
      assert (Hdvd2 : divides 2 p).
      { exists (p/4*2). rewrite (div_mod p 4 (ltac:(lia))) at 1. lia. }
      destruct (Hdvd 2 Hdvd2); lia.
    + left. exact H.
    + exfalso.
      assert (Hdvd2 : divides 2 p).
      { exists (p/4*2+1). rewrite (div_mod p 4 (ltac:(lia))) at 1. lia. }
      destruct (Hdvd 2 Hdvd2); lia.
    + right. exact H.
Qed.

(* ★ Fermat-Mersenne Duality                                         *)
(* If both are prime, their axial positions are field reflections    *)
Theorem fermat_mersenne_dual : forall n p,
  n >= 1 -> p >= 3 -> p mod 2 = 1 ->
  (reflect3 (fst (axial_pos (2^(2^n)+1))),
   reflect4 (snd (axial_pos (2^(2^n)+1)))) =
  axial_pos (2^p - 1).
Proof.
  intros n p Hn Hp Hodd.
  rewrite fermat_axial_pos; [| exact Hn].
  rewrite mersenne_axial_pos; [| exact Hp | exact Hodd].
  unfold reflect3, reflect4. reflexivity.
Qed.

(* ================================================================= *)
(*  SECTION 11 — THE REFINED CONJECTURE (all verified facts)         *)
(* ================================================================= *)

Theorem refined_axial_conjecture :
  (* Axis orthogonality *)
  Nat.gcd 3 4 = 1 /\
  (* Fermat numbers occupy position 5 *)
  (forall n, n >= 1 -> (2^(2^n)+1) mod 12 = 5) /\
  (* Mersenne numbers occupy position 7 *)
  (forall p, p >= 3 -> p mod 2 = 1 -> (2^p-1) mod 12 = 7) /\
  (* Both positions achieve minimum axial distance 2 *)
  (axial_distance 5 = 2 /\ axial_distance 7 = 2) /\
  (* The positions are field reflections of each other *)
  ((reflect3 2, reflect4 1) = (1,3) /\
   (reflect3 1, reflect4 3) = (2,1)) /\
  (* Every prime > 3 lives in the open interior (is stable) *)
  (forall p, is_prime p -> p > 3 -> is_stable p) /\
  (* Fermat numbers are stable excitations *)
  (forall n, n >= 1 -> is_stable (2^(2^n)+1)) /\
  (* Mersenne numbers are stable excitations *)
  (forall p, p >= 3 -> p mod 2 = 1 -> is_stable (2^p-1)).
Proof.
  refine (conj axes_orthogonal
         (conj fermat_mod12
         (conj mersenne_mod12
         (conj (conj fermat_axial_dist mersenne_axial_dist)
         (conj (conj fermat_reflects_to_mersenne mersenne_reflects_to_fermat)
         (conj _ (conj fermat_stable mersenne_stable))))))).
  intros p Hp Hgt.
  unfold is_stable.
  exact (primality_interior p Hp Hgt).
Qed.

(* ================================================================= *)
(*  SECTION 12 — VERIFY ZERO AXIOMS                                  *)
(* ================================================================= *)

Print Assumptions fermat_mod12.
Print Assumptions mersenne_mod12.
Print Assumptions axial_symmetry.
Print Assumptions fermat_mersenne_dual.
Print Assumptions refined_axial_conjecture.

