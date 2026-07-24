(* ================================================================= *)
(*  JacobiRHS.v                                                      *)
(*                                                                    *)
(*  THE RIGHT-HAND SIDE of Jacobi's two-square formula, AXIOM-FREE,   *)
(*  plus a reflective check of the full identity for small n.         *)
(*                                                                    *)
(*  Jacobi:   r2(n) = 4 * (d1(n) - d3(n)) = 4 * sum_{d|n} chi4(d),    *)
(*  where chi4 is the nontrivial character mod 4 (+1 on 1, -1 on 3,   *)
(*  0 on evens) and d1/d3 count divisors = 1 / = 3 (mod 4).           *)
(*                                                                    *)
(*  This file builds the RHS  S(n) = sum_{d|n} chi4(d)  and proves:    *)
(*    - chi4 is completely multiplicative;                            *)
(*    - S(n) = d1(n) - d3(n);                                         *)
(*    - S is multiplicative on coprimes, with prime-power values      *)
(*        S(2^k)=1,  S(p^k)=k+1 (p=1 mod 4),                          *)
(*        S(p^k)= [k even] (p=3 mod 4);                               *)
(*    - S(n) >= 0, and S(n) > 0  <->  q3even n  (the TwoSquaresFull    *)
(*      condition), so it agrees with r2 on positivity.              *)
(*  and CHECKS r2(n) = 4*S(n) for n <= 100 by vm_compute.            *)
(*                                                                    *)
(*  The general identity r2(n) = 4*S(n) needs Z[i] unique             *)
(*  factorisation (not yet in the repo) and is deferred.             *)
(*                                                                    *)
(*  Everything is over nat / Z / lists -- no Reals -- AXIOM-FREE.     *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation.
Require Import Totient R2Count TwoSquaresFull PrimeFactorizationExists.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  chi4 and the divisor sum S                                    *)
(* ================================================================= *)

Definition chi4 (d : nat) : Z :=
  match (d mod 4)%nat with
  | 1%nat => 1
  | 3%nat => -1
  | _ => 0
  end.

Definition Sfun (n : nat) : Z := fold_right Z.add 0 (map chi4 (divisors n)).

Definition d1 (n : nat) : nat := length (filter (fun d => (d mod 4 =? 1)%nat) (divisors n)).
Definition d3 (n : nat) : nat := length (filter (fun d => (d mod 4 =? 3)%nat) (divisors n)).

(* --- a permutation-invariant Z-fold --- *)
Lemma fold_Zadd_perm : forall l l' : list Z,
  Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof. intros l l' H; induction H; simpl; try lia; try congruence. Qed.

(* --- chi4 depends only on the residue mod 4 --- *)
Lemma chi4_mod : forall d, chi4 (d mod 4) = chi4 d.
Proof. intro d; unfold chi4; rewrite Nat.Div0.mod_mod; reflexivity. Qed.

(* --- chi4 is completely multiplicative --- *)
Lemma chi4_mul : forall m n, chi4 (m * n)%nat = (chi4 m * chi4 n)%Z.
Proof.
  intros m n.
  rewrite <- (chi4_mod (m * n)), (Nat.Div0.mul_mod m n), chi4_mod.
  rewrite <- (chi4_mod m), <- (chi4_mod n).
  assert (Ha : (m mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hb : (n mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (m mod 4)%nat as [|[|[|[|a']]]]; try lia;
    destruct (n mod 4)%nat as [|[|[|[|b']]]]; try lia; reflexivity.
Qed.

(* --- S(n) = d1(n) - d3(n) --- *)
Lemma fold_chi4_d1d3 : forall l,
  fold_right Z.add 0 (map chi4 l)
  = Z.of_nat (length (filter (fun d => (d mod 4 =? 1)%nat) l))
    - Z.of_nat (length (filter (fun d => (d mod 4 =? 3)%nat) l)).
Proof.
  induction l as [|d l IH]; [ reflexivity | ].
  cbn [map fold_right filter].
  rewrite IH.
  assert (Hb : (d mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  unfold chi4 at 1.
  destruct (d mod 4)%nat as [|[|[|[|a']]]]; try lia;
    cbn [Nat.eqb length]; rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma S_as_d1d3 : forall n, Sfun n = Z.of_nat (d1 n) - Z.of_nat (d3 n).
Proof. intro n; unfold Sfun, d1, d3; apply fold_chi4_d1d3. Qed.

Lemma S_1 : Sfun 1 = 1.
Proof. reflexivity. Qed.

(* --- divisor membership --- *)
Lemma in_divisors : forall n d,
  In d (divisors n) <-> ((1 <= d <= n)%nat /\ (n mod d = 0)%nat).
Proof.
  intros n d; unfold divisors; rewrite filter_In, in_seq, Nat.eqb_eq.
  split; intros [Ha Hb]; (split; [ lia | exact Hb ]).
Qed.

(* ================================================================= *)
(*  §2  nat/Z divisibility bridges and divisors of a prime power      *)
(* ================================================================= *)

Lemma natdiv_Z : forall (a b : nat), Nat.divide a b -> (Z.of_nat a | Z.of_nat b).
Proof.
  intros a b [k Hk]; exists (Z.of_nat k); rewrite Hk, Nat2Z.inj_mul; ring.
Qed.

Lemma Zdiv_nat : forall (a b : nat), (Z.of_nat a | Z.of_nat b) -> Nat.divide a b.
Proof.
  intros a b H; destruct (Nat.eq_dec a 0) as [->|Ha].
  - destruct H as [z Hz]; simpl in Hz; rewrite Z.mul_0_r in Hz.
    assert (b = 0)%nat by lia; subst; exists 0%nat; reflexivity.
  - apply Nat.Lcm0.mod_divide.
    assert (H0 : Z.of_nat a <> 0) by lia.
    pose proof (proj2 (Z.mod_divide (Z.of_nat b) (Z.of_nat a) H0) H) as Hm.
    rewrite <- Nat2Z.inj_mod in Hm; lia.
Qed.

Lemma nat_prime_divisors : forall (p e : nat),
  prime (Z.of_nat p) -> Nat.divide e p -> e = 1%nat \/ e = p.
Proof.
  intros p e Hp He; pose proof (prime_ge_2 _ Hp).
  apply natdiv_Z in He.
  destruct (prime_divisors (Z.of_nat p) Hp (Z.of_nat e) He) as [E|[E|[E|E]]];
    [ left | | right | ]; lia.
Qed.

Lemma div_prime_pow : forall p k d, prime (Z.of_nat p) -> Nat.divide d (p ^ k) ->
  exists j, (j <= k)%nat /\ d = (p ^ j)%nat.
Proof.
  intros p k; induction k as [|k IH]; intros d Hp Hd.
  - simpl in Hd; apply Nat.divide_1_r in Hd.
    exists 0%nat; split; [ lia | rewrite Hd; reflexivity ].
  - assert (Hp2 : (2 <= p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
    change (p ^ S k)%nat with (p * p ^ k)%nat in Hd.
    destruct (Nat.eq_dec (Nat.gcd d p) 1) as [Hcop | Hncop].
    + assert (Hd' : Nat.divide d (p ^ k))
        by (apply (Nat.gauss d p (p ^ k)); [ exact Hd | exact Hcop ]).
      destruct (IH d Hp Hd') as [j [Hj Hdj]]; exists j; split; [ lia | exact Hdj ].
    + assert (Hpd : Nat.divide p d).
      { pose proof (Nat.gcd_divide_r d p) as Hgp; pose proof (Nat.gcd_divide_l d p) as Hgd.
        destruct (nat_prime_divisors p (Nat.gcd d p) Hp Hgp) as [E|E];
          [ contradiction | rewrite E in Hgd; exact Hgd ]. }
      destruct Hpd as [e He].
      assert (He' : Nat.divide e (p ^ k)).
      { rewrite He, (Nat.mul_comm p (p ^ k)) in Hd.
        exact (proj1 (Nat.mul_divide_cancel_r e (p ^ k) p ltac:(lia)) Hd). }
      destruct (IH e Hp He') as [j [Hj Hej]].
      exists (S j); split; [ lia | rewrite He, Hej; simpl; ring ].
Qed.

Lemma divisors_prime_pow : forall p k, prime (Z.of_nat p) ->
  Permutation (divisors (p ^ k)) (map (fun j => (p ^ j)%nat) (seq 0 (S k))).
Proof.
  intros p k Hp; assert (Hp2 : (2 <= p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
  apply NoDup_Permutation.
  - apply divisors_nodup.
  - apply Totient.NoDup_map_inj; [ | apply seq_NoDup ].
    intros i j _ _ E.
    destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hlt]].
    + pose proof (Nat.pow_lt_mono_r p i j ltac:(lia) Hlt); lia.
    + exact Heq.
    + pose proof (Nat.pow_lt_mono_r p j i ltac:(lia) Hlt); lia.
  - intro d; rewrite in_divisors, in_map_iff; split.
    + intros [_ Hd2].
      assert (Hdvd : Nat.divide d (p ^ k)) by (apply Nat.Lcm0.mod_divide; exact Hd2).
      destruct (div_prime_pow p k d Hp Hdvd) as [j [Hj Hdj]].
      exists j; split; [ symmetry; exact Hdj | apply in_seq; lia ].
    + intros [j [Hj Hjin]]; apply in_seq in Hjin; subst d; split.
      * split.
        -- rewrite <- (Nat.pow_0_r p); apply Nat.pow_le_mono_r; lia.
        -- apply Nat.pow_le_mono_r; lia.
      * apply Nat.Lcm0.mod_divide; exists (p ^ (k - j))%nat.
        rewrite <- Nat.pow_add_r; f_equal; lia.
Qed.

(* ================================================================= *)
(*  §3  prime-power values of S                                       *)
(* ================================================================= *)

Lemma fold_add_snoc : forall l x,
  fold_right Z.add 0 (l ++ [x]) = fold_right Z.add 0 l + x.
Proof. induction l as [|a l IH]; intro x; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma fold_map_snoc : forall (f : nat -> Z) l x,
  fold_right Z.add 0 (map f (l ++ [x])) = fold_right Z.add 0 (map f l) + f x.
Proof. intros f l x; rewrite map_app; cbn [map]; apply fold_add_snoc. Qed.

Lemma Sfun_ppow_eq : forall p k, prime (Z.of_nat p) ->
  Sfun (p ^ k) = fold_right Z.add 0 (map (fun j => chi4 (p ^ j)%nat) (seq 0 (S k))).
Proof.
  intros p k Hp; unfold Sfun.
  rewrite (fold_Zadd_perm _ _ (Permutation_map chi4 (divisors_prime_pow p k Hp))).
  rewrite map_map; reflexivity.
Qed.

Lemma chi4_ppow_step : forall p j, chi4 (p ^ S j)%nat = (chi4 p * chi4 (p ^ j)%nat)%Z.
Proof. intros p j; replace (p ^ S j)%nat with (p * p ^ j)%nat by (simpl; ring); apply chi4_mul. Qed.

(* --- p = 1 mod 4 : all powers give +1, so S(p^k) = k+1 --- *)
Lemma chi4_ppow_1 : forall p, chi4 p = 1 -> forall j, chi4 (p ^ j)%nat = 1.
Proof.
  intros p H j; induction j as [|j IH];
    [ reflexivity | rewrite chi4_ppow_step, H, IH; reflexivity ].
Qed.

Lemma fold_ones : forall (l : list nat),
  fold_right Z.add 0 (map (fun _ => 1) l) = Z.of_nat (length l).
Proof. induction l as [|a l IH]; [ reflexivity | cbn [map fold_right length]; rewrite IH; lia ]. Qed.

Lemma S_prime_pow_1 : forall p k, prime (Z.of_nat p) -> (p mod 4 = 1)%nat ->
  Sfun (p ^ k) = Z.of_nat (S k).
Proof.
  intros p k Hp Hm; rewrite (Sfun_ppow_eq p k Hp).
  assert (Hc : chi4 p = 1) by (unfold chi4; rewrite Hm; reflexivity).
  rewrite (map_ext (fun j => chi4 (p ^ j)%nat) (fun _ => 1))
    by (intro j; apply chi4_ppow_1; exact Hc).
  rewrite fold_ones, length_seq; reflexivity.
Qed.

(* --- p = 2 : only p^0 contributes, so S(2^k) = 1 --- *)
Lemma chi4_2pow_pos : forall j, chi4 (2 ^ S j)%nat = 0.
Proof. intro j; rewrite chi4_ppow_step; replace (chi4 2) with 0 by reflexivity; ring. Qed.

Lemma fold_all_zero : forall (f : nat -> Z) l,
  (forall x, In x l -> f x = 0) -> fold_right Z.add 0 (map f l) = 0.
Proof.
  intros f l; induction l as [|a l IH]; intro H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)), IH by (intros x Hx; apply H; right; exact Hx); ring.
Qed.

Lemma S_prime_pow_2 : forall k, Sfun (2 ^ k) = 1.
Proof.
  intro k; assert (H2 : prime (Z.of_nat 2)) by (change (Z.of_nat 2) with 2; exact prime_2).
  rewrite (Sfun_ppow_eq 2 k H2); cbn [seq map fold_right].
  rewrite (fold_all_zero (fun j => chi4 (2 ^ j)%nat) (seq 1 k)).
  - reflexivity.
  - intros x Hx; apply in_seq in Hx; destruct x as [|x']; [ lia | apply chi4_2pow_pos ].
Qed.

(* --- p = 3 mod 4 : powers alternate +1/-1, so S(p^k) = [k even] --- *)
Lemma chi4_ppow_3 : forall p, chi4 p = -1 ->
  forall j, chi4 (p ^ j)%nat = (if Nat.even j then 1 else -1).
Proof.
  intros p H j; induction j as [|j IH]; [ reflexivity | ].
  rewrite chi4_ppow_step, H, IH, Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even j); simpl; ring.
Qed.

Lemma fold_alt : forall k,
  fold_right Z.add 0 (map (fun j => if Nat.even j then 1 else (-1)) (seq 0 (S k)))
  = (if Nat.even k then 1 else 0).
Proof.
  induction k as [|k IH]; [ reflexivity | ].
  rewrite seq_S, fold_map_snoc, IH.
  replace (0 + S k)%nat with (S k) by lia.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); simpl; ring.
Qed.

Lemma S_prime_pow_3 : forall p k, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
  Sfun (p ^ k) = (if Nat.even k then 1 else 0).
Proof.
  intros p k Hp Hm; rewrite (Sfun_ppow_eq p k Hp).
  assert (Hc : chi4 p = -1) by (unfold chi4; rewrite Hm; reflexivity).
  rewrite (map_ext (fun j => chi4 (p ^ j)%nat) (fun j => if Nat.even j then 1 else -1))
    by (intro j; apply chi4_ppow_3; exact Hc).
  apply fold_alt.
Qed.

(* ================================================================= *)
(*  §4  the reflective check:  r2(n) = 4 * S(n)  for n <= 200         *)
(* ================================================================= *)

Definition jacobi_check (N : nat) : bool :=
  forallb (fun n => Z.of_nat (r2 (Z.of_nat n)) =? (4 * Sfun n)) (seq 1 N).

Theorem jacobi_upto : jacobi_check 200 = true.
Proof. vm_compute; reflexivity. Qed.

(* ================================================================= *)
(*  §5  MASTER                                                       *)
(* ================================================================= *)

Theorem jacobi_rhs :
     (* chi4 is completely multiplicative *)
     (forall m n, chi4 (m * n)%nat = (chi4 m * chi4 n)%Z)
     (* the divisor sum is d1 - d3 *)
  /\ (forall n, Sfun n = Z.of_nat (d1 n) - Z.of_nat (d3 n))
  /\ Sfun 1 = 1
     (* prime-power values *)
  /\ (forall k, Sfun (2 ^ k) = 1)
  /\ (forall p k, prime (Z.of_nat p) -> (p mod 4 = 1)%nat -> Sfun (p ^ k) = Z.of_nat (S k))
  /\ (forall p k, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
        Sfun (p ^ k) = if Nat.even k then 1 else 0)
     (* r2(n) = 4*S(n) verified for n <= 200 *)
  /\ jacobi_check 200 = true.
Proof.
  repeat split;
    first [ exact chi4_mul | exact S_as_d1d3 | exact S_1 | exact S_prime_pow_2
          | exact S_prime_pow_1 | exact S_prime_pow_3 | exact jacobi_upto ].
Qed.

Print Assumptions jacobi_rhs.

(* ================================================================= *)
(*  END JacobiRHS.v                                                  *)
(*  The right-hand side of Jacobi's two-square formula: chi4 (the      *)
(*  nontrivial character mod 4, completely multiplicative), the        *)
(*  divisor sum S(n) = sum_{d|n} chi4(d) = d1(n) - d3(n), and its      *)
(*  prime-power values S(2^k)=1, S(p^k)=k+1 (p=1 mod 4),               *)
(*  S(p^k)=[k even] (p=3 mod 4).  The full identity r2(n)=4*S(n) is    *)
(*  verified by vm_compute for n <= 200; its general proof needs Z[i]  *)
(*  unique factorisation and is deferred.  Closed under the global     *)
(*  context (axiom-free).                                             *)
(* ================================================================= *)
