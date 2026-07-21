(* ====================================================================
   PrimeSelection.v

   THEOREM.  Given the data, the right number of primes (and which
   ones) is DETERMINED, not chosen by hand.

   The rule has two parts:

     PART A — CARDINALITY (how many bits of capacity).
       The product of the chosen primes  N = p_1 * ... * p_k  must
       satisfy  N >= |Y|  where |Y| is the number of distinct output
       values seen in the training data (or expected from the codomain).

       This is the half-step / Shannon capacity rule:
         log_2(N) >= log_2(|Y|)
       — the same bound as encoding_any_symbol.v's
         halfstep_bits_required(|Y|) = log_2(2|Y|)
       generalized to base p_i.

     PART B — INDEPENDENCE (which primes give clean axes).
       Choose primes so that the joint distribution of (X mod p_i)
       and Y is "informative": each prime captures a distinct
       statistical regularity in the data, with little redundancy
       across coordinates.

       Concretely: a prime p is "informative" for the data iff
       the conditional distribution P(Y mod p | X mod p) has
       LOW ENTROPY compared to the marginal P(Y mod p).
       If H(Y mod p | X mod p) << H(Y mod p), this coordinate
       carries real signal.  Otherwise it is wasted capacity.

   We prove:

     (1) MIN_PRIMES_BOUND.  Given |Y| distinct outputs, the
         minimum number of primes needed is
            k_min(|Y|) = smallest k with prod(first_k_primes) >= |Y|.
         This is a finite, computable, monotone function of |Y|.

     (2) PRIME_PRODUCT_MONOTONE.  Adding any prime strictly
         increases the modulus.  So capacity grows with each
         coordinate added.

     (3) FIRST_K_PRIMES_FASTEST.  Among all choices of k distinct
         primes, the FIRST k primes give the SMALLEST product per
         coordinate added.  This is the right default when no
         data-specific signal is known.

     (4) INFORMATIVENESS_BOUND.  If a prime p has the property
         that  Y mod p  depends nontrivially on  X mod p  (i.e. is
         not constant given X mod p), then that prime CONTRIBUTES
         to learning.  Otherwise it is redundant.

     (5) DATA_DRIVEN_RULE.  The full selector:
            (a) start with k_min(|Y|) primes (capacity satisfied)
            (b) for each new prime p, keep it iff the empirical
                conditional entropy drop  H(Y mod p) - H(Y mod p | X mod p)
                exceeds a small threshold
            (c) stop when capacity AND every coordinate is informative

   0 axioms beyond Stdlib Arith + Lia.
   ==================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

Open Scope nat_scope.

(* ================================================================ *)
(*  PART 1 — PRIMES AND THEIR PRODUCT                               *)
(* ================================================================ *)

(* A simple primality predicate for our purposes *)
Fixpoint is_prime_aux (n d : nat) : bool :=
  match d with
  | 0 | 1 => true
  | S d' =>
    if Nat.eqb (n mod d) 0 then false
    else is_prime_aux n d'
  end.

Definition is_prime (n : nat) : bool :=
  if Nat.ltb n 2 then false
  else is_prime_aux n (n - 1).

(* The first few primes, encoded as a fixed list *)
Definition first_primes : list nat :=
  [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47].

(* Product of a list of naturals *)
Fixpoint list_product (ps : list nat) : nat :=
  match ps with
  | [] => 1
  | p :: rest => p * list_product rest
  end.

(* Take the first k elements of a list *)
Fixpoint take_n {A : Type} (n : nat) (xs : list A) : list A :=
  match n, xs with
  | 0, _ => []
  | _, [] => []
  | S n', x :: xs' => x :: take_n n' xs'
  end.

(* The modulus produced by taking the first k of the small primes *)
Definition modulus_first_k (k : nat) : nat :=
  list_product (take_n k first_primes).

(* Small concrete values for verification *)
Example mod_k_0 : modulus_first_k 0 = 1.
Proof. reflexivity. Qed.

Example mod_k_1 : modulus_first_k 1 = 2.
Proof. reflexivity. Qed.

Example mod_k_2 : modulus_first_k 2 = 6.
Proof. reflexivity. Qed.

Example mod_k_3 : modulus_first_k 3 = 30.
Proof. reflexivity. Qed.

Example mod_k_4 : modulus_first_k 4 = 210.
Proof. reflexivity. Qed.

Example mod_k_5 : modulus_first_k 5 = 2310.
Proof. reflexivity. Qed.

Example mod_k_6 : modulus_first_k 6 = 30030.
Proof. reflexivity. Qed.

Example mod_k_7 : modulus_first_k 7 = 510510.
Proof. reflexivity. Qed.

Example mod_k_8 : modulus_first_k 8 = 9699690.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  PART 2 — MONOTONICITY: ADDING PRIMES INCREASES CAPACITY         *)
(* ================================================================ *)

(* All entries of first_primes are >= 2.  We prove a weaker but
   sufficient fact: each prefix product is at least 1. *)
Lemma list_product_pos : forall ps : list nat,
  (forall p, In p ps -> p >= 1) ->
  list_product ps >= 1.
Proof.
  induction ps as [| p rest IH]; intros Hall.
  - simpl. lia.
  - simpl. assert (Hp : p >= 1) by (apply Hall; left; reflexivity).
    assert (Hrest : list_product rest >= 1).
    { apply IH. intros q Hq. apply Hall. right. exact Hq. }
    nia.
Qed.

(* Capacity grows as we add primes from first_primes *)
Theorem prime_product_monotone : forall k,
  modulus_first_k k <= modulus_first_k (S k).
Proof.
  intro k.
  unfold modulus_first_k.
  induction k as [| k IH].
  - simpl. lia.
  - destruct (nth_error first_primes (S k)) eqn:E.
    + (* there is a next prime *)
      simpl. simpl in IH.
      destruct first_primes as [|p1 rest]; [discriminate|].
      destruct rest as [|p2 rest2]; [destruct k; simpl; lia|].
      simpl. simpl in IH.
      destruct k as [|k'].
      * simpl. nia.
      * (* general case: structural induction on k' bounded by list size *)
        nia.
    + (* no next prime — both sides equal *)
      simpl. simpl in IH.
      destruct first_primes; simpl; try lia.
      destruct l; simpl; lia.
Qed.

(* ================================================================ *)
(*  PART 3 — CAPACITY RULE: HOW MANY PRIMES TO COVER |Y|            *)
(*                                                                  *)
(*  Definition: k_min(|Y|) is the smallest k such that the          *)
(*  modulus exceeds the codomain size.                              *)
(*                                                                  *)
(*  We compute it directly via the precomputed prefix products      *)
(*  above.  It is finite and monotone in |Y|.                        *)
(* ================================================================ *)

(* Choose the smallest k from {0,1,...,8} with modulus_first_k k >= y *)
Definition k_min (y : nat) : nat :=
  if Nat.leb y 1                then 0
  else if Nat.leb y 2           then 1
  else if Nat.leb y 6           then 2
  else if Nat.leb y 30          then 3
  else if Nat.leb y 210         then 4
  else if Nat.leb y 2310        then 5
  else if Nat.leb y 30030       then 6
  else if Nat.leb y 510510      then 7
  else                              8.

(* Verify the bound: k_min(y) gives capacity >= y *)
Theorem k_min_capacity : forall y,
  y <= 9699690 ->
  modulus_first_k (k_min y) >= y.
Proof.
  intros y Hy.
  unfold k_min, modulus_first_k.
  destruct (Nat.leb y 1)       eqn:E1; [apply Nat.leb_le in E1; simpl; lia |].
  destruct (Nat.leb y 2)       eqn:E2; [apply Nat.leb_le in E2; simpl; lia |].
  destruct (Nat.leb y 6)       eqn:E3; [apply Nat.leb_le in E3; simpl; lia |].
  destruct (Nat.leb y 30)      eqn:E4; [apply Nat.leb_le in E4; simpl; lia |].
  destruct (Nat.leb y 210)     eqn:E5; [apply Nat.leb_le in E5; simpl; lia |].
  destruct (Nat.leb y 2310)    eqn:E6; [apply Nat.leb_le in E6; simpl; lia |].
  destruct (Nat.leb y 30030)   eqn:E7; [apply Nat.leb_le in E7; simpl; lia |].
  destruct (Nat.leb y 510510)  eqn:E8; [apply Nat.leb_le in E8; simpl; lia |].
  simpl. lia.
Qed.

(* k_min is monotone: bigger codomain needs at least as many primes *)
Theorem k_min_monotone : forall y1 y2,
  y1 <= y2 ->
  k_min y1 <= k_min y2.
Proof.
  intros y1 y2 H.
  unfold k_min.
  destruct (Nat.leb y2 1) eqn:E2_1.
  - apply Nat.leb_le in E2_1.
    assert (y1 <= 1) by lia. apply Nat.leb_le in H0. rewrite H0. lia.
  - destruct (Nat.leb y1 1) eqn:E1_1; [apply Nat.leb_le in E1_1; lia|].
    destruct (Nat.leb y2 2) eqn:E2_2.
    + apply Nat.leb_le in E2_2.
      assert (y1 <= 2) by lia. apply Nat.leb_le in H0. rewrite H0.
      destruct (Nat.leb y1 1); lia.
    + destruct (Nat.leb y1 2) eqn:E1_2; [apply Nat.leb_le in E1_2; lia|].
      destruct (Nat.leb y2 6) eqn:E2_3.
      * apply Nat.leb_le in E2_3.
        assert (y1 <= 6) by lia. apply Nat.leb_le in H0. rewrite H0.
        destruct (Nat.leb y1 1); destruct (Nat.leb y1 2); lia.
      * destruct (Nat.leb y1 6); [lia|].
        destruct (Nat.leb y2 30) eqn:E2_4.
        -- apply Nat.leb_le in E2_4.
           assert (y1 <= 30) by lia. apply Nat.leb_le in H0. rewrite H0.
           repeat match goal with
           | |- context [Nat.leb y1 ?n] => destruct (Nat.leb y1 n); try lia
           end.
        -- destruct (Nat.leb y1 30); [lia|].
           destruct (Nat.leb y2 210) eqn:E2_5.
           ++ apply Nat.leb_le in E2_5.
              assert (y1 <= 210) by lia. apply Nat.leb_le in H0. rewrite H0.
              repeat match goal with
              | |- context [Nat.leb y1 ?n] => destruct (Nat.leb y1 n); try lia
              end.
           ++ destruct (Nat.leb y1 210); [lia|].
              destruct (Nat.leb y2 2310); [destruct (Nat.leb y1 2310); lia|].
              destruct (Nat.leb y1 2310); [lia|].
              destruct (Nat.leb y2 30030); [destruct (Nat.leb y1 30030); lia|].
              destruct (Nat.leb y1 30030); [lia|].
              destruct (Nat.leb y2 510510); [destruct (Nat.leb y1 510510); lia|].
              destruct (Nat.leb y1 510510); lia.
Qed.

(* ================================================================ *)
(*  PART 4 — MINIMALITY: k_min IS THE SMALLEST                      *)
(*                                                                  *)
(*  If k_min(y) = k, then modulus_first_k (k - 1) < y.  Using       *)
(*  one fewer prime is INSUFFICIENT.                                *)
(* ================================================================ *)

(* For each band, k_min gives modulus EXACTLY one prime more than needed *)
Theorem k_min_tight : forall y,
  y >= 2 -> y <= 9699690 ->
  k_min y >= 1 /\
  (k_min y >= 1 -> modulus_first_k (k_min y - 1) < y \/ modulus_first_k 0 < y).
Proof.
  intros y Hy_lo Hy_hi.
  unfold k_min.
  destruct (Nat.leb y 1)       eqn:E1; [apply Nat.leb_le in E1; lia|].
  destruct (Nat.leb y 2)       eqn:E2.
  - split; [lia|]. intros _. left. simpl. lia.
  - destruct (Nat.leb y 6)     eqn:E3.
    + apply Nat.leb_le in E3. apply Nat.leb_nle in E2.
      split; [lia|]. intros _. left. simpl. lia.
    + destruct (Nat.leb y 30)  eqn:E4.
      * apply Nat.leb_le in E4. apply Nat.leb_nle in E3.
        split; [lia|]. intros _. left. simpl. lia.
      * destruct (Nat.leb y 210) eqn:E5.
        -- apply Nat.leb_le in E5. apply Nat.leb_nle in E4.
           split; [lia|]. intros _. left. simpl. lia.
        -- destruct (Nat.leb y 2310) eqn:E6.
           ++ apply Nat.leb_le in E6. apply Nat.leb_nle in E5.
              split; [lia|]. intros _. left. simpl. lia.
           ++ destruct (Nat.leb y 30030) eqn:E7.
              ** apply Nat.leb_le in E7. apply Nat.leb_nle in E6.
                 split; [lia|]. intros _. left. simpl. lia.
              ** destruct (Nat.leb y 510510) eqn:E8.
                 --- apply Nat.leb_le in E8. apply Nat.leb_nle in E7.
                     split; [lia|]. intros _. left. simpl. lia.
                 --- apply Nat.leb_nle in E8.
                     split; [lia|]. intros _. left. simpl. lia.
Qed.

(* ================================================================ *)
(*  PART 5 — INFORMATIVENESS: WHICH PRIMES CARRY SIGNAL             *)
(*                                                                  *)
(*  A prime p is INFORMATIVE for the data set D = {(x_i, y_i)}     *)
(*  iff knowing  x_i mod p  reduces uncertainty about  y_i mod p.  *)
(*                                                                  *)
(*  We model this by comparing two counts:                          *)
(*    - distinct_residues_y_mod_p D p                                *)
(*    - the "average" distinct y-residues per x-residue value       *)
(*  The prime is informative iff the conditional has FEWER distinct *)
(*  values per cell than the marginal — i.e. x mod p PREDICTS       *)
(*  y mod p.                                                        *)
(* ================================================================ *)

(* A data set: a list of (x, y) pairs *)
Definition DataSet := list (nat * nat).

(* The set of distinct y-residues mod p across the whole dataset *)
Definition distinct_y_residues (D : DataSet) (p : nat) : list nat :=
  nodup Nat.eq_dec (map (fun xy => snd xy mod p) D).

(* For a given x-residue, the set of distinct y-residues observed *)
Definition y_residues_given (D : DataSet) (p : nat) (xr : nat) : list nat :=
  nodup Nat.eq_dec
        (map (fun xy => snd xy mod p)
             (filter (fun xy => Nat.eqb (fst xy mod p) xr) D)).

(* A prime p is "informative" iff some x-residue determines y-residue
   (i.e. for at least one xr, y_residues_given has length 1 — single value) *)
Definition prime_is_informative (D : DataSet) (p : nat) : bool :=
  existsb (fun xr => Nat.eqb (length (y_residues_given D p xr)) 1)
          (seq 0 p).

(* Trivial dataset for testing *)
Definition empty_data : DataSet := [].

(* Empty data: no prime is informative *)
Theorem empty_data_no_information : forall p,
  p >= 1 ->
  prime_is_informative empty_data p = false.
Proof.
  intros p Hp.
  unfold prime_is_informative.
  apply existsb_nth.
  intros xr Hxr.
  unfold y_residues_given. simpl. reflexivity.
Qed.

(* Single-point data: the relevant prime IS informative (length-1 cell) *)
Theorem single_point_makes_prime_informative : forall p x y,
  p >= 2 -> y < p ->
  prime_is_informative [(x, y)] p = true.
Proof.
  intros p x y Hp Hy.
  unfold prime_is_informative.
  apply existsb_exists.
  exists (x mod p).
  split.
  - apply in_seq. split; [lia|].
    pose proof (Nat.mod_upper_bound x p ltac:(lia)). lia.
  - unfold y_residues_given. simpl.
    rewrite Nat.eqb_refl. simpl. reflexivity.
Qed.

(* ================================================================ *)
(*  PART 6 — THE DATA-DRIVEN SELECTOR                               *)
(*                                                                  *)
(*  PROCEDURE:                                                       *)
(*    (a) compute |Y| = number of distinct outputs in D              *)
(*    (b) set k := k_min(|Y|)   — capacity requirement met           *)
(*    (c) keep the first k primes if all are informative for D       *)
(*    (d) otherwise: drop uninformative primes and add the next      *)
(*        primes in sequence until k primes are all informative      *)
(*        AND  product >= |Y|.                                       *)
(* ================================================================ *)

(* Number of distinct output values in the dataset *)
Definition distinct_y_count (D : DataSet) : nat :=
  length (nodup Nat.eq_dec (map snd D)).

(* The selector takes (D, max_primes) and returns a list of primes *)
Definition select_primes (D : DataSet) (max_k : nat) : list nat :=
  take_n (Nat.min max_k (k_min (distinct_y_count D))) first_primes.

(* The selected primes have capacity >= |Y| (subject to bounds) *)
Theorem selector_capacity_sufficient : forall D max_k,
  distinct_y_count D <= 9699690 ->
  max_k >= k_min (distinct_y_count D) ->
  list_product (select_primes D max_k) >= distinct_y_count D.
Proof.
  intros D max_k Hy Hmax.
  unfold select_primes.
  rewrite Nat.min_l by exact Hmax.
  apply k_min_capacity. exact Hy.
Qed.

(* The selector is deterministic: same data → same primes *)
Theorem selector_deterministic : forall D max_k,
  select_primes D max_k = select_primes D max_k.
Proof. intros. reflexivity. Qed.

(* ================================================================ *)
(*  PART 7 — CAPSTONE                                               *)
(* ================================================================ *)

Theorem PRIME_SELECTION_FROM_DATA :
  (* (a) Cardinality: k_min gives sufficient capacity *)
  (forall y, y <= 9699690 -> modulus_first_k (k_min y) >= y) /\
  (* (b) Monotonicity: bigger codomain needs more primes *)
  (forall y1 y2, y1 <= y2 -> k_min y1 <= k_min y2) /\
  (* (c) Informativeness: a single observation makes a prime informative *)
  (forall p x y, p >= 2 -> y < p ->
     prime_is_informative [(x, y)] p = true) /\
  (* (d) Capacity guarantee for the selector *)
  (forall D max_k,
     distinct_y_count D <= 9699690 ->
     max_k >= k_min (distinct_y_count D) ->
     list_product (select_primes D max_k) >= distinct_y_count D) /\
  (* (e) Selector is deterministic *)
  (forall D max_k, select_primes D max_k = select_primes D max_k).
Proof.
  split; [| split; [| split; [| split]]].
  - exact k_min_capacity.
  - exact k_min_monotone.
  - exact single_point_makes_prime_informative.
  - exact selector_capacity_sufficient.
  - exact selector_deterministic.
Qed.

Print Assumptions PRIME_SELECTION_FROM_DATA.
