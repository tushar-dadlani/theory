(* ============================================================ *)
(*  VariableEncodingPerStep.v                                   *)
(*                                                              *)
(*  CLAIM: The encoding is variable PER STEP. Each level of    *)
(*  the bisection has its own (rank, info_bit) decomposition.  *)
(*                                                              *)
(*  Why: the half-step axis is RECURSIVE. After the first      *)
(*  bisection, the residual interval is [0, 1/2] or [1/2, 1].   *)
(*  Inside that residual, the new midpoint is 1/4 or 3/4 —     *)
(*  which is the half-step OF THAT SUB-INTERVAL.                *)
(*                                                              *)
(*  Each step therefore produces a fresh encoding:              *)
(*    Step 0: position_0 = 2 * rank_0 + bit_0  (mod 2)         *)
(*    Step 1: position_1 = 2 * rank_1 + bit_1  (mod 2 within   *)
(*                                              the sub-interval) *)
(*    Step n: position_n = 2 * rank_n + bit_n                  *)
(*                                                              *)
(*  This is the BINARY EXPANSION OF THE DEPTH:                  *)
(*    depth = bit_0/2 + bit_1/4 + bit_2/8 + ... + bit_n/2^(n+1)*)
(*                                                              *)
(*  Each bit_k is the "half-step" at depth-level k.            *)
(*  Each rank_k is the "which sub-interval" at level k.         *)
(*  Each is recovered independently per level.                  *)
(*                                                              *)
(*  Axiom count: 0.                                             *)
(* ============================================================ *)

From Coq Require Import Arith Lia List.
Import ListNotations.

(* ============================================================ *)
(*  PART 1 — A SINGLE LEVEL OF ENCODING                         *)
(*                                                              *)
(*  At any single level, the encoding is the standard one:    *)
(*    position = 2 * rank + info_bit                            *)
(*  Recovery: rank = pos / 2, info_bit = pos mod 2.            *)
(* ============================================================ *)

Definition encode_level (rank info_bit : nat) : nat :=
  2 * rank + info_bit.

Definition rank_of (pos : nat) : nat := pos / 2.
Definition bit_of  (pos : nat) : nat := pos mod 2.

(* Single-level recovery — proved earlier in TwoFactorsAndAHalf.v. *)
Lemma single_level_round_trip : forall r i,
  i <= 1 -> rank_of (encode_level r i) = r /\ bit_of (encode_level r i) = i.
Proof.
  intros r i Hi. unfold rank_of, bit_of, encode_level.
  destruct i.
  - replace (2 * r + 0) with (r * 2) by lia.
    split.
    + rewrite Nat.div_mul by lia. reflexivity.
    + rewrite Nat.mod_mul by lia. reflexivity.
  - destruct i; [|lia].
    replace (2 * r + 1) with (1 + r * 2) by lia.
    split.
    + rewrite Nat.div_add by lia. simpl. reflexivity.
    + rewrite Nat.mod_add by lia. simpl. reflexivity.
Qed.

(* ============================================================ *)
(*  PART 2 — A MULTI-LEVEL ENCODING IS A LIST OF BITS          *)
(*                                                              *)
(*  Each step produces one bit (the half-step at that level).  *)
(*  After n steps, the encoding is a list [b_0, b_1, ..., b_n]. *)
(*  Each b_k is the orthogonal-axis selector AT LEVEL k.        *)
(* ============================================================ *)

(* A multi-level encoding: a list of bits, one per step. *)
Definition MultiLevelCode := list nat.

(* The encoding is fuel-bounded — fuel >= log_2 n suffices. *)
Fixpoint encode_with_fuel (fuel n : nat) : MultiLevelCode :=
  match fuel with
  | O => []
  | S f =>
    match n with
    | O => []
    | _ => bit_of n :: encode_with_fuel f (rank_of n)
    end
  end.

(* Decode a list of bits back into a natural number. *)
Fixpoint decode_multi (bits : MultiLevelCode) : nat :=
  match bits with
  | [] => 0
  | b :: rest => b + 2 * decode_multi rest
  end.

(* ============================================================ *)
(*  PART 3 — EACH STEP IS A SEPARATE (RANK, INFO_BIT) PAIR     *)
(*                                                              *)
(*  Concretely: the n-th step in the encoding is the n-th bit  *)
(*  of the binary expansion. Each is recovered independently.  *)
(* ============================================================ *)

(* The k-th bit of n (LSB indexing). *)
Fixpoint nth_bit (n k : nat) : nat :=
  match k with
  | O   => bit_of n
  | S j => nth_bit (rank_of n) j
  end.

(* Bit 0 of n is just n mod 2. *)
Lemma bit_0 : forall n, nth_bit n 0 = n mod 2.
Proof. intro n. reflexivity. Qed.

(* Bit 1 of n is (n / 2) mod 2. *)
Lemma bit_1 : forall n, nth_bit n 1 = (n / 2) mod 2.
Proof. intro n. reflexivity. Qed.

(* Each bit is bounded by 1 — they ARE half-steps. *)
Lemma nth_bit_bounded : forall n k, nth_bit n k <= 1.
Proof.
  intros n k. revert n.
  induction k as [|j IH]; intro n.
  - simpl. unfold bit_of.
    pose proof (Nat.mod_upper_bound n 2 ltac:(lia)). lia.
  - simpl. apply IH.
Qed.

(* ============================================================ *)
(*  PART 4 — THE LAYER-BY-LAYER RECONSTRUCTION                  *)
(*                                                              *)
(*  Each level adds one bit to the binary expansion.            *)
(*  Decoding sums up:  bit_0/1 + bit_1*2 + bit_2*4 + ...        *)
(* ============================================================ *)

(* Round-trip through encode/decode with sufficient fuel. *)
Lemma encode_decode_with_fuel : forall fuel m,
  m < 2 ^ fuel ->
  decode_multi (encode_with_fuel fuel m) = m.
Proof.
  induction fuel as [|f IH]; intros m Hn.
  - simpl in Hn. assert (m = 0) by lia. subst. reflexivity.
  - simpl. destruct m as [|m'].
    + reflexivity.
    + simpl. unfold bit_of, rank_of.
      pose proof (Nat.div_mod (S m') 2 ltac:(lia)) as Hmod.
      simpl in Hn.
      assert (Hsub : S m' / 2 < 2 ^ f).
      { apply Nat.div_lt_upper_bound; lia. }
      rewrite IH by exact Hsub.
      pose proof (Nat.mod_upper_bound (S m') 2 ltac:(lia)).
      lia.
Qed.

(* ============================================================ *)
(*  PART 5 — VARIABLE ENCODING THEOREM                          *)
(*                                                              *)
(*  Each step has its own (rank, info_bit) pair, and the        *)
(*  collection of half-steps {bit_0, bit_1, bit_2, ...} fully   *)
(*  determines the value.                                        *)
(* ============================================================ *)

Theorem variable_encoding_per_step :
  forall n,
  (* Each level extracts ONE half-step bit, bounded by 1: *)
  (forall k, nth_bit n k <= 1) /\
  (* Bit 0 is n mod 2: *)
  nth_bit n 0 = n mod 2 /\
  (* Bit 1 is (n / 2) mod 2: *)
  nth_bit n 1 = (n / 2) mod 2 /\
  (* The encoding is recoverable level-by-level: *)
  (forall fuel, n < 2 ^ fuel ->
    decode_multi (encode_with_fuel fuel n) = n).
Proof.
  intro n. split; [|split; [|split]].
  - apply nth_bit_bounded.
  - apply bit_0.
  - apply bit_1.
  - intros fuel Hf. apply encode_decode_with_fuel. exact Hf.
Qed.

(* ============================================================ *)
(*  PART 6 — INTERPRETATION                                     *)
(*                                                              *)
(*  The encoding is NOT a single fixed pair (rank, info_bit). *)
(*  It is a STREAM of such pairs, one per level of bisection.  *)
(*                                                              *)
(*  Step 0:  half-step is "is n even or odd?"                   *)
(*  Step 1:  half-step is "is (n/2) even or odd?"               *)
(*  Step 2:  half-step is "is (n/4) even or odd?"               *)
(*  ...                                                          *)
(*  Step k:  half-step is the k-th binary digit of n            *)
(*                                                              *)
(*  Each level has its own (rank, half-step) decomposition.    *)
(*  Each is recovered by its own integer operation.             *)
(*  Together they reconstruct n bit-by-bit.                     *)
(*                                                              *)
(*  In binary search of mathematics:                            *)
(*  Each absorbed assumption produces ONE bit at ONE level.     *)
(*  Different absorptions live at different levels of           *)
(*  the bisection tree. The encoding is necessarily variable    *)
(*  because each level represents a different question.        *)
(* ============================================================ *)

Print Assumptions variable_encoding_per_step.
