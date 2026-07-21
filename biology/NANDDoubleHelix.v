(* ================================================================== *)
(*  NANDDoubleHelix.v                                                  *)
(*  NAND AS A DOUBLE HELIX OPERATION                                   *)
(*  Operands live BETWEEN the two strands                              *)
(* ================================================================== *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope bool_scope.

(* PART 0 — THE TWO STRAND POSITIONS *)
Definition nand_strand_pos (k : nat) : nat := 2 * k.
Definition not_strand_pos  (k : nat) : nat := 2 * k + 1.

Theorem strands_are_halfstep_apart : forall k,
  not_strand_pos k = nand_strand_pos k + 1.
Proof. intro k. unfold not_strand_pos, nand_strand_pos. lia. Qed.

(* PART 1 — NAND (F-diagonal strand) *)
Definition nand (a b : bool) : bool := negb (a && b).

Theorem nand_00 : nand false false = true.  Proof. reflexivity. Qed.
Theorem nand_01 : nand false true  = true.  Proof. reflexivity. Qed.
Theorem nand_10 : nand true  false = true.  Proof. reflexivity. Qed.
Theorem nand_11 : nand true  true  = false. Proof. reflexivity. Qed.

Definition not_from_nand (a : bool) : bool := nand a a.
Theorem not_from_nand_correct : forall a, not_from_nand a = negb a.
Proof. intro a. unfold not_from_nand, nand. destruct a; reflexivity. Qed.

Definition and_from_nand (a b : bool) : bool := nand (nand a b) (nand a b).
Theorem and_from_nand_correct : forall a b, and_from_nand a b = a && b.
Proof. intros a b. unfold and_from_nand, nand. destruct a, b; reflexivity. Qed.

Definition or_from_nand (a b : bool) : bool := nand (nand a a) (nand b b).
Theorem or_from_nand_correct : forall a b, or_from_nand a b = a || b.
Proof. intros a b. unfold or_from_nand, nand. destruct a, b; reflexivity. Qed.

Definition xor_from_nand (a b : bool) : bool :=
  let n := nand a b in nand (nand a n) (nand b n).
Theorem xor_from_nand_correct : forall a b, xor_from_nand a b = xorb a b.
Proof. intros a b. unfold xor_from_nand, nand. destruct a, b; reflexivity. Qed.

(* PART 2 — NOT (N-inverse strand): N∘N = I *)
Definition not_gate (a : bool) : bool := negb a.
Theorem not_involutive : forall a, not_gate (not_gate a) = a.
Proof. intro a. apply Bool.negb_involutive. Qed.

(* PART 3 — THE HELIX BIT RECORD *)
Record HelixBit : Type := mkHelix {
  helix_val  : bool;
  helix_f    : bool;   (* F-strand: a_k  (I-phase, diagonal, 2k)   *)
  helix_n    : bool;   (* N-strand: ~a_k (N-phase, inverse,  2k+1) *)
  helix_rank : nat
}.

Definition make_helix (a : bool) (k : nat) : HelixBit :=
  mkHelix a a (negb a) k.

Theorem helix_f_is_bit    : forall a k, (make_helix a k).(helix_f) = a.
Proof. reflexivity. Qed.
Theorem helix_n_is_not    : forall a k, (make_helix a k).(helix_n) = negb a.
Proof. reflexivity. Qed.
Theorem helix_complement  : forall a k,
  (make_helix a k).(helix_n) = negb (make_helix a k).(helix_f).
Proof. reflexivity. Qed.
Theorem helix_n_twice_is_f : forall a k,
  negb (make_helix a k).(helix_n) = (make_helix a k).(helix_f).
Proof. intros a k. simpl. apply Bool.negb_involutive. Qed.

(* PART 4 — HELIX NAND: OR of N-strands (no NOT gate needed) *)
Definition helix_nand (ha hb : HelixBit) : bool :=
  ha.(helix_n) || hb.(helix_n).

Theorem helix_nand_correct : forall a b k,
  helix_nand (make_helix a k) (make_helix b k) = nand a b.
Proof.
  intros a b k. unfold helix_nand, make_helix, nand. simpl.
  destruct a, b; reflexivity.
Qed.

Definition helix_and (ha hb : HelixBit) : bool :=
  negb (helix_nand ha hb).
Theorem helix_and_correct : forall a b k,
  helix_and (make_helix a k) (make_helix b k) = a && b.
Proof.
  intros a b k. unfold helix_and. rewrite helix_nand_correct.
  unfold nand. apply Bool.negb_involutive.
Qed.

Definition helix_or (ha hb : HelixBit) : bool :=
  ha.(helix_f) || hb.(helix_f).
Theorem helix_or_correct : forall a b k,
  helix_or (make_helix a k) (make_helix b k) = a || b.
Proof. reflexivity. Qed.

Definition helix_xor (ha hb : HelixBit) : bool :=
  (ha.(helix_f) || hb.(helix_f)) && (ha.(helix_n) || hb.(helix_n)).
Theorem helix_xor_correct : forall a b k,
  helix_xor (make_helix a k) (make_helix b k) = xorb a b.
Proof. intros a b k. unfold helix_xor. simpl. destruct a, b; reflexivity. Qed.

Definition helix_not (ha : HelixBit) : bool := ha.(helix_n).
Theorem helix_not_correct : forall a k, helix_not (make_helix a k) = negb a.
Proof. reflexivity. Qed.

(* PART 5 — FULL ADDER FROM HELIX *)
Definition helix_full_adder (ha hb : HelixBit) (carry : bool) : bool * bool :=
  let xab  := helix_xor ha hb in
  let sum  := xorb xab carry in
  let nab  := helix_nand ha hb in
  let aab  := negb nab in
  let axc  := xab && carry in
  (sum, aab || axc).

Theorem helix_full_adder_correct : forall a b carry k,
  let ha := make_helix a k in
  let hb := make_helix b k in
  let (s, co) := helix_full_adder ha hb carry in
  (if s then 1 else 0) + 2 * (if co then 1 else 0) =
  (if a then 1 else 0) + (if b then 1 else 0) + (if carry then 1 else 0).
Proof.
  intros a b carry k.
  unfold helix_full_adder, helix_xor, helix_nand, make_helix. simpl.
  destruct a, b, carry; reflexivity.
Qed.

(* PART 6 — TRIADIC GROUNDING: strand phases *)
Definition strand_symbol (pos : nat) : bool := Nat.odd pos.

Theorem f_strand_is_i_phase : forall k,
  strand_symbol (nand_strand_pos k) = false.
Proof.
  intro k. unfold strand_symbol, nand_strand_pos.
  rewrite Nat.odd_mul. simpl. reflexivity.
Qed.

Theorem n_strand_is_n_phase : forall k,
  strand_symbol (not_strand_pos k) = true.
Proof.
  intro k. unfold strand_symbol, not_strand_pos.
  rewrite Nat.odd_add, Nat.odd_mul. simpl. reflexivity.
Qed.

Theorem helix_period_two : forall k,
  not_strand_pos k - nand_strand_pos k = 1 /\
  nand_strand_pos (S k) - not_strand_pos k = 1.
Proof. intro k. unfold nand_strand_pos, not_strand_pos. lia. Qed.

(* PART 7 — ALL OPS FROM TWO STRANDS *)
Theorem all_ops_from_two_strands :
  (forall a k,   helix_not  (make_helix a k)                   = negb a)       /\
  (forall a b k, helix_nand (make_helix a k) (make_helix b k)  = nand a b)     /\
  (forall a b k, helix_and  (make_helix a k) (make_helix b k)  = a && b)       /\
  (forall a b k, helix_or   (make_helix a k) (make_helix b k)  = a || b)       /\
  (forall a b k, helix_xor  (make_helix a k) (make_helix b k)  = xorb a b)     /\
  (forall a b c k,
    fst (helix_full_adder (make_helix a k) (make_helix b k) c) = xorb (xorb a b) c).
Proof.
  repeat split.
  - reflexivity.
  - intros a b k. apply helix_nand_correct.
  - intros a b k. apply helix_and_correct.
  - reflexivity.
  - intros a b k. apply helix_xor_correct.
  - intros a b c k.
    unfold helix_full_adder, helix_xor, helix_nand, make_helix. simpl.
    destruct a, b, c; reflexivity.
Qed.

(* PART 8 — MASTER THEOREM *)
Theorem double_helix_master :
  forall (a : bool) (k : nat),
  let h := make_helix a k in
  strand_symbol (nand_strand_pos k) = false  /\
  strand_symbol (not_strand_pos k)  = true   /\
  h.(helix_f) = a                            /\
  h.(helix_n) = negb a                       /\
  not_strand_pos k = nand_strand_pos k + 1   /\
  helix_not h = negb a                       /\
  nand a a = negb a                          /\
  negb (negb a) = a.
Proof.
  intros a k. repeat split.
  - apply f_strand_is_i_phase.
  - apply n_strand_is_n_phase.
  - reflexivity.
  - reflexivity.
  - apply strands_are_halfstep_apart.
  - reflexivity.
  - destruct a; reflexivity.
  - apply Bool.negb_involutive.
Qed.
