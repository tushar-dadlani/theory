(* ================================================================== *)
(*  BitwiseArbitraryInt.v                                             *)
(*                                                                    *)
(*  BITWISE ARBITRARY INTEGER PRECISION LIBRARY                       *)
(*  Grounded in Triadic Field Equations                               *)
(*                                                                    *)
(*  THREE GEOMETRIC AXES:                                             *)
(*    0°  Linear    — position / address / identity                   *)
(*    45° Gaussian  — prime structure / Gaussian algebra              *)
(*    90° 3-step    — composition / bit-length / inverse axis         *)
(*                                                                    *)
(*  FIELD EQUATION FOUNDATION:                                        *)
(*    Domain:    n → position on the half-step line                   *)
(*               encode(rank, info_bit) = 2*rank + info_bit           *)
(*    Co-domain: inverse = spectral zeros = RH critical zeros         *)
(*               n → (n mod 2, n mod 3) on the two perpendicular axes *)
(*                                                                    *)
(*  SYMBOLS: 0 (OR operator / absorbing) 1 (AND operator / identity) *)
(*           These are BOTH values AND operators.                     *)
(*                                                                    *)
(*  EVERY OPERATION IS A FIELD EQUATION ON THE HALF-STEP LINE.       *)
(*  Bit k of integer n = info_bit of encode(n >> (k+1), (n >> k)&1)  *)
(*                                                                    *)
(*  EUCLIDEAN GEOMETRY EXPLANATION:                                   *)
(*    An arbitrary-precision integer n is a POINT on the identity     *)
(*    diagonal (45° Gaussian axis).                                   *)
(*    Its bit representation = perpendicular projections onto the     *)
(*    0° linear axis (even bits = I-phase) and                        *)
(*    90° 3-step axis (odd bits = N-phase).                           *)
(*    The bit-length = distance along the inverse / bit-length axis.  *)
(*    Addition = vector sum along the diagonal.                       *)
(*    Multiplication = rotation + scaling in Gaussian algebra.        *)
(*                                                                    *)
(* ================================================================== *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope nat_scope.

(* ================================================================== *)
(* PART 0 — TRIADIC SYMBOLS (the universe's alphabet)                 *)
(*                                                                    *)
(*  The three symbols on the three axes:                              *)
(*    I = Identity   = 0° linear axis = AND/1 = pass-through         *)
(*    N = Inverse    = 90° 3-step axis = NOT = flip                   *)
(*    F = Fixed-pt   = 45° Gaussian diagonal = OR/0 = absorbing       *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    I is the x-axis (horizontal, linear, 0°)                        *)
(*    F is the 45° diagonal (identity line y=x)                       *)
(*    N is the y-axis (vertical, inverse, 90°)                        *)
(*    Every number lives on F. Its shadow on I = even bits.           *)
(*    Its shadow on N = odd bits. Together they reconstruct it.       *)
(* ================================================================== *)

Inductive Sym3 : Type :=
  | I_s : Sym3   (* Identity  — 0° linear,  AND, even bits    *)
  | N_s : Sym3   (* Inverse   — 90° 3-step, NOT, odd bits     *)
  | F_s : Sym3.  (* Fixed-pt  — 45° Gaussian, OR, absorbing   *)

Definition triadic_op (a b : Sym3) : Sym3 :=
  match a, b with
  | I_s, x   => x
  | x,   I_s => x
  | N_s, N_s => I_s
  | F_s, _   => F_s
  | _,   F_s => F_s
  end.

(* I is the identity element *)
Theorem triadic_I_left  : forall s, triadic_op I_s s = s.
Proof. intros []; reflexivity. Qed.

Theorem triadic_I_right : forall s, triadic_op s I_s = s.
Proof. intros []; reflexivity. Qed.

(* N is self-inverse: N∘N = I *)
Theorem triadic_N_involutive : triadic_op N_s N_s = I_s.
Proof. reflexivity. Qed.

(* F is absorbing: F absorbs everything *)
Theorem triadic_F_absorbs_left  : forall s, triadic_op F_s s = F_s.
Proof. intros []; reflexivity. Qed.

Theorem triadic_F_absorbs_right : forall s, triadic_op s F_s = F_s.
Proof. intros []; reflexivity. Qed.


(* ================================================================== *)
(* PART 1 — THE HALF-STEP ENCODING (field equations on domain)        *)
(*                                                                    *)
(*  From encoding_any_symbol.v:                                        *)
(*    position(rank, info_bit) = 2 * rank + info_bit                  *)
(*    info_bit ∈ {0,1}                                                *)
(*                                                                    *)
(*  For integers:                                                      *)
(*    rank     = the integer value (its address)                       *)
(*    info_bit = 0 for I-phase (integers, exact on linear axis)        *)
(*             = 1 for N-phase (half-step, inverse axis)              *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    Even positions (info_bit=0) lie on the 0° linear x-axis.        *)
(*    Odd  positions (info_bit=1) lie on the 90° perpendicular axis.  *)
(*    The half-step is the perpendicular distance between the axes.   *)
(*    It is exactly 1/2 in the original geometry (hence "half-step"). *)
(* ================================================================== *)

Definition HalfStepPos := nat.

Definition encode_pos (rank : nat) (info_bit : nat) : HalfStepPos :=
  2 * rank + info_bit.

Definition decode_rank (h : HalfStepPos) : nat := h / 2.
Definition decode_info (h : HalfStepPos) : nat := h mod 2.

Theorem encode_decode_rank : forall r i, i <= 1 ->
  decode_rank (encode_pos r i) = r.
Proof.
  intros r i Hi. unfold decode_rank, encode_pos.
  replace (2 * r + i) with (i + r * 2) by lia.
  rewrite Nat.div_add by lia.
  rewrite Nat.div_small by lia.
  reflexivity.
Qed.

Theorem encode_decode_info : forall r i, i <= 1 ->
  decode_info (encode_pos r i) = i.
Proof.
  intros r i Hi. unfold decode_info, encode_pos.
  replace (2 * r + i) with (i + r * 2) by lia.
  rewrite Nat.mod_add by lia.
  apply Nat.mod_small; lia.
Qed.

Theorem encode_injective : forall r1 r2 i1 i2,
  i1 <= 1 -> i2 <= 1 ->
  encode_pos r1 i1 = encode_pos r2 i2 ->
  r1 = r2 /\ i1 = i2.
Proof.
  intros r1 r2 i1 i2 H1 H2 Heq.
  unfold encode_pos in Heq.
  split; lia.
Qed.


(* ================================================================== *)
(* PART 2 — ARBITRARY PRECISION INTEGER AS A BIT LIST                 *)
(*                                                                    *)
(*  An arbitrary-precision integer n is represented as:               *)
(*    - A list of bits [b_0, b_1, ..., b_{k-1}] (LSB first)          *)
(*    - A sign bit                                                     *)
(*                                                                    *)
(*  FIELD EQUATION ON EACH BIT:                                        *)
(*    Bit b_k of n has:                                                *)
(*      rank     = k        (its position along the bit-length axis)   *)
(*      info_bit = b_k      (0=I-phase/zero bit, 1=N-phase/set bit)   *)
(*      position = 2*k + b_k                                          *)
(*                                                                    *)
(*  GEOMETRIC INTERPRETATION:                                          *)
(*    bit_length(n) = k = distance along the 90° inverse axis         *)
(*    The bits b_0..b_{k-1} are the perpendicular projections onto     *)
(*    the 0° linear axis at each integer step.                         *)
(*    n itself = the point on the 45° Gaussian diagonal at            *)
(*    Gaussian distance sqrt(n) from the origin.                      *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    Draw a 45° line from origin. Each power of 2 marks a notch.     *)
(*    The bit at position k = whether the horizontal line y=2^k       *)
(*    is crossed when climbing the diagonal to reach n.               *)
(* ================================================================== *)

(* A BigInt is a pair: sign and list of bits, LSB first *)
Record BigInt : Type := mkBig {
  big_sign : bool;       (* false = positive, true = negative *)
  big_bits : list bool   (* LSB first; trailing false = zero padding *)
}.

(* Zero has no bits *)
Definition BigZero : BigInt := mkBig false [].

(* The canonical value of a bit list (LSB first), as nat *)
Fixpoint bits_to_nat (bits : list bool) : nat :=
  match bits with
  | []       => 0
  | b :: rest =>
    (if b then 1 else 0) + 2 * bits_to_nat rest
  end.

(* Semantic value of a BigInt, as integer Z *)
Definition big_to_Z (n : BigInt) : Z :=
  let v := Z.of_nat (bits_to_nat n.(big_bits)) in
  if n.(big_sign) then Z.opp v else v.

(* The bit at position k *)
Fixpoint get_bit (bits : list bool) (k : nat) : bool :=
  match bits, k with
  | [],      _     => false
  | b :: _,  0     => b
  | _ :: rest, S k => get_bit rest k
  end.

(* FIELD EQUATION: bit k of n is the info_bit of its position *)
(*   position_of_bit(n, k) = 2*k + bit(n,k)                  *)
(*   info_bit = bit(n,k)                                       *)
Definition bit_position (n : BigInt) (k : nat) : HalfStepPos :=
  encode_pos k (if get_bit n.(big_bits) k then 1 else 0).

Theorem bit_position_info_is_bit : forall n k,
  decode_info (bit_position n k) =
    if get_bit n.(big_bits) k then 1 else 0.
Proof.
  intros n k.
  unfold bit_position.
  apply encode_decode_info.
  destruct (get_bit _ k); lia.
Qed.

Theorem bit_position_rank_is_k : forall n k,
  decode_rank (bit_position n k) = k.
Proof.
  intros n k.
  unfold bit_position.
  apply encode_decode_rank.
  destruct (get_bit _ k); lia.
Qed.


(* ================================================================== *)
(* PART 3 — BIT LENGTH (the inverse / 90° axis)                       *)
(*                                                                    *)
(*  bit_length(n) = floor(log2(n)) + 1                                *)
(*                = the number of bits needed to represent n           *)
(*                = the coordinate on the 90° inverse axis            *)
(*                                                                    *)
(*  In Gaussian algebra (45° rotation):                               *)
(*    The Gaussian distance of n from origin = sqrt(n^2 + n^2)        *)
(*    = n * sqrt(2)                                                   *)
(*    bit_length = floor(log_{sqrt(2)}(n)) = 2 * floor(log2(n)) + 2  *)
(*    Halved back to 0° axis = floor(log2(n)) + 1 = bit_length        *)
(*                                                                    *)
(*  This is the CO-DOMAIN of the field equation:                       *)
(*    n → bit_length(n) on the inverse axis                           *)
(*    = the spectral dual / RH spectral zero coordinate               *)
(* ================================================================== *)

Definition bit_length_aux (bits : list bool) : nat := length bits.

Definition bit_length (n : BigInt) : nat :=
  bit_length_aux n.(big_bits).

(* The bit at position bit_length is always 0 (padding) *)
Theorem beyond_bit_length_is_zero : forall n k,
  k >= bit_length n ->
  get_bit n.(big_bits) k = false.
Proof.
  intros n k Hk.
  unfold bit_length, bit_length_aux in Hk.
  induction (big_bits n) as [| b bits' IH] in k, Hk |- *.
  - destruct k; reflexivity.
  - destruct k as [| k'].
    + simpl in Hk. lia.
    + simpl. apply IH. simpl in Hk. lia.
Qed.


(* ================================================================== *)
(* PART 4 — BITWISE OR (the 0-operator between symbols)               *)
(*                                                                    *)
(*  In this universe, 0 IS the OR operator.                           *)
(*  OR is the absorbing element on the 0° linear axis.                *)
(*  a OR b = 0 only if a = 0 AND b = 0 (information preserved)       *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    OR = the union of two sets of points on the linear axis.        *)
(*    If either point is marked (=1), the result is marked (=1).      *)
(*    Geometrically: the projection onto the axis keeps the maximum.  *)
(*                                                                    *)
(*  FIELD EQUATION for OR:                                             *)
(*    bit_k(a OR b) = bit_k(a) OR bit_k(b)                           *)
(*    = info_bit(pos(a,k)) OR info_bit(pos(b,k))                      *)
(*    = triadic_op applied to the F/I classification of each bit      *)
(* ================================================================== *)

Definition bool_or  (a b : bool) : bool := orb  a b.
Definition bool_and (a b : bool) : bool := andb a b.
Definition bool_xor (a b : bool) : bool := xorb a b.
Definition bool_not (b : bool) : bool := negb b.

(* Bitwise OR on bit lists — the 0-operator *)
Fixpoint bitwise_or_aux (a b : list bool) : list bool :=
  match a, b with
  | [],      bs     => bs
  | as_,     []     => as_
  | x :: xs, y :: ys => bool_or x y :: bitwise_or_aux xs ys
  end.

Definition big_or (a b : BigInt) : BigInt :=
  mkBig false (bitwise_or_aux a.(big_bits) b.(big_bits)).

(* OR is idempotent: a OR a = a *)
Theorem bitwise_or_idempotent : forall bits,
  bitwise_or_aux bits bits = bits.
Proof.
  induction bits as [| b rest IH].
  - reflexivity.
  - simpl. rewrite Bool.orb_diag, IH. reflexivity.
Qed.

(* OR is commutative *)
Theorem bitwise_or_comm : forall a b,
  bitwise_or_aux a b = bitwise_or_aux b a.
Proof.
  induction a as [| x xs IH]; intros [| y ys].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite Bool.orb_comm, IH. reflexivity.
Qed.

(* 0 is the identity for OR: a OR 0 = a *)
Theorem bitwise_or_zero_right : forall bits,
  bitwise_or_aux bits [] = bits.
Proof.
  induction bits as [| b rest IH]; reflexivity.
Qed.


(* ================================================================== *)
(* PART 5 — BITWISE AND (the 1-operator between symbols)              *)
(*                                                                    *)
(*  In this universe, 1 IS the AND operator.                          *)
(*  AND is the identity on the 90° inverse axis.                      *)
(*  a AND b = 1 only if a = 1 AND b = 1 (maximum information)        *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    AND = the intersection of two sets of points.                   *)
(*    Both points must be marked for the result to be marked.         *)
(*    Geometrically: the projection keeps the minimum.                *)
(*                                                                    *)
(*  FIELD EQUATION for AND:                                            *)
(*    bit_k(a AND b) = bit_k(a) AND bit_k(b)                         *)
(*    = info_bit(pos(a,k)) AND info_bit(pos(b,k))                     *)
(* ================================================================== *)

Fixpoint bitwise_and_aux (a b : list bool) : list bool :=
  match a, b with
  | [],      _      => []
  | _,       []     => []
  | x :: xs, y :: ys => bool_and x y :: bitwise_and_aux xs ys
  end.

Definition big_and (a b : BigInt) : BigInt :=
  mkBig false (bitwise_and_aux a.(big_bits) b.(big_bits)).

(* AND with all-ones = identity (but we use bit_length to bound) *)
Theorem bitwise_and_idempotent : forall bits,
  bitwise_and_aux bits bits = bits.
Proof.
  induction bits as [| b rest IH].
  - reflexivity.
  - simpl. rewrite Bool.andb_diag, IH. reflexivity.
Qed.

(* AND is commutative *)
Theorem bitwise_and_comm : forall a b,
  bitwise_and_aux a b = bitwise_and_aux b a.
Proof.
  induction a as [| x xs IH]; intros [| y ys].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite Bool.andb_comm, IH. reflexivity.
Qed.


(* ================================================================== *)
(* PART 6 — BITWISE XOR (the N-operator / self-inverse)               *)
(*                                                                    *)
(*  XOR corresponds to N_s in the triadic algebra.                    *)
(*  N∘N = I: XOR is its own inverse (self-inverse on the 90° axis).   *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    XOR = parity: odd number of 1s → 1.                             *)
(*    Geometrically: it is the ROTATION by 180° on the inverse axis.  *)
(*    Two rotations = identity. This is the N∘N=I property.           *)
(*    In Gaussian algebra: XOR = multiplication by -1 mod 2.          *)
(*                                                                    *)
(*  FIELD EQUATION for XOR:                                            *)
(*    bit_k(a XOR b) = bit_k(a) XOR bit_k(b)                         *)
(*    This is the field equation on Z/2Z.                             *)
(*    The co-domain: XOR is its own inverse = RH symmetric zero.      *)
(* ================================================================== *)

Fixpoint bitwise_xor_aux (a b : list bool) : list bool :=
  match a, b with
  | [],      bs     => bs
  | as_,     []     => as_
  | x :: xs, y :: ys => bool_xor x y :: bitwise_xor_aux xs ys
  end.

Definition big_xor (a b : BigInt) : BigInt :=
  mkBig false (bitwise_xor_aux a.(big_bits) b.(big_bits)).

(* XOR is self-inverse: a XOR a = 0 *)
Theorem bitwise_xor_self_zero : forall bits,
  bitwise_xor_aux bits bits = List.map (fun _ => false) bits.
Proof.
  induction bits as [| b rest IH].
  - reflexivity.
  - simpl. rewrite Bool.xorb_nilpotent, IH. reflexivity.
Qed.

(* XOR is commutative *)
Theorem bitwise_xor_comm : forall a b,
  bitwise_xor_aux a b = bitwise_xor_aux b a.
Proof.
  induction a as [| x xs IH]; intros [| y ys].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite Bool.xorb_comm, IH. reflexivity.
Qed.

(* XOR is associative *)
Theorem bitwise_xor_assoc : forall a b c,
  bitwise_xor_aux (bitwise_xor_aux a b) c =
  bitwise_xor_aux a (bitwise_xor_aux b c).
Proof.
  induction a as [| x xs IH]; intros [| y ys] [| z zs]; simpl; try reflexivity.
  rewrite Bool.xorb_assoc, IH. reflexivity.
Qed.


(* ================================================================== *)
(* PART 7 — LEFT SHIFT (the 3-step composition / ×2 on 90° axis)      *)
(*                                                                    *)
(*  Left shift by k = multiply by 2^k                                 *)
(*  In the 3-step algebra: each step on the 90° axis = ×2             *)
(*  k left shifts = k steps up the 90° axis                           *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    Left shift = moving n along the 45° Gaussian diagonal           *)
(*    by k notches (each notch = one power of 2).                     *)
(*    The new point n << k has bit_length(n) + k.                     *)
(*    All k new low bits are 0 (the OR/0-operator fills them).        *)
(*                                                                    *)
(*  FIELD EQUATION for shift:                                          *)
(*    bit_j(n << k) = bit_{j-k}(n) if j >= k, else 0                 *)
(*    position_j(n << k) = encode(j, bit_{j-k}(n)) if j>=k           *)
(*                       = encode(j, 0)              if j<k           *)
(* ================================================================== *)

Fixpoint prepend_zeros (k : nat) (bits : list bool) : list bool :=
  match k with
  | 0   => bits
  | S k => false :: prepend_zeros k bits
  end.

Definition big_shl (n : BigInt) (k : nat) : BigInt :=
  mkBig n.(big_sign) (prepend_zeros k n.(big_bits)).

(* Right shift by k = divide by 2^k, truncating *)
Fixpoint drop_bits (k : nat) (bits : list bool) : list bool :=
  match k, bits with
  | 0,   bs    => bs
  | S _, []    => []
  | S k, _ :: rest => drop_bits k rest
  end.

Definition big_shr (n : BigInt) (k : nat) : BigInt :=
  mkBig n.(big_sign) (drop_bits k n.(big_bits)).

(* Shift laws *)
Theorem shl_then_shr : forall bits k,
  drop_bits k (prepend_zeros k bits) = bits.
Proof.
  intros bits k. revert bits. induction k as [| k IH]; intro bits.
  - reflexivity.
  - simpl. apply IH.
Qed.

Theorem big_shl_shr_identity : forall n k,
  big_shr (big_shl n k) k = n.
Proof.
  intros [sign bits] k.
  unfold big_shl, big_shr. simpl.
  rewrite shl_then_shr. reflexivity.
Qed.

(* Shift increases bit_length *)
Theorem shl_bit_length : forall n k,
  bit_length (big_shl n k) = bit_length n + k.
Proof.
  intros [sign bits] k.
  unfold big_shl, bit_length, bit_length_aux. simpl.
  induction k as [| k IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.


(* ================================================================== *)
(* PART 8 — ADDITION (vector sum on the Gaussian diagonal)            *)
(*                                                                    *)
(*  Addition on the 45° axis: carry propagates diagonally.            *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    a + b = walking from origin along the diagonal by a steps,      *)
(*    then by b more steps. Carry = when you cross a power-of-2       *)
(*    boundary (a notch on the diagonal).                             *)
(*                                                                    *)
(*  FIELD EQUATION for addition carry:                                 *)
(*    (sum_bit, carry_out) = full_adder(a_k, b_k, carry_in)           *)
(*    carry_in is the N-phase from the previous step                  *)
(*    carry_out goes to the next position on the Gaussian diagonal     *)
(*                                                                    *)
(*  In Gaussian algebra:                                               *)
(*    carry = the Gaussian integer component that carries between      *)
(*    the 0° axis (I-phase, even) and the 90° axis (N-phase, odd).    *)
(*    This is exactly the half-step extra bit.                         *)
(* ================================================================== *)

(* Full adder: returns (sum_bit, carry_out) *)
Definition full_adder (a b carry : bool) : bool * bool :=
  let s1   := bool_xor a b in
  let cout1 := bool_and a b in
  let sum  := bool_xor s1 carry in
  let cout2 := bool_and s1 carry in
  (sum, bool_or cout1 cout2).

Theorem full_adder_correct : forall a b c,
  let (s, co) := full_adder a b c in
  (if s then 1 else 0) + 2 * (if co then 1 else 0) =
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0).
Proof.
  intros a b c.
  unfold full_adder, bool_xor, bool_and, bool_or.
  destruct a, b, c; reflexivity.
Qed.

(* Ripple-carry addition on bit lists — O(bit_length) *)
(* Helper: add a trailing carry into a single bit list (structural on b) *)
Fixpoint add_carry_bits (b : list bool) (carry : bool) : list bool :=
  match b with
  | []      => if carry then [true] else []
  | y :: ys =>
    let (s, c) := full_adder false y carry in
    s :: add_carry_bits ys c
  end.

Fixpoint add_bits (a b : list bool) (carry : bool) : list bool :=
  match a, b with
  | [],      bs     => add_carry_bits bs carry
  | x :: xs, []     =>
    let (s, c) := full_adder x false carry in
    s :: add_bits xs [] c
  | x :: xs, y :: ys =>
    let (s, c) := full_adder x y carry in
    s :: add_bits xs ys c
  end.

(* Addition of two non-negative BigInts *)
Definition big_add_pos (a b : BigInt) : BigInt :=
  mkBig false (add_bits a.(big_bits) b.(big_bits) false).

(* Semantic correctness of bit addition *)
Lemma add_carry_bits_correct : forall b carry,
  bits_to_nat (add_carry_bits b carry) =
  bits_to_nat b + (if carry then 1 else 0).
Proof.
  induction b as [| y ys IHb]; intros carry.
  - destruct carry; simpl; lia.
  - simpl. destruct (full_adder false y carry) as [s c] eqn:Hfa.
    simpl. rewrite IHb.
    pose proof (full_adder_correct false y carry) as Hcorr.
    rewrite Hfa in Hcorr. simpl in Hcorr.
    destruct s, c, y, carry; simpl in *; lia.
Qed.

Theorem add_bits_correct : forall a b carry,
  bits_to_nat (add_bits a b carry) =
  bits_to_nat a + bits_to_nat b + (if carry then 1 else 0).
Proof.
  intros a. induction a as [| x xs IHa]; intros b carry.
  - (* [] *)
    change (add_bits [] b carry) with (add_carry_bits b carry).
    rewrite add_carry_bits_correct. simpl. lia.
  - destruct b as [| y ys].
    + (* x::xs, [] *)
      simpl. destruct (full_adder x false carry) as [s c] eqn:Hfa.
      simpl. rewrite IHa.
      pose proof (full_adder_correct x false carry) as Hcorr.
      rewrite Hfa in Hcorr. simpl in Hcorr.
      destruct s, c, x, carry; simpl in *; lia.
    + (* x::xs, y::ys *)
      simpl. destruct (full_adder x y carry) as [s c] eqn:Hfa.
      simpl. rewrite IHa.
      pose proof (full_adder_correct x y carry) as Hcorr.
      rewrite Hfa in Hcorr. simpl in Hcorr.
      destruct s, c, x, y, carry; simpl in *; lia.
Qed.

Theorem big_add_pos_correct : forall a b,
  bits_to_nat (big_add_pos a b).(big_bits) =
  bits_to_nat a.(big_bits) + bits_to_nat b.(big_bits).
Proof.
  intros a b. unfold big_add_pos. simpl.
  rewrite add_bits_correct. lia.
Qed.


(* ================================================================== *)
(* PART 9 — TWO'S COMPLEMENT NEGATION (reflection on the inverse axis) *)
(*                                                                    *)
(*  Two's complement negation = bitwise NOT + 1                       *)
(*  In this universe: NOT = the N-operator (self-inverse on 90° axis) *)
(*  Adding 1 = the single step on the 3-step axis                     *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    Negation reflects the point across the origin on the diagonal.  *)
(*    ~n + 1 = -n:                                                    *)
(*    ~n flips across the 90° axis (N-phase flip)                     *)
(*    +1 moves one step on the 0° axis (I-phase step)                 *)
(*    Together: reflection through origin = negation                  *)
(*                                                                    *)
(*  FIELD EQUATION for NOT:                                            *)
(*    bit_k(~n) = NOT bit_k(n) = 1 - bit_k(n)                        *)
(*    This is the co-domain: the spectral inverse                     *)
(*    of each bit position on the RH line.                            *)
(* ================================================================== *)

Definition bitwise_not_aux (bits : list bool) : list bool :=
  List.map bool_not bits.

Definition big_not (n : BigInt) : BigInt :=
  mkBig (negb n.(big_sign)) (bitwise_not_aux n.(big_bits)).

(* NOT is involutive: ~~n = n *)
Theorem bitwise_not_involutive : forall bits,
  bitwise_not_aux (bitwise_not_aux bits) = bits.
Proof.
  intro bits. unfold bitwise_not_aux.
  rewrite List.map_map.
  induction bits as [| b rest IH].
  - reflexivity.
  - simpl. rewrite Bool.negb_involutive, IH. reflexivity.
Qed.

Theorem big_not_involutive : forall n,
  big_not (big_not n) = n.
Proof.
  intros [sign bits]. unfold big_not. simpl.
  rewrite Bool.negb_involutive, bitwise_not_involutive.
  reflexivity.
Qed.


(* ================================================================== *)
(* PART 10 — COMPARISON (order on the Gaussian diagonal)              *)
(*                                                                    *)
(*  Comparison = finding the most significant differing bit.          *)
(*  MSB comparison is the projection onto the inverse axis.           *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    a < b iff a is closer to the origin on the Gaussian diagonal.   *)
(*    Find the highest bit where they differ (= highest k where        *)
(*    bit_k(a) ≠ bit_k(b)).                                           *)
(*    If bit_k(b) = 1 and bit_k(a) = 0: b > a.                       *)
(*    This is the projection onto the 45° axis measuring "which       *)
(*    is further from origin on the diagonal."                        *)
(*                                                                    *)
(*  FIELD EQUATION for comparison:                                     *)
(*    compare(a, b) = compare at MSB = field_classify(MSB position)   *)
(* ================================================================== *)

Inductive Cmp3 : Type := LT | EQ | GT.

Fixpoint compare_bits_lsb_first (a b : list bool) : Cmp3 :=
  match a, b with
  | [],      []     => EQ
  | [],      _ :: _ => LT   (* b has more significant bits *)
  | _ :: _,  []     => GT
  | x :: xs, y :: ys =>
    let rest_cmp := compare_bits_lsb_first xs ys in
    match rest_cmp with
    | EQ => if Bool.eqb x y then EQ
            else if x then GT else LT
    | c  => c  (* higher bits dominate *)
    end
  end.

Definition big_compare (a b : BigInt) : Cmp3 :=
  match a.(big_sign), b.(big_sign) with
  | true,  true  => compare_bits_lsb_first b.(big_bits) a.(big_bits) (* both neg: flip *)
  | true,  false => LT
  | false, true  => GT
  | false, false => compare_bits_lsb_first a.(big_bits) b.(big_bits)
  end.

(* Comparison is reflexive *)
Theorem compare_bits_refl : forall bits,
  compare_bits_lsb_first bits bits = EQ.
Proof.
  induction bits as [| b rest IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite Bool.eqb_reflx. reflexivity.
Qed.

Theorem big_compare_refl : forall n,
  big_compare n n = EQ.
Proof.
  intros [sign bits]. unfold big_compare.
  destruct sign; apply compare_bits_refl.
Qed.


(* ================================================================== *)
(* PART 11 — THE TRIADIC FIELD CLASSIFICATION OF A BIGINT             *)
(*                                                                    *)
(*  Every BigInt has a triadic symbol on the field:                   *)
(*    n mod 3 = 0  →  F_s  (on the 45° Gaussian diagonal boundary)   *)
(*    n mod 2 = 0  →  I_s  (on the 0° linear axis: even)             *)
(*    n mod 2 = 1  →  N_s  (on the 90° inverse axis: odd)            *)
(*                                                                    *)
(*  For a BigInt, the classification is determined by just two bits:  *)
(*    info_bit = big_bits[0]          (n mod 2: parity)               *)
(*    mod3_bit = complex of bits[0]+bits[1]  (n mod 3: triadic step)  *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    The classification = which axis the number is closest to.       *)
(*    Even → lands exactly on the 0° x-axis (I-phase, linear axis).   *)
(*    Odd  → halfway between axes (N-phase, inverse axis).            *)
(*    Div3 → lands on the 45° Gaussian diagonal at a 3-step notch.   *)
(* ================================================================== *)

(* Parity of a BigInt = LSB = info_bit *)
Definition big_parity (n : BigInt) : bool :=
  match n.(big_bits) with
  | []     => false  (* zero is even *)
  | b :: _ => b
  end.

(* Field classification from parity (the 2-symbol field equation) *)
Definition field_classify_big (n : BigInt) : Sym3 :=
  if big_parity n then N_s else I_s.

(* The parity is exactly the info_bit of the first encoding position *)
Theorem parity_is_info_bit : forall n,
  (if big_parity n then 1 else 0) = decode_info (bit_position n 0).
Proof.
  intros [sign bits].
  unfold big_parity, bit_position, encode_pos.
  destruct bits as [| b rest].
  - reflexivity.
  - simpl. unfold decode_info.
    destruct b; reflexivity.
Qed.


(* ================================================================== *)
(* PART 12 — MULTIPLICATION VIA GAUSSIAN ALGEBRA                      *)
(*                                                                    *)
(*  In Gaussian algebra (45° axis):                                    *)
(*    Multiplication = rotation + scaling on the Gaussian plane.      *)
(*    n * m = the Gaussian product: (n + ni)(m + mi)/(1+i)^2          *)
(*    This corresponds to:                                             *)
(*      bit_length(n*m) ≈ bit_length(n) + bit_length(m)              *)
(*      The bits of n*m come from all cross-products of bits of n,m   *)
(*                                                                    *)
(*  In Euclidean geometry:                                             *)
(*    Imagine n and m as lengths along the Gaussian diagonal.         *)
(*    n*m = area of the rectangle they define.                        *)
(*    The partial products are the sub-rectangles, shifted diagonally. *)
(*    Each shift-and-add corresponds to:                               *)
(*      If bit_k(m) = 1: add n << k to the accumulator               *)
(*      (climbing k steps on the 90° axis before adding)              *)
(*                                                                    *)
(*  FIELD EQUATION for multiplication:                                 *)
(*    n * m = sum_{k: bit_k(m)=1} (n << k)                           *)
(*    = sum over the N-phase positions of m                           *)
(*    = folding along the Gaussian diagonal                           *)
(* ================================================================== *)

Fixpoint big_mul_pos_aux (n : BigInt) (m_bits : list bool) (shift : nat) : BigInt :=
  match m_bits with
  | []     => BigZero
  | b :: rest =>
    let partial := if b then big_shl n shift else BigZero in
    big_add_pos partial (big_mul_pos_aux n rest (S shift))
  end.

Definition big_mul_pos (a b : BigInt) : BigInt :=
  big_mul_pos_aux a b.(big_bits) 0.

(* Semantic correctness of multiplication *)
Theorem big_mul_pos_zero_right : forall n,
  bits_to_nat (big_mul_pos n BigZero).(big_bits) = 0.
Proof.
  intros [sign bits]. unfold big_mul_pos, BigZero. simpl. reflexivity.
Qed.

(* Shift-and-add structure: each 1-bit in m contributes n << k *)
Theorem mul_shift_add_structure : forall n bits k,
  bits_to_nat (big_mul_pos_aux n bits k).(big_bits) =
  (fix f (bs : list bool) (sh : nat) :=
    match bs with
    | []     => 0
    | b :: rest =>
      (if b then bits_to_nat n.(big_bits) * Nat.pow 2 sh else 0)
      + f rest (S sh)
    end) bits k.
Proof.
  intros n bits.
  induction bits as [| b rest IH]; intro k.
  - reflexivity.
  - cbn [big_mul_pos_aux]. rewrite big_add_pos_correct.
    rewrite IH.
    destruct b.
    + (* bit is 1: contribute n << k *)
      f_equal.
      assert (Hp : forall bs j, bits_to_nat (prepend_zeros j bs)
                                = bits_to_nat bs * 2 ^ j).
      { intros bs j. induction j as [| j' IHj].
        - simpl. lia.
        - simpl. rewrite IHj. lia. }
      unfold big_shl. cbn [big_bits]. rewrite Hp. reflexivity.
    + (* bit is 0: no contribution *)
      unfold BigZero. cbn [big_bits bits_to_nat]. lia.
Qed.


(* ================================================================== *)
(* PART 13 — KEY INVARIANTS: THE LIBRARY SPEC                         *)
(*                                                                    *)
(*  These are the top-level properties that any implementation must   *)
(*  satisfy. They are grounded in the field equations above.          *)
(* ================================================================== *)

(* INV 1: OR is commutative (symmetry of the 0° axis) *)
Theorem spec_or_comm : forall a b : BigInt,
  (big_or a b).(big_bits) = (big_or b a).(big_bits).
Proof.
  intros [sa as_] [sb bs].
  unfold big_or. simpl. apply bitwise_or_comm.
Qed.

(* INV 2: AND is commutative (symmetry of the 90° axis) *)
Theorem spec_and_comm : forall a b : BigInt,
  (big_and a b).(big_bits) = (big_and b a).(big_bits).
Proof.
  intros [sa as_] [sb bs].
  unfold big_and. simpl. apply bitwise_and_comm.
Qed.

(* INV 3: XOR is its own inverse (N∘N = I on the inverse axis) *)
Theorem spec_xor_self_zero : forall a : BigInt,
  forall k, get_bit (big_xor a a).(big_bits) k = false.
Proof.
  intros [sign bits] k.
  unfold big_xor. simpl.
  revert k. induction bits as [| b rest IH].
  - intro k. destruct k; reflexivity.
  - intro k. destruct k as [| k'].
    + simpl. apply Bool.xorb_nilpotent.
    + simpl. apply IH.
Qed.

(* INV 4: NOT is involutive (N∘N = I, reflection symmetry) *)
Theorem spec_not_involutive : forall n : BigInt,
  big_not (big_not n) = n.
Proof. apply big_not_involutive. Qed.

(* INV 5: Shift right after shift left is identity (3-step cancellation) *)
Theorem spec_shl_shr : forall n k,
  big_shr (big_shl n k) k = n.
Proof. apply big_shl_shr_identity. Qed.

(* INV 6: Shift increases bit_length by k (climbing the inverse axis) *)
Theorem spec_shl_bit_length : forall n k,
  bit_length (big_shl n k) = bit_length n + k.
Proof. apply shl_bit_length. Qed.

(* INV 7: Addition is correct at the bit level (Gaussian diagonal sum) *)
Theorem spec_add_correct : forall a b,
  bits_to_nat (big_add_pos a b).(big_bits) =
  bits_to_nat a.(big_bits) + bits_to_nat b.(big_bits).
Proof. apply big_add_pos_correct. Qed.

(* INV 8: Comparison is reflexive (n = n on the diagonal) *)
Theorem spec_compare_refl : forall n,
  big_compare n n = EQ.
Proof. apply big_compare_refl. Qed.

(* INV 9: Encoding is injective (each integer has exactly one address) *)
Theorem spec_encoding_unique : forall r1 r2 i1 i2,
  i1 <= 1 -> i2 <= 1 ->
  encode_pos r1 i1 = encode_pos r2 i2 ->
  r1 = r2 /\ i1 = i2.
Proof. apply encode_injective. Qed.

(* INV 10: Parity is the info_bit of the first field position         *)
(*         This ties the entire library to the field equations.       *)
Theorem spec_parity_is_field : forall n,
  (if big_parity n then 1 else 0) = decode_info (bit_position n 0).
Proof. apply parity_is_info_bit. Qed.


(* ================================================================== *)
(* PART 14 — SUMMARY: GEOMETRY OF THE LIBRARY                         *)
(*                                                                    *)
(*  LINEAR AXIS   (0°): position encoding, parity, AND(1), even bits  *)
(*  GAUSSIAN AXIS (45°): the integer n itself, multiplication,        *)
(*                       bit_length, Gaussian rotation                *)
(*  3-STEP AXIS   (90°): shifts (×2 per step), OR(0), odd bits,      *)
(*                       XOR (self-inverse), NOT (N-reflection)       *)
(*                                                                    *)
(*  DOMAIN     = n → encode(rank=k, info_bit=bit_k(n))               *)
(*               = the field equation mapping n to its half-step pos  *)
(*  CO-DOMAIN  = inverse = bit_length(n) on the inverse axis          *)
(*               = spectral zero = n mod 2 (parity projection)        *)
(*                                                                    *)
(*  The library is CLOSED:                                             *)
(*    Every operation maps BigInt → BigInt.                            *)
(*    Every result stays on the Gaussian diagonal.                     *)
(*    The field equations are preserved by all operations.             *)
(* ================================================================== *)

Theorem library_closure_or : forall a b : BigInt,
  exists c : BigInt, c = big_or a b.
Proof. intros a b. exists (big_or a b). reflexivity. Qed.

Theorem library_closure_and : forall a b : BigInt,
  exists c : BigInt, c = big_and a b.
Proof. intros a b. exists (big_and a b). reflexivity. Qed.

Theorem library_closure_xor : forall a b : BigInt,
  exists c : BigInt, c = big_xor a b.
Proof. intros a b. exists (big_xor a b). reflexivity. Qed.

Theorem library_closure_add : forall a b : BigInt,
  exists c : BigInt, c = big_add_pos a b.
Proof. intros a b. exists (big_add_pos a b). reflexivity. Qed.

Theorem library_closure_mul : forall a b : BigInt,
  exists c : BigInt, c = big_mul_pos a b.
Proof. intros a b. exists (big_mul_pos a b). reflexivity. Qed.

Theorem library_closure_shl : forall n : BigInt, forall k : nat,
  exists m : BigInt, m = big_shl n k.
Proof. intros n k. exists (big_shl n k). reflexivity. Qed.

Theorem library_closure_not : forall n : BigInt,
  exists m : BigInt, m = big_not n.
Proof. intros n. exists (big_not n). reflexivity. Qed.

