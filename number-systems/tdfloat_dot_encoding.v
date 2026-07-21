(* ============================================================ *)
(*   TDFLOAT DOT ENCODING                                        *)
(*                                                               *)
(*   Instantiates the abstract half-step symbol encoding         *)
(*   (encoding_any_symbol.v) for TDFloat's specific              *)
(*   "integer vs fractional" number kinds.                       *)
(*                                                               *)
(*   THE CLAIM:                                                  *)
(*     The decimal dot "." is exactly the info_bit.              *)
(*     Numbers without a dot → integer axis  (info_bit = 0)     *)
(*     Numbers with a dot    → half-step axis (info_bit = 1)    *)
(*     The two axes are perpendicular → they never collide.      *)
(*                                                               *)
(*   In TDFloat's encoding:                                      *)
(*     position = 2 * rank + info_bit                           *)
(*     rank     = abs_digits * 78 + dot_pos                     *)
(*     info_bit = 0  when dot_pos = 0  (integer, no dot)        *)
(*     info_bit = 1  when dot_pos > 0  (fractional, has dot)    *)
(*                                                               *)
(*   So td(3) and td('3.0') have:                               *)
(*     td(3)   : rank=3,  info_bit=0  → position  6 (even)     *)
(*     td(3.0) : rank=3*78+1=235, info_bit=1 → position 471    *)
(*   They occupy DIFFERENT positions on the half-step line.      *)
(*                                                               *)
(*   STRUCTURE:                                                  *)
(*   1. Define TDKind (Integer | Fractional)                     *)
(*   2. Map TDKind to info_bit (0 | 1)                           *)
(*   3. Prove Integer and Fractional are on disjoint axes        *)
(*   4. Prove the dot IS the info_bit                            *)
(*   5. Prove decode is exact inverse (reuse parent theorems)    *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.

(* Load the abstract encoding theory from the same directory.
   Requires: coqc encoding_any_symbol.v  before this file.      *)
Require Import encoding_any_symbol.


(* ==== Step 1: The two kinds of TDFloat number ================ *)

(*  In TDFloat, every number is one of:
      Integer    — stored on the integer axis   (no decimal dot)
      Fractional — stored on the half-step axis (decimal dot present)

    This mirrors the abstract {info_bit=0, info_bit=1} split.    *)

Inductive TDKind : Type :=
  | Integer    : TDKind     (*  e.g. td(3)   — no dot  *)
  | Fractional : TDKind.    (*  e.g. td(3.0) — has dot *)


(* ==== Step 2: Map TDKind to info_bit ========================= *)

(*  The info_bit is the parity bit that chooses the axis:
      Integer    → 0  (even position: integer axis)
      Fractional → 1  (odd  position: half-step axis)           *)

Definition kind_to_info_bit (k : TDKind) : nat :=
  match k with
  | Integer    => 0
  | Fractional => 1
  end.

(*  The info_bit is always 0 or 1 — within the valid range      *)
Lemma kind_info_bit_bounded :
  forall k : TDKind,
  kind_to_info_bit k <= 1.
Proof.
  intro k. destruct k; simpl; lia.
Qed.


(* ==== Step 3: The axes are perpendicular (disjoint) ========== *)

(*  Integers go to even positions (info_bit=0 → 2*rank+0 = even).
    Fractionals go to odd positions (info_bit=1 → 2*rank+1 = odd).
    Even and odd are disjoint → the two kinds never collide.     *)

Theorem integer_fractional_perpendicular :
  forall rank : nat,
  encode_symbol rank (kind_to_info_bit Integer) <>
  encode_symbol rank (kind_to_info_bit Fractional).
Proof.
  intro rank.
  unfold encode_symbol, kind_to_info_bit.
  simpl. lia.
Qed.

(*  More strongly: no combination of ranks can cause a collision
    between kinds (the even/odd parity split is absolute).       *)
Theorem integer_fractional_never_collide :
  forall r1 r2 : nat,
  encode_symbol r1 (kind_to_info_bit Integer) <>
  encode_symbol r2 (kind_to_info_bit Fractional).
Proof.
  intros r1 r2.
  unfold encode_symbol, kind_to_info_bit.
  simpl.
  (* 2*r1 is always even; 2*r2+1 is always odd; they can never be equal *)
  lia.
Qed.


(* ==== Step 4: The dot IS the info_bit ======================== *)

(*  The decimal dot '.' is the syntactic indicator of fractional
    numbers.  In the encoding:
      dot_pos = 0  ↔  no dot    ↔  Integer    ↔  info_bit = 0
      dot_pos > 0  ↔  has dot   ↔  Fractional ↔  info_bit = 1

    We represent this faithfully: a number has a dot iff its
    kind is Fractional, iff its info_bit is 1.                   *)

Definition has_dot (k : TDKind) : bool :=
  match k with
  | Integer    => false
  | Fractional => true
  end.

(*  The dot flag and the info_bit carry the same information      *)
Theorem dot_is_info_bit :
  forall k : TDKind,
  has_dot k = true <-> kind_to_info_bit k = 1.
Proof.
  intro k. destruct k; simpl.
  - (* Integer: has_dot = false, info_bit = 0 *)
    split; intro H; discriminate.
  - (* Fractional: has_dot = true, info_bit = 1 *)
    split; intro H; reflexivity.
Qed.

(*  Contrapositive: no dot ↔ info_bit = 0                        *)
Theorem no_dot_is_integer_axis :
  forall k : TDKind,
  has_dot k = false <-> kind_to_info_bit k = 0.
Proof.
  intro k. destruct k; simpl.
  - split; intro H; reflexivity.
  - split; intro H; discriminate.
Qed.

(*  Corollary: the dot is the sole distinguishing bit between
    the two axes.  No other information is needed.               *)
Corollary dot_uniquely_determines_axis :
  forall k1 k2 : TDKind,
  has_dot k1 = has_dot k2 -> k1 = k2.
Proof.
  intros k1 k2 H.
  destruct k1, k2; simpl in H; try reflexivity; discriminate.
Qed.


(* ==== Step 5: Decode is exact inverse ======================== *)

(*  The TDFloat encoding inherits perfect reversibility from the
    abstract scheme.  We instantiate with the concrete info bits. *)

(*  For Integer kind: decode recovers rank and info_bit = 0      *)
Theorem tdfloat_integer_decode_perfect :
  forall rank : nat,
  let pos := encode_symbol rank (kind_to_info_bit Integer) in
  decode_rank pos = rank /\
  decode_info pos = kind_to_info_bit Integer.
Proof.
  intro rank.
  apply halfstep_encoding_perfect.
  apply kind_info_bit_bounded.
Qed.

(*  For Fractional kind: decode recovers rank and info_bit = 1   *)
Theorem tdfloat_fractional_decode_perfect :
  forall rank : nat,
  let pos := encode_symbol rank (kind_to_info_bit Fractional) in
  decode_rank pos = rank /\
  decode_info pos = kind_to_info_bit Fractional.
Proof.
  intro rank.
  apply halfstep_encoding_perfect.
  apply kind_info_bit_bounded.
Qed.

(*  Injectivity: distinct (rank, kind) pairs → distinct positions *)
Theorem tdfloat_encoding_injective :
  forall r1 r2 : nat,
  forall k1 k2 : TDKind,
  encode_symbol r1 (kind_to_info_bit k1) =
  encode_symbol r2 (kind_to_info_bit k2) ->
  r1 = r2 /\ k1 = k2.
Proof.
  intros r1 r2 k1 k2 Heq.
  assert (Hi1 := kind_info_bit_bounded k1).
  assert (Hi2 := kind_info_bit_bounded k2).
  destruct (encode_injective r1 r2
              (kind_to_info_bit k1) (kind_to_info_bit k2)
              Hi1 Hi2 Heq) as [Hr Hi].
  split.
  - exact Hr.
  - (* Recover k1 = k2 from the info_bit equality *)
    destruct k1, k2; simpl in Hi; try reflexivity; discriminate.
Qed.


(* ============================================================ *)
(*   SUMMARY                                                     *)
(*                                                               *)
(*   We have proved:                                             *)
(*                                                               *)
(*   1. TDKind has exactly two values: Integer and Fractional.   *)
(*      kind_to_info_bit maps them to {0, 1}.                   *)
(*                                                               *)
(*   2. The two axes are perpendicular:                          *)
(*      integer_fractional_never_collide proves that for ANY    *)
(*      pair of ranks r1, r2, the Integer encoding of r1 and    *)
(*      the Fractional encoding of r2 are always distinct.      *)
(*      (2*r1 is even; 2*r2+1 is odd.)                         *)
(*                                                               *)
(*   3. The dot IS the info_bit (dot_is_info_bit):              *)
(*      has_dot = true  ↔  kind_to_info_bit = 1                *)
(*      has_dot = false ↔  kind_to_info_bit = 0                *)
(*      The decimal "." is the exact one-bit axis selector.     *)
(*                                                               *)
(*   4. Encoding is perfectly reversible:                        *)
(*      tdfloat_integer_decode_perfect and                       *)
(*      tdfloat_fractional_decode_perfect (inherit from the      *)
(*      abstract halfstep_encoding_perfect theorem).             *)
(*                                                               *)
(*   5. Encoding is injective over (rank × TDKind) pairs:        *)
(*      tdfloat_encoding_injective proves that two encodings    *)
(*      agree iff both the rank and the kind agree.             *)
(* ============================================================ *)
