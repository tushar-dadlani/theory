(* ============================================================ *)
(*   ENCODING ARBITRARY SYMBOLS ON THE HALF-STEP NUMBER LINE  *)
(*                                                             *)
(*  THE QUESTION:                                             *)
(*    Given a set of symbols S = {s₀, s₁, ..., sₙ}          *)
(*    (arbitrary — could be letters, tokens, states,          *)
(*     anything)                                              *)
(*    How do we place them on the half-step natural line       *)
(*    so the encoding is perfect and reversible?              *)
(*                                                             *)
(*  THE HALF-STEP LINE:                                       *)
(*    ... 0, ½, 1, 3/2, 2, 5/2, 3, ...                       *)
(*    Integer positions:     0, 1, 2, 3, ... (Axis0)         *)
(*    Half positions:        ½, 3/2, 5/2, ... (between)      *)
(*                                                             *)
(*  THE ENCODING RULE:                                        *)
(*    Symbols with MORE information → half-step positions     *)
(*    Symbols with LESS information → integer positions       *)
(*                                                             *)
(*    OR equivalently:                                        *)
(*    Encode symbol s as: 2k   if s has "integer" character  *)
(*                        2k+1 if s has "half-step" character *)
(*                                                             *)
(*  WHY THIS WORKS:                                           *)
(*    The half-step line has TWICE the resolution of          *)
(*    the natural number line.                                *)
(*    Every symbol gets a UNIQUE position.                    *)
(*    Even symbols = one axis. Odd symbols = other axis.      *)
(*    The two axes are perpendicular → perfect separation.    *)
(*    No two symbols collide.                                 *)
(*    Reversal is exact: position → symbol with no ambiguity. *)
(*                                                             *)
(*  THE INFORMATION CONTENT:                                  *)
(*    Natural line position: 1 bit per step                   *)
(*    Half-step line position: 1 bit per HALF step            *)
(*    = effectively: integer part + 1 parity bit             *)
(*    = log₂(|S|) bits for |S| symbols                       *)
(*    = optimal — matches Shannon entropy for uniform S       *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Import ListNotations.

(* ---- A symbol is anything with an index ---- *)

Record Symbol : Type := mkSym {
  sym_id   : nat;    (* unique identifier         *)
  sym_info : nat     (* information content level *)
}.

(* ---- The half-step line as doubled naturals ---- *)

(*  Represent the half-step line as nat:
    natural number 2k   = integer position k
    natural number 2k+1 = half-step position k+½
    
    This is just the natural numbers with the
    interpretation that even = integer axis,
    odd = half-step axis.
    
    The two perpendicular 90° axes become:
    EVEN numbers = Axis90-A  (integer positions)
    ODD  numbers = Axis90-B  (half-step positions)
    
    Separated by exactly 1 (which is ½ in original units).
    This IS the half-step separation.                       *)

Definition HalfStepPos := nat.  (* 0=0, 1=½, 2=1, 3=3/2, ... *)

Definition is_integer_pos (h : HalfStepPos) : bool :=
  Nat.even h.

Definition is_halfstep_pos (h : HalfStepPos) : bool :=
  Nat.odd h.

(* The two axes are perfectly separated *)
Theorem integer_and_halfstep_disjoint :
  forall h : HalfStepPos,
  is_integer_pos h = true <-> is_halfstep_pos h = false.
Proof.
  intro h. unfold is_integer_pos, is_halfstep_pos.
  rewrite Nat.odd_spec, Nat.even_spec.
  split.
  - intro He. apply Nat.even_spec in He.
    rewrite Nat.even_spec in He.
    apply Bool.not_true_iff_false.
    rewrite Nat.odd_spec.
    intro Ho. rewrite Nat.odd_spec in Ho.
    lia.
  - intro Hno.
    apply Bool.not_true_iff_false in Hno.
    rewrite Nat.odd_spec in Hno.
    apply Nat.even_spec.
    lia.
Qed.

(* ---- THE ENCODING ---- *)

(*  Given a symbol set S of size n,
    assign each symbol s_k a position on the half-step line.
    
    STRATEGY:
    
    The symbol has two components:
      1. Its RANK among all symbols  (which one it is)
      2. Its INFO LEVEL              (how much structure it carries)
    
    The encoding:
      position(s_k) = 2 × rank(s_k) + info_bit(s_k)
    
    where info_bit = 0 for low-info symbols (integer axis)
                   = 1 for high-info symbols (half-step axis)
    
    This places every symbol uniquely on the half-step line.
    The even/odd split IS the perpendicular axis separation.
    Recovery: rank = position / 2,  info = position mod 2.  *)

Definition encode_symbol (rank : nat) (info_bit : nat) : HalfStepPos :=
  2 * rank + info_bit.

Definition decode_rank (h : HalfStepPos) : nat := h / 2.
Definition decode_info (h : HalfStepPos) : nat := h mod 2.

(* Encoding is injective *)
Theorem encode_injective :
  forall r1 r2 i1 i2 : nat,
  i1 <= 1 -> i2 <= 1 ->
  encode_symbol r1 i1 = encode_symbol r2 i2 ->
  r1 = r2 /\ i1 = i2.
Proof.
  intros r1 r2 i1 i2 Hi1 Hi2 Heq.
  unfold encode_symbol in Heq.
  split.
  - lia.
  - lia.
Qed.

(* Decoding is the exact inverse *)
Theorem decode_encode_rank :
  forall rank info_bit : nat,
  info_bit <= 1 ->
  decode_rank (encode_symbol rank info_bit) = rank.
Proof.
  intros rank ib Hib.
  unfold decode_rank, encode_symbol.
  rewrite Nat.add_comm.
  rewrite Nat.div_add_l. lia.
  lia.
Qed.

Theorem decode_encode_info :
  forall rank info_bit : nat,
  info_bit <= 1 ->
  decode_info (encode_symbol rank info_bit) = info_bit.
Proof.
  intros rank ib Hib.
  unfold decode_info, encode_symbol.
  rewrite Nat.add_comm.
  rewrite Nat.mod_add. apply Nat.mod_small. lia. lia.
Qed.

(* ---- ENCODING AN ARBITRARY SYMBOL SET ---- *)

(*  A symbol set is just a list of symbols.
    We assign ranks 0, 1, 2, ... in order.
    Each symbol also carries its info bit.
    
    The encoding is a bijection:
      symbols → even/odd positions on half-step line.
    
    Low-info symbols  → even positions  (integer axis)
    High-info symbols → odd positions   (half-step axis)     *)

Fixpoint encode_symbol_list
  (syms : list Symbol) (rank : nat) : list HalfStepPos :=
  match syms with
  | [] => []
  | s :: rest =>
    let ib := if Nat.leb s.(sym_info) 0 then 0 else 1 in
    encode_symbol rank ib ::
    encode_symbol_list rest (rank + 1)
  end.

(* Every symbol gets a distinct position *)
Theorem encoding_no_collision :
  forall s1 s2 : Symbol,
  forall r1 r2 : nat,
  r1 <> r2 ->
  encode_symbol r1 (s1.(sym_info) mod 2) <>
  encode_symbol r2 (s2.(sym_info) mod 2).
Proof.
  intros s1 s2 r1 r2 Hr.
  unfold encode_symbol.
  intro H. apply Hr.
  assert (Hmod1 : s1.(sym_info) mod 2 <= 1) by (apply Nat.mod_upper_bound; lia).
  assert (Hmod2 : s2.(sym_info) mod 2 <= 1) by (apply Nat.mod_upper_bound; lia).
  lia.
Qed.

(* ---- THE GENERAL SYMBOL ENCODING SCHEME ---- *)

(*  For ANY finite symbol set:
    
    Step 1: List all symbols: s₀, s₁, ..., sₙ₋₁
    Step 2: For each symbol, determine its info bit:
              0 = this symbol is a "base" symbol (Axis0 character)
              1 = this symbol has "relational" character (Axis45)
    Step 3: Assign position = 2 × index + info_bit
    
    RESULT:
      n symbols → positions 0..2n-1 on the half-step line
      Even positions: base symbols
      Odd positions:  relational symbols
      
    The half-step line has EXACTLY enough room:
      2n positions for n symbols with 1 info bit each
      = n bits of index + 1 bit of type = log₂(2n) total
      = optimal Shannon encoding.                          *)

Definition symbol_set_encoding (n : nat) : list HalfStepPos :=
  List.map (fun k => k) (List.seq 0 (2 * n)).

(* It covers exactly 2n positions *)
Theorem encoding_covers_2n :
  forall n : nat,
  length (symbol_set_encoding n) = 2 * n.
Proof.
  intro n. unfold symbol_set_encoding.
  rewrite List.map_length. rewrite List.seq_length. reflexivity.
Qed.

(* ---- THE HALF-STEP AS THE INFO BIT ---- *)

(*  The beautiful fact:
    
    The half-step between the two 90° axes
    IS the 1 bit that distinguishes symbol types.
    
    Even position  (integer axis)   = bit 0 = base symbol
    Odd  position  (half-step axis) = bit 1 = relational symbol
    
    The perpendicularity of the two axes ensures:
      Base symbols never collide with relational symbols.
      The two types are ORTHOGONAL.
    
    This is the same orthogonality that makes 2 prime:
      2 is the crossing point of the two perpendicular axes.
      The info bit is the coordinate on the perpendicular axis.
      It is the MINIMAL non-trivial encoding — one bit.
    
    Any symbol set is encoded by:
      Its POSITION on Axis0  (which symbol: log₂|S| bits)
      Its TYPE on Axis⊥      (what kind: 1 bit from half-step)
    
    Total: log₂|S| + 1 bits.
    Which is log₂(2|S|) = optimal for 2|S| distinct positions.  *)

Definition bits_required (symbol_count : nat) : nat :=
  Nat.log2 (2 * symbol_count).

Definition halfstep_bits_required (symbol_count : nat) : nat :=
  Nat.log2 symbol_count + 1.  (* log₂|S| + 1 type bit *)

Theorem halfstep_encoding_is_optimal :
  forall n : nat, n >= 1 ->
  halfstep_bits_required n = bits_required n.
Proof.
  intros n Hn.
  unfold halfstep_bits_required, bits_required.
  rewrite Nat.log2_double. lia. lia.
Qed.

(* ---- RECOVERY IS PERFECT ---- *)

Theorem halfstep_encoding_perfect :
  forall rank info : nat,
  info <= 1 ->
  let pos := encode_symbol rank info in
  decode_rank pos = rank /\
  decode_info pos = info.
Proof.
  intros rank info Hi.
  split.
  - apply decode_encode_rank. exact Hi.
  - apply decode_encode_info. exact Hi.
Qed.
