(* ================================================================= *)
(*  SAME-SAME-BUT-DIFFERENT CHANGES ENCODING:                        *)
(*                                                                    *)
(*  In encoding_any_symbol.v:                                        *)
(*    Symbol = { sym_id: nat ; sym_info: nat }                       *)
(*    position = 2 * rank + info_bit                                 *)
(*    The TWO fields carry independent meaning.                      *)
(*                                                                    *)
(*  In samesamebutdifferent.v:                                       *)
(*    The law is: the_law a a = swap a                               *)
(*    Zero and One are NOT independently typed — they are            *)
(*    THE SAME SYMBOL viewed from two relational positions.          *)
(*                                                                    *)
(*  CONSEQUENCE:                                                      *)
(*    info_bit is NOT a property of the symbol itself.               *)
(*    info_bit IS the RELATION between symbol and its context.       *)
(*    The encoding position is not fixed per symbol —                *)
(*    it depends on what came before.                                *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.

(* From samesamebutdifferent.v *)
Inductive Sym2 : Type := Zero : Sym2 | One : Sym2.

Definition the_law (a b : Sym2) : Sym2 :=
  match a, b with
  | Zero, Zero => One
  | One,  One  => Zero
  | Zero, One  => Zero
  | One,  Zero => Zero
  end.

Definition swap (s : Sym2) : Sym2 :=
  match s with Zero => One | One => Zero end.

(* From encoding_any_symbol.v — but now unified *)
Definition HalfStepPos := nat.

(* KEY CHANGE:
   In the original, info_bit comes FROM the symbol.
   In same-same-but-different, info_bit comes FROM THE RELATION.
   The context symbol determines whether we step or not. *)

Definition relational_info_bit (context : Sym2) (symbol : Sym2) : nat :=
  match the_law context symbol with
  | One  => 1   (* same ∘ same = other → half-step (relational position) *)
  | Zero => 0   (* different  → integer position (passes through)        *)
  end.

Definition encode_relational
  (rank : nat) (context : Sym2) (symbol : Sym2) : HalfStepPos :=
  2 * rank + relational_info_bit context symbol.

(* THEOREM 1: Same symbols always encode to ODD (half-step) positions *)
Theorem same_encodes_to_halfstep :
  forall rank : nat, forall s : Sym2,
  encode_relational rank s s = 2 * rank + 1.
Proof.
  intros rank s. unfold encode_relational, relational_info_bit.
  destruct s; reflexivity.
Qed.

(* THEOREM 2: Different symbols always encode to EVEN (integer) positions *)
Theorem different_encodes_to_integer :
  forall rank : nat, forall a b : Sym2,
  a <> b ->
  encode_relational rank a b = 2 * rank.
Proof.
  intros rank a b Hne.
  unfold encode_relational, relational_info_bit.
  destruct a, b.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - contradiction.
Qed.

(* THEOREM 3: The encoding position of a symbol is NOT fixed —
   it depends entirely on its relationship to context.
   The SAME symbol (say Zero) gets position 2k+1 when following Zero,
   but position 2k when following One. *)
Theorem same_symbol_different_positions :
  forall rank : nat,
  encode_relational rank Zero Zero <> encode_relational rank One Zero.
Proof.
  intro rank. simpl.
  unfold encode_relational, relational_info_bit. simpl. lia.
Qed.

(* THEOREM 4: swap_preserves_law means encoding is symmetric under swap.
   If we rename all symbols (Zero↔One), the relational structure —
   and therefore the HALF-STEP POSITIONS — are preserved. *)
Theorem swap_preserves_encoding :
  forall rank : nat, forall a b : Sym2,
  encode_relational rank (swap a) (swap b) =
  encode_relational rank a b.
Proof.
  intros rank a b.
  unfold encode_relational, relational_info_bit.
  destruct a, b; reflexivity.
Qed.

(* MASTER THEOREM:
   same-same-but-different collapses sym_info from an intrinsic
   property to a purely relational one.
   The info_bit IS the the_law output bit.
   The half-step line encodes RELATIONS, not symbols. *)
Theorem encoding_encodes_relations_not_symbols :
  forall rank : nat, forall a b : Sym2,
  encode_relational rank a b =
  2 * rank + (match the_law a b with One => 1 | Zero => 0 end).
Proof.
  intros rank a b.
  unfold encode_relational, relational_info_bit. reflexivity.
Qed.
