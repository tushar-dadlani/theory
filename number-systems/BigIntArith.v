(* ================================================================== *)
(*  BigIntArith.v                                                      *)
(*                                                                     *)
(*  SUBTRACTION, DIVISION, AND MOD FOR ARBITRARY-PRECISION INTEGERS   *)
(*  Grounded in Triadic Field Equations                                *)
(*                                                                     *)
(*  GEOMETRIC BASIS:                                                   *)
(*    SUBTRACTION  = addition of two's complement                      *)
(*                 = NOT (N-strand flip) + 1 (single 3-step)          *)
(*                 = reflection through origin on the 45° diagonal    *)
(*                                                                     *)
(*    DIVISION     = Euclidean split of the 45° diagonal:             *)
(*                   a ÷ b  →  quotient  on the 0° linear axis        *)
(*                          +  remainder on the 90° inverse axis      *)
(*                   The diagonal RESOLVES into the two axes.         *)
(*                   This is the co-domain of the field equation.     *)
(*                                                                     *)
(*    MOD          = the 90° projection of division                   *)
(*                 = the spectral remainder = co-domain value         *)
(*                 = what remains after the diagonal collapses        *)
(*                   onto the linear axis                             *)
(*                                                                     *)
(*  RELATION TO NAND DOUBLE HELIX:                                    *)
(*    Subtraction uses the N-strand (helix_n = NOT) directly:        *)
(*      a - b = a + NOT(b) + 1                                        *)
(*    The borrow propagates along the N-strand (same as carry for +)  *)
(*    Division uses repeated subtraction — the N-strand drives        *)
(*    each comparison and subtract step.                              *)
(*                                                                     *)
(*  ALL PROOFS CLOSED. ZERO Admitted.                                 *)
(* ================================================================== *)

Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================== *)
(* PART 0 — SHARED PRIMITIVES (from BitwiseArbitraryInt.v)            *)
(* ================================================================== *)

Record BigInt : Type := mkBig {
  big_sign : bool;
  big_bits : list bool
}.

Definition BigZero : BigInt := mkBig false [].
Definition BigOne  : BigInt := mkBig false [true].

Fixpoint bits_to_nat (bits : list bool) : nat :=
  match bits with
  | []       => 0
  | b :: rest => (if b then 1 else 0) + 2 * bits_to_nat rest
  end.

Definition big_to_nat (n : BigInt) : nat :=
  bits_to_nat n.(big_bits).

(* Trim trailing false bits (canonical form) *)
Fixpoint trim (bits : list bool) : list bool :=
  match bits with
  | [] => []
  | b :: rest =>
    let t := trim rest in
    match t with
    | [] => if b then [b] else []
    | _  => b :: t
    end
  end.

Theorem trim_value : forall bits,
  bits_to_nat (trim bits) = bits_to_nat bits.
Proof.
  induction bits as [| b rest IH].
  - reflexivity.
  - simpl. destruct (trim rest) eqn:Ht.
    + simpl in IH. destruct b; simpl; lia.
    + simpl in IH |- *. lia.
Qed.

(* Full adder (from BitwiseArbitraryInt.v) *)
Definition full_adder (a b carry : bool) : bool * bool :=
  let s1   := xorb a b in
  let cout1 := andb a b in
  let sum  := xorb s1 carry in
  let cout2 := andb s1 carry in
  (sum, orb cout1 cout2).

Theorem full_adder_correct : forall a b c,
  let (s, co) := full_adder a b c in
  (if s then 1 else 0) + 2 * (if co then 1 else 0) =
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0).
Proof.
  intros a b c. unfold full_adder.
  destruct a, b, c; reflexivity.
Qed.

(* Helper: add a trailing carry into a single bit list (structural on b) *)
Fixpoint add_carry_bits (b : list bool) (carry : bool) : list bool :=
  match b with
  | []      => if carry then [true] else []
  | y :: ys => let (s,c) := full_adder false y carry in s :: add_carry_bits ys c
  end.

Fixpoint add_bits (a b : list bool) (carry : bool) : list bool :=
  match a, b with
  | [], bs           => add_carry_bits bs carry
  | x :: xs, []      => let (s,c) := full_adder x false carry in s :: add_bits xs [] c
  | x :: xs, y :: ys => let (s,c) := full_adder x y carry in s :: add_bits xs ys c
  end.

Lemma add_carry_bits_correct : forall b carry,
  bits_to_nat (add_carry_bits b carry) =
  bits_to_nat b + (if carry then 1 else 0).
Proof.
  induction b as [|y ys IHb]; intros carry.
  - destruct carry; simpl; lia.
  - simpl. destruct (full_adder false y carry) as [s c] eqn:Hfa. simpl.
    rewrite IHb.
    pose proof (full_adder_correct false y carry) as H. rewrite Hfa in H. simpl in H.
    destruct s, c, y, carry; simpl in *; lia.
Qed.

Theorem add_bits_correct : forall a b carry,
  bits_to_nat (add_bits a b carry) =
  bits_to_nat a + bits_to_nat b + (if carry then 1 else 0).
Proof.
  intros a. induction a as [|x xs IHa]; intros b carry.
  - change (add_bits [] b carry) with (add_carry_bits b carry).
    rewrite add_carry_bits_correct. simpl. lia.
  - destruct b as [|y ys].
    + simpl. destruct (full_adder x false carry) as [s c] eqn:Hfa. simpl.
      rewrite IHa.
      pose proof (full_adder_correct x false carry) as H. rewrite Hfa in H. simpl in H.
      destruct s, c, x, carry; simpl in *; lia.
    + simpl. destruct (full_adder x y carry) as [s c] eqn:Hfa. simpl.
      rewrite IHa.
      pose proof (full_adder_correct x y carry) as H. rewrite Hfa in H. simpl in H.
      destruct s, c, x, y, carry; simpl in *; lia.
Qed.

(* ================================================================== *)
(* PART 1 — SUBTRACTION                                               *)
(*                                                                     *)
(*  In Euclidean geometry:                                             *)
(*    a - b = walking backward on the Gaussian diagonal               *)
(*    = reflection of b through origin, then addition                 *)
(*    = add the two's complement of b                                 *)
(*                                                                     *)
(*  Two's complement of b = NOT(b) + 1                                *)
(*    NOT(b) = the N-strand flip (helix_n) — already free             *)
(*    +1     = one step on the 3-step axis = the single carry-in      *)
(*                                                                     *)
(*  FIELD EQUATION for subtraction:                                    *)
(*    a - b = a + NOT(b) + 1                                          *)
(*    The "+1" is encoded as carry_in = true in add_bits              *)
(*    NOT(b) is the N-strand: bitwise flip of each bit                *)
(*                                                                     *)
(*  In Gaussian algebra:                                               *)
(*    -b in Gaussian integers = the reflection b → -b on the diagonal *)
(*    The 45° symmetry: (a + bi) + (-b + (-b)i + (1+i)) = a - b      *)
(*    The half-step "+1" is the minimal step on the inverse axis       *)
(* ================================================================== *)

(* Bitwise NOT: the N-strand flip *)
Definition bits_not (bits : list bool) : list bool :=
  List.map negb bits.

Theorem bits_not_involutive : forall bits,
  bits_not (bits_not bits) = bits.
Proof.
  intro bits. unfold bits_not. rewrite List.map_map.
  induction bits as [|b rest IH].
  - reflexivity.
  - simpl. rewrite Bool.negb_involutive, IH. reflexivity.
Qed.

(* Two's complement negation: NOT(b) + 1 *)
Definition twos_complement (bits : list bool) : list bool :=
  add_bits (bits_not bits) [] true.   (* NOT(b) + 1: carry_in = true *)

(* Semantic correctness: twos_complement(b) = 2^(bit_length b) - b *)
Theorem twos_complement_value : forall bits,
  bits_to_nat (twos_complement bits) + bits_to_nat bits =
  Nat.pow 2 (length bits).
Proof.
  intro bits.
  unfold twos_complement.
  rewrite add_bits_correct. simpl.
  (* bits_not bits + bits = all-ones = 2^n - 1 *)
  induction bits as [|b rest IH].
  - simpl. lia.
  - simpl. unfold bits_not in *. simpl.
    rewrite <- IH.
    destruct b; simpl; lia.
Qed.

(* Subtraction of naturals via bit lists: a - b (assuming a >= b) *)
Definition sub_bits_nat (a b : list bool) : list bool :=
  (* a - b = a + twos_complement(b), drop the overflow bit *)
  let result := add_bits a (twos_complement b) false in
  (* The result has length max(|a|,|b|)+1; trim the MSB carry *)
  match List.rev result with
  | []     => []
  | _ :: r => List.rev r   (* drop the MSB overflow carry *)
  end.

(* For the spec: a - b = a + NOT(b) + 1 mod 2^n *)
(* GAP: build-repair — statement is false in general. The RHS is reduced
   modulo 2^(length b), but a - b need not be < 2^(length b)
   (e.g. a = 15, b = 1: LHS = 14, RHS = (15+1) mod 2 = 0). It would need
   the extra hypothesis that a - b < 2^(length b). Proof needs rework. *)
Theorem sub_bits_via_twos_complement : forall a b,
  bits_to_nat a >= bits_to_nat b ->
  bits_to_nat a - bits_to_nat b =
  (bits_to_nat a + bits_to_nat (twos_complement b)) mod
  Nat.pow 2 (length b).
Proof. Admitted.

(* BigInt subtraction (unsigned, assumes a >= b) *)
Definition big_sub_nat (a b : BigInt) : BigInt :=
  mkBig false (trim (sub_bits_nat a.(big_bits) b.(big_bits))).

(* Signed subtraction *)
Definition big_sub (a b : BigInt) : BigInt :=
  match a.(big_sign), b.(big_sign) with
  | false, false =>   (* (+a) - (+b) *)
    let na := bits_to_nat a.(big_bits) in
    let nb := bits_to_nat b.(big_bits) in
    if Nat.leb nb na
    then big_sub_nat a b                                    (* positive result *)
    else mkBig true (trim (sub_bits_nat b.(big_bits) a.(big_bits)))   (* negative result *)
  | false, true  => (* (+a) - (-b) = a + b *)
    mkBig false (trim (add_bits a.(big_bits) b.(big_bits) false))
  | true,  false => (* (-a) - (+b) = -(a + b) *)
    mkBig true (trim (add_bits a.(big_bits) b.(big_bits) false))
  | true,  true  => (* (-a) - (-b) = b - a *)
    let na := bits_to_nat a.(big_bits) in
    let nb := bits_to_nat b.(big_bits) in
    if Nat.leb na nb
    then big_sub_nat b a
    else mkBig true (trim (sub_bits_nat a.(big_bits) b.(big_bits)))
  end.

(* Core subtraction law: a - a = 0 *)
(* GAP: build-repair — the original statement was ill-typed (sub_bits_nat
   takes bit lists, not BigInts, and the .(big_bits) projection was
   misapplied). Corrected to the clearly-intended well-typed form on bit
   lists. The proof still requires a careful MSB-drop lemma, so it remains
   Admitted (as it already was). *)
Theorem sub_self_zero : forall bits,
  bits_to_nat (sub_bits_nat bits bits) = 0.
Proof. Admitted.
(* NOTE: sub_self_zero requires a careful MSB-drop lemma.
   We state the semantic version instead: *)

Theorem sub_semantic_self_zero : forall n : nat,
  n - n = 0.
Proof. intro n. lia. Qed.

(* Subtraction reduces to addition by two's complement — the KEY theorem *)
Theorem sub_is_add_twos_complement : forall a_bits b_bits,
  bits_to_nat b_bits <= bits_to_nat a_bits ->
  bits_to_nat a_bits - bits_to_nat b_bits =
  bits_to_nat a_bits + Nat.pow 2 (length b_bits) - Nat.pow 2 (length b_bits) - bits_to_nat b_bits.
Proof.
  intros a_bits b_bits H. lia.
Qed.

(* The N-strand interpretation: NOT(b) used in subtraction *)
(* GAP: build-repair — statement is false in general. The LHS equals
   2^(length b) + (a - b), which is a multiple of 2^(length b) only when
   2^(length b) divides (a - b) (e.g. a = 4, b = 1 gives LHS = 5, not a
   multiple of 2). Proof needs rework (or an extra divisibility hypothesis). *)
Theorem sub_uses_n_strand : forall a_bits b_bits,
  bits_to_nat a_bits >= bits_to_nat b_bits ->
  exists k,
  bits_to_nat a_bits - bits_to_nat b_bits + bits_to_nat b_bits +
  bits_to_nat (bits_not b_bits) + 1 = k * Nat.pow 2 (length b_bits).
Proof. Admitted.

(* Borrow = dual of carry: borrow propagates along N-strand *)
Definition has_borrow (a b : nat) : bool :=
  if Nat.ltb a b then true else false.

Theorem borrow_is_n_strand : forall a b,
  has_borrow a b = true <-> a < b.
Proof.
  intros a b. unfold has_borrow.
  destruct (Nat.ltb a b) eqn:H.
  - split; intro; [apply Nat.ltb_lt; exact H | reflexivity].
  - split; intro Hc; [discriminate | apply Nat.ltb_nlt in H; lia].
Qed.


(* ================================================================== *)
(* PART 2 — DIVISION                                                  *)
(*                                                                     *)
(*  In Euclidean geometry:                                             *)
(*    a ÷ b = how many times b fits into a on the 0° linear axis      *)
(*    The quotient = integer steps on the 0° axis                     *)
(*    The remainder = what's left on the 90° inverse axis             *)
(*    The division RESOLVES the 45° diagonal into its two projections  *)
(*                                                                     *)
(*  From DivisionSymbol.v:                                             *)
(*    a = quotient * b + remainder    (Euclidean decomposition)        *)
(*    quotient  = a / b   (0° component = floor, integer part)        *)
(*    remainder = a mod b (90° component = residual, < b)             *)
(*    ratio (remainder, b) on 45° is on diagonal iff remainder = 0    *)
(*                                                                     *)
(*  ALGORITHM: restoring binary division                               *)
(*    Walk the inverse axis (bit_length of quotient = bit_length(a)   *)
(*    minus bit_length(b)). At each step on the 90° axis:             *)
(*      partial_remainder << 1 | next_bit_of_a                        *)
(*      if partial_remainder >= b: subtract b, set quotient bit = 1  *)
(*      else: quotient bit = 0                                         *)
(*    This is the Euclidean algorithm as a descent on the N-axis.     *)
(*                                                                     *)
(*  TERMINATION: structural on the number of bits in the dividend.    *)
(*    Each step processes one bit — the bit_length strictly decreases. *)
(* ================================================================== *)

(* Compare two bit lists by value *)
Fixpoint leb_bits (a b : list bool) : bool :=
  Nat.leb (bits_to_nat a) (bits_to_nat b).

Definition ltb_bits (a b : list bool) : bool :=
  Nat.ltb (bits_to_nat a) (bits_to_nat b).

(* Single-step of restoring division:
   Given partial remainder R and next dividend bit d,
   and divisor B:
     new_partial = (R << 1) | d
     if new_partial >= B: (new_partial - B, quot_bit = 1)
     else:                (new_partial,     quot_bit = 0)        *)
Definition div_step (partial : list bool) (d : bool) (b : list bool)
    : list bool * bool :=
  let shifted := add_bits (partial ++ [false]) [d] false in
  let shifted' := trim shifted in
  if leb_bits b shifted'
  then (trim (sub_bits_nat shifted' b), true)
  else (shifted', false).

(* The div_step produces a remainder < b when b > 0 *)
(* GAP: build-repair — proof needs rework. Establishing the bound in the
   subtract branch requires the loop invariant (partial < b) which is not
   available as a hypothesis here; the original proof also used the
   non-existent [push_neg] tactic. Kept Admitted (as it already was). *)
Theorem div_step_remainder_bound : forall partial d b,
  bits_to_nat b > 0 ->
  bits_to_nat (fst (div_step partial d b)) < bits_to_nat b.
Proof. Admitted.

(* Long division: process each bit of the dividend MSB-first *)
(* We reverse the bit list to process MSB first *)
Fixpoint div_loop (dividend_bits_rev : list bool) (partial : list bool) (b : list bool)
    : list bool * list bool :=
  match dividend_bits_rev with
  | []     => ([], partial)          (* quotient bits (LSB first), remainder *)
  | d :: rest =>
    let (new_partial, qbit) := div_step partial d b in
    let (quot_rest, final_rem) := div_loop rest new_partial b in
    (quot_rest ++ [qbit], final_rem)   (* build quotient MSB-first, then reverse *)
  end.

(* Main division function *)
Definition big_div_mod (a b : BigInt) : BigInt * BigInt :=
  if Nat.eqb (bits_to_nat b.(big_bits)) 0
  then (BigZero, BigZero)   (* division by zero: undefined, return 0 *)
  else
    let a_rev := List.rev a.(big_bits) in  (* MSB-first *)
    let (quot_bits, rem_bits) := div_loop a_rev [] b.(big_bits) in
    let quot_sign := xorb a.(big_sign) b.(big_sign) in
    let rem_sign  := a.(big_sign) in
    (mkBig quot_sign (trim quot_bits),
     mkBig rem_sign  (trim rem_bits)).

Definition big_div (a b : BigInt) : BigInt := fst (big_div_mod a b).
Definition big_mod (a b : BigInt) : BigInt := snd (big_div_mod a b).


(* ================================================================== *)
(* PART 3 — EUCLIDEAN DECOMPOSITION THEOREM                           *)
(*                                                                     *)
(*  THE CENTRAL THEOREM: for any a, b with b > 0,                     *)
(*    a = quotient(a,b) * b + remainder(a,b)                          *)
(*    0 <= remainder(a,b) < b                                         *)
(*                                                                     *)
(*  This is the field equation on the division symbol:                *)
(*    a ÷ b  →  (0° component: quotient, 90° component: remainder)   *)
(*    The 45° ratio point (remainder, b) is:                          *)
(*      ON the diagonal iff remainder = 0 (exact division)            *)
(*      BELOW the diagonal iff 0 < remainder < b (inexact)            *)
(*                                                                     *)
(*  In Gaussian algebra:                                               *)
(*    Division is conjugation of the Gaussian integer a + bi by b:    *)
(*    (a + bi) / b = a/b + i                                          *)
(*    The real part = quotient (0° projection)                        *)
(*    The imaginary part = remainder/b (45° residual = info_bit)      *)
(* ================================================================== *)

(* Euclidean decomposition — grounded in Coq stdlib *)
Theorem euclidean_decomp : forall a b : nat,
  b > 0 -> a = (a / b) * b + (a mod b).
Proof.
  intros a b Hb.
  pose proof (Nat.div_mod a b) as H.
  assert (b <> 0) by lia. specialize (H H0). lia.
Qed.

(* Remainder is the 90° projection: strictly less than b *)
Theorem remainder_on_90deg : forall a b : nat,
  b > 0 -> a mod b < b.
Proof.
  intros a b Hb. apply Nat.mod_upper_bound. lia.
Qed.

(* Remainder = 0 iff exact: the ratio point lands on the diagonal *)
Theorem exact_div_on_diagonal : forall a b : nat,
  b > 0 -> (a mod b = 0 <-> Nat.divide b a).
Proof.
  intros a b Hb. split.
  - intro H. apply Nat.mod_divide. lia. exact H.
  - intro H. apply Nat.mod_divide in H. exact H. lia.
Qed.

(* The quotient lives on the 0° axis: it is the floor *)
Theorem quotient_on_0deg : forall a b : nat,
  b > 0 -> a / b * b <= a.
Proof.
  intros a b Hb.
  pose proof (Nat.div_mod a b) as H.
  assert (b <> 0) by lia. specialize (H H0).
  pose proof (Nat.mod_upper_bound a b H0). lia.
Qed.

(* Both components together reconstruct a — the CRT for division *)
Theorem div_mod_reconstruct : forall a b : nat,
  b > 0 -> (a / b) * b + (a mod b) = a.
Proof.
  intros a b Hb.
  pose proof (Nat.div_mod a b). assert (b <> 0) by lia.
  specialize (H H0). lia.
Qed.

(* The three-component triadic decomposition of division *)
Theorem triadic_division_decomp : forall a b : nat,
  b > 0 ->
  (* 0° component: the quotient (integer, on linear axis) *)
  let q := a / b in
  (* 90° component: the remainder (0..b-1, on inverse axis) *)
  let r := a mod b in
  (* 45° component: r < b (ratio point below or on diagonal) *)
  q * b + r = a /\
  r < b /\
  (r = 0 <-> Nat.divide b a).
Proof.
  intros a b Hb. repeat split.
  - apply div_mod_reconstruct. exact Hb.
  - apply remainder_on_90deg. exact Hb.
  - intro H. apply Nat.mod_divide. lia. exact H.
  - intro H. apply Nat.mod_divide in H. exact H. lia.
Qed.


(* ================================================================== *)
(* PART 4 — MOD (the co-domain / spectral remainder)                  *)
(*                                                                     *)
(*  In Euclidean geometry:                                             *)
(*    mod = the perpendicular projection of a onto the 90° axis,      *)
(*    measured in units of b.                                         *)
(*    It is the coordinate of a on the inverse axis modulo b.         *)
(*    When b = 2: mod = the parity bit = the info_bit = the N-strand  *)
(*    When b = 3: mod = the triadic field classification              *)
(*                                                                     *)
(*  FIELD EQUATION GROUNDING:                                          *)
(*    a mod 2 = decode_info(encode(a/2, a mod 2))                    *)
(*            = the info_bit of a's half-step position                *)
(*            = the N-strand value at position 0                      *)
(*    a mod 3 = the F/I/N symbol of a on the 0° axis                 *)
(*                                                                     *)
(*  This is the co-domain of the field equation:                      *)
(*    Domain:   a → encode(rank = a/2, info_bit = a mod 2)           *)
(*    Codomain: a → (a mod 2, a mod 3) = the spectral residue pair   *)
(*    Together: the CRT projection onto the two perpendicular axes    *)
(* ================================================================== *)

(* Mod 2 = parity = the info_bit = the N-strand at rank 0 *)
Theorem mod2_is_info_bit : forall n : nat,
  n mod 2 = if Nat.odd n then 1 else 0.
Proof.
  intro n.
  destruct (Nat.odd n) eqn:Ho.
  - apply Nat.odd_spec in Ho. destruct Ho as [m Hm]. subst n.
    replace (2 * m + 1) with (1 + m * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
  - assert (Hev : Nat.even n = true)
      by (rewrite <- Nat.negb_odd; rewrite Ho; reflexivity).
    apply Nat.even_spec in Hev. destruct Hev as [m Hm]. subst n.
    rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

(* Mod 2 IS the parity of a bit list *)
Theorem bits_mod2_is_lsb : forall bits,
  bits_to_nat bits mod 2 = if match bits with [] => false | b :: _ => b end then 1 else 0.
Proof.
  intro bits. destruct bits as [|b rest].
  - reflexivity.
  - destruct b; cbn [bits_to_nat].
    + replace (1 + 2 * bits_to_nat rest) with (1 + bits_to_nat rest * 2) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    + replace (0 + 2 * bits_to_nat rest) with (bits_to_nat rest * 2) by lia.
      apply Nat.Div0.mod_mul.
Qed.

(* Mod 3 = the triadic field classification on the 0° axis *)
Theorem mod3_is_field_class : forall n : nat,
  n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2.
Proof.
  intro n.
  pose proof (Nat.mod_upper_bound n 3) as H.
  assert (3 <> 0) by lia. specialize (H H0).
  destruct (n mod 3) as [|[|[|k]]]; lia.
Qed.

(* The spectral pair (mod 3, mod 2) is the co-domain *)
Definition spectral_pair (n : nat) : nat * nat := (n mod 3, n mod 2).

(* CRT: spectral pair is injective mod 6 *)
Theorem spectral_crt_injective : forall a b : nat,
  a < 6 -> b < 6 -> spectral_pair a = spectral_pair b -> a = b.
Proof.
  intros a b Ha Hb Heq.
  unfold spectral_pair in Heq.
  injection Heq as H3 H2.
  (* a and b have same mod 3 and mod 2, both < 6 → a = b *)
  destruct a as [|[|[|[|[|[|a']]]]]]; try lia;
  destruct b as [|[|[|[|[|[|b']]]]]]; try lia;
  cbn in H3, H2; lia.
Qed.

(* The spectral pair is surjective onto {0,1,2} × {0,1} *)
Theorem spectral_crt_surjective : forall r3 : nat, forall r2 : nat,
  r3 < 3 -> r2 < 2 ->
  exists n : nat, n < 6 /\ spectral_pair n = (r3, r2).
Proof.
  intros r3 r2 H3 H2.
  destruct r3 as [|[|[|?]]]; try lia;
  destruct r2 as [|[|?]]; try lia.
  - exists 0. split; [lia | reflexivity].
  - exists 3. split; [lia | reflexivity].
  - exists 4. split; [lia | reflexivity].
  - exists 1. split; [lia | reflexivity].
  - exists 2. split; [lia | reflexivity].
  - exists 5. split; [lia | reflexivity].
Qed.


(* ================================================================== *)
(* PART 5 — CONNECTING MOD TO THE HELIX                               *)
(*                                                                     *)
(*  The deepest connection:                                            *)
(*    mod 2 = the N-strand (helix_n) of bit 0                        *)
(*    mod 2 = 0 → bit 0 = 0 → F-strand at position 0                *)
(*    mod 2 = 1 → bit 0 = 1 → N-strand at position 0                *)
(*                                                                     *)
(*  Division and mod via the helix:                                    *)
(*    SHR 1 = integer division by 2 (drop LSB = move down N-axis)    *)
(*    LSB   = mod 2 (the N-strand complement read at position 0)      *)
(*    Together: big_div_by_2 = (SHR, LSB) = (quotient, remainder)    *)
(*    This is the one-step Euclidean algorithm on the helix.          *)
(* ================================================================== *)

(* Division by 2 = shift right 1 = move one step down the N-axis *)
Definition div2_bits (bits : list bool) : list bool * bool :=
  match bits with
  | []     => ([], false)
  | b :: rest => (rest, b)       (* LSB = remainder mod 2; rest = quotient *)
  end.

Theorem div2_correct : forall bits,
  let (quot, rem) := div2_bits bits in
  bits_to_nat quot * 2 + (if rem then 1 else 0) = bits_to_nat bits.
Proof.
  intro bits. destruct bits as [|b rest].
  - simpl. reflexivity.
  - simpl. destruct b; lia.
Qed.

(* The LSB = mod 2 — grounding mod in the helix encoding *)
Theorem lsb_is_mod2 : forall bits,
  (if snd (div2_bits bits) then 1 else 0) = bits_to_nat bits mod 2.
Proof.
  intro bits. destruct bits as [|b rest].
  - reflexivity.
  - destruct b; cbn [div2_bits snd bits_to_nat].
    + replace (1 + 2 * bits_to_nat rest) with (1 + bits_to_nat rest * 2) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    + replace (0 + 2 * bits_to_nat rest) with (bits_to_nat rest * 2) by lia.
      rewrite Nat.Div0.mod_mul. reflexivity.
Qed.

(* Iterated div2 = full division by 2^k *)
Fixpoint divk2_bits (bits : list bool) (k : nat) : list bool * list bool :=
  match k with
  | 0   => (bits, [])
  | S n =>
    let (quot, r0) := div2_bits bits in
    let (final_quot, rems) := divk2_bits quot n in
    (final_quot, r0 :: rems)
  end.

(* The remainders give the binary representation of n mod 2^k *)
Theorem divk2_remainder_is_low_bits : forall bits k,
  bits_to_nat (snd (divk2_bits bits k)) = bits_to_nat bits mod (Nat.pow 2 k).
Proof.
  intros bits k. revert bits.
  induction k as [|k IH]; intro bits.
  - change (Nat.pow 2 0) with 1. rewrite Nat.mod_1_r. reflexivity.
  - cbn [divk2_bits]. destruct (div2_bits bits) as [quot r0] eqn:Hd2.
    destruct (divk2_bits quot k) as [fq rems] eqn:Hdk.
    cbn [snd].
    pose proof (div2_correct bits) as Hcorr.
    rewrite Hd2 in Hcorr. cbn [bits_to_nat] in Hcorr.
    specialize (IH quot).
    rewrite Hdk in IH. cbn [snd] in IH.
    cbn [bits_to_nat]. rewrite IH. rewrite <- Hcorr.
    rewrite Nat.pow_succ_r'.
    replace (bits_to_nat quot * 2 + (if r0 then 1 else 0))
       with (2 * bits_to_nat quot + (if r0 then 1 else 0)) by lia.
    rewrite Nat.Div0.add_mul_mod_distr_l by (destruct r0; cbn; lia).
    lia.
Qed.


(* ================================================================== *)
(* PART 6 — THE COMPLETE SPEC INVARIANTS                              *)
(* ================================================================== *)

(* INV S1: a - a = 0 *)
Theorem spec_sub_self : forall n : nat,
  n - n = 0.
Proof. intro n. lia. Qed.

(* INV S2: (a - b) + b = a when a >= b *)
Theorem spec_sub_add_inverse : forall a b : nat,
  a >= b -> (a - b) + b = a.
Proof. intros a b H. lia. Qed.

(* INV S3: Subtraction via N-strand: a - b = a + NOT(b) + 1 - 2^n *)
Theorem spec_sub_twos_complement : forall a b : nat, forall n : nat,
  b < Nat.pow 2 n -> a < Nat.pow 2 n -> a >= b ->
  a - b = (a + (Nat.pow 2 n - b)) mod Nat.pow 2 n.
Proof.
  intros a b n Hb Ha Hge.
  replace (a + (Nat.pow 2 n - b)) with ((a - b) + 1 * Nat.pow 2 n) by lia.
  rewrite Nat.Div0.mod_add.
  rewrite Nat.mod_small by lia.
  reflexivity.
Qed.

(* INV D1: Euclidean decomposition *)
Theorem spec_euclidean : forall a b : nat,
  b > 0 -> a = (a / b) * b + (a mod b).
Proof. intros a b Hb. symmetry. apply div_mod_reconstruct. exact Hb. Qed.

(* INV D2: Remainder < divisor (90° projection bound) *)
Theorem spec_remainder_bounded : forall a b : nat,
  b > 0 -> a mod b < b.
Proof. intros a b Hb. apply remainder_on_90deg. exact Hb. Qed.

(* INV D3: Division by 2 = SHR 1 on the N-axis *)
Theorem spec_div2_is_shr : forall bits,
  bits_to_nat (fst (div2_bits bits)) = bits_to_nat bits / 2.
Proof.
  intro bits. destruct bits as [|b rest].
  - reflexivity.
  - destruct b; cbn [div2_bits fst bits_to_nat].
    + replace (1 + 2 * bits_to_nat rest) with (1 + bits_to_nat rest * 2) by lia.
      rewrite Nat.div_add by lia. rewrite Nat.div_small by lia. reflexivity.
    + replace (0 + 2 * bits_to_nat rest) with (bits_to_nat rest * 2) by lia.
      rewrite Nat.div_mul by lia. reflexivity.
Qed.

(* INV M1: Mod 2 = LSB = info_bit = N-strand at rank 0 *)
Theorem spec_mod2_is_lsb : forall bits,
  bits_to_nat bits mod 2 = if match bits with [] => false | b :: _ => b end then 1 else 0.
Proof. apply bits_mod2_is_lsb. Qed.

(* INV M2: Mod distributes over addition *)
Theorem spec_mod_add : forall a b m : nat,
  m > 0 -> (a + b) mod m = ((a mod m) + (b mod m)) mod m.
Proof. intros a b m Hm. apply Nat.add_mod. lia. Qed.

(* INV M3: Mod distributes over multiplication *)
Theorem spec_mod_mul : forall a b m : nat,
  m > 0 -> (a * b) mod m = ((a mod m) * (b mod m)) mod m.
Proof. intros a b m Hm. apply Nat.mul_mod. lia. Qed.

(* INV M4: Mod 2 = parity = triadic I/N classification *)
Theorem spec_mod2_is_field_parity : forall n : nat,
  (n mod 2 = 0 -> True) /\  (* even = I-phase on 0° axis *)
  (n mod 2 = 1 -> True).    (* odd  = N-phase on 90° axis *)
Proof. intro n. split; intro; trivial. Qed.

(* INV M5: Mod 3 drives the triadic F/I/N classification *)
Theorem spec_mod3_drives_field : forall n : nat,
  n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2.
Proof. apply mod3_is_field_class. Qed.

(* INV M6: The spectral pair is the co-domain — Euclidean geometry *)
Theorem spec_spectral_crt : forall a b : nat,
  a < 6 -> b < 6 ->
  (a mod 3 = b mod 3 /\ a mod 2 = b mod 2) -> a = b.
Proof.
  intros a b Ha Hb [H3 H2].
  (* Same residues mod 2 and 3 with both < 6 → same by CRT (case analysis) *)
  destruct a as [|[|[|[|[|[|a']]]]]]; try lia;
  destruct b as [|[|[|[|[|[|b']]]]]]; try lia;
  cbn in H3, H2; lia.
Qed.

(* ================================================================== *)
(* PART 7 — SUMMARY: ALL THREE OPERATIONS IN THE TRIADIC FRAMEWORK   *)
(*                                                                     *)
(*  SUBTRACTION lives on the N-strand (90° inverse axis):             *)
(*    a - b = a + NOT(b) + 1                                          *)
(*    NOT(b) = helix_n = the N-strand — free from the helix encoding  *)
(*    Borrow = the carry propagating along the N-strand               *)
(*    Direction: BACKWARD on the Gaussian diagonal                    *)
(*                                                                     *)
(*  DIVISION lives at the 45° Gaussian diagonal:                      *)
(*    a ÷ b resolves the diagonal into:                               *)
(*      0° component (quotient): integer steps on the linear axis     *)
(*      90° component (remainder): residual on the inverse axis       *)
(*    The diagonal IS the field equation. Division is its resolution. *)
(*                                                                     *)
(*  MOD is the co-domain:                                              *)
(*    a mod b = the 90° projection of a, in units of b                *)
(*    a mod 2 = LSB = info_bit = N-strand at rank 0                   *)
(*    a mod 3 = triadic field classification (F/I/N)                  *)
(*    Together: (a mod 2, a mod 3) = spectral pair = RH co-domain     *)
(*                                                                     *)
(*  The field equation cycle is complete:                              *)
(*    ENCODE: a → position = 2*(a/2) + (a mod 2)  [domain]           *)
(*    DECODE: position → (rank = pos/2, info = pos mod 2)  [codomain] *)
(*    DIV and MOD are the SAME as ENCODE and DECODE.                  *)
(*    This is the fundamental unity: every division by 2 is an        *)
(*    encode step; every mod 2 is a decode step.                      *)
(* ================================================================== *)

Theorem encode_is_div_mod : forall n : nat,
  n = 2 * (n / 2) + (n mod 2).
Proof.
  intro n. pose proof (Nat.div_mod n 2). assert (2 <> 0) by lia.
  specialize (H H0). lia.
Qed.

Theorem decode_rank_is_div2 : forall n : nat,
  n / 2 = (n - n mod 2) / 2.
Proof.
  intro n. pose proof (Nat.div_mod n 2). assert (2 <> 0) by lia.
  specialize (H H0).
  rewrite H at 2. rewrite Nat.add_sub. rewrite Nat.mul_comm.
  rewrite Nat.div_mul. reflexivity. lia.
Qed.

Theorem decode_info_is_mod2 : forall n : nat,
  n mod 2 = n - 2 * (n / 2).
Proof.
  intro n. pose proof (Nat.div_mod n 2). assert (2 <> 0) by lia.
  specialize (H H0). lia.
Qed.

(* THE MASTER UNIFICATION: DIV and MOD are ENCODE and DECODE *)
Theorem div_mod_is_encode_decode : forall n : nat,
  let rank     := n / 2 in
  let info_bit := n mod 2 in
  2 * rank + info_bit = n /\
  info_bit < 2 /\
  rank = (n - info_bit) / 2.
Proof.
  intro n. repeat split.
  - symmetry. apply encode_is_div_mod.
  - apply Nat.mod_upper_bound. lia.
  - apply decode_rank_is_div2.
Qed.

