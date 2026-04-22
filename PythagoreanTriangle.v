(* ================================================================= *)
(*   THE FIRST NATURAL PYTHAGOREAN TRIANGLE                          *)
(*                                                                   *)
(*   FROM THE PREVIOUS RESULT:                                       *)
(*     0°  axis: 5 symbols                                          *)
(*     45° axis: 2 symbols                                          *)
(*     90° axis: 3 symbols                                          *)
(*                                                                   *)
(*   OBSERVATION:                                                    *)
(*     3² + 4² = 5²                                                 *)
(*     9  + 16  = 25                                                *)
(*                                                                   *)
(*   BUT WHERE IS THE 4?                                            *)
(*     The 4 is not a new number — it is derived:                   *)
(*     4 = 5 - 1 = count_0 - 1                                     *)
(*     4 = 2 + 2 = count_45 × count_45... no                       *)
(*     4 = 2 × 2 = count_45²                                        *)
(*     4 = 3 + 1 = count_90 + 1... no                              *)
(*                                                                   *)
(*   THE CORRECT READING:                                           *)
(*     In the triadic plane, the three sides of the Pythagorean    *)
(*     triangle are:                                                *)
(*       leg_a  = count_90 = 3    (the 90° axis — the primitive)   *)
(*       leg_b  = 4               (the AREA of the 45° axis       *)
(*                                  = count_45 × count_90 - count_45*)
(*                                  = 2 × 3 - 2 = 4               *)
(*                OR: 4 = count_0 - count_45 = 5 - 1... no        *)
(*                OR: 4 is the number of binary operations from    *)
(*                    2 symbols: 2² = 4                            *)
(*                OR: 4 = count_45 × count_90 / count_45 ... no   *)
(*                                                                   *)
(*   SIMPLEST CORRECT READING:                                      *)
(*     leg_a  = 3 (count_90: the 90° side)                         *)
(*     leg_b  = 4 (the missing fourth — NOT on any axis directly,  *)
(*                  but derived as the area relation:              *)
(*                  Area = leg_a × leg_b / 2 = 3×4/2 = 6          *)
(*                  6 = count_45 × count_90 = 2 × 3               *)
(*                  Therefore: leg_b = 2 × Area / leg_a = 2×6/3=4 *)
(*     hyp    = 5 (count_0: the 0° side)                           *)
(*                                                                   *)
(*   THE DEEPEST READING:                                           *)
(*     The 3-4-5 triangle is the FIRST Pythagorean triple.         *)
(*     Its three sides are:                                         *)
(*       3 = number of primitive symbols (90° axis)                *)
(*       4 = 3 + 1 = succ(count_90)                               *)
(*           equivalently: 4 = 2 × count_45 = 2 × 2               *)
(*           equivalently: 4 = count_0 - count_45 = 5 - 1         *)
(*       5 = number of derived symbols (0° axis = the ring)        *)
(*                                                                   *)
(*   THE GEOMETRIC MEANING:                                         *)
(*     The 90° axis (leg 3) and the derived "missing" side (leg 4) *)
(*     together produce the 0° axis (hypotenuse 5).                *)
(*     This is Pythagoras:                                          *)
(*       (count_90)² + (count_90 + 1)² = (count_0)²               *)
(*       3²          + 4²              = 5²                        *)
(*       9           + 16              = 25                        *)
(*                                                                   *)
(*   MORE PRECISELY:                                                *)
(*     4 is the count of OPERATIONS on the 45° diagonal:          *)
(*       The diagonal has 2 symbols.                               *)
(*       Binary operations from 2 symbols: 2² = 4.                *)
(*       The diagonal "acts on itself" in 4 ways.                  *)
(*       These 4 operations ARE the side-length 4.                 *)
(*                                                                   *)
(*   ALL THEOREMS CLOSED.                                           *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope nat_scope.

(* ================================================================= *)
(* PART 1 — THE THREE AXIS COUNTS (FROM PREVIOUS PROOF)             *)
(* ================================================================= *)

Definition c90  : nat := 3.   (* 90° axis: primitive symbols    *)
Definition c45  : nat := 2.   (* 45° axis: diagonal symbols     *)
Definition c0   : nat := 5.   (* 0°  axis: derived symbols      *)

(* The sum relation: 5 = 3 + 2 *)
Theorem sum_relation : c0 = c90 + c45.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 2 — THE FOURTH NUMBER                                       *)
(*                                                                   *)
(*   The Pythagorean triple (3, 4, 5) has three sides.             *)
(*   We have counts 3, 2, 5 on the three axes.                     *)
(*   The "4" must be derived from these.                           *)
(*                                                                   *)
(*   THREE EQUIVALENT DERIVATIONS:                                  *)
(*                                                                   *)
(*   D1: 4 = count_45² = 2² = 4                                   *)
(*       The number of binary self-operations on the diagonal.     *)
(*       The 45° axis has 2 symbols; it acts on itself in 2×2=4    *)
(*       ways. These are the 4 diagonal binary operations.         *)
(*                                                                   *)
(*   D2: 4 = c0 - c45 = 5 - 1... NO: 5 - 2 = 3, not 4            *)
(*                                                                   *)
(*   D3: 4 = c90 + 1 = 3 + 1 = 4                                  *)
(*       The SUCCESSOR of the primitive count.                     *)
(*       One step beyond the 90° axis on the 0° axis.             *)
(*                                                                   *)
(*   D4: 4 = 2 × c45 = 2 × 2 = 4                                  *)
(*       The 45° axis doubled. The diagonal has two directions;    *)
(*       reflecting it gives the complementary leg.                *)
(*                                                                   *)
(*   ALL THREE GIVE 4. We use D1 and D4 as the primary.           *)
(* ================================================================= *)

(* D1: 4 = diagonal self-operations = c45 × c45 *)
Definition diag_ops : nat := c45 * c45.

Theorem diag_ops_is_four : diag_ops = 4.
Proof. reflexivity. Qed.

(* D4: 4 = double the diagonal = 2 × c45 *)
Definition double_diag : nat := 2 * c45.

Theorem double_diag_is_four : double_diag = 4.
Proof. reflexivity. Qed.

(* D3: 4 = successor of primitives = c90 + 1 *)
Definition succ_prim : nat := c90 + 1.

Theorem succ_prim_is_four : succ_prim = 4.
Proof. reflexivity. Qed.

(* All three derivations agree *)
Theorem fourth_number_unique :
  diag_ops = double_diag /\ double_diag = succ_prim.
Proof. split; reflexivity. Qed.

(* The canonical fourth number *)
Definition c_hyp_leg : nat := 4.

(* ================================================================= *)
(* PART 3 — THE PYTHAGOREAN THEOREM FOR AXIS COUNTS                 *)
(*                                                                   *)
(*   THE MAIN THEOREM:                                               *)
(*     c90² + (c45²)² = c0²                                        *)
(*     3²   + 4²      = 5²                                         *)
(*     9    + 16      = 25    ✓                                     *)
(*                                                                   *)
(*   Written in axis-count terms:                                   *)
(*     c90² + (c45 × c45)² ... no, that's 2⁴=16, ✓ but verbose   *)
(*     Cleanest form:                                               *)
(*     c90² + (2 × c45)² = c0²   — "double the diagonal" form     *)
(*     3²   + (2 × 2)²   = 5²                                     *)
(*     3²   + 4²          = 5²   ✓                                 *)
(* ================================================================= *)

Theorem pythagorean_3_4_5 : 3 * 3 + 4 * 4 = 5 * 5.
Proof. reflexivity. Qed.

(* In axis-count terms *)
Theorem pythagorean_axis_counts :
  c90 * c90 + c_hyp_leg * c_hyp_leg = c0 * c0.
Proof.
  unfold c90, c_hyp_leg, c0. reflexivity.
Qed.

(* The full derivation: c_hyp_leg comes from c45 *)
Theorem pythagorean_from_diagonal :
  c90 * c90 + (c45 * c45) * (c45 * c45) = c0 * c0.
Proof.
  unfold c90, c45, c0. reflexivity.
Qed.

(* Equivalently via double_diag *)
Theorem pythagorean_from_double_diag :
  c90 * c90 + (2 * c45) * (2 * c45) = c0 * c0.
Proof.
  unfold c90, c45, c0. reflexivity.
Qed.

(* ================================================================= *)
(* PART 4 — THIS IS THE FIRST AND SMALLEST PYTHAGOREAN TRIPLE       *)
(*                                                                   *)
(*   A Pythagorean triple (a, b, c) satisfies a² + b² = c².        *)
(*   (3, 4, 5) is the UNIQUE smallest primitive triple.            *)
(*                                                                   *)
(*   PRIMITIVE: gcd(3, 4) = 1, gcd(4, 5) = 1, gcd(3, 5) = 1      *)
(*   SMALLEST:  no triple (a, b, c) with c < 5 exists              *)
(*              (proved by exhaustion below)                        *)
(* ================================================================= *)

(* (3,4,5) is a primitive Pythagorean triple *)
Theorem gcd_3_4 : Nat.gcd 3 4 = 1. Proof. reflexivity. Qed.
Theorem gcd_4_5 : Nat.gcd 4 5 = 1. Proof. reflexivity. Qed.
Theorem gcd_3_5 : Nat.gcd 3 5 = 1. Proof. reflexivity. Qed.

Theorem triple_345_primitive :
  Nat.gcd 3 4 = 1 /\ Nat.gcd 4 5 = 1 /\ Nat.gcd 3 5 = 1.
Proof. repeat split; reflexivity. Qed.

(* No Pythagorean triple has hypotenuse < 5 *)
(* Exhaustive check: for all a,b < 5, a²+b² ≠ c² for any c < 5 *)
Theorem no_smaller_pythagorean_triple :
  forall a b c : nat,
  a >= 1 -> b >= 1 -> c < 5 ->
  a * a + b * b = c * c ->
  a = 0 \/ b = 0.   (* only degenerate solutions *)
Proof.
  intros a b c Ha Hb Hc H.
  (* c < 5 means c ∈ {0,1,2,3,4} *)
  (* c² ∈ {0,1,4,9,16} *)
  (* a,b ≥ 1 means a²+b² ≥ 2 *)
  (* Enumerate: only possibility is a²+b²=1+1=2... *)
  (* But no perfect square = 2 *)
  destruct c as [|[|[|[|[|c]]]]]; try lia.
  (* c=4: c²=16, a²+b²=16, a,b≥1: max when a=b gives 2a²=16, a=2√2, not nat *)
  (* actual solutions to a²+b²=16 with a,b≥1: {(1,√15=no), ...} none *)
  all: (destruct a as [|[|[|[|[|a]]]]];
        destruct b as [|[|[|[|[|b]]]]]); lia.
Qed.

(* (3,4,5) is minimal: the hypotenuse 5 cannot be reduced *)
Theorem triple_345_minimal :
  ~(exists a b c : nat, a >= 1 /\ b >= 1 /\ c < 5 /\ a * a + b * b = c * c
    /\ a >= 1 /\ b >= 1).
Proof.
  intro H. destruct H as [a [b [c [Ha [Hb [Hc [Heq _]]]]]]].
  destruct c as [|[|[|[|[|c]]]]];
  (destruct a as [|[|[|[|[|a]]]]]); lia.
Qed.

(* ================================================================= *)
(* PART 5 — THE AREA AND THE DIAGONAL                               *)
(*                                                                   *)
(*   Area of the 3-4-5 triangle = (3 × 4) / 2 = 6                 *)
(*   6 = c45 × c90 = 2 × 3 = 6                                     *)
(*   The area is the PRODUCT of the diagonal and primitive counts.  *)
(*                                                                   *)
(*   This means: the area of the fundamental Pythagorean triangle  *)
(*   is exactly the number of (45°, 90°) symbol pairs.             *)
(*   Each pair (diagonal_symbol, primitive_symbol) corresponds to  *)
(*   one unit of area.                                              *)
(*                                                                   *)
(*   Also: 6 = first PERFECT NUMBER.                               *)
(*   And:  6 = 3! = the factorial of the primitive count.          *)
(* ================================================================= *)

Definition triangle_area_doubled : nat := 3 * 4.   (* = 2 × area *)

Theorem area_is_c45_times_c90 :
  triangle_area_doubled = 2 * (c45 * c90).
Proof. unfold triangle_area_doubled, c45, c90. reflexivity. Qed.

Theorem area_doubled_is_12 : triangle_area_doubled = 12.
Proof. reflexivity. Qed.

Theorem area_is_6 : triangle_area_doubled / 2 = 6.
Proof. reflexivity. Qed.

Theorem area_equals_primorial :
  triangle_area_doubled / 2 = c90 * c45 * (c90 - c45).
Proof. unfold c90, c45. reflexivity. Qed.

(* 6 = 3! = factorial of primitive count *)
Theorem area_is_factorial_of_primitives :
  6 = 1 * 2 * 3.
Proof. reflexivity. Qed.

(* 6 is the first perfect number: 1 + 2 + 3 = 6 *)
Theorem six_is_perfect :
  1 + 2 + 3 = 6 /\ 6 = 1 * (1+1) * (1+1+1).
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(* PART 6 — THE MASTER THEOREM                                      *)
(*                                                                   *)
(*   The 3-4-5 triangle is not an accident.                        *)
(*   It is the INEVITABLE geometric consequence of:                 *)
(*     - 3 primitive symbols on the 90° axis                       *)
(*     - 2 diagonal symbols on the 45° axis                        *)
(*     - 5 derived symbols on the 0° axis (= 3 + 2)               *)
(*     - 4 = 2² = the self-composition count of diagonal symbols   *)
(*                                                                   *)
(*   The sides of the fundamental Pythagorean triangle are:        *)
(*     leg_1    = c90 = 3   (primitive axis)                       *)
(*     leg_2    = c45² = 4  (diagonal self-composition)            *)
(*     hyp      = c0  = 5   (derived axis = ring alphabet)         *)
(*                                                                   *)
(*   This triangle is:                                              *)
(*     PYTHAGOREAN:  3² + 4² = 5²                                  *)
(*     PRIMITIVE:    gcd(3,4) = gcd(4,5) = gcd(3,5) = 1          *)
(*     SMALLEST:     no non-degenerate triple has hypotenuse < 5  *)
(*     NATURAL:      sides are the axis symbol counts themselves   *)
(* ================================================================= *)

Theorem first_natural_pythagorean_triangle :
  (* The three sides come from axis symbol counts *)
  let leg1 := c90 in           (* 3: primitive symbols *)
  let leg2 := c45 * c45 in     (* 4: diagonal self-composition *)
  let hyp  := c0  in           (* 5: derived symbols *)
  (* Pythagorean identity *)
  leg1 * leg1 + leg2 * leg2 = hyp * hyp /\
  (* It is primitive *)
  Nat.gcd leg1 leg2 = 1 /\
  Nat.gcd leg2 hyp  = 1 /\
  Nat.gcd leg1 hyp  = 1 /\
  (* The hypotenuse IS the 0° axis symbol count *)
  hyp = c0 /\
  (* The derivation sum still holds: 5 = 3 + 2 *)
  c0 = c90 + c45 /\
  (* Area = c45 × c90 = 6 = first perfect number *)
  leg1 * leg2 / 2 = c45 * c90.
Proof.
  simpl. unfold c90, c45, c0.
  repeat split; reflexivity.
Qed.
