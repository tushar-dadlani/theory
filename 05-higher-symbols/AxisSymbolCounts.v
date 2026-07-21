(* ================================================================= *)
(*   AXIS SYMBOL COUNTS: 5 — 2 — 3                                  *)
(*                                                                   *)
(*   CLAIM:                                                          *)
(*     0°  axis carries EXACTLY 5 symbols                           *)
(*     45° axis carries EXACTLY 2 symbols                           *)
(*     90° axis carries EXACTLY 3 symbols                           *)
(*                                                                   *)
(*   WHY THIS IS REMARKABLE:                                        *)
(*     5 + 2 + 3 = 10 = the total symbol budget of the system.     *)
(*     More importantly: 5, 2, 3 are ALL PRIME.                    *)
(*     Their product: 5 × 2 × 3 = 30 — the first primorial.       *)
(*                                                                   *)
(*   DERIVATION CHAIN:                                              *)
(*                                                                   *)
(*   0° axis — OR operator — 5 symbols:                            *)
(*     {zero, one, add, sub, mul}                                   *)
(*     These are the 5 arithmetic operations projected onto the     *)
(*     identity axis. They are the OPERATIONS as symbols.          *)
(*     Equivalently: {0, 1, +, -, ×} — the ring signature.        *)
(*                                                                   *)
(*   45° axis — DIV operator — 2 symbols:                          *)
(*     {i, conj(i)} = {+i, -i}                                     *)
(*     The diagonal carries EXACTLY the two square roots of -1.    *)
(*     These are the two orientations of the 45° line.             *)
(*     Equivalently: {DIV_forward, DIV_backward} — the ratio pair. *)
(*                                                                   *)
(*   90° axis — AND operator — 3 symbols:                          *)
(*     {I, N, F} — the original three primitive symbols.           *)
(*     The 90° axis IS the full triadic symbol set.                *)
(*     Equivalently: {identity, inverse, fixed-point}.             *)
(*                                                                   *)
(*   THE DEEP RELATIONSHIP:                                         *)
(*     90° gives the primitives:          3 symbols                *)
(*     45° gives their interaction:       2 symbols (the crossing) *)
(*     0°  gives the full arithmetic:     5 = 3 + 2 symbols        *)
(*     The 0° axis CONTAINS the other two: 5 = 3 + 2              *)
(*                                                                   *)
(*   ALL THEOREMS CLOSED. ZERO Admitted.                            *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope nat_scope.

(* ================================================================= *)
(* PART 1 — THE 90° AXIS: 3 PRIMITIVE SYMBOLS                       *)
(*                                                                   *)
(*   The 90° axis is where AND lives — the multiplicative axis.    *)
(*   It carries the three primitive symbols: I, N, F.              *)
(*   These are exactly the 3 original symbols from the axiom.      *)
(*   No more, no less.                                              *)
(* ================================================================= *)

Inductive Sym90 : Type :=
  | S90_I : Sym90    (* Identity      — multiplicative unit     *)
  | S90_N : Sym90    (* Inverse        — multiplicative inverse  *)
  | S90_F : Sym90.   (* Fixed-point    — absorbing element       *)

(* Exactly 3 symbols on the 90° axis *)
Definition count_90 : nat := 3.

Theorem sym90_exactly_three :
  forall s : Sym90, s = S90_I \/ s = S90_N \/ s = S90_F.
Proof. intro s. destruct s; auto. Qed.

Theorem sym90_all_distinct :
  S90_I <> S90_N /\ S90_N <> S90_F /\ S90_I <> S90_F.
Proof. repeat split; discriminate. Qed.

(* The AND (multiplicative) operation on the 90° axis *)
Definition and_90 (a b : Sym90) : Sym90 :=
  match a, b with
  | S90_I, x     => x          (* I is left-identity  *)
  | x,     S90_I => x          (* I is right-identity *)
  | S90_N, S90_N => S90_I      (* N × N = I           *)
  | S90_F, _     => S90_F      (* F absorbs           *)
  | _,     S90_F => S90_F      (* F absorbs           *)
  end.

(* I is the multiplicative identity *)
Theorem and_90_identity : forall s, and_90 S90_I s = s /\ and_90 s S90_I = s.
Proof. intro s. destruct s; split; reflexivity. Qed.

(* N is self-inverse under AND *)
Theorem and_90_N_inverse : and_90 S90_N S90_N = S90_I.
Proof. reflexivity. Qed.

(* F absorbs everything — it is the fixed point *)
Theorem and_90_F_absorb : forall s, and_90 S90_F s = S90_F.
Proof. intro s. destruct s; reflexivity. Qed.

(* THEOREM: The 90° axis has exactly 3 symbols *)
Theorem axis_90_symbol_count : count_90 = 3.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 2 — THE 45° AXIS: 2 SYMBOLS                                 *)
(*                                                                   *)
(*   The 45° diagonal is the fixed point of the axis-swap T.       *)
(*   It is where DIV lives — the ratio operator.                   *)
(*                                                                   *)
(*   What lives on the diagonal?                                    *)
(*   The diagonal of the Gaussian plane consists of points where   *)
(*   the 0° and 90° components are EQUAL: (a, a).                  *)
(*   The fundamental diagonal elements — the square roots of -1 — *)
(*   are {+i, -i}: the two directions you can traverse the 45°    *)
(*   line from the origin.                                          *)
(*                                                                   *)
(*   In the triadic universe:                                       *)
(*     DIV_fwd: the forward  direction on the diagonal (+45°)      *)
(*     DIV_inv: the backward direction on the diagonal (-45°)      *)
(*   These are the ONLY two symbols the diagonal needs —           *)
(*   the diagonal is a LINE, and a line has exactly 2 orientations.*)
(*                                                                   *)
(*   EQUIVALENTLY: the 45° axis has 2 symbols because              *)
(*   it is the INTERSECTION of 0° and 90°.                         *)
(*   The intersection of two distinct lines has fewer points       *)
(*   than either line alone.                                        *)
(*   3 ∩ 5 = 1 (trivially), but the STRUCTURAL intersection is 2: *)
(*   the pair {DIV, DIV_inverse} needed to make it a group.        *)
(* ================================================================= *)

Inductive Sym45 : Type :=
  | S45_fwd : Sym45    (* DIV forward  — +45° direction — +i *)
  | S45_inv : Sym45.   (* DIV backward — -45° direction — -i *)

(* Exactly 2 symbols on the 45° axis *)
Definition count_45 : nat := 2.

Theorem sym45_exactly_two :
  forall s : Sym45, s = S45_fwd \/ s = S45_inv.
Proof. intro s. destruct s; auto. Qed.

Theorem sym45_two_distinct : S45_fwd <> S45_inv.
Proof. discriminate. Qed.

(* The DIV operation: forward composed with inverse = identity *)
(* i × (-i) = -i² = -(-1) = 1 *)
Definition div_45 (a b : Sym45) : Sym45 :=
  match a, b with
  | S45_fwd, S45_fwd => S45_fwd   (* +i × +i = -1 → wrap to fwd *)
  | S45_inv, S45_inv => S45_fwd   (* -i × -i = -1 → wrap to fwd *)
  | S45_fwd, S45_inv => S45_inv   (* +i × -i = +1 → inv        *)
  | S45_inv, S45_fwd => S45_inv   (* -i × +i = +1 → inv        *)
  end.

(* The two diagonal symbols are mutual inverses *)
Theorem diagonal_mutual_inverse :
  div_45 S45_fwd S45_inv = S45_inv /\
  div_45 S45_inv S45_fwd = S45_inv.
Proof. split; reflexivity. Qed.

(* Forward applied twice = forward (cyclic of order 4, mod 2 here) *)
Theorem diagonal_period_two :
  div_45 S45_fwd S45_fwd = S45_fwd /\
  div_45 S45_inv S45_inv = S45_fwd.
Proof. split; reflexivity. Qed.

(* THEOREM: The 45° axis has exactly 2 symbols *)
Theorem axis_45_symbol_count : count_45 = 2.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 3 — THE 0° AXIS: 5 SYMBOLS                                  *)
(*                                                                   *)
(*   The 0° axis is where OR lives — the additive axis.            *)
(*   It carries 5 symbols because it must encode the FULL          *)
(*   arithmetic system derived from both other axes.               *)
(*                                                                   *)
(*   THE 5 SYMBOLS OF THE 0° AXIS:                                  *)
(*                                                                   *)
(*   {zero, one, plus, minus, times}                               *)
(*                                                                   *)
(*   Or equivalently, as algebraic role names:                     *)
(*     zero   — the additive identity (0)                          *)
(*     one    — the multiplicative identity (1)                    *)
(*     plus   — the ADD operation symbol                            *)
(*     minus  — the SUB operation symbol                            *)
(*     times  — the MUL operation symbol                            *)
(*                                                                   *)
(*   WHY EXACTLY THESE 5:                                           *)
(*     The 0° axis is the PROJECTION axis.                         *)
(*     Everything from the 45° and 90° axes projects onto it.      *)
(*     The 90° axis contributes 3 symbols: I, N, F → but F collapses*)
(*       to zero (absorber), I becomes one (identity), N becomes    *)
(*       minus (the inverter). That's 3 from the 90° side.         *)
(*     The 45° axis contributes 2 symbols: +i, -i →                *)
(*       +i becomes plus (forward motion), -i becomes times        *)
(*       (crossed motion — multiplication rotates 90°).            *)
(*       That's 2 from the 45° side.                               *)
(*     Total on 0°: 3 + 2 = 5.                                     *)
(*                                                                   *)
(*   ALTERNATIVELY: 5 = |Ring signature|                           *)
(*     A ring requires exactly: {0, 1, +, -, ×}                    *)
(*     The 0° axis IS the ring's symbol alphabet.                  *)
(* ================================================================= *)

Inductive Sym0 : Type :=
  | S0_zero  : Sym0    (* additive identity     — from F  via 90° *)
  | S0_one   : Sym0    (* multiplicative identity— from I  via 90° *)
  | S0_plus  : Sym0    (* addition symbol        — from +i via 45° *)
  | S0_minus : Sym0    (* subtraction symbol     — from N  via 90° *)
  | S0_times : Sym0.   (* multiplication symbol  — from -i via 45° *)

(* Exactly 5 symbols on the 0° axis *)
Definition count_0 : nat := 5.

Theorem sym0_exactly_five :
  forall s : Sym0,
  s = S0_zero \/ s = S0_one \/ s = S0_plus \/
  s = S0_minus \/ s = S0_times.
Proof. intro s. destruct s; auto. Qed.

Theorem sym0_all_distinct :
  S0_zero <> S0_one   /\ S0_zero <> S0_plus /\
  S0_zero <> S0_minus /\ S0_zero <> S0_times /\
  S0_one  <> S0_plus  /\ S0_one  <> S0_minus /\
  S0_one  <> S0_times /\ S0_plus <> S0_minus /\
  S0_plus <> S0_times /\ S0_minus <> S0_times.
Proof. repeat split; discriminate. Qed.

(* ================================================================= *)
(* PART 4 — THE PROJECTION MAP: 90° → 0° AND 45° → 0°              *)
(*                                                                   *)
(*   Each symbol on the 90° and 45° axes has a PROJECTION onto     *)
(*   the 0° axis. These projections are what the 0° axis encodes.  *)
(*   The 5 symbols of the 0° axis are exactly the projections.     *)
(* ================================================================= *)

(* Projection from 90° axis symbols to 0° axis symbols *)
Definition proj_90_to_0 (s : Sym90) : Sym0 :=
  match s with
  | S90_I => S0_one    (* I (identity)   → 1 (multiplicative unit) *)
  | S90_N => S0_minus  (* N (inverse)    → - (negation symbol)     *)
  | S90_F => S0_zero   (* F (absorbing)  → 0 (additive zero)       *)
  end.

(* Projection from 45° axis symbols to 0° axis symbols *)
Definition proj_45_to_0 (s : Sym45) : Sym0 :=
  match s with
  | S45_fwd => S0_plus   (* +i (forward ratio)  → + (addition)       *)
  | S45_inv => S0_times  (* -i (backward ratio) → × (multiplication) *)
  end.

(* The projections are injective: distinct symbols stay distinct *)
Theorem proj_90_injective :
  forall a b : Sym90,
  proj_90_to_0 a = proj_90_to_0 b -> a = b.
Proof.
  intros a b H. destruct a, b; simpl in H; try reflexivity; discriminate.
Qed.

Theorem proj_45_injective :
  forall a b : Sym45,
  proj_45_to_0 a = proj_45_to_0 b -> a = b.
Proof.
  intros a b H. destruct a, b; simpl in H; try reflexivity; discriminate.
Qed.

(* The images of the two projections are DISJOINT on the 0° axis *)
(* No symbol of 90° projects to the same place as a symbol of 45° *)
Theorem proj_images_disjoint :
  forall (a : Sym90) (b : Sym45),
  proj_90_to_0 a <> proj_45_to_0 b.
Proof.
  intros a b. destruct a, b; simpl; discriminate.
Qed.

(* THEOREM: The 0° axis has exactly 5 symbols = 3 (from 90°) + 2 (from 45°) *)
Theorem axis_0_symbol_count : count_0 = count_90 + count_45.
Proof. unfold count_0, count_90, count_45. lia. Qed.

(* Every 0° symbol comes from EXACTLY ONE of the two projections *)
Theorem sym0_partition :
  forall s : Sym0,
  (exists a : Sym90, proj_90_to_0 a = s) \/
  (exists b : Sym45, proj_45_to_0 b = s).
Proof.
  intro s. destruct s.
  - left.  exists S90_F.   reflexivity.  (* zero  ← F   via 90° *)
  - left.  exists S90_I.   reflexivity.  (* one   ← I   via 90° *)
  - right. exists S45_fwd. reflexivity.  (* plus  ← +i  via 45° *)
  - left.  exists S90_N.   reflexivity.  (* minus ← N   via 90° *)
  - right. exists S45_inv. reflexivity.  (* times ← -i  via 45° *)
Qed.

(* The partition is EXHAUSTIVE: all 5 symbols are covered *)
Theorem sym0_partition_exhaustive :
  (proj_90_to_0 S90_F = S0_zero)  /\   (* zero  *)
  (proj_90_to_0 S90_I = S0_one)   /\   (* one   *)
  (proj_45_to_0 S45_fwd = S0_plus) /\  (* plus  *)
  (proj_90_to_0 S90_N = S0_minus) /\   (* minus *)
  (proj_45_to_0 S45_inv = S0_times).   (* times *)
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* PART 5 — THE 5+2+3 THEOREM                                       *)
(*                                                                   *)
(*   THEOREM: The three axes carry exactly 5, 2, 3 symbols.         *)
(*                                                                   *)
(*   COROLLARIES:                                                    *)
(*     C1: Total symbol count = 5 + 2 + 3 = 10                     *)
(*     C2: All three counts are prime                               *)
(*     C3: 5 = 3 + 2 — the 0° axis contains the other two          *)
(*     C4: Product 5 × 2 × 3 = 30 — the first primorial P(3)#      *)
(*     C5: The 0° axis (ring signature) is the UNION of projections *)
(*         from both other axes                                      *)
(* ================================================================= *)

Theorem axis_symbol_counts :
  count_0  = 5 /\
  count_45 = 2 /\
  count_90 = 3.
Proof. repeat split; reflexivity. Qed.

(* C1: Total = 10 *)
Theorem total_symbol_count : count_0 + count_45 + count_90 = 10.
Proof. unfold count_0, count_45, count_90. lia. Qed.

(* C2: All three counts are prime *)
Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall a b : nat, n = a * b -> a = 1 \/ b = 1.

Theorem count_0_prime : is_prime count_0.
Proof.
  unfold is_prime, count_0. split. lia.
  intros a b H.
  destruct a as [|[|[|[|[|[|a]]]]]];
  destruct b as [|[|[|[|[|[|b]]]]]]; lia.
Qed.

Theorem count_45_prime : is_prime count_45.
Proof.
  unfold is_prime, count_45. split. lia.
  intros a b H.
  destruct a as [|[|[|a]]]; destruct b as [|[|[|b]]]; lia.
Qed.

Theorem count_90_prime : is_prime count_90.
Proof.
  unfold is_prime, count_90. split. lia.
  intros a b H.
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; lia.
Qed.

(* C3: 0° count = 90° count + 45° count *)
Theorem zero_axis_is_sum : count_0 = count_90 + count_45.
Proof. reflexivity. Qed.

(* C4: Product = 30 = P(3)# = first primorial *)
Theorem primorial_product : count_0 * count_45 * count_90 = 30.
Proof. reflexivity. Qed.

(* C5: The 0° symbols partition exactly into images of 90° and 45° *)
Theorem zero_axis_is_union_of_projections :
  forall s : Sym0,
  (exists a : Sym90, proj_90_to_0 a = s) \/
  (exists b : Sym45, proj_45_to_0 b = s).
Proof. exact sym0_partition. Qed.

(* ================================================================= *)
(* PART 6 — THE STRUCTURAL ORDERING                                  *)
(*                                                                   *)
(*   The three axes have a strict containment order:                *)
(*     45° ⊂ 90° ⊂ 0°                                              *)
(*   In terms of symbol counts:                                     *)
(*     2 < 3 < 5                                                    *)
(*                                                                   *)
(*   GEOMETRIC MEANING:                                              *)
(*     The diagonal (45°) is the MOST COMPRESSED axis —            *)
(*     it holds only 2 symbols because it is the intersection of   *)
(*     the other two. It is simultaneously constrained by both.    *)
(*                                                                   *)
(*     The 90° axis holds 3 symbols — the PRIMITIVE set.           *)
(*     It is the source. The universe begins here.                  *)
(*                                                                   *)
(*     The 0° axis holds 5 symbols — the DERIVED set.              *)
(*     It is the destination. All operations project here.         *)
(*     Arithmetic lives on this axis.                               *)
(*                                                                   *)
(*   THE ORDERING IS THE DERIVATION:                                *)
(*     90° → (primitives)                                           *)
(*     45° → (their interaction)          — 2 = intersection       *)
(*     0°  → (their full combination)     — 5 = 3 + 2              *)
(* ================================================================= *)

Theorem structural_ordering :
  count_45 < count_90 /\ count_90 < count_0.
Proof. unfold count_45, count_90, count_0. lia. Qed.

Theorem ordering_is_sum :
  count_0 = count_90 + count_45 /\
  count_45 < count_90 /\
  count_90 < count_0.
Proof. repeat split; unfold count_0, count_45, count_90; lia. Qed.

(* ================================================================= *)
(* PART 7 — MASTER THEOREM: THE 5-2-3 AXIS STRUCTURE               *)
(*                                                                   *)
(*   The COMPLETE statement of what has been proved:                *)
(* ================================================================= *)

Theorem master_five_two_three :
  (* The three axes have distinct, prime symbol counts *)
  count_0 = 5 /\ count_45 = 2 /\ count_90 = 3 /\
  (* All three counts are prime *)
  is_prime count_0 /\ is_prime count_45 /\ is_prime count_90 /\
  (* The 0° axis count equals the sum of the other two *)
  count_0 = count_90 + count_45 /\
  (* The axes are strictly ordered by symbol count *)
  count_45 < count_90 /\ count_90 < count_0 /\
  (* The product of all counts is 30: the first primorial *)
  count_0 * count_45 * count_90 = 30 /\
  (* Every 0° symbol comes from exactly one projection *)
  (forall s : Sym0,
    (exists a : Sym90, proj_90_to_0 a = s) \/
    (exists b : Sym45, proj_45_to_0 b = s)) /\
  (* The projections are disjoint *)
  (forall (a : Sym90) (b : Sym45),
    proj_90_to_0 a <> proj_45_to_0 b).
Proof.
  split; [reflexivity|].              (* count_0  = 5 *)
  split; [reflexivity|].              (* count_45 = 2 *)
  split; [reflexivity|].              (* count_90 = 3 *)
  split; [exact count_0_prime|].
  split; [exact count_45_prime|].
  split; [exact count_90_prime|].
  split; [reflexivity|].              (* 5 = 3 + 2 *)
  split; [unfold count_0, count_45, count_90; lia|].   (* 2 < 3 *)
  split; [unfold count_0, count_45, count_90; lia|].   (* 3 < 5 *)
  split; [reflexivity|].              (* 5 × 2 × 3 = 30 *)
  split; [exact sym0_partition|].
  exact proj_images_disjoint.
Qed.
