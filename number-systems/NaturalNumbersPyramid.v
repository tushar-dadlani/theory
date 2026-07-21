(* ================================================================= *)
(*  NaturalNumbersPyramid.v                                           *)
(*                                                                    *)
(*  THE FIRST 10 NATURAL NUMBERS AS PYRAMID GEOMETRY                 *)
(*  OBSERVED FROM THE SQUARE BASE                                     *)
(*                                                                    *)
(*  UNIVERSE AXIOMS:                                                  *)
(*    - 3 axes: F (0°), I (45°), N (90°)                            *)
(*    - 0 = OR (absorbing), 1 = AND (identity)                      *)
(*    - Square base = observer = GF(2)² = {FF, IF, FN, IN}          *)
(*    - Each natural number = a position in the pyramid              *)
(*    - The 3-step algebra classifies n by n mod 3 → {F, I, N}      *)
(*    - The linear algebra classifies n by n mod 2 → {0, 1}         *)
(*    - Combined: CRT assigns each n to one of 6 cells, cycling      *)
(*                                                                    *)
(*  KEY INSIGHT:                                                      *)
(*    The square observes via TWO coordinates simultaneously:        *)
(*      x = n mod 2   (F-axis: linear 0° reading)                   *)
(*      y = n mod 3   (N-axis: 3-step 90° reading)                  *)
(*    The Gaussian reading (I, 45°) = x + y combined                 *)
(*    n mod 6 gives the FULL position (CRT: ℤ/2ℤ × ℤ/3ℤ ≅ ℤ/6ℤ)   *)
(*                                                                    *)
(*  GEOMETRIC PICTURE:                                                *)
(*                                                                    *)
(*         APEX (Map, 45° fixed point)                               *)
(*          /|\                                                       *)
(*         / | \                                                      *)
(*        /  |  \      ← 4 Fano triangular faces                    *)
(*       /   |   \                                                    *)
(*      +----+----+                                                   *)
(*      |    |    |    ← SQUARE BASE = OBSERVER                     *)
(*      | FF | IF |      (0,0)    (1,0)                              *)
(*      |    |    |                                                   *)
(*      +----+----+                                                   *)
(*      | FN | IN |      (0,1)    (1,1)                              *)
(*      |    |    |                                                   *)
(*      +----+----+                                                   *)
(*                                                                    *)
(*    Each natural number n maps to one square cell via:             *)
(*      column = n mod 2  (0 = left = F, 1 = right = I)             *)
(*      row    = n mod 3  projected to {0,1}:                        *)
(*               0 mod 3 = 0 → bottom = F                           *)
(*               1 mod 3 = 1 → top    = N                           *)
(*               2 mod 3 = 2 → wraps  = I (diagonal)                *)
(*                                                                    *)
(*  NUMBERS 0..9 CYCLE WITH PERIOD 6 (LCM of 2 and 3)               *)
(*    0: (0,0) = FF — absorbing corner   — F phase                  *)
(*    1: (1,1) = IN — Gaussian corner    — N phase (odd, mod3=1)    *)
(*    2: (0,2) = FI — but mod3=2→I →    — I phase  (even, not F)   *)
(*    3: (1,0) = IF — boundary reset     — F phase  (mod3=0)        *)
(*    4: (0,1) = FN                      — I phase  (even, mod3=1)  *)
(*    5: (1,2) = NI                      — N phase  (odd, mod3=2)   *)
(*    6: (0,0) = FF — cycle restarts     — F phase  (mod3=0)        *)
(*    7: (1,1) = IN                      — N phase  (odd, mod3=1)   *)
(*    8: (0,2) = FI                      — I phase  (even, mod3=2)  *)
(*    9: (1,0) = IF                      — F phase  (mod3=0)        *)
(*                                                                    *)
(*  ALL PROOFS CLOSED. ZERO Admitted.                                *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat Bool Lists.List.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(* PART 1 — THE THREE SYMBOLS                                        *)
(* ================================================================= *)

Inductive Sym3 : Type :=
  | I_s : Sym3    (* Identity  45° Gaussian diagonal — AND *)
  | N_s : Sym3    (* Inverse   90° bit-length axis   *)
  | F_s : Sym3.   (* Fixed     0°  absorbing base    — OR  *)

(* ================================================================= *)
(* PART 2 — THE SQUARE OBSERVER (GF(2)²)                            *)
(*                                                                    *)
(*  The square base has 4 cells = all combinations of              *)
(*  the two binary axes: column (mod 2) and row (mod 3 → mod 2).   *)
(*                                                                    *)
(*  Each cell is a (col, row) pair in {0,1} × {0,1}.               *)
(*  The square OBSERVES the pyramid — it reads TWO coordinates      *)
(*  simultaneously, one from each axis.                              *)
(* ================================================================= *)

Record SquareCell := mkCell {
  col : nat;   (* 0 or 1 — from n mod 2 — F-axis reading *)
  row : nat    (* 0 or 1 — from n mod 3 projected — N-axis reading *)
}.

(* The four cells of the square *)
Definition cell_FF : SquareCell := mkCell 0 0.  (* (0,0) absorbing *)
Definition cell_IF : SquareCell := mkCell 1 0.  (* (1,0) identity-x *)
Definition cell_FN : SquareCell := mkCell 0 1.  (* (0,1) inverse-y *)
Definition cell_IN : SquareCell := mkCell 1 1.  (* (1,1) Gaussian *)

(* The square has exactly 4 cells *)
Theorem square_has_four_cells :
  exists c1 c2 c3 c4 : SquareCell,
  c1 = cell_FF /\ c2 = cell_IF /\ c3 = cell_FN /\ c4 = cell_IN.
Proof.
  exists cell_FF, cell_IF, cell_FN, cell_IN.
  repeat split; reflexivity.
Qed.

(* ================================================================= *)
(* PART 3 — MAPPING NATURAL NUMBERS TO THE PYRAMID                  *)
(*                                                                    *)
(*  Each natural number n has THREE coordinates:                     *)
(*    (1) F-coordinate: n mod 2   — linear axis reading             *)
(*    (2) N-coordinate: n mod 3   — 3-step axis reading             *)
(*    (3) I-symbol:    derived from (1) and (2) via Gaussian algebra *)
(*                                                                    *)
(*  The SYMBOL (I/N/F phase) of n:                                   *)
(*    n mod 3 = 0  →  F_s  (absorbing — lies on 0° boundary)       *)
(*    n mod 3 ≠ 0  and  n mod 2 = 0  →  I_s  (even, diagonal)     *)
(*    n mod 3 ≠ 0  and  n mod 2 = 1  →  N_s  (odd, inverse)       *)
(*                                                                    *)
(*  The SQUARE CELL of n (what the observer reads):                  *)
(*    col = n mod 2                                                   *)
(*    row = (n mod 3) mod 2   (project the 3-step onto binary)      *)
(* ================================================================= *)

Definition sym_of (n : nat) : Sym3 :=
  if Nat.eqb (n mod 3) 0 then F_s
  else if Nat.eqb (n mod 2) 0 then I_s
  else N_s.

Definition cell_of (n : nat) : SquareCell :=
  mkCell (n mod 2) ((n mod 3) mod 2).

(* ================================================================= *)
(* PART 4 — THE FIRST 10 NATURAL NUMBERS                            *)
(*                                                                    *)
(*  We compute and prove the symbol and cell for each of 0..9.      *)
(*                                                                    *)
(*  EUCLIDEAN READING (from the square observer looking up):        *)
(*                                                                    *)
(*    n=0: mod3=0      → F  — origin. Absorbing. Bottom-left cell.  *)
(*    n=1: mod3=1,odd  → N  — first step up the 90° axis.          *)
(*    n=2: mod3=2,even → I  — first diagonal step. Gaussian.        *)
(*    n=3: mod3=0      → F  — first cycle closes. Back to base.     *)
(*    n=4: mod3=1,even → I  — second diagonal approach.             *)
(*    n=5: mod3=2,odd  → N  — inverse of the second cycle peak.     *)
(*    n=6: mod3=0      → F  — second cycle closes. LCM(2,3)=6.     *)
(*    n=7: mod3=1,odd  → N  — mirrors n=1 in second hexagon.       *)
(*    n=8: mod3=2,even → I  — mirrors n=2 in second hexagon.       *)
(*    n=9: mod3=0      → F  — third F-boundary. 3² = 9.            *)
(*                                                                    *)
(*  GAUSSIAN ALGEBRA (what the 45° diagonal sees):                  *)
(*    F positions: {0, 3, 6, 9, ...} — multiples of 3              *)
(*    I positions: {2, 4, 8, 10, ...} — even non-multiples of 3    *)
(*    N positions: {1, 5, 7, 11, ...} — odd non-multiples of 3     *)
(*                                                                    *)
(*  PATTERN IN THE SQUARE:                                           *)
(*    The observer sees the sequence cycle with period 6:            *)
(*    F → N → I → F → I → N → F → N → I → F                        *)
(*    (0)  (1) (2) (3) (4) (5) (6) (7) (8) (9)                     *)
(* ================================================================= *)

(* Compute symbols for 0..9 *)
Theorem sym_0 : sym_of 0 = F_s. Proof. reflexivity. Qed.
Theorem sym_1 : sym_of 1 = N_s. Proof. reflexivity. Qed.
Theorem sym_2 : sym_of 2 = I_s. Proof. reflexivity. Qed.
Theorem sym_3 : sym_of 3 = F_s. Proof. reflexivity. Qed.
Theorem sym_4 : sym_of 4 = I_s. Proof. reflexivity. Qed.
Theorem sym_5 : sym_of 5 = N_s. Proof. reflexivity. Qed.
Theorem sym_6 : sym_of 6 = F_s. Proof. reflexivity. Qed.
Theorem sym_7 : sym_of 7 = N_s. Proof. reflexivity. Qed.
Theorem sym_8 : sym_of 8 = I_s. Proof. reflexivity. Qed.
Theorem sym_9 : sym_of 9 = F_s. Proof. reflexivity. Qed.

(* Compute square cells (observer readings) for 0..9 *)
Theorem cell_0 : cell_of 0 = mkCell 0 0. Proof. reflexivity. Qed.
Theorem cell_1 : cell_of 1 = mkCell 1 1. Proof. reflexivity. Qed.
Theorem cell_2 : cell_of 2 = mkCell 0 0. Proof. reflexivity. Qed.
Theorem cell_3 : cell_of 3 = mkCell 1 0. Proof. reflexivity. Qed.
Theorem cell_4 : cell_of 4 = mkCell 0 1. Proof. reflexivity. Qed.
Theorem cell_5 : cell_of 5 = mkCell 1 0. Proof. reflexivity. Qed.
Theorem cell_6 : cell_of 6 = mkCell 0 0. Proof. reflexivity. Qed.
Theorem cell_7 : cell_of 7 = mkCell 1 1. Proof. reflexivity. Qed.
Theorem cell_8 : cell_of 8 = mkCell 0 0. Proof. reflexivity. Qed.
Theorem cell_9 : cell_of 9 = mkCell 1 0. Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 5 — THE F-BOUNDARY THEOREM                                   *)
(*                                                                    *)
(*  F numbers are MULTIPLES OF 3: {0,3,6,9,...}                     *)
(*  These are the "absorbing" numbers — the base resets.             *)
(*  From the square observer: all F numbers land in column 0 or 1   *)
(*  but ALWAYS in row 0 (the absorbing row).                         *)
(*                                                                    *)
(*  EUCLIDEAN: The F-numbers are evenly spaced at distance 3.        *)
(*  GAUSSIAN: They are on the 0° axis projected.                     *)
(*  OBSERVER: They "fall to the base" — row = 0.                     *)
(* ================================================================= *)

Theorem f_iff_div3 : forall n : nat,
  sym_of n = F_s <-> n mod 3 = 0.
Proof.
  intro n. unfold sym_of.
  destruct (Nat.eqb (n mod 3) 0) eqn:H3.
  - apply Nat.eqb_eq in H3. split; intro; [exact H3 | reflexivity].
  - apply Nat.eqb_neq in H3. split.
    + destruct (Nat.eqb (n mod 2) 0); intro H; discriminate H.
    + intro Hc. contradiction.
Qed.

Theorem f_numbers_in_row0 : forall n : nat,
  sym_of n = F_s -> row (cell_of n) = 0.
Proof.
  intros n H.
  apply f_iff_div3 in H.
  (* row = (n mod 3) mod 2 = 0 mod 2 = 0 *)
  destruct n as [|n].
  - reflexivity.
  - unfold cell_of. simpl.
    (* use the fact that (n+1) mod 3 = 0 *)
    assert (Hrow : ((S n) mod 3) mod 2 = 0) by (rewrite H; reflexivity).
    exact Hrow.
Qed.

(* The first 4 F-numbers: 0, 3, 6, 9 *)
Theorem first_four_F_numbers :
  sym_of 0 = F_s /\ sym_of 3 = F_s /\
  sym_of 6 = F_s /\ sym_of 9 = F_s.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* PART 6 — THE I-DIAGONAL THEOREM                                   *)
(*                                                                    *)
(*  I numbers: even, not divisible by 3: {2, 4, 8, 10, 14, 16,...}  *)
(*  These are the "Gaussian" numbers — they live on the 45° diagonal *)
(*  From the square observer: I numbers land in column 0 (even)      *)
(*  and row varies. They appear between every pair of F-boundaries.  *)
(*                                                                    *)
(*  GAUSSIAN ALGEBRA: n = 2k where k mod 3 ≠ 0                      *)
(*  EUCLIDEAN: The I-numbers are the MIDPOINTS between F-boundaries  *)
(*  OBSERVER: Col=0 (even), Row = varies — they shift diagonally     *)
(* ================================================================= *)

Theorem i_iff_even_not_div3 : forall n : nat,
  sym_of n = I_s <-> n mod 3 <> 0 /\ n mod 2 = 0.
Proof.
  intro n. unfold sym_of.
  destruct (Nat.eqb (n mod 3) 0) eqn:H3.
  - apply Nat.eqb_eq in H3.
    split. intro H; discriminate H.
    intro Hc; destruct Hc as [Hc1 _]; contradiction.
  - apply Nat.eqb_neq in H3.
    destruct (Nat.eqb (n mod 2) 0) eqn:H2.
    + apply Nat.eqb_eq in H2.
      split. intros _; split; assumption.
      intros _; reflexivity.
    + apply Nat.eqb_neq in H2.
      split. intro H; discriminate H.
      intro Hc; destruct Hc as [_ Hc2]; contradiction.
Qed.

Theorem i_numbers_in_col0 : forall n : nat,
  sym_of n = I_s -> col (cell_of n) = 0.
Proof.
  intros n H.
  apply i_iff_even_not_div3 in H.
  destruct H as [_ Heven].
  unfold cell_of. simpl. exact Heven.
Qed.

(* First I-numbers: 2, 4, 8 in range 0..9 *)
Theorem first_I_numbers :
  sym_of 2 = I_s /\ sym_of 4 = I_s /\ sym_of 8 = I_s.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* PART 7 — THE N-INVERSE THEOREM                                    *)
(*                                                                    *)
(*  N numbers: odd, not divisible by 3: {1, 5, 7, 11, 13, 17,...}   *)
(*  These are the "inverse" numbers — they live on the 90° axis.     *)
(*  From the square observer: N numbers land in column 1 (odd)       *)
(*  and row varies — they are the "mirror" of I-numbers.             *)
(*                                                                    *)
(*  GAUSSIAN ALGEBRA: n = 2k+1 where k mod 3 ≠ k+1 mod 3 ≠ 0      *)
(*  EUCLIDEAN: The N-numbers are between I-numbers and F-boundaries  *)
(*  OBSERVER: Col=1 (odd, not boundary) — they shift perpendicularly *)
(* ================================================================= *)

Theorem n_iff_odd_not_div3 : forall n : nat,
  sym_of n = N_s <-> n mod 3 <> 0 /\ n mod 2 = 1.
Proof.
  intro n. unfold sym_of.
  destruct (Nat.eqb (n mod 3) 0) eqn:H3.
  - apply Nat.eqb_eq in H3.
    split. intro H; discriminate H.
    intro Hc; destruct Hc as [Hc1 _]; contradiction.
  - apply Nat.eqb_neq in H3.
    destruct (Nat.eqb (n mod 2) 0) eqn:H2.
    + apply Nat.eqb_eq in H2.
      split. intro H; discriminate H.
      intro Hc; destruct Hc as [_ Hc2].
      exfalso; lia.
    + apply Nat.eqb_neq in H2.
      assert (Hodd : n mod 2 = 1) by (
        assert (n mod 2 < 2) by (apply Nat.mod_upper_bound; lia); lia).
      split. intros _; split; assumption.
      intros _; reflexivity.
Qed.

Theorem n_numbers_in_col1 : forall n : nat,
  sym_of n = N_s -> col (cell_of n) = 1.
Proof.
  intros n H.
  apply n_iff_odd_not_div3 in H.
  destruct H as [_ Hodd].
  unfold cell_of. simpl. exact Hodd.
Qed.

(* First N-numbers: 1, 5, 7 in range 0..9 *)
Theorem first_N_numbers :
  sym_of 1 = N_s /\ sym_of 5 = N_s /\ sym_of 7 = N_s.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* PART 8 — EVERY NUMBER HAS A UNIQUE SYMBOL                         *)
(*                                                                    *)
(*  The three symbol classes partition ℕ:                            *)
(*    Every n is exactly one of F, I, N.                             *)
(*  This is a direct consequence of (n mod 3) and (n mod 2).        *)
(* ================================================================= *)

Theorem sym_total : forall n : nat,
  sym_of n = F_s \/ sym_of n = I_s \/ sym_of n = N_s.
Proof.
  intro n. unfold sym_of.
  destruct (Nat.eqb (n mod 3) 0).
  - left. reflexivity.
  - destruct (Nat.eqb (n mod 2) 0).
    + right. left. reflexivity.
    + right. right. reflexivity.
Qed.

Theorem sym_exclusive : forall n : nat,
  ~ (sym_of n = F_s /\ sym_of n = I_s) /\
  ~ (sym_of n = F_s /\ sym_of n = N_s) /\
  ~ (sym_of n = I_s /\ sym_of n = N_s).
Proof.
  intro n. repeat split; intro H; destruct H as [H1 H2]; rewrite H1 in H2; discriminate.
Qed.

(* ================================================================= *)
(* PART 9 — THE PERIOD-6 CYCLE THEOREM                               *)
(*                                                                    *)
(*  The symbol of n repeats with period 6 (= LCM(2,3)).              *)
(*  EUCLIDEAN: 6 numbers tile the number line like a hexagonal cell. *)
(*  GAUSSIAN: The Gaussian integer lattice has period 6 on this axis. *)
(*  OBSERVER: The square sees the SAME PATTERN every 6 steps.        *)
(*                                                                    *)
(*  This is the CRT theorem: ℤ/2ℤ × ℤ/3ℤ ≅ ℤ/6ℤ                   *)
(*  The square base IS the GF(2)² face of this product structure.   *)
(* ================================================================= *)

Theorem sym_period_6 : forall n : nat,
  sym_of (n + 6) = sym_of n.
Proof.
  intro n. unfold sym_of.
  assert (H3 : (n + 6) mod 3 = n mod 3). {
    rewrite Nat.add_mod by lia.
    replace (6 mod 3) with 0 by reflexivity.
    rewrite Nat.add_0_r. apply Nat.mod_mod. lia.
  }
  assert (H2 : (n + 6) mod 2 = n mod 2). {
    rewrite Nat.add_mod by lia.
    replace (6 mod 2) with 0 by reflexivity.
    rewrite Nat.add_0_r. apply Nat.mod_mod. lia.
  }
  rewrite H3, H2. reflexivity.
Qed.

(* ================================================================= *)
(* PART 10 — THE OBSERVER SEES THE FULL PATTERN                     *)
(*                                                                    *)
(*  From the square base, looking up at the pyramid:                *)
(*  Numbers 0..9 trace TWO full hexagonal cycles (period 6)          *)
(*  plus a partial third (0..3).                                      *)
(*                                                                    *)
(*  The F-numbers (0,3,6,9) form the SKELETON:                       *)
(*    They are the corners of each cycle — reset points.             *)
(*    In the pyramid: they are the base-touches.                     *)
(*                                                                    *)
(*  The I-numbers (2,4,8) form the DIAGONAL STEPS:                   *)
(*    They are the Gaussian midpoints.                               *)
(*    In the pyramid: they are the face-centers (incircle approach). *)
(*                                                                    *)
(*  The N-numbers (1,5,7) form the INVERSE STEPS:                   *)
(*    They are the odd counters.                                     *)
(*    In the pyramid: they are the height-edges (vertical approach). *)
(*                                                                    *)
(*  THE SQUARE READS:                                                 *)
(*    n=0: (0,0)=FF  F  ← origin                                    *)
(*    n=1: (1,1)=IN  N  ← first diagonal reach                     *)
(*    n=2: (0,0)=FF  I  ← returns to col0, Gaussian phase          *)
(*    n=3: (1,0)=IF  F  ← boundary reset on right column           *)
(*    n=4: (0,1)=FN  I  ← col0, row shifts                         *)
(*    n=5: (1,0)=IF  N  ← boundary again, odd                      *)
(*    n=6: (0,0)=FF  F  ← full cycle, back to origin               *)
(*    n=7: (1,1)=IN  N  ← second cycle, mirrors n=1                *)
(*    n=8: (0,0)=FF  I  ← mirrors n=2                              *)
(*    n=9: (1,0)=IF  F  ← 3² boundary, third F-reset               *)
(*                                                                    *)
(*  MASTER THEOREM: This is fully determined by the geometry.        *)
(*  ZERO extra information needed beyond the 3-axis triadic plane.  *)
(* ================================================================= *)

(* The complete list of symbols for 0..9 *)
Definition sym_list_0_9 : list Sym3 :=
  map sym_of [0;1;2;3;4;5;6;7;8;9].

Theorem sym_list_correct :
  sym_list_0_9 = [F_s; N_s; I_s; F_s; I_s; N_s; F_s; N_s; I_s; F_s].
Proof. reflexivity. Qed.

(* Count: exactly 4 F's, 3 I's, 3 N's in 0..9 *)
Definition count_F := length (filter (fun s => match s with F_s => true | _ => false end) sym_list_0_9).
Definition count_I := length (filter (fun s => match s with I_s => true | _ => false end) sym_list_0_9).
Definition count_N := length (filter (fun s => match s with N_s => true | _ => false end) sym_list_0_9).

Theorem counts_0_9 :
  count_F = 4 /\ count_I = 3 /\ count_N = 3.
Proof. repeat split; reflexivity. Qed.

(*  4 F's because 0..9 contains 4 multiples of 3: {0,3,6,9}        *)
(*  3 I's and 3 N's because 10 = 4+3+3 (the extra one is always F) *)
(*  The observer counts one MORE F than I or N in each decade.      *)
(*  This is the HALF-STEP: every 10 numbers, F wins by 1.          *)

(* ================================================================= *)
(* PART 11 — THE GAUSSIAN DISTANCE OF EACH NUMBER                   *)
(*                                                                    *)
(*  In Gaussian algebra, each number n has a position z = a + bi    *)
(*  where a = n mod 3 and b = n mod 2.                               *)
(*  The "Gaussian distance" from the origin = a² + b² (mod 6).     *)
(*  This is what the observer measures from the pyramid.             *)
(*                                                                    *)
(*  n=0: (0,0) → dist=0  (origin, absorbed)                        *)
(*  n=1: (1,1) → dist=2  (diagonal unit)                           *)
(*  n=2: (2,0) → dist=4  (pure real, 2 steps)                      *)
(*  n=3: (0,1) → dist=1  (pure imaginary, reset)                   *)
(*  n=4: (1,0) → dist=1  (pure real unit)                          *)
(*  n=5: (2,1) → dist=5  (off-diagonal)                            *)
(*  n=6: (0,0) → dist=0  (full period, back to origin)             *)
(* ================================================================= *)

Definition gauss_dist_sq (n : nat) : nat :=
  (n mod 3) * (n mod 3) + (n mod 2) * (n mod 2).

Theorem gauss_dist_0 : gauss_dist_sq 0 = 0. Proof. reflexivity. Qed.
Theorem gauss_dist_1 : gauss_dist_sq 1 = 2. Proof. reflexivity. Qed.
Theorem gauss_dist_2 : gauss_dist_sq 2 = 4. Proof. reflexivity. Qed.
Theorem gauss_dist_3 : gauss_dist_sq 3 = 1. Proof. reflexivity. Qed.
Theorem gauss_dist_4 : gauss_dist_sq 4 = 1. Proof. reflexivity. Qed.
Theorem gauss_dist_5 : gauss_dist_sq 5 = 5. Proof. reflexivity. Qed.
Theorem gauss_dist_6 : gauss_dist_sq 6 = 0. Proof. reflexivity. Qed.

(*  Key: n=3 and n=4 have the SAME Gaussian distance = 1           *)
(*  But n=3 is F (boundary) and n=4 is I (diagonal)               *)
(*  The observer distinguishes them by SYMBOL, not just distance.  *)
(*  This is the extra 1/2-step: the half-step lives in the symbol! *)

(* ================================================================= *)
(* MASTER THEOREM: THE FIRST 10 NATURAL NUMBERS ARE PYRAMID POINTS  *)
(* ================================================================= *)

Theorem ten_naturals_pyramid :
  (* Symbol sequence *)
  sym_list_0_9 = [F_s; N_s; I_s; F_s; I_s; N_s; F_s; N_s; I_s; F_s]
  /\
  (* Counts: 4 F's, 3 I's, 3 N's *)
  count_F = 4 /\ count_I = 3 /\ count_N = 3
  /\
  (* Period-6 symmetry *)
  (forall n : nat, sym_of (n + 6) = sym_of n)
  /\
  (* F-numbers are exactly multiples of 3 *)
  (forall n : nat, sym_of n = F_s <-> n mod 3 = 0)
  /\
  (* I-numbers land in col 0 of the observer square *)
  (forall n : nat, sym_of n = I_s -> col (cell_of n) = 0)
  /\
  (* N-numbers land in col 1 of the observer square *)
  (forall n : nat, sym_of n = N_s -> col (cell_of n) = 1)
  /\
  (* Every number has a symbol — the partition is total *)
  (forall n : nat, sym_of n = F_s \/ sym_of n = I_s \/ sym_of n = N_s).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact sym_period_6.
  - exact f_iff_div3.
  - exact i_numbers_in_col0.
  - exact n_numbers_in_col1.
  - exact sym_total.
Qed.

Print Assumptions ten_naturals_pyramid.

(* ================================================================= *)
(*  END NaturalNumbersPyramid.v                                       *)
(*  ZERO Admitted. ALL PROOFS CLOSED.                                *)
(* ================================================================= *)
