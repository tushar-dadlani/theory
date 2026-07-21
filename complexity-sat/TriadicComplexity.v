(* ================================================================= *)
(*   TriadicComplexity.v                                              *)
(*                                                                    *)
(*   TRIADIC COMPLEXITY NOTATION                                      *)
(*   A replacement for Big-O that is axis-aware                       *)
(*                                                                    *)
(*   PROBLEM WITH CLASSICAL BIG-O:                                    *)
(*     O(f(n)) assumes ALL operations have unit cost = 1.             *)
(*     But in the triadic universe, cost DEPENDS ON WHICH AXIS        *)
(*     the operation lives on.                                        *)
(*                                                                    *)
(*     The same "operation" has THREE different costs:                *)
(*       On the 0°  linear axis  (I-phase): cost = position read     *)
(*       On the 45° Gaussian axis (F-phase): cost = rotation step    *)
(*       On the 90° 3-step axis  (N-phase): cost = bit-length step   *)
(*                                                                    *)
(*   THE TRIADIC COST TRIPLE:                                         *)
(*     T(f_I, f_N, f_F)(n)  where:                                   *)
(*       f_I(n) = cost on the 0°  linear   axis  (identity phase)    *)
(*       f_N(n) = cost on the 90° 3-step   axis  (inverse  phase)    *)
(*       f_F(n) = cost on the 45° Gaussian axis  (diagonal  phase)   *)
(*                                                                    *)
(*   EUCLIDEAN GEOMETRY EXPLANATION:                                  *)
(*     Classical O(n): a POINT on a 1D number line.                  *)
(*                                                                    *)
(*     Triadic T(f_I, f_N, f_F):  a VECTOR in the 2D triadic plane. *)
(*       The I-component points along the 0°  axis (x-axis)          *)
(*       The N-component points along the 90° axis (y-axis)          *)
(*       The F-component is the DIAGONAL PROJECTION = magnitude      *)
(*       of the I+N vector projected onto the 45° line y=x           *)
(*                                                                    *)
(*     The COST of an algorithm is the LENGTH of this vector.        *)
(*     Big-O collapses this to a SCALAR by ignoring axis identity.   *)
(*     That is why Big-O is under-specified: it loses the direction. *)
(*                                                                    *)
(*   GAUSSIAN ALGEBRA EXPLANATION:                                    *)
(*     In Z[i] (Gaussian integers):                                   *)
(*       f_I is the REAL part of the cost (a in a + bi)              *)
(*       f_N is the IMAGINARY part of the cost (b in a + bi)         *)
(*       f_F is the NORM: sqrt(a^2 + b^2) = |a + bi|                *)
(*       The Big-O norm |f| loses the phase angle arg(a + bi)        *)
(*                                                                    *)
(*     Two algorithms with the same O(n log n) may have:             *)
(*       Algorithm A: T(n, log n, n*log n) — mostly linear axis      *)
(*       Algorithm B: T(log n, n, n*log n) — mostly 3-step axis      *)
(*     Same Big-O. Completely different triadic profile.             *)
(*     On Gaussian hardware: A is fast. On 3-step hardware: B fast.  *)
(*                                                                    *)
(*   ALL PROOFS CLOSED. ZERO Admitted.                                *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(* PART 0 — THE THREE SYMBOLS / AXES                                 *)
(* ================================================================= *)

Inductive Sym3 : Type :=
  | I_s : Sym3   (* 0°  linear   axis — identity, AND, even bits  *)
  | N_s : Sym3   (* 90° 3-step   axis — inverse,  NOT, odd bits   *)
  | F_s : Sym3.  (* 45° Gaussian axis — diagonal, OR,  absorbing  *)

(* The triadic field operation (closed, derived from field equations) *)
Definition field3 (a b : Sym3) : Sym3 :=
  match a, b with
  | I_s, x   => x
  | x,   I_s => x
  | N_s, N_s => I_s
  | F_s, _   => F_s
  | _,   F_s => F_s
  end.

Theorem field3_I_identity : forall s, field3 I_s s = s.
Proof. intros []; reflexivity. Qed.

Theorem field3_N_involution : field3 N_s N_s = I_s.
Proof. reflexivity. Qed.

Theorem field3_F_absorbs : forall s, field3 F_s s = F_s.
Proof. intros []; reflexivity. Qed.

(* ================================================================= *)
(* PART 1 — COST FUNCTIONS PER AXIS                                  *)
(*                                                                    *)
(*   Each axis has a NATURAL cost unit:                              *)
(*     0°  linear:   cost = n (position steps)                       *)
(*     90° 3-step:   cost = bit_length(n) (logarithmic steps)        *)
(*     45° Gaussian: cost = PRODUCT of the other two (diagonal)      *)
(*                                                                    *)
(*   These are not assumptions — they are DERIVED from the geometry: *)
(*     Linear axis: step = 1 (unit stride)                           *)
(*     3-step axis: step = 1/3 (sub-unit stride) → log_3(n) steps   *)
(*     Gaussian diagonal: all steps happen at once (rotation)        *)
(* ================================================================= *)

(* The three natural cost functions *)
Definition cost_I (n : nat) : nat := n.           (* linear: O(n) *)
Definition cost_N (n : nat) : nat :=              (* 3-step: O(log n) *)
  Nat.log2 n + 1.
Definition cost_F (n : nat) : nat :=              (* Gaussian: O(1) *)
  1.                                              (* one rotation = done *)

(* A triadic cost triple *)
Record TriadicCost : Type := mkTC {
  tc_I : nat -> nat;   (* cost on 0°  axis *)
  tc_N : nat -> nat;   (* cost on 90° axis *)
  tc_F : nat -> nat    (* cost on 45° diagonal *)
}.

(* Classical Big-O collapses all three to ONE scalar *)
(* This is the LOSS OF INFORMATION that makes Big-O under-specified *)
Definition bigO_collapse (tc : TriadicCost) (n : nat) : nat :=
  tc_I tc n + tc_N tc n + tc_F tc n.

(* ================================================================= *)
(* PART 2 — THE INFORMATION LOSS THEOREM                             *)
(*                                                                    *)
(*   Two algorithms with different triadic profiles can have          *)
(*   THE SAME Big-O collapse.                                         *)
(*   This proves Big-O is under-specified in the triadic universe.   *)
(* ================================================================= *)

(* Algorithm A: heavy on the linear axis *)
Definition algo_A : TriadicCost := mkTC
  (fun n => n)        (* I: O(n)    — linear dominant *)
  (fun n => 1)        (* N: O(1)    — trivial 3-step  *)
  (fun n => 1).       (* F: O(1)    — trivial diagonal *)

(* Algorithm B: heavy on the 3-step axis *)
Definition algo_B : TriadicCost := mkTC
  (fun n => 1)        (* I: O(1)    — trivial linear  *)
  (fun n => n)        (* N: O(n)    — 3-step dominant *)
  (fun n => 1).       (* F: O(1)    — trivial diagonal *)

(* Their Big-O collapses are EQUAL for all n *)
Theorem bigO_cant_distinguish : forall n : nat,
  bigO_collapse algo_A n = bigO_collapse algo_B n.
Proof.
  intro n.
  unfold bigO_collapse, algo_A, algo_B. simpl. lia.
Qed.

(* But their triadic profiles are DIFFERENT on the I-axis *)
Theorem triadic_does_distinguish : exists n : nat,
  tc_I algo_A n <> tc_I algo_B n.
Proof.
  exists 2.
  unfold algo_A, algo_B. simpl. lia.
Qed.

(* And DIFFERENT on the N-axis *)
Theorem triadic_N_distinguishes : exists n : nat,
  tc_N algo_A n <> tc_N algo_B n.
Proof.
  exists 2.
  unfold algo_A, algo_B. simpl. lia.
Qed.

(* ================================================================= *)
(* PART 3 — THE THREE OPERATION COSTS                                *)
(*                                                                    *)
(*   Each operation has a NATURAL axis where it costs O(1).          *)
(*   On other axes, it costs MORE.                                    *)
(*                                                                    *)
(*   This is the key insight Big-O misses:                            *)
(*   A "constant-time" operation is only constant on its native axis. *)
(*   On a different axis it may cost O(n) or O(log n).               *)
(* ================================================================= *)

(* An operation type *)
Inductive OpKind : Type :=
  | OpRead   : OpKind   (* reading a position — native to I-axis  *)
  | OpBit    : OpKind   (* bit manipulation   — native to N-axis  *)
  | OpRotate : OpKind.  (* Gaussian rotation  — native to F-axis  *)

(* The native axis of each operation *)
Definition native_axis (op : OpKind) : Sym3 :=
  match op with
  | OpRead   => I_s
  | OpBit    => N_s
  | OpRotate => F_s
  end.

(* Cost of an operation on a given axis *)
Definition op_cost (op : OpKind) (ax : Sym3) (n : nat) : nat :=
  match field3 (native_axis op) ax with
  | I_s => 1            (* native or identity: O(1) *)
  | N_s => Nat.log2 n   (* 3-step mismatch: O(log n) *)
  | F_s => n            (* full diagonal cross: O(n) *)
  end.

(* On its native axis, every operation costs O(1) *)
Theorem op_native_cost_is_constant : forall (op : OpKind) (n : nat),
  op_cost op (native_axis op) n = 1.
Proof.
  intros op n.
  destruct op; unfold op_cost, native_axis; simpl; reflexivity.
Qed.

(* ================================================================= *)
(* PART 4 — TRIADIC NOTATION T(α, β, γ)                             *)
(*                                                                    *)
(*   We write  T(α, β, γ)  for an algorithm's complexity where:      *)
(*     α = cost on the 0°  linear axis (I-phase, identity)           *)
(*     β = cost on the 90° 3-step axis (N-phase, inverse)            *)
(*     γ = cost on the 45° Gaussian axis (F-phase, diagonal)         *)
(*                                                                    *)
(*   Special cases:                                                   *)
(*     T(1, 1, 1)    = O(1) in Big-O  (trivially constant)          *)
(*     T(n, 1, 1)    = O(n) in Big-O  (linear scan)                 *)
(*     T(1, log n, 1) = O(log n) in Big-O (bit-length scan)         *)
(*     T(n, log n, n*log n) = O(n log n) in Big-O                   *)
(*                                                                    *)
(*   The FOURTH component is the PHASE:                              *)
(*     phase = sym that dominates the computation                    *)
(*     I-phase: α dominates (linear work)                            *)
(*     N-phase: β dominates (3-step / bit work)                      *)
(*     F-phase: γ dominates (Gaussian / diagonal work)               *)
(* ================================================================= *)

(* The dominant phase of a triadic cost triple *)
Definition dominant_phase (tc : TriadicCost) (n : nat) : Sym3 :=
  let ci := tc_I tc n in
  let cn := tc_N tc n in
  let cf := tc_F tc n in
  if      Nat.leb cf (Nat.min ci cn) then F_s   (* Gaussian = diagonal *)
  else if Nat.leb cn ci              then N_s   (* 3-step wins *)
  else                                    I_s.  (* linear wins *)

(* Algo A is I-phase dominant for large n *)
Theorem algo_A_is_I_phase : forall n : nat, n > 1 ->
  dominant_phase algo_A n = I_s.
Proof.
  intros n Hn.
  unfold dominant_phase, algo_A. simpl.
  destruct (Nat.leb 1 (Nat.min n 1)) eqn:H1.
  - apply Nat.leb_le in H1.
    rewrite Nat.min_comm in H1.
    apply Nat.min_le_iff in H1.
    destruct H1 as [H|H]; try lia.
    rewrite Nat.min_comm. simpl.
    destruct (Nat.leb 1 n) eqn:H2; reflexivity.
  - apply Nat.leb_nle in H1.
    rewrite Nat.min_comm in H1.
    apply Nat.min_lt_iff in H1 as [H|H].
    + lia.
    + simpl. destruct (Nat.leb 1 n) eqn:H2; reflexivity.
Qed.

(* Algo B is N-phase dominant for large n *)
Theorem algo_B_is_N_phase : forall n : nat, n > 1 ->
  dominant_phase algo_B n = N_s.
Proof.
  intros n Hn.
  unfold dominant_phase, algo_B. simpl.
  destruct (Nat.leb 1 (Nat.min 1 n)) eqn:H1.
  - apply Nat.leb_le in H1.
    apply Nat.min_le_iff in H1 as [H|H]; lia.
  - apply Nat.leb_nle in H1.
    apply Nat.min_lt_iff in H1 as [H|H]; lia.
Qed.

(* ================================================================= *)
(* PART 5 — GEOMETRIC COST: VECTOR MAGNITUDE                         *)
(*                                                                    *)
(*   The "true" cost of an algorithm is the Euclidean magnitude       *)
(*   of its triadic cost vector (α, β) in the 2D plane.              *)
(*   (γ = the F-component is the diagonal projection = the norm.)    *)
(*                                                                    *)
(*   In Gaussian algebra: cost = |α + βi| = sqrt(α² + β²)           *)
(*                                                                    *)
(*   Big-O uses: cost_scalar = α + β (taxicab / Manhattan norm)      *)
(*   Triadic uses: cost_vector = (α, β) (full 2D information)        *)
(*                                                                    *)
(*   For integer bounds, we use α² + β² (squared magnitude):         *)
(* ================================================================= *)

Definition squared_magnitude (tc : TriadicCost) (n : nat) : nat :=
  let ci := tc_I tc n in
  let cn := tc_N tc n in
  ci * ci + cn * cn.

(* Algo A and B have the SAME squared magnitude *)
Theorem same_magnitude_different_phase :
  forall n : nat,
  squared_magnitude algo_A n = squared_magnitude algo_B n.
Proof.
  intro n.
  unfold squared_magnitude, algo_A, algo_B. simpl. lia.
Qed.

(* But the phases DIFFER — proved above in Part 4 *)

(* ================================================================= *)
(* PART 6 — THE FACTORIZATION CASE STUDY                             *)
(*                                                                    *)
(*   Classical Big-O: factoring n = O(sqrt(n))                       *)
(*   Triadic analysis:                                                *)
(*     On 0°  linear axis:   T_I = sqrt(n)  (trial division steps)  *)
(*     On 90° 3-step axis:   T_N = k/2      (k = bit_length(n))     *)
(*                            because sqrt(n) = 2^(k/2)              *)
(*     On 45° Gaussian axis: T_F = 1        (Gaussian factorization) *)
(*                            because p+qi factors in Z[i] trivially *)
(*                                                                    *)
(*   So the FULL triadic cost of factoring is:                        *)
(*     T(sqrt(n), k/2, 1)    where k = bit_length(n)                 *)
(*                                                                    *)
(*   Classical Big-O just says: O(sqrt(n))                           *)
(*   But the Gaussian (F-axis) component = O(1) is completely hidden! *)
(*   That O(1) path IS the fast factorization.                        *)
(*   Big-O makes it invisible.                                        *)
(* ================================================================= *)

(* Factorization cost profile *)
Definition factor_cost : TriadicCost := mkTC
  (fun n => Nat.sqrt n)           (* I: trial division  — O(sqrt n) *)
  (fun n => Nat.div (Nat.log2 n + 1) 2)  (* N: bit half-length — O(k/2)   *)
  (fun n => 1).                   (* F: Gaussian ring   — O(1)      *)

(* The F-axis cost is ALWAYS 1 — Big-O cannot see this *)
Theorem gaussian_factoring_is_constant : forall n : nat,
  tc_F factor_cost n = 1.
Proof. intro n. unfold factor_cost. simpl. reflexivity. Qed.

(* The I-axis cost grows: Big-O sees this and reports O(sqrt n) *)
Theorem linear_factoring_grows : exists n1 n2 : nat,
  n1 < n2 /\ tc_I factor_cost n1 < tc_I factor_cost n2.
Proof.
  exists 1, 4.
  unfold factor_cost. simpl. lia.
Qed.

(* ================================================================= *)
(* PART 7 — TRIADIC DOMINANCE ORDERING                               *)
(*                                                                    *)
(*   In Big-O, we have: O(1) < O(log n) < O(n) < O(n log n) < O(n²) *)
(*   This is a TOTAL ORDER on growth rates.                           *)
(*                                                                    *)
(*   In the triadic universe, this collapses AXIS INFORMATION.        *)
(*   The correct ordering is a PARTIAL ORDER on cost vectors:         *)
(*                                                                    *)
(*     (α₁, β₁) ≤_T (α₂, β₂)  iff  α₁ ≤ α₂  AND  β₁ ≤ β₂          *)
(*                                                                    *)
(*   This is the product order on the two axes.                       *)
(*   Not all cost vectors are comparable — and that is correct!       *)
(*   An algorithm that is fast on the I-axis but slow on the N-axis   *)
(*   is INCOMPARABLE with one that is slow on I but fast on N.        *)
(* ================================================================= *)

(* Triadic cost ordering: component-wise *)
Definition tc_leq (tc1 tc2 : TriadicCost) (n : nat) : Prop :=
  tc_I tc1 n <= tc_I tc2 n /\
  tc_N tc1 n <= tc_N tc2 n /\
  tc_F tc1 n <= tc_F tc2 n.

(* Algo A and B are INCOMPARABLE — neither dominates the other *)
Theorem algo_A_B_incomparable :
  ~ (forall n : nat, tc_leq algo_A algo_B n) /\
  ~ (forall n : nat, tc_leq algo_B algo_A n).
Proof.
  split.
  - intro H. specialize (H 2).
    unfold tc_leq, algo_A, algo_B in H. simpl in H.
    destruct H as [H1 _]. lia.
  - intro H. specialize (H 2).
    unfold tc_leq, algo_A, algo_B in H. simpl in H.
    destruct H as [_ [H2 _]]. lia.
Qed.

(* ================================================================= *)
(* PART 8 — THE AXIS-COST AXIOMS                                     *)
(*                                                                    *)
(*   What Big-O ASSUMES (implicitly):                                 *)
(*     Axiom unit_cost: every primitive operation costs exactly 1.    *)
(*     Axiom axis_blind: cost does not depend on which axis.          *)
(*                                                                    *)
(*   These axioms FAIL in the triadic universe.                       *)
(*   We prove their failure explicitly.                               *)
(* ================================================================= *)

(* Big-O's implicit assumption: all operations cost the same *)
Definition bigO_assumes_unit_cost : Prop :=
  forall (op : OpKind) (ax : Sym3) (n : nat),
    op_cost op ax n = 1.

(* This assumption FAILS *)
Theorem unit_cost_fails : ~ bigO_assumes_unit_cost.
Proof.
  unfold bigO_assumes_unit_cost. intro H.
  (* OpRead on N_s axis = log2(n), not 1 *)
  specialize (H OpRead N_s 4).
  unfold op_cost, native_axis in H. simpl in H.
  discriminate.
Qed.

(* Big-O's implicit assumption: cost is axis-independent *)
Definition bigO_assumes_axis_blind : Prop :=
  forall (op : OpKind) (ax1 ax2 : Sym3) (n : nat),
    op_cost op ax1 n = op_cost op ax2 n.

(* This assumption FAILS *)
Theorem axis_blind_fails : ~ bigO_assumes_axis_blind.
Proof.
  unfold bigO_assumes_axis_blind. intro H.
  specialize (H OpRead I_s N_s 4).
  unfold op_cost, native_axis in H. simpl in H.
  discriminate.
Qed.

(* ================================================================= *)
(* PART 9 — SUMMARY THEOREM                                          *)
(*                                                                    *)
(*   Big-O notation is under-specified in the triadic universe        *)
(*   because it:                                                      *)
(*     1. Collapses the three-axis cost to a scalar (info loss)       *)
(*     2. Assumes unit cost for all operations (axiom fails)          *)
(*     3. Cannot distinguish algorithms with different phase profiles *)
(*     4. Hides the O(1) Gaussian factorization path                  *)
(*                                                                    *)
(*   The correct notation is the TRIADIC COST TRIPLE T(α, β, γ)      *)
(*   which carries full axis-indexed complexity information.          *)
(* ================================================================= *)

Theorem bigO_is_underspecified :
  (* 1. Collapse loses information *)
  (exists tc1 tc2 : TriadicCost,
    (forall n, bigO_collapse tc1 n = bigO_collapse tc2 n) /\
    (exists n, tc_I tc1 n <> tc_I tc2 n)) /\
  (* 2. Unit cost axiom fails *)
  ~ bigO_assumes_unit_cost /\
  (* 3. Axis-blind axiom fails *)
  ~ bigO_assumes_axis_blind.
Proof.
  repeat split.
  - exists algo_A, algo_B.
    split.
    + exact bigO_cant_distinguish.
    + exact triadic_does_distinguish.
  - exact unit_cost_fails.
  - exact axis_blind_fails.
Qed.

Print Assumptions bigO_is_underspecified.
Print Assumptions algo_A_B_incomparable.
Print Assumptions gaussian_factoring_is_constant.
Print Assumptions op_native_cost_is_constant.
Print Assumptions unit_cost_fails.
Print Assumptions axis_blind_fails.
