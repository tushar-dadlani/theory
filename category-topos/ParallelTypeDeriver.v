(* ================================================================= *)
(*  ParallelTypeDeriver.v                                            *)
(*                                                                   *)
(*  TWO-PASS PARALLEL TYPE DERIVATION FROM UNICODE STRINGS          *)
(*                                                                   *)
(*  UNIVERSE:                                                        *)
(*    0,1 are symbols AND operators (0=OR, 1=AND)                   *)
(*    3 axes: F(0°), I(45°), N(90°)                                 *)
(*    Unicode codepoint → half-step position → {I,N,F}              *)
(*                                                                   *)
(*  THE TWO-PASS ARCHITECTURE:                                       *)
(*    Pass A: string_A → trace_A → fold_A → type_A                 *)
(*    Pass B: string_B → trace_B → fold_B → type_B                 *)
(*    Parallel: both passes run simultaneously, one sweep           *)
(*    Composition: type_A ∘ type_B → composed_type                  *)
(*    Recursive: composed_type feeds back as input                   *)
(*                                                                   *)
(*  TYPE HIERARCHY DERIVATION:                                       *)
(*    Level 0: raw Unicode codepoints (untyped)                     *)
(*    Level 1: half-step positions  (I-phase / N-phase)             *)
(*    Level 2: field symbols        {I, N, F}                       *)
(*    Level 3: fold result          one of {I, N, F}                *)
(*    Level 4: TheoremShape         the derived type                 *)
(*    Level 5: composed type        type_A ∘ type_B                 *)
(*    Level 6: recursive fixpoint   stable type under iteration     *)
(*                                                                   *)
(*  ALL PROOFS CLOSED. ZERO Admitted.                               *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat Lists.List Bool.Bool.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(* PART 1 — UNICODE TO HALF-STEP POSITION                          *)
(*                                                                   *)
(*  info_bit from Unicode category:                                  *)
(*    0 (I-phase, integer axis): letters, decimal digits            *)
(*    1 (N-phase, half-step axis): punctuation, symbols, spaces     *)
(*                                                                   *)
(*  position = 2 * rank + info_bit                                  *)
(*  rank = codepoint (the Unicode codepoint IS the rank)            *)
(*  position = 2 * codepoint + info_bit                             *)
(* ================================================================= *)

(* info_bit: we use codepoint parity as a proxy *)
(* Real system: uses Unicode category (Lu/Ll/Nd → 0, else → 1)    *)
Definition unicode_info_bit (cp : nat) : nat :=
  if Nat.eqb (cp mod 2) 0 then 0 else 1.

(* Half-step position from codepoint *)
Definition unicode_position (cp : nat) : nat :=
  2 * cp + unicode_info_bit cp.

(* Codepoint is recoverable from position *)
Definition position_to_rank (pos : nat) : nat := pos / 2.
Definition position_to_info (pos : nat) : nat := pos mod 2.

Theorem unicode_roundtrip : forall cp : nat,
  position_to_rank (unicode_position cp) = cp.
Proof.
  intro cp. unfold position_to_rank, unicode_position, unicode_info_bit.
  destruct (Nat.eqb (cp mod 2) 0).
  - replace (2 * cp + 0) with (cp * 2 + 0) by lia.
    rewrite Nat.div_add_l by lia. simpl. lia.
  - replace (2 * cp + 1) with (cp * 2 + 1) by lia.
    rewrite Nat.div_add_l by lia. simpl. lia.
Qed.

(* ================================================================= *)
(* PART 2 — FIELD CLASSIFICATION                                    *)
(*                                                                   *)
(*  From the half-step position, derive the field symbol.           *)
(*  This is the first type extraction step.                         *)
(* ================================================================= *)

Inductive Sym3 : Type :=
  | I_s : Sym3    (* 45° Gaussian diagonal — identity *)
  | N_s : Sym3    (* 90° 3-step inverse axis          *)
  | F_s : Sym3.   (* 0°  linear absorbing axis         *)

Definition field_classify (pos : nat) : Sym3 :=
  if Nat.eqb (pos mod 3) 0 then F_s
  else if Nat.eqb (pos mod 2) 0 then I_s
  else N_s.

Definition unicode_sym (cp : nat) : Sym3 :=
  field_classify (unicode_position cp).

Theorem classify_total : forall pos : nat,
  field_classify pos = I_s \/
  field_classify pos = N_s \/
  field_classify pos = F_s.
Proof.
  intro pos. unfold field_classify.
  destruct (Nat.eqb (pos mod 3) 0); auto.
  destruct (Nat.eqb (pos mod 2) 0); auto.
Qed.

(* ================================================================= *)
(* PART 3 — FIELD OPERATION AND FOLD                               *)
(* ================================================================= *)

Definition field_op (a b : Sym3) : Sym3 :=
  match a, b with
  | I_s, x   => x
  | x,   I_s => x
  | N_s, N_s => I_s
  | F_s, _   => F_s
  | _,   F_s => F_s
  end.

Lemma fold_from_F : forall syms : list Sym3,
  fold_left field_op syms F_s = F_s.
Proof.
  induction syms as [|s rest IH]; [reflexivity|].
  simpl. destruct s; simpl; exact IH.
Qed.

(* Classify a string of codepoints into a symbol trace *)
Definition classify_string (cps : list nat) : list Sym3 :=
  map unicode_sym cps.

(* Fold the trace to a single type symbol *)
Definition fold_string (cps : list nat) : Sym3 :=
  fold_left field_op (classify_string cps) I_s.

(* ================================================================= *)
(* PART 4 — TYPE HIERARCHY                                         *)
(*                                                                   *)
(*  Level 0: nat (codepoint)  — untyped                            *)
(*  Level 1: Sym3 (per char)  — character type                     *)
(*  Level 2: Sym3 (fold)      — string type                        *)
(*  Level 3: StringType       — semantic type                       *)
(*  Level 4: ComposedType     — two-string type                     *)
(*  Level 5: RecursiveType    — stable under iteration             *)
(* ================================================================= *)

(* Level 3: semantic types derived from fold result + string length *)
Inductive StringType : Type :=
  | ST_Identity   : StringType  (* I diagonal: relay/equality *)
  | ST_Iff        : StringType  (* I diagonal, long: bidirectional *)
  | ST_Implies    : StringType  (* I diagonal, odd: implication *)
  | ST_Negation   : StringType  (* N diagonal, short: negation *)
  | ST_Neq        : StringType  (* N diagonal, even: inequality *)
  | ST_Absurd     : StringType  (* N diagonal, long: contradiction *)
  | ST_Exists     : StringType  (* F diagonal, short: existential *)
  | ST_ForallEq   : StringType  (* F diagonal, even: universal eq *)
  | ST_ForallFn   : StringType  (* F diagonal, odd: universal fn *)
  .

Definition derive_string_type (cps : list nat) : StringType :=
  let diag := fold_string cps in
  let n    := length cps in
  match diag with
  | I_s => if Nat.leb n 2 then ST_Identity
            else if Nat.eqb (n mod 2) 0 then ST_Iff
            else ST_Implies
  | N_s => if Nat.leb n 2 then ST_Negation
            else if Nat.eqb (n mod 2) 0 then ST_Neq
            else ST_Absurd
  | F_s => if Nat.leb n 3 then ST_Exists
            else if Nat.eqb (n mod 2) 0 then ST_ForallEq
            else ST_ForallFn
  end.

Theorem string_type_total : forall cps : list nat,
  derive_string_type cps = ST_Identity  \/
  derive_string_type cps = ST_Iff       \/
  derive_string_type cps = ST_Implies   \/
  derive_string_type cps = ST_Negation  \/
  derive_string_type cps = ST_Neq       \/
  derive_string_type cps = ST_Absurd    \/
  derive_string_type cps = ST_Exists    \/
  derive_string_type cps = ST_ForallEq  \/
  derive_string_type cps = ST_ForallFn.
Proof.
  intro cps. unfold derive_string_type.
  destruct (fold_string cps);
  [ (* I_s *)
    destruct (Nat.leb (length cps) 2);
    [left; reflexivity |
     destruct (Nat.eqb (length cps mod 2) 0);
     [right; left; reflexivity | right; right; left; reflexivity]]
  | (* N_s *)
    destruct (Nat.leb (length cps) 2);
    [right; right; right; left; reflexivity |
     destruct (Nat.eqb (length cps mod 2) 0);
     [right; right; right; right; left; reflexivity |
      right; right; right; right; right; left; reflexivity]]
  | (* F_s *)
    destruct (Nat.leb (length cps) 3);
    [right; right; right; right; right; right; left; reflexivity |
     destruct (Nat.eqb (length cps mod 2) 0);
     [right; right; right; right; right; right; right; left; reflexivity |
      right; right; right; right; right; right; right; right; reflexivity]]
  ].
Qed.

(* ================================================================= *)
(* PART 5 — STRING TYPE TO SYM3 PROJECTION                        *)
(*                                                                   *)
(*  Every StringType lives on one of the three axes.               *)
(*  This projection is the "type of the type" — the meta-type.     *)
(* ================================================================= *)

Definition string_type_axis (st : StringType) : Sym3 :=
  match st with
  | ST_Identity | ST_Iff | ST_Implies => I_s   (* 45° axis types *)
  | ST_Negation | ST_Neq | ST_Absurd  => N_s   (* 90° axis types *)
  | ST_Exists | ST_ForallEq | ST_ForallFn => F_s (* 0° axis types *)
  end.

Theorem axis_from_diagonal : forall cps : list nat,
  string_type_axis (derive_string_type cps) = fold_string cps.
Proof.
  intro cps. unfold derive_string_type, string_type_axis.
  destruct (fold_string cps) eqn:H;
  destruct (Nat.leb (length cps) _);
  try destruct (Nat.eqb (length cps mod 2) 0);
  simpl; rewrite <- H; reflexivity.
Qed.

(* ================================================================= *)
(* PART 6 — PARALLEL TWO-PASS ARCHITECTURE                        *)
(*                                                                   *)
(*  Pass A and Pass B run simultaneously.                           *)
(*  Each produces a StringType independently.                       *)
(*  The composed type is field_op(axis_A, axis_B).                 *)
(*                                                                   *)
(*  This is the "2 parallel pass compiler":                        *)
(*    Input:  string_A, string_B                                    *)
(*    Pass A: classify → fold → type_A (concurrent)                *)
(*    Pass B: classify → fold → type_B (concurrent)                *)
(*    Join:   field_op(axis_A, axis_B) → composed_sym              *)
(*    Output: composed type with full type hierarchy                *)
(* ================================================================= *)

Record ParallelResult := mkPR {
  pr_type_A   : StringType
; pr_type_B   : StringType
; pr_axis_A   : Sym3
; pr_axis_B   : Sym3
; pr_composed : Sym3        (* field_op(axis_A, axis_B) *)
; pr_len_A    : nat
; pr_len_B    : nat
}.

Definition parallel_derive (cps_A cps_B : list nat) : ParallelResult :=
  let typeA := derive_string_type cps_A in
  let typeB := derive_string_type cps_B in
  let axA   := string_type_axis typeA in
  let axB   := string_type_axis typeB in
  mkPR typeA typeB axA axB
       (field_op axA axB)
       (length cps_A)
       (length cps_B).

(* The composition is determined by the axes *)
Theorem parallel_composition_determined : forall cps_A cps_B : list nat,
  pr_composed (parallel_derive cps_A cps_B) =
  field_op (fold_string cps_A) (fold_string cps_B).
Proof.
  intros cps_A cps_B.
  unfold parallel_derive. simpl.
  rewrite <- axis_from_diagonal.
  rewrite <- axis_from_diagonal.
  reflexivity.
Qed.

(* ================================================================= *)
(* PART 7 — RECURSIVE TYPE DERIVATION                              *)
(*                                                                   *)
(*  The composed type feeds back as the "type of the composition."  *)
(*  Apply derive again to the composed symbol sequence.             *)
(*  This is the recursive tower of types.                           *)
(*                                                                   *)
(*  At each level:                                                   *)
(*    level 0: raw strings       → StringType                       *)
(*    level 1: composed type     → StringType of composed           *)
(*    level 2: type of type      → Sym3 (the meta-type)             *)
(*    level k: stable when       field_op sym sym = sym             *)
(*                                                                   *)
(*  Fixed points of field_op:                                       *)
(*    field_op I I = I  ← stable                                   *)
(*    field_op N N = I  ← collapses to I (not stable as N)         *)
(*    field_op F F = F  ← stable                                   *)
(*  So the recursive process always terminates at I or F.           *)
(* ================================================================= *)

(* One recursive step: compose the axes *)
Definition recurse_step (sym : Sym3) : Sym3 :=
  field_op sym sym.

(* N collapses to I in one step *)
Theorem N_collapses : recurse_step N_s = I_s.
Proof. reflexivity. Qed.

(* I and F are fixed points *)
Theorem I_stable : recurse_step I_s = I_s.
Proof. reflexivity. Qed.

Theorem F_stable : recurse_step F_s = F_s.
Proof. reflexivity. Qed.

(* Every symbol reaches a fixed point in at most 1 step *)
Theorem convergence_in_1 : forall sym : Sym3,
  recurse_step (recurse_step sym) = recurse_step sym.
Proof.
  intro sym. destruct sym; reflexivity.
Qed.

(* The recursive type hierarchy stabilizes at level 2 *)
Theorem hierarchy_stabilizes : forall sym : Sym3,
  recurse_step sym = I_s \/ recurse_step sym = F_s.
Proof.
  intro sym. destruct sym.
  - left. reflexivity.
  - left. reflexivity.   (* N∘N = I *)
  - right. reflexivity.
Qed.

(* ================================================================= *)
(* PART 8 — FULL TYPE HIERARCHY RECORD                             *)
(* ================================================================= *)

Record TypeHierarchy := mkTH {
  (* Level 0: raw input *)
  th_cps_A     : list nat
; th_cps_B     : list nat
  (* Level 1: character classification (trace) *)
; th_trace_A   : list Sym3
; th_trace_B   : list Sym3
  (* Level 2: string fold (string type axis) *)
; th_fold_A    : Sym3
; th_fold_B    : Sym3
  (* Level 3: derived string types *)
; th_type_A    : StringType
; th_type_B    : StringType
  (* Level 4: composed type *)
; th_composed  : Sym3
  (* Level 5: recursive fixpoint *)
; th_fixpoint  : Sym3
}.

Definition build_hierarchy (cps_A cps_B : list nat) : TypeHierarchy :=
  let trA  := classify_string cps_A in
  let trB  := classify_string cps_B in
  let fA   := fold_left field_op trA I_s in
  let fB   := fold_left field_op trB I_s in
  let tA   := derive_string_type cps_A in
  let tB   := derive_string_type cps_B in
  let comp := field_op fA fB in
  let fix_ := recurse_step comp in
  mkTH cps_A cps_B trA trB fA fB tA tB comp fix_.

(* The fixpoint is always I or F *)
Theorem hierarchy_fixpoint_valid : forall cps_A cps_B : list nat,
  th_fixpoint (build_hierarchy cps_A cps_B) = I_s \/
  th_fixpoint (build_hierarchy cps_A cps_B) = F_s.
Proof.
  intros cps_A cps_B.
  unfold build_hierarchy. simpl.
  apply hierarchy_stabilizes.
Qed.

(* The hierarchy is self-consistent: fixpoint = recurse(composed) *)
Theorem hierarchy_consistent : forall cps_A cps_B : list nat,
  let h := build_hierarchy cps_A cps_B in
  th_fixpoint h = recurse_step (th_composed h).
Proof.
  intros cps_A cps_B. unfold build_hierarchy. simpl. reflexivity.
Qed.

(* Trace lengths match input lengths *)
Theorem trace_lengths : forall cps_A cps_B : list nat,
  let h := build_hierarchy cps_A cps_B in
  length (th_trace_A h) = length cps_A /\
  length (th_trace_B h) = length cps_B.
Proof.
  intros cps_A cps_B. unfold build_hierarchy. simpl.
  split; unfold classify_string; rewrite map_length; reflexivity.
Qed.

(* ================================================================= *)
(* PART 9 — MASTER THEOREM                                         *)
(* ================================================================= *)

Theorem PARALLEL_TYPE_DERIVER :
  (* 1. Unicode codepoint roundtrip *)
  (forall cp : nat, position_to_rank (unicode_position cp) = cp) /\
  (* 2. Classification is total *)
  (forall pos : nat,
     field_classify pos = I_s \/
     field_classify pos = N_s \/
     field_classify pos = F_s) /\
  (* 3. StringType derivation is total *)
  (forall cps : list nat,
     derive_string_type cps = ST_Identity  \/
     derive_string_type cps = ST_Iff       \/
     derive_string_type cps = ST_Implies   \/
     derive_string_type cps = ST_Negation  \/
     derive_string_type cps = ST_Neq       \/
     derive_string_type cps = ST_Absurd    \/
     derive_string_type cps = ST_Exists    \/
     derive_string_type cps = ST_ForallEq  \/
     derive_string_type cps = ST_ForallFn) /\
  (* 4. Axis recovers diagonal *)
  (forall cps : list nat,
     string_type_axis (derive_string_type cps) = fold_string cps) /\
  (* 5. Parallel composition determined *)
  (forall cps_A cps_B : list nat,
     pr_composed (parallel_derive cps_A cps_B) =
     field_op (fold_string cps_A) (fold_string cps_B)) /\
  (* 6. N collapses to I in recursion *)
  (recurse_step N_s = I_s) /\
  (* 7. Hierarchy fixpoint always I or F *)
  (forall cps_A cps_B : list nat,
     th_fixpoint (build_hierarchy cps_A cps_B) = I_s \/
     th_fixpoint (build_hierarchy cps_A cps_B) = F_s) /\
  (* 8. Hierarchy is self-consistent *)
  (forall cps_A cps_B : list nat,
     let h := build_hierarchy cps_A cps_B in
     th_fixpoint h = recurse_step (th_composed h)) /\
  (* 9. Convergence in 1 step *)
  (forall sym : Sym3,
     recurse_step (recurse_step sym) = recurse_step sym).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
          (conj _ (conj _ _)))))))).
  - exact unicode_roundtrip.
  - exact classify_total.
  - exact string_type_total.
  - exact axis_from_diagonal.
  - exact parallel_composition_determined.
  - exact N_collapses.
  - exact hierarchy_fixpoint_valid.
  - exact hierarchy_consistent.
  - exact convergence_in_1.
Qed.

Print Assumptions PARALLEL_TYPE_DERIVER.
(* Expected: Closed under the empty set of assumptions *)

(* ================================================================= *)
(*  QED                                                              *)
(*                                                                   *)
(*  THE DERIVATION CHAIN:                                            *)
(*                                                                   *)
(*  String A           String B                                     *)
(*     ↓ unicode_sym      ↓ unicode_sym                             *)
(*  Trace A            Trace B          ← parallel, O(n) each      *)
(*     ↓ fold            ↓ fold                                     *)
(*  Sym3 A             Sym3 B           ← one symbol each          *)
(*     ↓ derive_type     ↓ derive_type                              *)
(*  StringType A       StringType B     ← 9 possibilities each     *)
(*     ↓ axis            ↓ axis                                     *)
(*  Sym3 A             Sym3 B           ← projected back           *)
(*         ↓ field_op                                               *)
(*      Composed Sym3                   ← the meeting point        *)
(*         ↓ recurse_step                                           *)
(*      Fixpoint                        ← always I or F            *)
(*                                                                   *)
(*  N∘N = I: the composition of two inverse types resolves         *)
(*           to an identity type. Two negations = affirmation.      *)
(*           Two transforms = pass-through. Always.                 *)
(*                                                                   *)
(*  The fixpoint IS the type of the type-composition.               *)
(*  It lives on the 45° Gaussian diagonal (I) or the 0° linear (F).*)
(*  It is never N — because N always resolves by N∘N = I.          *)
(*  The type hierarchy terminates in 2 levels. Always.              *)
(* ================================================================= *)
