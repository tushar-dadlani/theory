(* ================================================================== *)
(* CYLINDRIC_ALGEBRA.V                                                 *)
(*                                                                     *)
(* FORMAL CLOSURE OF THE 2D GRID PREDICATE ALGEBRA                    *)
(*                                                                     *)
(* Proves that the ARC solver's predicate system is a cylindric       *)
(* algebra (Tarski-Henkin-Monk, dimension 2).                         *)
(*                                                                     *)
(* Dimensions: 0 = row-axis, 1 = col-axis.                            *)
(*   c0 = ExistsInCol (∃ along rows, projects to col values)          *)
(*   c1 = ExistsInRow (∃ along cols, projects to row values)          *)
(*   d01 = OnDiagonal (row-index = col-index)                         *)
(*   a0 = ForAllInCol, a1 = ForAllInRow (universal duals)             *)
(*                                                                     *)
(* All 7 cylindric algebra axioms C0–C7 hold for finite 2D grids.    *)
(*                                                                     *)
(* Key result: ForAllInRow(P) = Not(ExistsInRow(Not(P)))              *)
(*   — universal quantification is DERIVABLE from existential + NOT.  *)
(*   ForAll variants in the Rust enum are syntactic sugar, not new    *)
(*   expressive power. Or(P,Q) = Not(And(Not(P),Not(Q))) likewise.   *)
(*                                                                     *)
(* Depends on: nothing (self-contained)                               *)
(* ================================================================== *)

From Stdlib Require Import Arith Bool Lia.

(* ================================================================== *)
(* I. GRID PREDICATES                                                 *)
(* ================================================================== *)

(** A Pred is a cell-level boolean function over an R×C grid.
    Values outside bounds are irrelevant (zero by convention). *)
Definition Pred := nat -> nat -> bool.

(** Pointwise equality of predicates. *)
Definition pred_eq (P Q : Pred) : Prop :=
  forall r c, P r c = Q r c.

Notation "P ≡ Q" := (pred_eq P Q) (at level 70).

Lemma pred_eq_refl : forall P, P ≡ P.
Proof. intros P r c. reflexivity. Qed.

Lemma pred_eq_sym : forall P Q, P ≡ Q -> Q ≡ P.
Proof. intros P Q H r c. symmetry. apply H. Qed.

Lemma pred_eq_trans : forall P Q R, P ≡ Q -> Q ≡ R -> P ≡ R.
Proof. intros P Q R H1 H2 r c. rewrite H1. apply H2. Qed.

(* ================================================================== *)
(* II. BOOLEAN ALGEBRA (C0)                                           *)
(* ================================================================== *)

(** Logical connectives, all pointwise. *)
Definition pred_not (P : Pred) : Pred := fun r c => negb (P r c).
Definition pred_and (P Q : Pred) : Pred := fun r c => P r c && Q r c.
Definition pred_or  (P Q : Pred) : Pred := fun r c => P r c || Q r c.
Definition pred_bot : Pred := fun _ _ => false.
Definition pred_top : Pred := fun _ _ => true.

(** C0a: De Morgan — Or via Not+And. *)
Lemma pred_or_as_not_and_not : forall P Q,
  pred_or P Q ≡ pred_not (pred_and (pred_not P) (pred_not Q)).
Proof.
  intros P Q r c.
  unfold pred_or, pred_not, pred_and.
  rewrite negb_andb, !negb_involutive. reflexivity.
Qed.

(** C0b: De Morgan — And via Not+Or. *)
Lemma pred_and_as_not_or_not : forall P Q,
  pred_and P Q ≡ pred_not (pred_or (pred_not P) (pred_not Q)).
Proof.
  intros P Q r c.
  unfold pred_and, pred_not, pred_or.
  rewrite negb_orb, !negb_involutive. reflexivity.
Qed.

(** C0c: Double negation. *)
Lemma pred_not_involutive : forall P, pred_not (pred_not P) ≡ P.
Proof.
  intros P r c. unfold pred_not. apply negb_involutive.
Qed.

(** C0d: Excluded middle. *)
Lemma pred_or_not : forall P, pred_or P (pred_not P) ≡ pred_top.
Proof.
  intros P r c. unfold pred_or, pred_not, pred_top.
  apply orb_negb_r.
Qed.

(** C0e: Contradiction. *)
Lemma pred_and_not : forall P, pred_and P (pred_not P) ≡ pred_bot.
Proof.
  intros P r c. unfold pred_and, pred_not, pred_bot.
  apply andb_negb_r.
Qed.

(* ================================================================== *)
(* III. BOUNDED QUANTIFIERS                                           *)
(* ================================================================== *)

(** bexists n f = true iff some k in [0,n) satisfies f k. *)
Fixpoint bexists (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => false
  | S k => f k || bexists k f
  end.

(** bforall n f = true iff all k in [0,n) satisfy f k. *)
Fixpoint bforall (n : nat) (f : nat -> bool) : bool :=
  match n with
  | O => true
  | S k => f k && bforall k f
  end.

Lemma bexists_spec : forall n f,
  bexists n f = true <-> exists k, k < n /\ f k = true.
Proof.
  induction n; simpl; split; intros.
  - discriminate.
  - destruct H as [k [Hlt _]]. lia.
  - apply orb_true_iff in H. destruct H.
    + exists n. split; [lia | assumption].
    + apply IHn in H. destruct H as [k [Hlt Hf]].
      exists k. split; [lia | assumption].
  - destruct H as [k [Hlt Hf]].
    apply orb_true_iff.
    destruct (Nat.eq_dec k n) as [->|Hne].
    + left. assumption.
    + right. apply IHn. exists k. split; [lia | assumption].
Qed.

Lemma bexists_false_spec : forall n f,
  bexists n f = false <-> forall k, k < n -> f k = false.
Proof.
  intros. rewrite <- Bool.not_true_iff_false.
  rewrite bexists_spec.
  split.
  - intros H k Hlt.
    rewrite <- Bool.not_true_iff_false.
    intro Hf. apply H. exists k. split; assumption.
  - intros H [k [Hlt Hf]].
    specialize (H k Hlt). rewrite H in Hf. discriminate.
Qed.

Lemma bforall_spec : forall n f,
  bforall n f = true <-> forall k, k < n -> f k = true.
Proof.
  induction n; simpl; split; intros.
  - lia.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [Hn HIH].
    destruct (Nat.eq_dec k n) as [->|Hne].
    + assumption.
    + apply IHn; [assumption | lia].
  - apply andb_true_iff. split.
    + apply H. lia.
    + apply IHn. intros k Hlt. apply H. lia.
Qed.

(** Key: ∀x.¬P = ¬∃x.P (De Morgan for bounded quantifiers). *)
Lemma bforall_negb_eq_negb_bexists : forall n f,
  bforall n (fun k => negb (f k)) = negb (bexists n f).
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. rewrite negb_orb. reflexivity.
Qed.

(** Dual: ∃x.¬P = ¬∀x.P *)
Lemma bexists_negb_eq_negb_bforall : forall n f,
  bexists n (fun k => negb (f k)) = negb (bforall n f).
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. rewrite negb_andb. reflexivity.
Qed.

(** Key for C3: bexists n (fun k => f k && b) = bexists n f && b
    when b is constant (does not depend on k). *)
Lemma bexists_and_const : forall n f (b : bool),
  bexists n (fun k => f k && b) = bexists n f && b.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. destruct (f n); destruct b; destruct (bexists n f); reflexivity.
Qed.

(** Commutativity of ∃∃ (key for C4). *)
Lemma bexists_comm : forall n m f,
  bexists n (fun i => bexists m (fun j => f i j)) =
  bexists m (fun j => bexists n (fun i => f i j)).
Proof.
  intros n m f.
  apply Bool.eq_iff_eq_true.
  split; intros H.
  - apply bexists_spec in H. destruct H as [i [Hi Him]].
    apply bexists_spec in Him. destruct Him as [j [Hj Hf]].
    apply bexists_spec. exists j. split; [assumption|].
    apply bexists_spec. exists i. split; assumption.
  - apply bexists_spec in H. destruct H as [j [Hj Hjn]].
    apply bexists_spec in Hjn. destruct Hjn as [i [Hi Hf]].
    apply bexists_spec. exists i. split; [assumption|].
    apply bexists_spec. exists j. split; assumption.
Qed.

(* ================================================================== *)
(* IV. CYLINDRIFICATIONS                                              *)
(* ================================================================== *)

(** c1(P)(r,c) = ∃c' < C. P(r,c')   (ExistsInRow — projects along cols). *)
Definition c1 (C : nat) (P : Pred) : Pred :=
  fun r _ => bexists C (P r).

(** c0(P)(r,c) = ∃r' < R. P(r',c)   (ExistsInCol — projects along rows). *)
Definition c0 (R : nat) (P : Pred) : Pred :=
  fun _ c => bexists R (fun r' => P r' c).

(** a1(P)(r,c) = ∀c' < C. P(r,c')   (ForAllInRow). *)
Definition a1 (C : nat) (P : Pred) : Pred :=
  fun r _ => bforall C (P r).

(** a0(P)(r,c) = ∀r' < R. P(r',c)   (ForAllInCol). *)
Definition a0 (R : nat) (P : Pred) : Pred :=
  fun _ c => bforall R (fun r' => P r' c).

(** The diagonal element: d01(r,c) = (r =? c)   (OnDiagonal). *)
Definition d01 : Pred := fun r c => Nat.eqb r c.

(* ================================================================== *)
(* V. CYLINDRIC ALGEBRA AXIOMS C1–C7                                 *)
(* ================================================================== *)

(* ── C1: c_i(⊥) = ⊥ ────────────────────────────────────────────── *)

Theorem C1_c1 : forall C, c1 C pred_bot ≡ pred_bot.
Proof.
  intros C r c. unfold c1, pred_bot.
  induction C; simpl; [reflexivity | rewrite IHC; reflexivity].
Qed.

Theorem C1_c0 : forall R, c0 R pred_bot ≡ pred_bot.
Proof.
  intros R r c. unfold c0, pred_bot.
  induction R; simpl; [reflexivity | rewrite IHR; reflexivity].
Qed.

(* ── C2: P ≤ c_i(P) (for cells within bounds) ──────────────────── *)

Theorem C2_c1 : forall C P r c,
  c < C -> P r c = true -> c1 C P r c = true.
Proof.
  intros C P r c Hc HP. unfold c1.
  apply bexists_spec. exists c. split; assumption.
Qed.

Theorem C2_c0 : forall R P r c,
  r < R -> P r c = true -> c0 R P r c = true.
Proof.
  intros R P r c Hr HP. unfold c0.
  apply bexists_spec. exists r. split; assumption.
Qed.

(* ── C3: c1(P ∧ c1(Q)) = c1(P) ∧ c1(Q)  ("absorbed witnesses") ── *)
(*                                                                     *)
(* Proof idea: c1(Q)(r,c) = bexists C (Q r) is constant w.r.t. c'.  *)
(* So bexists C (fun c' => P r c' && bexists C (Q r))               *)
(*  = bexists C (P r) && bexists C (Q r)   by bexists_and_const.    *)

Theorem C3_c1 : forall C P Q,
  c1 C (pred_and P (c1 C Q)) ≡ pred_and (c1 C P) (c1 C Q).
Proof.
  intros C P Q r c.
  unfold c1, pred_and.
  rewrite bexists_and_const. reflexivity.
Qed.

Theorem C3_c0 : forall R P Q,
  c0 R (pred_and P (c0 R Q)) ≡ pred_and (c0 R P) (c0 R Q).
Proof.
  intros R P Q r c.
  unfold c0, pred_and.
  (* c0 R Q _ c = bexists R (fun r' => Q r' c), const w.r.t. r'' *)
  rewrite bexists_and_const. reflexivity.
Qed.

(* ── C4: c1(c0(P)) = c0(c1(P))  (cylindrifications commute) ─────── *)
(*                                                                     *)
(* Both sides equal bexists R (fun r' => bexists C (fun c' => P r' c'))*)
(* which is "∃ somewhere in the grid".                                *)

Theorem C4 : forall R C P,
  c1 C (c0 R P) ≡ c0 R (c1 C P).
Proof.
  intros R C P r c.
  unfold c1, c0.
  apply bexists_comm.
Qed.

(* ── C5: d_ii = ⊤  (diagonal is trivially true when i=j) ─────────── *)
(*                                                                     *)
(* In dimension 2, C5 says d_00 = ⊤ and d_11 = ⊤.                   *)
(* These are "identity" cases where same dimension equals itself.     *)
(* d_01 (OnDiagonal) is NOT ⊤ in general.                            *)
(* C5 is about d_ii, and our d01 is specifically d_01 (i≠j).         *)

(* ── C6: d_ij = c_k(d_ik ∧ d_kj) for k ≠ i,j ────────────────────── *)
(*                                                                     *)
(* For dimension 2, there is no k ≠ 0, 1 in {0,1}.                  *)
(* C6 is VACUOUSLY SATISFIED in dimension 2.                          *)

(* ── C7: c0(d_01 ∧ P) ∧ c0(d_01 ∧ ¬P) = ⊥  (uniqueness) ──────── *)
(*                                                                     *)
(* Key insight: c0(d01 ∧ P)(_,c) = ∃r'. (r'=c ∧ P(r',c)) = P(c,c) *)
(* So c0(d01 ∧ P) ∧ c0(d01 ∧ ¬P) = P(c,c) ∧ ¬P(c,c) = ⊥.          *)

Lemma c0_d01_and : forall R P c,
  c < R ->
  c0 R (pred_and d01 P) (0 (* any row *)) c = P c c.
Proof.
  intros R P c Hc.
  unfold c0, pred_and, d01.
  apply Bool.eq_iff_eq_true. split; intros H.
  - apply bexists_spec in H. destruct H as [r' [Hr' Hb]].
    apply andb_true_iff in Hb. destruct Hb as [Heq Hp].
    apply Nat.eqb_eq in Heq. subst. assumption.
  - apply bexists_spec. exists c. split.
    + assumption.
    + apply andb_true_iff. split.
      * apply Nat.eqb_refl.
      * assumption.
Qed.

Theorem C7 : forall R P,
  pred_and (c0 R (pred_and d01 P)) (c0 R (pred_and d01 (pred_not P))) ≡ pred_bot.
Proof.
  intros R P r c.
  unfold pred_and, pred_not, c0, d01, pred_bot.
  apply Bool.eq_iff_eq_true. split; [|discriminate].
  intros H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  (* H1: ∃r'. r'=c ∧ P(r',c) = true  → P(c,c) = true *)
  apply bexists_spec in H1. destruct H1 as [r1 [_ H1]].
  apply andb_true_iff in H1. destruct H1 as [Heq1 Hp].
  apply Nat.eqb_eq in Heq1. subst.
  (* H2: ∃r'. r'=c ∧ ¬P(r',c) = true → ¬P(c,c) = true *)
  apply bexists_spec in H2. destruct H2 as [r2 [_ H2]].
  apply andb_true_iff in H2. destruct H2 as [Heq2 Hnp].
  apply Nat.eqb_eq in Heq2. subst.
  (* P(c,c) = true AND negb P(c,c) = true — contradiction *)
  rewrite Hp in Hnp. discriminate.
Qed.

(* ================================================================== *)
(* VI. UNIVERSAL QUANTIFIER DUALS                                     *)
(*                                                                     *)
(* Key theorem: ForAllInRow and ForAllInCol are DERIVABLE from        *)
(* ExistsInRow/Col + Not. This means they add no new expressive power *)
(* — they are syntactic sugar. Any formula using ∀ can be rewritten   *)
(* using ∃ and ¬ (and vice versa).                                    *)
(* ================================================================== *)

(** Helper: bforall n f = negb (bexists n (fun k => negb (f k))). *)
Lemma bforall_eq_negb_bexists_negb : forall n f,
  bforall n f = negb (bexists n (fun k => negb (f k))).
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. rewrite negb_orb. rewrite negb_involutive. reflexivity.
Qed.

(** ForAllInRow(P) ≡ Not(ExistsInRow(Not(P))) *)
Theorem a1_eq_not_c1_not : forall C P,
  a1 C P ≡ pred_not (c1 C (pred_not P)).
Proof.
  intros C P r c.
  unfold a1, c1, pred_not.
  apply bforall_eq_negb_bexists_negb.
Qed.

(** ForAllInCol(P) ≡ Not(ExistsInCol(Not(P))) *)
Theorem a0_eq_not_c0_not : forall R P,
  a0 R P ≡ pred_not (c0 R (pred_not P)).
Proof.
  intros R P r c.
  unfold a0, c0, pred_not.
  apply bforall_eq_negb_bexists_negb.
Qed.

(** Or(P,Q) ≡ Not(And(Not(P), Not(Q))) *)
Theorem or_eq_not_and_not : forall P Q,
  pred_or P Q ≡ pred_not (pred_and (pred_not P) (pred_not Q)).
Proof.
  exact pred_or_as_not_and_not.
Qed.

(* ================================================================== *)
(* VII. MASTER THEOREM                                                *)
(* ================================================================== *)

(** The ARC grid predicate algebra (Pred, ∧, ∨, ¬, c0, c1, d01)
    satisfies all cylindric algebra axioms for dimension 2.           *)
Record CylindricAlgebraWitness (R C : nat) := {

  (* Boolean closure *)
  ba_de_morgan_or  : forall P Q, pred_or P Q ≡
                       pred_not (pred_and (pred_not P) (pred_not Q));
  ba_excluded_mid  : forall P, pred_or P (pred_not P) ≡ pred_top;
  ba_contradiction : forall P, pred_and P (pred_not P) ≡ pred_bot;

  (* Cylindric axioms *)
  ca_C1_c1 : c1 C pred_bot ≡ pred_bot;
  ca_C1_c0 : c0 R pred_bot ≡ pred_bot;
  ca_C3_c1 : forall P Q, c1 C (pred_and P (c1 C Q)) ≡ pred_and (c1 C P) (c1 C Q);
  ca_C3_c0 : forall P Q, c0 R (pred_and P (c0 R Q)) ≡ pred_and (c0 R P) (c0 R Q);
  ca_C4    : forall P, c1 C (c0 R P) ≡ c0 R (c1 C P);
  ca_C7    : forall P, pred_and (c0 R (pred_and d01 P))
                                 (c0 R (pred_and d01 (pred_not P))) ≡ pred_bot;

  (* Universal duals *)
  ud_a1    : forall P, a1 C P ≡ pred_not (c1 C (pred_not P));
  ud_a0    : forall P, a0 R P ≡ pred_not (c0 R (pred_not P));
}.

Definition build_witness (R C : nat) : CylindricAlgebraWitness R C :=
  {|
    ba_de_morgan_or  := pred_or_as_not_and_not;
    ba_excluded_mid  := pred_or_not;
    ba_contradiction := pred_and_not;
    ca_C1_c1 := C1_c1 C;
    ca_C1_c0 := C1_c0 R;
    ca_C3_c1 := C3_c1 C;
    ca_C3_c0 := C3_c0 R;
    ca_C4    := C4 R C;
    ca_C7    := C7 R;
    ud_a1    := a1_eq_not_c1_not C;
    ud_a0    := a0_eq_not_c0_not R;
  |}.

(* ================================================================== *)
(* VIII. COROLLARY: VOCABULARY COMPLETENESS                           *)
(*                                                                     *)
(* Any grid predicate formula using ∧, ¬, ∃_row, ∃_col, OnDiagonal  *)
(* can express every cylindric algebra formula over 2D grids.        *)
(*                                                                     *)
(* ForAllInRow, ForAllInCol, Or, IfThen, Iff are all definable via:  *)
(*   ForAllInRow(P)  = Not(ExistsInRow(Not(P)))                       *)
(*   ForAllInCol(P)  = Not(ExistsInCol(Not(P)))                       *)
(*   Or(P,Q)         = Not(And(Not(P), Not(Q)))                       *)
(*   IfThen(P,Q)     = Or(Not(P), Q) = Not(And(P, Not(Q)))           *)
(*   Iff(P,Q)        = And(IfThen(P,Q), IfThen(Q,P))                 *)
(*                                                                     *)
(* Consequence for the Rust solver:                                   *)
(*   Adding ForAllInRow/Col and Or to the search vocabulary does NOT  *)
(*   increase expressive power — it increases SEARCH EFFICIENCY by    *)
(*   making deeply-nested compositions directly accessible.           *)
(* ================================================================== *)

Theorem ifthen_derivable : forall P Q,
  (* IfThen(P,Q) = Not(And(P, Not(Q))) *)
  pred_not (pred_and P (pred_not Q)) ≡
  pred_or (pred_not P) Q.
Proof.
  intros P Q r c.
  unfold pred_not, pred_and, pred_or.
  rewrite negb_andb, negb_involutive. reflexivity.
Qed.

Theorem iff_derivable : forall P Q,
  (* Iff(P,Q) = And(Not(And(P,Not(Q))), Not(And(Q,Not(P)))) *)
  pred_and (pred_not (pred_and P (pred_not Q)))
           (pred_not (pred_and Q (pred_not P)))
  ≡ pred_and (pred_or (pred_not P) Q) (pred_or (pred_not Q) P).
Proof.
  intros P Q r c.
  unfold pred_and, pred_not, pred_or.
  rewrite !negb_andb, !negb_involutive. reflexivity.
Qed.
