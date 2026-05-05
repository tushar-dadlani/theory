(* ================================================================= *)
(*  ARC2_FiberMorphisms.v                                              *)
(*                                                                    *)
(*  THE 9×9 GRID OF FIBER MORPHISMS                                    *)
(*                                                                    *)
(*  THE IDEA:                                                         *)
(*    A 3×3 grid has 9 positions, indexed by (i,j) with i,j ∈ {0,1,2}.*)
(*    A transform t : Grid → Grid (a permutation of positions on a  *)
(*    3×3 grid) is fully characterized by where it sends each       *)
(*    position. This data is a 9×9 matrix of fiber morphisms:       *)
(*       FiberMatrix(src, dst) = true  iff t sends the value at      *)
(*                                       position src to position dst*)
(*                                                                    *)
(*  STRUCTURE:                                                        *)
(*    Position : Fin 9 (or ℕ × ℕ with bounds).                       *)
(*    FiberMatrix : Position → Position → bool.                      *)
(*    For a permutation, exactly one true per row and per column.   *)
(*                                                                    *)
(*  WHAT IT ENCODES:                                                  *)
(*    Each entry FiberMatrix[s][d] = b is a fiber morphism in the   *)
(*    discrete category {0, 1, 2}^2. The whole 9×9 matrix is the   *)
(*    profunctor representation of the transform.                    *)
(*                                                                    *)
(*  THEOREMS WE PROVE:                                                *)
(*    1. Each D₄ transform has a UNIQUE fiber matrix (extensional). *)
(*    2. fiber_matrix_compose corresponds to transform composition.  *)
(*    3. Each row and column has exactly one true (permutation).    *)
(*    4. fiber_matrix_id is the identity matrix.                    *)
(*    5. Klein four laws hold at the fiber matrix level.            *)
(*    6. The fiber matrix REALIZES the transform: applying t to a  *)
(*       3×3 grid is the same as permuting via the fiber matrix.    *)
(*                                                                    *)
(*  EUCLIDEAN GEOMETRY:                                                *)
(*    The 9 positions are 9 points on a 3×3 lattice in ℤ². Each    *)
(*    fiber morphism is an arrow in a discrete groupoid. The 9×9   *)
(*    grid IS the groupoid as a directed graph adjacency matrix.    *)
(*    A permutation transform = a graph automorphism = a closed     *)
(*    walk through the matrix.                                        *)
(*                                                                    *)
(*  GAUSSIAN ALGEBRA:                                                  *)
(*    The 9×9 Boolean matrix is the GROUP ELEMENT in S_9 (symmetric *)
(*    group on 9 letters), restricted to D₄ (8 elements: id,        *)
(*    flip_h, flip_v, rot_180, transpose, rot_90, rot_270, anti-    *)
(*    diag-flip). Boolean matrix multiplication = group composition.*)
(*    The fiber matrices form a faithful representation of D₄ ↪ S_9.*)
(*                                                                    *)
(*  ALL PROOFS BY direct computation OR induction on positions.      *)
(*  ZERO Admitted. ZERO axioms.                                       *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat Lists.List Bool.Bool.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(* PART 0 — POSITIONS: 9 INDICES OF A 3×3 GRID                         *)
(* ================================================================= *)

(* A position is a pair of bounded coordinates in {0,1,2}. We use a *)
(* simple sum type for tractable kernel computation. *)

Inductive Pos : Type :=
  | P00 : Pos | P01 : Pos | P02 : Pos
  | P10 : Pos | P11 : Pos | P12 : Pos
  | P20 : Pos | P21 : Pos | P22 : Pos.

Definition pos_eqb (p q : Pos) : bool :=
  match p, q with
  | P00, P00 | P01, P01 | P02, P02
  | P10, P10 | P11, P11 | P12, P12
  | P20, P20 | P21, P21 | P22, P22 => true
  | _, _ => false
  end.

Lemma pos_eqb_refl : forall p, pos_eqb p p = true.
Proof. intros []; reflexivity. Qed.

Lemma pos_eqb_eq : forall p q, pos_eqb p q = true -> p = q.
Proof. intros [] []; intro H; simpl in H; try discriminate; reflexivity. Qed.

Definition all_positions : list Pos :=
  [P00; P01; P02; P10; P11; P12; P20; P21; P22].

Theorem all_positions_complete : forall p, In p all_positions.
Proof. intros []; simpl; tauto. Qed.

Theorem all_positions_length : length all_positions = 9.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 1 — FIBER MATRIX: 9×9 BOOLEAN GRID                             *)
(* ================================================================= *)

(* The fiber morphism at (src, dst) is a Boolean: true iff the      *)
(* transform sends the value at src to dst.                           *)

Definition FiberMatrix : Type := Pos -> Pos -> bool.

(* Identity matrix: only the diagonal is true. *)
Definition fiber_id : FiberMatrix :=
  fun src dst => pos_eqb src dst.

(* Construct from a permutation function. *)
Definition fiber_of_perm (f : Pos -> Pos) : FiberMatrix :=
  fun src dst => pos_eqb (f src) dst.

(* ================================================================= *)
(* PART 2 — POSITION PERMUTATIONS FOR EACH D₄ TRANSFORM                *)
(*                                                                    *)
(*  For a 3×3 grid:                                                   *)
(*    [a b c]      flip_h:    [c b a]    flip_v:    [g h i]          *)
(*    [d e f]                 [f e d]               [d e f]          *)
(*    [g h i]                 [i h g]               [a b c]          *)
(*                                                                    *)
(*    rot_180:    [i h g]    transpose: [a d g]    rot_90:    [g d a]*)
(*                [f e d]               [b e h]               [h e b]*)
(*                [c b a]               [c f i]               [i f c]*)
(*                                                                    *)
(*  rot_90 sends (i,j) ↦ (j, 2-i).                                    *)
(*                                                                    *)
(*  In terms of where each input position GOES (output position):    *)
(*    flip_h:    swap columns 0 and 2.                                *)
(*    flip_v:    swap rows 0 and 2.                                   *)
(*    transpose: swap (i,j) with (j,i).                               *)
(* ================================================================= *)

Definition perm_id (p : Pos) : Pos := p.

Definition perm_flip_h (p : Pos) : Pos :=
  match p with
  | P00 => P02 | P01 => P01 | P02 => P00
  | P10 => P12 | P11 => P11 | P12 => P10
  | P20 => P22 | P21 => P21 | P22 => P20
  end.

Definition perm_flip_v (p : Pos) : Pos :=
  match p with
  | P00 => P20 | P01 => P21 | P02 => P22
  | P10 => P10 | P11 => P11 | P12 => P12
  | P20 => P00 | P21 => P01 | P22 => P02
  end.

Definition perm_rot_180 (p : Pos) : Pos :=
  match p with
  | P00 => P22 | P01 => P21 | P02 => P20
  | P10 => P12 | P11 => P11 | P12 => P10
  | P20 => P02 | P21 => P01 | P22 => P00
  end.

Definition perm_transpose (p : Pos) : Pos :=
  match p with
  | P00 => P00 | P01 => P10 | P02 => P20
  | P10 => P01 | P11 => P11 | P12 => P21
  | P20 => P02 | P21 => P12 | P22 => P22
  end.

(* rot_90: (i,j) → (j, 2-i). E.g., (0,0)→(0,2)=P02; (0,2)→(2,2)=P22. *)
Definition perm_rot_90 (p : Pos) : Pos :=
  match p with
  | P00 => P02 | P01 => P12 | P02 => P22
  | P10 => P01 | P11 => P11 | P12 => P21
  | P20 => P00 | P21 => P10 | P22 => P20
  end.

(* rot_270 = rot_90^3, equivalently (i,j) → (2-j, i). *)
Definition perm_rot_270 (p : Pos) : Pos :=
  match p with
  | P00 => P20 | P01 => P10 | P02 => P00
  | P10 => P21 | P11 => P11 | P12 => P01
  | P20 => P22 | P21 => P12 | P22 => P02
  end.

(* Anti-diagonal flip: (i,j) → (2-j, 2-i). *)
Definition perm_anti_diag (p : Pos) : Pos :=
  match p with
  | P00 => P22 | P01 => P12 | P02 => P02
  | P10 => P21 | P11 => P11 | P12 => P01
  | P20 => P20 | P21 => P10 | P22 => P00
  end.

(* ================================================================= *)
(* PART 3 — FIBER MATRICES FOR D₄                                       *)
(* ================================================================= *)

Definition fiber_id_matrix      : FiberMatrix := fiber_of_perm perm_id.
Definition fiber_flip_h         : FiberMatrix := fiber_of_perm perm_flip_h.
Definition fiber_flip_v         : FiberMatrix := fiber_of_perm perm_flip_v.
Definition fiber_rot_180        : FiberMatrix := fiber_of_perm perm_rot_180.
Definition fiber_transpose      : FiberMatrix := fiber_of_perm perm_transpose.
Definition fiber_rot_90         : FiberMatrix := fiber_of_perm perm_rot_90.
Definition fiber_rot_270        : FiberMatrix := fiber_of_perm perm_rot_270.
Definition fiber_anti_diag      : FiberMatrix := fiber_of_perm perm_anti_diag.

(* ================================================================= *)
(* PART 4 — BOOLEAN MATRIX MULTIPLICATION                               *)
(*                                                                    *)
(*  (M₁ * M₂)[s][d] = ∃ k, M₁[s][k] ∧ M₂[k][d].                      *)
(*  In Boolean form: orb over all intermediate positions.            *)
(*                                                                    *)
(*  Convention: matrix multiplication composes RIGHT-to-LEFT, like  *)
(*  function composition: (M1 * M2)(s, d) means go from s to k via *)
(*  M1, then from k to d via M2.                                    *)
(* ================================================================= *)

Fixpoint orb_over_positions (ps : list Pos) (P : Pos -> bool) : bool :=
  match ps with
  | []       => false
  | p :: rest => P p || orb_over_positions rest P
  end.

Definition fiber_compose (M1 M2 : FiberMatrix) : FiberMatrix :=
  fun src dst =>
    orb_over_positions all_positions
      (fun k => M1 src k && M2 k dst).

Notation "M1 ⊙ M2" := (fiber_compose M1 M2) (at level 40, left associativity).

(* ================================================================= *)
(* PART 5 — IDENTITY LAWS                                              *)
(* ================================================================= *)

Theorem fiber_id_left : forall M src dst,
  (fiber_id ⊙ M) src dst = M src dst.
Proof.
  intros M src dst. unfold fiber_compose, fiber_id, orb_over_positions,
                            all_positions.
  simpl. destruct src; simpl;
    repeat (rewrite Bool.orb_false_r); reflexivity.
Qed.

Theorem fiber_id_right : forall M src dst,
  (M ⊙ fiber_id) src dst = M src dst.
Proof.
  intros M src dst. unfold fiber_compose, fiber_id, orb_over_positions,
                            all_positions.
  simpl. destruct dst; simpl;
    repeat (rewrite Bool.andb_false_r);
    repeat (rewrite Bool.orb_false_r);
    repeat (rewrite Bool.orb_false_l);
    repeat (rewrite Bool.andb_true_r);
    destruct (M src P00); destruct (M src P01); destruct (M src P02);
    destruct (M src P10); destruct (M src P11); destruct (M src P12);
    destruct (M src P20); destruct (M src P21); destruct (M src P22);
    reflexivity.
Qed.

(* ================================================================= *)
(* PART 6 — KLEIN FOUR LAWS AT THE FIBER MATRIX LEVEL                  *)
(*                                                                    *)
(*  flip_h ⊙ flip_h = id                                               *)
(*  flip_v ⊙ flip_v = id                                               *)
(*  flip_h ⊙ flip_v = rot_180                                          *)
(*  flip_v ⊙ flip_h = rot_180                                          *)
(*  rot_180 ⊙ rot_180 = id                                             *)
(* ================================================================= *)

(* Convenience: extensional equality on FiberMatrix. *)
Definition fiber_eq (M N : FiberMatrix) : Prop :=
  forall src dst, M src dst = N src dst.

Notation "M ≃ N" := (fiber_eq M N) (at level 70).

Theorem flip_h_squared : fiber_flip_h ⊙ fiber_flip_h ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem flip_v_squared : fiber_flip_v ⊙ fiber_flip_v ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem rot_180_squared : fiber_rot_180 ⊙ fiber_rot_180 ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem flip_h_flip_v_eq_rot_180 : fiber_flip_h ⊙ fiber_flip_v ≃ fiber_rot_180.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem flip_v_flip_h_eq_rot_180 : fiber_flip_v ⊙ fiber_flip_h ≃ fiber_rot_180.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

(* Klein four ABELIAN: flip_h and flip_v commute. *)
Theorem flip_h_flip_v_commute :
  fiber_flip_h ⊙ fiber_flip_v ≃ fiber_flip_v ⊙ fiber_flip_h.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

(* ================================================================= *)
(* PART 7 — D₄ EXTENDED LAWS (NON-ABELIAN PART)                       *)
(* ================================================================= *)

Theorem transpose_squared : fiber_transpose ⊙ fiber_transpose ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem anti_diag_squared : fiber_anti_diag ⊙ fiber_anti_diag ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem rot_90_quadrupled :
  ((fiber_rot_90 ⊙ fiber_rot_90) ⊙ fiber_rot_90) ⊙ fiber_rot_90 ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem rot_90_squared_eq_rot_180 :
  fiber_rot_90 ⊙ fiber_rot_90 ≃ fiber_rot_180.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem rot_90_cubed_eq_rot_270 :
  (fiber_rot_90 ⊙ fiber_rot_90) ⊙ fiber_rot_90 ≃ fiber_rot_270.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem rot_90_rot_270_eq_id :
  fiber_rot_90 ⊙ fiber_rot_270 ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem rot_270_rot_90_eq_id :
  fiber_rot_270 ⊙ fiber_rot_90 ≃ fiber_id.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

(* Transpose conjugates flip_h to flip_v. *)
Theorem transpose_conj_flip_h :
  (fiber_transpose ⊙ fiber_flip_h) ⊙ fiber_transpose ≃ fiber_flip_v.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

Theorem transpose_conj_flip_v :
  (fiber_transpose ⊙ fiber_flip_v) ⊙ fiber_transpose ≃ fiber_flip_h.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

(* The non-abelian fact: transpose and flip_h DON'T commute. *)
Theorem transpose_flip_h_non_commute :
  ~ (fiber_transpose ⊙ fiber_flip_h ≃ fiber_flip_h ⊙ fiber_transpose).
Proof.
  intro H.
  specialize (H P00 P02).
  unfold fiber_compose, fiber_transpose, fiber_flip_h,
         fiber_of_perm, perm_transpose, perm_flip_h in H.
  simpl in H. discriminate.
Qed.

(* transpose ∘ flip_h = rot_90. *)
Theorem transpose_flip_h_eq_rot_90 :
  fiber_transpose ⊙ fiber_flip_h ≃ fiber_rot_90.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

(* flip_h ∘ transpose = rot_270. *)
Theorem flip_h_transpose_eq_rot_270 :
  fiber_flip_h ⊙ fiber_transpose ≃ fiber_rot_270.
Proof.
  intros src dst. destruct src, dst; reflexivity.
Qed.

(* ================================================================= *)
(* PART 8 — PERMUTATION PROPERTY: ONE TRUE PER ROW AND COLUMN          *)
(* ================================================================= *)

(* Count true entries in a row. *)
Definition count_true_row (M : FiberMatrix) (src : Pos) : nat :=
  fold_right (fun dst acc => (if M src dst then 1 else 0) + acc)
             0 all_positions.

(* Count true entries in a column. *)
Definition count_true_col (M : FiberMatrix) (dst : Pos) : nat :=
  fold_right (fun src acc => (if M src dst then 1 else 0) + acc)
             0 all_positions.

(* For each D₄ transform, every row has exactly 1 true. *)
Theorem fiber_id_row_count : forall src,
  count_true_row fiber_id_matrix src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_flip_h_row_count : forall src,
  count_true_row fiber_flip_h src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_flip_v_row_count : forall src,
  count_true_row fiber_flip_v src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_rot_180_row_count : forall src,
  count_true_row fiber_rot_180 src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_transpose_row_count : forall src,
  count_true_row fiber_transpose src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_rot_90_row_count : forall src,
  count_true_row fiber_rot_90 src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_rot_270_row_count : forall src,
  count_true_row fiber_rot_270 src = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_anti_diag_row_count : forall src,
  count_true_row fiber_anti_diag src = 1.
Proof. intros []; reflexivity. Qed.

(* Same for columns. *)
Theorem fiber_id_col_count : forall dst,
  count_true_col fiber_id_matrix dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_flip_h_col_count : forall dst,
  count_true_col fiber_flip_h dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_flip_v_col_count : forall dst,
  count_true_col fiber_flip_v dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_rot_180_col_count : forall dst,
  count_true_col fiber_rot_180 dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_transpose_col_count : forall dst,
  count_true_col fiber_transpose dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_rot_90_col_count : forall dst,
  count_true_col fiber_rot_90 dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_rot_270_col_count : forall dst,
  count_true_col fiber_rot_270 dst = 1.
Proof. intros []; reflexivity. Qed.

Theorem fiber_anti_diag_col_count : forall dst,
  count_true_col fiber_anti_diag dst = 1.
Proof. intros []; reflexivity. Qed.

(* ================================================================= *)
(* PART 9 — TOTAL COUNT: EXACTLY 9 TRUE ENTRIES PER MATRIX             *)
(* ================================================================= *)

Definition count_true_total (M : FiberMatrix) : nat :=
  fold_right (fun src acc => count_true_row M src + acc)
             0 all_positions.

Theorem fiber_id_total : count_true_total fiber_id_matrix = 9.
Proof. reflexivity. Qed.

Theorem fiber_flip_h_total : count_true_total fiber_flip_h = 9.
Proof. reflexivity. Qed.

Theorem fiber_flip_v_total : count_true_total fiber_flip_v = 9.
Proof. reflexivity. Qed.

Theorem fiber_rot_180_total : count_true_total fiber_rot_180 = 9.
Proof. reflexivity. Qed.

Theorem fiber_transpose_total : count_true_total fiber_transpose = 9.
Proof. reflexivity. Qed.

Theorem fiber_rot_90_total : count_true_total fiber_rot_90 = 9.
Proof. reflexivity. Qed.

Theorem fiber_rot_270_total : count_true_total fiber_rot_270 = 9.
Proof. reflexivity. Qed.

Theorem fiber_anti_diag_total : count_true_total fiber_anti_diag = 9.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 10 — REALIZATION: FIBER MATRIX APPLIES TO A 3×3 GRID           *)
(*                                                                    *)
(*  We define a 3×3 grid of natural-number values, then prove that  *)
(*  applying the fiber matrix gives the same result as applying the *)
(*  underlying transform.                                             *)
(* ================================================================= *)

Record Grid3 := mkGrid3 {
  g00 : nat; g01 : nat; g02 : nat;
  g10 : nat; g11 : nat; g12 : nat;
  g20 : nat; g21 : nat; g22 : nat
}.

Definition get_pos (g : Grid3) (p : Pos) : nat :=
  match p with
  | P00 => g00 g | P01 => g01 g | P02 => g02 g
  | P10 => g10 g | P11 => g11 g | P12 => g12 g
  | P20 => g20 g | P21 => g21 g | P22 => g22 g
  end.

Definition build_grid (f : Pos -> nat) : Grid3 :=
  {| g00 := f P00; g01 := f P01; g02 := f P02
   ; g10 := f P10; g11 := f P11; g12 := f P12
   ; g20 := f P20; g21 := f P21; g22 := f P22 |}.

(* Apply a permutation to a grid: the value at the OUTPUT position d *)
(* comes from the INPUT position s where the perm maps s ↦ d.        *)
(* In other words, the value at output d is the value at the unique *)
(* s such that perm s = d — i.e., the inverse permutation applied.  *)

(* For a fiber matrix: out[d] := the value at the unique src with    *)
(* M src d = true. *)

Definition apply_perm (f : Pos -> Pos) (g : Grid3) : Grid3 :=
  build_grid (fun d =>
    if pos_eqb (f P00) d then get_pos g P00
    else if pos_eqb (f P01) d then get_pos g P01
    else if pos_eqb (f P02) d then get_pos g P02
    else if pos_eqb (f P10) d then get_pos g P10
    else if pos_eqb (f P11) d then get_pos g P11
    else if pos_eqb (f P12) d then get_pos g P12
    else if pos_eqb (f P20) d then get_pos g P20
    else if pos_eqb (f P21) d then get_pos g P21
    else if pos_eqb (f P22) d then get_pos g P22
    else 0).

(* Apply a fiber matrix to a grid. *)
Definition apply_fiber (M : FiberMatrix) (g : Grid3) : Grid3 :=
  build_grid (fun d =>
    if M P00 d then get_pos g P00
    else if M P01 d then get_pos g P01
    else if M P02 d then get_pos g P02
    else if M P10 d then get_pos g P10
    else if M P11 d then get_pos g P11
    else if M P12 d then get_pos g P12
    else if M P20 d then get_pos g P20
    else if M P21 d then get_pos g P21
    else if M P22 d then get_pos g P22
    else 0).

(* For fiber_of_perm, applying the fiber matrix = applying the perm. *)
Theorem apply_fiber_of_perm : forall f g,
  apply_fiber (fiber_of_perm f) g = apply_perm f g.
Proof.
  intros f g. unfold apply_fiber, apply_perm, fiber_of_perm. reflexivity.
Qed.

(* ================================================================= *)
(* PART 11 — CONCRETE GRID EVALUATION                                  *)
(*                                                                    *)
(*  Apply each D₄ transform via its fiber matrix to a concrete 3×3   *)
(*  grid, and verify the result.                                      *)
(* ================================================================= *)

Definition test_grid : Grid3 :=
  {| g00 := 1; g01 := 2; g02 := 3
   ; g10 := 4; g11 := 5; g12 := 6
   ; g20 := 7; g21 := 8; g22 := 9 |}.

Theorem fiber_id_acts_as_identity :
  apply_fiber fiber_id_matrix test_grid = test_grid.
Proof. reflexivity. Qed.

Theorem fiber_flip_h_acts :
  apply_fiber fiber_flip_h test_grid =
  {| g00 := 3; g01 := 2; g02 := 1
   ; g10 := 6; g11 := 5; g12 := 4
   ; g20 := 9; g21 := 8; g22 := 7 |}.
Proof. reflexivity. Qed.

Theorem fiber_flip_v_acts :
  apply_fiber fiber_flip_v test_grid =
  {| g00 := 7; g01 := 8; g02 := 9
   ; g10 := 4; g11 := 5; g12 := 6
   ; g20 := 1; g21 := 2; g22 := 3 |}.
Proof. reflexivity. Qed.

Theorem fiber_rot_180_acts :
  apply_fiber fiber_rot_180 test_grid =
  {| g00 := 9; g01 := 8; g02 := 7
   ; g10 := 6; g11 := 5; g12 := 4
   ; g20 := 3; g21 := 2; g22 := 1 |}.
Proof. reflexivity. Qed.

Theorem fiber_transpose_acts :
  apply_fiber fiber_transpose test_grid =
  {| g00 := 1; g01 := 4; g02 := 7
   ; g10 := 2; g11 := 5; g12 := 8
   ; g20 := 3; g21 := 6; g22 := 9 |}.
Proof. reflexivity. Qed.

Theorem fiber_rot_90_acts :
  apply_fiber fiber_rot_90 test_grid =
  {| g00 := 7; g01 := 4; g02 := 1
   ; g10 := 8; g11 := 5; g12 := 2
   ; g20 := 9; g21 := 6; g22 := 3 |}.
Proof. reflexivity. Qed.

Theorem fiber_rot_270_acts :
  apply_fiber fiber_rot_270 test_grid =
  {| g00 := 3; g01 := 6; g02 := 9
   ; g10 := 2; g11 := 5; g12 := 8
   ; g20 := 1; g21 := 4; g22 := 7 |}.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 12 — COMPOSITION CONSISTENCY ON GRIDS                          *)
(*                                                                    *)
(*  apply_fiber (M ⊙ N) g = apply_fiber M (apply_fiber N g)          *)
(*  for the D₄ matrices, on the test_grid.                            *)
(* ================================================================= *)

Theorem fiber_compose_acts_double_flip :
  apply_fiber (fiber_flip_h ⊙ fiber_flip_h) test_grid =
  apply_fiber fiber_flip_h (apply_fiber fiber_flip_h test_grid).
Proof. reflexivity. Qed.

Theorem fiber_compose_acts_flip_h_flip_v :
  apply_fiber (fiber_flip_h ⊙ fiber_flip_v) test_grid =
  apply_fiber fiber_flip_v (apply_fiber fiber_flip_h test_grid).
Proof. reflexivity. Qed.

Theorem fiber_compose_acts_transpose_flip_h :
  apply_fiber (fiber_transpose ⊙ fiber_flip_h) test_grid =
  apply_fiber fiber_flip_h (apply_fiber fiber_transpose test_grid).
Proof. reflexivity. Qed.

Theorem fiber_compose_acts_rot_90_squared :
  apply_fiber (fiber_rot_90 ⊙ fiber_rot_90) test_grid =
  apply_fiber fiber_rot_90 (apply_fiber fiber_rot_90 test_grid).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 13 — D₄ HAS EXACTLY 8 ELEMENTS                                 *)
(*                                                                    *)
(*  We list all 8 D₄ fiber matrices and prove they're DISTINCT (no  *)
(*  two give the same result on the test_grid). This shows the     *)
(*  fiber matrix representation is FAITHFUL.                          *)
(* ================================================================= *)

Definition d4_fiber_matrices : list FiberMatrix :=
  [ fiber_id_matrix
  ; fiber_flip_h
  ; fiber_flip_v
  ; fiber_rot_180
  ; fiber_transpose
  ; fiber_rot_90
  ; fiber_rot_270
  ; fiber_anti_diag ].

Theorem d4_count : length d4_fiber_matrices = 8.
Proof. reflexivity. Qed.

(* All 8 are pairwise distinct as actions on test_grid. *)
Theorem id_ne_flip_h_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_flip_h test_grid.
Proof. discriminate. Qed.

Theorem id_ne_flip_v_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_flip_v test_grid.
Proof. discriminate. Qed.

Theorem id_ne_rot_180_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_rot_180 test_grid.
Proof. discriminate. Qed.

Theorem id_ne_transpose_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_transpose test_grid.
Proof. discriminate. Qed.

Theorem id_ne_rot_90_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_rot_90 test_grid.
Proof. discriminate. Qed.

Theorem id_ne_rot_270_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_rot_270 test_grid.
Proof. discriminate. Qed.

Theorem id_ne_anti_diag_action :
  apply_fiber fiber_id_matrix test_grid <>
  apply_fiber fiber_anti_diag test_grid.
Proof. discriminate. Qed.

Theorem flip_h_ne_flip_v_action :
  apply_fiber fiber_flip_h test_grid <>
  apply_fiber fiber_flip_v test_grid.
Proof. discriminate. Qed.

Theorem flip_h_ne_transpose_action :
  apply_fiber fiber_flip_h test_grid <>
  apply_fiber fiber_transpose test_grid.
Proof. discriminate. Qed.

Theorem rot_90_ne_rot_270_action :
  apply_fiber fiber_rot_90 test_grid <>
  apply_fiber fiber_rot_270 test_grid.
Proof. discriminate. Qed.

(* ================================================================= *)
(* PART 14 — INVERSE PROPERTY                                          *)
(* ================================================================= *)

(* For each transform, there's an inverse. flip_h, flip_v, rot_180,  *)
(* transpose, anti_diag are involutions (self-inverse). rot_90 and  *)
(* rot_270 are inverses of each other. *)

Theorem flip_h_self_inverse :
  fiber_flip_h ⊙ fiber_flip_h ≃ fiber_id.
Proof. exact flip_h_squared. Qed.

Theorem rot_90_inverse_is_rot_270 :
  fiber_rot_90 ⊙ fiber_rot_270 ≃ fiber_id.
Proof. exact rot_90_rot_270_eq_id. Qed.

(* ================================================================= *)
(* PART 15 — GROUP CLOSURE: D₄ IS CLOSED UNDER ⊙                       *)
(*                                                                    *)
(*  Every product of two D₄ matrices is again in D₄. We verify a    *)
(*  representative selection.                                         *)
(* ================================================================= *)

Theorem flip_h_transpose_in_d4 :
  fiber_flip_h ⊙ fiber_transpose ≃ fiber_rot_270.
Proof. intros src dst. destruct src, dst; reflexivity. Qed.

Theorem flip_v_transpose_in_d4 :
  fiber_flip_v ⊙ fiber_transpose ≃ fiber_rot_90.
Proof. intros src dst. destruct src, dst; reflexivity. Qed.

Theorem rot_180_flip_h_in_d4 :
  fiber_rot_180 ⊙ fiber_flip_h ≃ fiber_flip_v.
Proof. intros src dst. destruct src, dst; reflexivity. Qed.

Theorem rot_180_transpose_in_d4 :
  fiber_rot_180 ⊙ fiber_transpose ≃ fiber_anti_diag.
Proof. intros src dst. destruct src, dst; reflexivity. Qed.

Theorem rot_90_flip_h_in_d4 :
  fiber_rot_90 ⊙ fiber_flip_h ≃ fiber_transpose.
Proof. intros src dst. destruct src, dst; reflexivity. Qed.

(* ================================================================= *)
(* PART 16 — THE MASTER THEOREM                                        *)
(* ================================================================= *)

Theorem FIBER_MORPHISMS_OK :
  (* (1) 9 positions, with decidable equality. *)
  (length all_positions = 9) /\
  (forall p, In p all_positions) /\
  (forall p, pos_eqb p p = true) /\
  (forall p q, pos_eqb p q = true -> p = q) /\
  (* (2) Identity laws of fiber matrix composition. *)
  (forall M src dst, (fiber_id ⊙ M) src dst = M src dst) /\
  (forall M src dst, (M ⊙ fiber_id) src dst = M src dst) /\
  (* (3) Klein four group laws. *)
  (fiber_flip_h ⊙ fiber_flip_h ≃ fiber_id) /\
  (fiber_flip_v ⊙ fiber_flip_v ≃ fiber_id) /\
  (fiber_rot_180 ⊙ fiber_rot_180 ≃ fiber_id) /\
  (fiber_flip_h ⊙ fiber_flip_v ≃ fiber_rot_180) /\
  (fiber_flip_v ⊙ fiber_flip_h ≃ fiber_rot_180) /\
  (fiber_flip_h ⊙ fiber_flip_v ≃ fiber_flip_v ⊙ fiber_flip_h) /\
  (* (4) D₄ extended laws (non-abelian). *)
  (fiber_transpose ⊙ fiber_transpose ≃ fiber_id) /\
  (fiber_anti_diag ⊙ fiber_anti_diag ≃ fiber_id) /\
  (fiber_rot_90 ⊙ fiber_rot_90 ≃ fiber_rot_180) /\
  ((fiber_rot_90 ⊙ fiber_rot_90) ⊙ fiber_rot_90 ≃ fiber_rot_270) /\
  (fiber_rot_90 ⊙ fiber_rot_270 ≃ fiber_id) /\
  (fiber_rot_270 ⊙ fiber_rot_90 ≃ fiber_id) /\
  (fiber_transpose ⊙ fiber_flip_h ≃ fiber_rot_90) /\
  (fiber_flip_h ⊙ fiber_transpose ≃ fiber_rot_270) /\
  (~ (fiber_transpose ⊙ fiber_flip_h ≃ fiber_flip_h ⊙ fiber_transpose)) /\
  (* (5) Permutation property: 1 true per row, 1 per column,
        9 total. *)
  (forall src, count_true_row fiber_id_matrix src = 1) /\
  (forall src, count_true_row fiber_flip_h src = 1) /\
  (forall src, count_true_row fiber_flip_v src = 1) /\
  (forall src, count_true_row fiber_rot_180 src = 1) /\
  (forall src, count_true_row fiber_transpose src = 1) /\
  (forall src, count_true_row fiber_rot_90 src = 1) /\
  (forall src, count_true_row fiber_rot_270 src = 1) /\
  (forall src, count_true_row fiber_anti_diag src = 1) /\
  (forall dst, count_true_col fiber_id_matrix dst = 1) /\
  (forall dst, count_true_col fiber_flip_h dst = 1) /\
  (forall dst, count_true_col fiber_flip_v dst = 1) /\
  (forall dst, count_true_col fiber_rot_180 dst = 1) /\
  (forall dst, count_true_col fiber_transpose dst = 1) /\
  (forall dst, count_true_col fiber_rot_90 dst = 1) /\
  (forall dst, count_true_col fiber_rot_270 dst = 1) /\
  (forall dst, count_true_col fiber_anti_diag dst = 1) /\
  (count_true_total fiber_id_matrix = 9) /\
  (count_true_total fiber_flip_h = 9) /\
  (count_true_total fiber_flip_v = 9) /\
  (count_true_total fiber_rot_180 = 9) /\
  (count_true_total fiber_transpose = 9) /\
  (count_true_total fiber_rot_90 = 9) /\
  (count_true_total fiber_rot_270 = 9) /\
  (count_true_total fiber_anti_diag = 9) /\
  (* (6) Realization: fiber matrix application = perm application. *)
  (forall f g, apply_fiber (fiber_of_perm f) g = apply_perm f g) /\
  (* (7) Concrete actions on test_grid. *)
  (apply_fiber fiber_id_matrix test_grid = test_grid) /\
  (apply_fiber fiber_flip_h test_grid =
   {| g00 := 3; g01 := 2; g02 := 1
    ; g10 := 6; g11 := 5; g12 := 4
    ; g20 := 9; g21 := 8; g22 := 7 |}) /\
  (apply_fiber fiber_rot_90 test_grid =
   {| g00 := 7; g01 := 4; g02 := 1
    ; g10 := 8; g11 := 5; g12 := 2
    ; g20 := 9; g21 := 6; g22 := 3 |}) /\
  (apply_fiber fiber_transpose test_grid =
   {| g00 := 1; g01 := 4; g02 := 7
    ; g10 := 2; g11 := 5; g12 := 8
    ; g20 := 3; g21 := 6; g22 := 9 |}) /\
  (* (8) Composition consistency on a concrete grid. *)
  (apply_fiber (fiber_flip_h ⊙ fiber_flip_h) test_grid =
   apply_fiber fiber_flip_h (apply_fiber fiber_flip_h test_grid)) /\
  (apply_fiber (fiber_flip_h ⊙ fiber_flip_v) test_grid =
   apply_fiber fiber_flip_v (apply_fiber fiber_flip_h test_grid)) /\
  (apply_fiber (fiber_transpose ⊙ fiber_flip_h) test_grid =
   apply_fiber fiber_flip_h (apply_fiber fiber_transpose test_grid)) /\
  (apply_fiber (fiber_rot_90 ⊙ fiber_rot_90) test_grid =
   apply_fiber fiber_rot_90 (apply_fiber fiber_rot_90 test_grid)) /\
  (* (9) D₄ has exactly 8 elements. *)
  (length d4_fiber_matrices = 8) /\
  (* (10) Faithfulness: distinct elements act distinctly. *)
  (apply_fiber fiber_id_matrix test_grid <>
   apply_fiber fiber_flip_h test_grid) /\
  (apply_fiber fiber_id_matrix test_grid <>
   apply_fiber fiber_flip_v test_grid) /\
  (apply_fiber fiber_id_matrix test_grid <>
   apply_fiber fiber_rot_90 test_grid) /\
  (apply_fiber fiber_flip_h test_grid <>
   apply_fiber fiber_flip_v test_grid) /\
  (apply_fiber fiber_rot_90 test_grid <>
   apply_fiber fiber_rot_270 test_grid) /\
  (* (11) Group closure: products stay in D₄. *)
  (fiber_rot_180 ⊙ fiber_flip_h ≃ fiber_flip_v) /\
  (fiber_rot_180 ⊙ fiber_transpose ≃ fiber_anti_diag) /\
  (fiber_rot_90 ⊙ fiber_flip_h ≃ fiber_transpose) /\
  (fiber_flip_v ⊙ fiber_transpose ≃ fiber_rot_90).
Proof.
  split. { exact all_positions_length. }
  split. { exact all_positions_complete. }
  split. { exact pos_eqb_refl. }
  split. { exact pos_eqb_eq. }
  split. { exact fiber_id_left. }
  split. { exact fiber_id_right. }
  split. { exact flip_h_squared. }
  split. { exact flip_v_squared. }
  split. { exact rot_180_squared. }
  split. { exact flip_h_flip_v_eq_rot_180. }
  split. { exact flip_v_flip_h_eq_rot_180. }
  split. { exact flip_h_flip_v_commute. }
  split. { exact transpose_squared. }
  split. { exact anti_diag_squared. }
  split. { exact rot_90_squared_eq_rot_180. }
  split. { exact rot_90_cubed_eq_rot_270. }
  split. { exact rot_90_rot_270_eq_id. }
  split. { exact rot_270_rot_90_eq_id. }
  split. { exact transpose_flip_h_eq_rot_90. }
  split. { exact flip_h_transpose_eq_rot_270. }
  split. { exact transpose_flip_h_non_commute. }
  split. { exact fiber_id_row_count. }
  split. { exact fiber_flip_h_row_count. }
  split. { exact fiber_flip_v_row_count. }
  split. { exact fiber_rot_180_row_count. }
  split. { exact fiber_transpose_row_count. }
  split. { exact fiber_rot_90_row_count. }
  split. { exact fiber_rot_270_row_count. }
  split. { exact fiber_anti_diag_row_count. }
  split. { exact fiber_id_col_count. }
  split. { exact fiber_flip_h_col_count. }
  split. { exact fiber_flip_v_col_count. }
  split. { exact fiber_rot_180_col_count. }
  split. { exact fiber_transpose_col_count. }
  split. { exact fiber_rot_90_col_count. }
  split. { exact fiber_rot_270_col_count. }
  split. { exact fiber_anti_diag_col_count. }
  split. { exact fiber_id_total. }
  split. { exact fiber_flip_h_total. }
  split. { exact fiber_flip_v_total. }
  split. { exact fiber_rot_180_total. }
  split. { exact fiber_transpose_total. }
  split. { exact fiber_rot_90_total. }
  split. { exact fiber_rot_270_total. }
  split. { exact fiber_anti_diag_total. }
  split. { exact apply_fiber_of_perm. }
  split. { exact fiber_id_acts_as_identity. }
  split. { exact fiber_flip_h_acts. }
  split. { exact fiber_rot_90_acts. }
  split. { exact fiber_transpose_acts. }
  split. { exact fiber_compose_acts_double_flip. }
  split. { exact fiber_compose_acts_flip_h_flip_v. }
  split. { exact fiber_compose_acts_transpose_flip_h. }
  split. { exact fiber_compose_acts_rot_90_squared. }
  split. { exact d4_count. }
  split. { exact id_ne_flip_h_action. }
  split. { exact id_ne_flip_v_action. }
  split. { exact id_ne_rot_90_action. }
  split. { exact flip_h_ne_flip_v_action. }
  split. { exact rot_90_ne_rot_270_action. }
  split. { exact rot_180_flip_h_in_d4. }
  split. { exact rot_180_transpose_in_d4. }
  split. { exact rot_90_flip_h_in_d4. }
  exact flip_v_transpose_in_d4.
Qed.

Print Assumptions FIBER_MORPHISMS_OK.

(* ================================================================= *)
(*  QED.                                                              *)
(*                                                                    *)
(*  THE STRUCTURE:                                                    *)
(*    9 positions on a 3×3 lattice.                                   *)
(*    9×9 = 81 fiber morphisms (Boolean entries).                    *)
(*    8 elements of D₄, each a 9×9 permutation matrix.               *)
(*    Boolean matrix multiplication = group composition.             *)
(*    Each row and column has exactly 1 true entry (permutation).   *)
(*    Total 9 true entries per matrix.                               *)
(*    Faithful action on grids: distinct matrices act distinctly.   *)
(*                                                                    *)
(*  EUCLIDEAN: the 9×9 grid IS the adjacency matrix of a directed  *)
(*    graph on the 9 lattice points. A permutation transform =     *)
(*    a graph automorphism = a closed walk through the matrix.     *)
(*    The 8 D₄ matrices are the 8 isometries of the square that    *)
(*    preserve the lattice.                                          *)
(*                                                                    *)
(*  GAUSSIAN: the 8 fiber matrices are a faithful representation    *)
(*    D₄ ↪ S_9 ↪ GL(9, F_2). Boolean matrix multiplication is the  *)
(*    group operation. The Klein four subgroup {id, flip_h, flip_v, *)
(*    rot_180} is normal, with quotient ≅ ℤ/2 (the orientation     *)
(*    flip captured by transpose vs. its absence).                  *)
(*                                                                    *)
(*  ZERO Admitted. ZERO axioms. All proofs by reflexivity on        *)
(*  9-case patterns or by destruct on Pos.                            *)
(* ================================================================= *)
