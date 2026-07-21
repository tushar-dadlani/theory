(** Grid.v — Base types for ARC grids.

    Color = finite set {0..9}
    Grid  = bounded matrix of colors
    Pair  = input/output grids (possibly different dimensions)
    Task  = training pairs + test pairs
*)

From Stdlib Require Import List.
Import ListNotations.

(** Color: the 10 ARC colors *)
Inductive Color : Set :=
  | c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9.

(** Decidable equality on Color *)
Definition color_eq_dec (a b : Color) : {a = b} + {a <> b}.
Proof.
  destruct a, b;
    try (left; reflexivity);
    try (right; discriminate).
Defined.

(** Boolean color equality *)
Definition color_eqb (a b : Color) : bool :=
  if color_eq_dec a b then true else false.

Lemma color_eqb_refl : forall c, color_eqb c c = true.
Proof.
  intros c. unfold color_eqb.
  destruct (color_eq_dec c c) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma color_eqb_eq : forall a b, color_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold color_eqb.
  destruct (color_eq_dec a b) as [Heq | Hneq].
  - split; intros; assumption || reflexivity.
  - split; intros H.
    + discriminate H.
    + exfalso. apply Hneq. exact H.
Qed.

(** Bounded natural number — position index *)
Inductive Fin : nat -> Set :=
  | FZ : forall {n}, Fin (S n)
  | FS : forall {n}, Fin n -> Fin (S n).

(** Grid: a bounded matrix of colors *)
Definition Grid (rows cols : nat) : Type :=
  Fin rows -> Fin cols -> Color.

(** Pair: input/output grids (possibly different dimensions) *)
Record Pair : Type := mkPair {
  inp_r : nat;
  inp_c : nat;
  out_r : nat;
  out_c : nat;
  input  : Grid inp_r inp_c;
  output : Grid out_r out_c;
}.

(** Task: training pairs + test pairs *)
Record Task : Type := mkTask {
  train : list Pair;
  test  : list Pair;
}.

(** Grid equality is decidable (finite domain) *)
Definition grid_eq_at {r c} (g1 g2 : Grid r c) (i : Fin r) (j : Fin c) : bool :=
  color_eqb (g1 i j) (g2 i j).

(** The constant (all-same-color) grid *)
Definition const_grid {r c} (col : Color) : Grid r c :=
  fun _ _ => col.
