(** Evolution.v — The kernel evolution equation.

    ∂invariant/∂t = -2 · kernel(invariant)

    Discrete formulation:
    - invariant(t) is the current transformation, evolving over iterations
    - kernel(invariant) = cells where invariant acts as identity but SHOULD change
    - The -2 factor is realized as 2x spatial expansion (dilation) of the error kernel
    - Fixed point: error kernel shrinks to empty, invariant IS the solution
*)

Require Import Grid.
Require Import Zone.
From Stdlib Require Import List.
Import ListNotations.

(** Invariant: a transformation function on same-dimension grids *)
Definition Invariant (r c : nat) : Type := Grid r c -> Grid r c.

(** Identity invariant *)
Definition id_invariant {r c} : Invariant r c := fun g => g.

(** Invariant kernel: cells where the invariant acts as identity *)
Definition inv_kernel {r c} (inv : Invariant r c) (g : Grid r c) : Mask r c :=
  fun i j => color_eqb (inv g i j) (g i j).

(** Error kernel: cells in the invariant kernel that SHOULD change.
    These are cells where:
    1. The invariant produces the same value as the input (it's in the kernel)
    2. But the input differs from the expected output (it should have changed) *)
Definition error_kernel {r c} (inv : Invariant r c) (inp out : Grid r c) : Mask r c :=
  fun i j => andb (color_eqb (inv inp i j) (inp i j))
                   (negb (color_eqb (inp i j) (out i j))).

(** Combined error kernel across multiple training pairs *)
Fixpoint combined_error_kernel {r c} (inv : Invariant r c)
    (pairs : list (Grid r c * Grid r c)) : Mask r c :=
  match pairs with
  | [] => empty_mask
  | (inp, out) :: rest =>
      mask_or (error_kernel inv inp out) (combined_error_kernel inv rest)
  end.

(** Mask cardinality: count of true cells.
    We define this over a bounded traversal. *)

(** Count true cells in a single row *)
Fixpoint count_row {c} (m : Fin c -> bool) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S _ => 0  (* Simplified — actual counting requires Fin enumeration *)
  end.

(** Error count: number of true cells in a mask.
    Abstract for the convergence theorem. *)
Parameter mask_count : forall {r c}, Mask r c -> nat.

(** Axiom: empty mask has count 0 *)
Axiom empty_mask_count : forall r c, mask_count (@empty_mask r c) = 0.

(** Axiom: count is bounded by grid size *)
Axiom mask_count_bounded : forall r c (m : Mask r c), mask_count m <= r * c.

(** Discrete evolution step:
    Given current invariant and a correction function,
    apply the correction at the (expanded) error kernel cells,
    keep the current invariant elsewhere. *)
Definition evolve_step {r c}
    (inv : Invariant r c)
    (pairs : list (Grid r c * Grid r c))
    (correction : Invariant r c)
    (expanded_ek : Mask r c) : Invariant r c :=
  fun g i j =>
    if expanded_ek i j then correction g i j
    else inv g i j.

(** Iterate evolution for n steps.
    At each step, we need a correction oracle that provides:
    1. A correction invariant
    2. The expanded error kernel mask
    We model this as a function from step index to (correction, mask). *)
Fixpoint iterate_evolve {r c}
    (n : nat)
    (inv : Invariant r c)
    (pairs : list (Grid r c * Grid r c))
    (oracle : nat -> Invariant r c * Mask r c) : Invariant r c :=
  match n with
  | 0 => inv
  | S n' =>
      let (correction, expanded_ek) := oracle n' in
      let inv' := evolve_step inv pairs correction expanded_ek in
      iterate_evolve n' inv' pairs oracle
  end.

(** Key property: if correction is correct on expanded region,
    error count strictly decreases. *)
Axiom correction_decreases_error :
  forall r c (inv : Invariant r c) (pairs : list (Grid r c * Grid r c))
         (correction : Invariant r c) (expanded_ek : Mask r c),
    (* If the correction produces correct output on expanded cells *)
    (forall g_in g_out i j,
      In (g_in, g_out) pairs ->
      expanded_ek i j = true ->
      correction g_in i j = g_out i j) ->
    (* And the expanded kernel covers the error kernel *)
    mask_subset (combined_error_kernel inv pairs) expanded_ek ->
    (* Then the new error count is strictly less *)
    mask_count (combined_error_kernel (evolve_step inv pairs correction expanded_ek) pairs) <
    mask_count (combined_error_kernel inv pairs).

(** Convergence theorem:
    For any finite grid and training pairs, the evolution terminates.

    Proof sketch:
    - Grid state space is finite (r * c cells, 10 colors each)
    - Error kernel count is a natural number bounded by r * c
    - Each correct evolution step strictly decreases the error count
    - Therefore, evolution must terminate in at most r * c steps
    - At termination, error kernel is empty: the invariant IS the solution *)
Theorem convergence :
  forall r c (pairs : list (Grid r c * Grid r c)),
    pairs <> [] ->
    exists (n : nat) (oracle : nat -> Invariant r c * Mask r c),
      let inv := iterate_evolve n id_invariant pairs oracle in
      n <= r * c /\
      combined_error_kernel inv pairs = empty_mask.
Proof.
  (* The error kernel count is bounded by r*c and strictly decreases.
     By well-founded induction on nat, this terminates. *)
  (* Full proof requires enumerating Fin positions — admitted for now. *)
Admitted.

(** The -2 factor: expansion covers twice the error region.
    This is formalized as: the expanded mask is a superset of the
    error kernel dilated once (covering immediate neighbors). *)

(** Dilation of a mask: a cell is true if it or any of its 4-neighbors is true.
    For Fin-indexed grids, we need neighbor access, which requires
    successor/predecessor on Fin. We state the property abstractly. *)
Parameter dilate_mask : forall {r c}, Mask r c -> Mask r c.

(** Dilation is expansive *)
Axiom dilate_expansive : forall r c (m : Mask r c),
  mask_subset m (dilate_mask m).

(** The -2 factor = double dilation covers 2x the error region *)
Definition double_dilate {r c} (m : Mask r c) : Mask r c :=
  dilate_mask (dilate_mask m).

(** Double dilation expands coverage *)
Lemma double_dilate_expansive : forall r c (m : Mask r c),
  mask_subset m (double_dilate m).
Proof.
  intros r c m i j H.
  apply dilate_expansive. apply dilate_expansive. exact H.
Qed.
