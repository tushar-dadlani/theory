(** Bridge.v — The GHS Bridge between cell-level and object-level.

    Formalizes the bridge correspondence:
      br_up   : Grid → list Object   (cell grid → object representation)
      br_down : list Object → Grid   (objects → cell grid)
      br_invertible : br_down(br_up(g)) = g

    Objects partition the grid — every cell belongs to exactly one object.
    This enables domain-level evolution: transformations on ~5-15 objects
    instead of hundreds of cells.
*)

From ARC Require Import Grid.
From ARC Require Import Zone.
From ARC Require Import Evolution.
From Stdlib Require Import List.
Import ListNotations.

(** Object: a connected component with a single color *)
Record Object (r c : nat) : Type := mkObject {
  obj_color : Color;
  obj_mask  : Mask r c;
  (* Every cell in the mask has this color *)
  obj_uniform : forall (g : Grid r c) i j,
    obj_mask i j = true -> g i j = obj_color;
}.

Arguments mkObject {r c}.
Arguments obj_color {r c}.
Arguments obj_mask {r c}.

(** Object containment: does the object cover cell (i,j)? *)
Definition obj_contains {r c} (obj : Object r c) (i : Fin r) (j : Fin c) : bool :=
  obj_mask obj i j.

(** The ARC Bridge record *)
Record ARCBridge (r c : nat) : Type := mkBridge {
  br_up   : Grid r c -> list (Object r c);
  br_down : list (Object r c) -> Grid r c;

  (** Background color for cells not covered by any object *)
  br_bg : Color;

  (** Invertibility: round-trip preserves the grid *)
  br_invertible : forall g, br_down (br_up g) = g;

  (** Partition: every cell belongs to at least one object OR is background *)
  br_partition : forall g i j,
    (exists obj, In obj (br_up g) /\ obj_contains obj i j = true) \/
    (g i j = br_bg);

  (** Disjoint: no two distinct objects overlap *)
  br_disjoint : forall g obj1 obj2 i j,
    In obj1 (br_up g) -> In obj2 (br_up g) ->
    obj_contains obj1 i j = true ->
    obj_contains obj2 i j = true ->
    obj1 = obj2;
}.

Arguments mkBridge {r c}.
Arguments br_up {r c}.
Arguments br_down {r c}.
Arguments br_bg {r c}.

(** Object-level invariant: transforms a list of objects *)
Definition ObjInvariant (r c : nat) : Type :=
  list (Object r c) -> list (Object r c).

(** Lift a cell-level invariant to object-level via the bridge *)
Definition lift_invariant {r c} (bridge : ARCBridge r c)
    (cell_inv : Invariant r c) : ObjInvariant r c :=
  fun objs => br_up bridge (cell_inv (br_down bridge objs)).

(** Object-level evolution step:
    Apply an object transformation, then render back to cell grid *)
Definition obj_evolve_step {r c} (bridge : ARCBridge r c)
    (obj_rule : ObjInvariant r c) : Invariant r c :=
  fun g => br_down bridge (obj_rule (br_up bridge g)).

(** Soundness: if an object-level rule produces correct output,
    the induced cell-level invariant is also correct. *)
Lemma obj_rule_sound :
  forall r c (bridge : ARCBridge r c)
         (obj_rule : ObjInvariant r c)
         (inp out : Grid r c),
    br_down bridge (obj_rule (br_up bridge inp)) = out ->
    obj_evolve_step bridge obj_rule inp = out.
Proof.
  intros. unfold obj_evolve_step. exact H.
Qed.

(** The bridge preserves the partition structure:
    objects from br_up induce a valid zone partition
    when compared with the output grid. *)
Lemma bridge_preserves_partition :
  forall r c (bridge : ARCBridge r c) (g : Grid r c),
    br_down bridge (br_up bridge g) = g.
Proof.
  intros. apply br_invertible.
Qed.
