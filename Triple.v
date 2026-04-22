(** * Triple.v — The Cause/Observer/Effect primitive

    The triple is ONE thing with internal structure.
    Not three separate entities composed — one entity
    that, when examined, presents three co-constitutive aspects.

    Axiom: you cannot have any one without the other two.
    Effect without Observer has no boundary.
    Observer without Effect has nothing to bound.
    Observer without Cause has no other side.

    We formalize this as a single record with a well-formedness
    proof baked into the constructor. *)

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import Lia.
Open Scope Q_scope.

(* ================================================================ *)
(** ** Depth                                                         *)
(* ================================================================ *)

(** A rational number in (0, 1].
    Depth 1 = most observable (disc_point).
    Depth → 0 = ground (unreachable limit, never reached). *)

Record Depth := mkDepth {
  depth_val : Q;
  depth_pos : 0 < depth_val;
  depth_le1 : depth_val <= 1;
}.

(** Canonical depths. *)

Lemma one_pos : 0 < 1. Proof. reflexivity. Qed.
Lemma one_le1 : (1 <= 1)%Q. Proof. apply Qle_refl. Qed.
Definition disc_point : Depth := mkDepth 1 one_pos one_le1.

Lemma half_pos : 0 < 1#2. Proof. reflexivity. Qed.
Lemma half_le1 : (1#2 <= 1)%Q. Proof. unfold Qle; simpl; lia. Qed.
Definition clifford_t : Depth := mkDepth (1#2) half_pos half_le1.

Lemma third_pos : 0 < 1#3. Proof. reflexivity. Qed.
Lemma third_le1 : (1#3 <= 1)%Q. Proof. unfold Qle; simpl; lia. Qed.
Definition gauge_circ : Depth := mkDepth (1#3) third_pos third_le1.

(** The tower function: tower(n) = 1/(n+1). *)

Lemma tower_pos (n : positive) : 0 < 1 # (n + 1).
Proof. unfold Qlt; simpl. lia. Qed.

Lemma tower_le1 (n : positive) : 1 # (n + 1) <= 1.
Proof. unfold Qle; simpl. lia. Qed.

Definition tower (n : positive) : Depth :=
  mkDepth (1 # (n + 1)) (tower_pos n) (tower_le1 n).

(** Depth ordering. *)

Definition deeper (a b : Depth) : Prop := depth_val a < depth_val b.

(* ================================================================ *)
(** ** Zone predicates                                               *)
(* ================================================================ *)

(** The Observer divides the stratum space into two zones.
    These must be defined before the Triple record. *)

Definition in_effect_zone (d obs : Depth) : Prop :=
  depth_val obs <= depth_val d.

Definition in_cause_zone (d obs : Depth) : Prop :=
  depth_val d < depth_val obs.

(* ================================================================ *)
(** ** The Triple                                                    *)
(* ================================================================ *)

(** A triple (Effect, Observer, Cause) is well-formed when:
    1. Effect depth >= Observer depth  (Effect is in observable zone)
    2. Observer depth > 0              (from Depth record)
    3. Cause ceiling = Observer depth  (they share a boundary)

    These are not independent constraints — they are the SAME fact
    seen from three angles:
    - From Effect's side: "I am above the boundary"
    - From Observer's side: "I am the boundary"
    - From Cause's side: "the boundary is my ceiling" *)

Record Triple := mkTriple {
  effect_depth  : Depth;
  observer_depth : Depth;
  cause_ceiling : Depth;

  (** Effect is in the observable zone *)
  effect_above_observer : in_effect_zone effect_depth observer_depth;

  (** Cause ceiling IS the Observer position.
      The Observer doesn't just separate two zones —
      it IS the shared boundary. Co-constitutive. *)
  cause_shares_boundary : depth_val cause_ceiling = depth_val observer_depth;
}.

(* ================================================================ *)
(** ** Zone partition                                                 *)
(* ================================================================ *)

(** Every depth is in exactly one zone relative to a triple. *)

Theorem zone_partition : forall (t : Triple) (d : Depth),
  in_effect_zone d (observer_depth t) \/ in_cause_zone d (observer_depth t).
Proof.
  intros t d.
  unfold in_effect_zone, in_cause_zone.
  destruct (Qlt_le_dec (depth_val d) (depth_val (observer_depth t))).
  - right; exact q.
  - left; exact q.
Qed.

Theorem zone_exclusive : forall (t : Triple) (d : Depth),
  in_effect_zone d (observer_depth t) ->
  in_cause_zone d (observer_depth t) ->
  False.
Proof.
  intros t d H1 H2.
  unfold in_effect_zone, in_cause_zone in *.
  exact (Qlt_not_le _ _ H2 H1).
Qed.

(** The triple's own Effect is always in the Effect zone.
    (Immediate from the well-formedness constraint.) *)

Theorem effect_in_effect_zone : forall t : Triple,
  in_effect_zone (effect_depth t) (observer_depth t).
Proof.
  intro t. exact (effect_above_observer t).
Qed.

(* ================================================================ *)
(** ** Canonical construction                                        *)
(* ================================================================ *)

Lemma disc_above_tower (n : positive) :
  in_effect_zone disc_point (tower n).
Proof.
  unfold in_effect_zone; simpl. unfold Qle; simpl. lia.
Qed.

Definition canonical_triple (n : positive) : Triple :=
  mkTriple disc_point (tower n) (tower n) (disc_above_tower n) eq_refl.

(** The canonical triple at gauge_circ (n=2, depth 1/3). *)
Definition transformer_triple : Triple := canonical_triple 2.

(* ================================================================ *)
(** ** Co-constitution                                               *)
(* ================================================================ *)

(** The Observer IS the boundary. This is the formal statement
    that the triple is one thing, not three. *)

Theorem observer_is_boundary : forall t : Triple,
  depth_val (observer_depth t) = depth_val (cause_ceiling t).
Proof.
  intro t. symmetry. exact (cause_shares_boundary t).
Qed.

(** Shared Observer → shared Cause ceiling. *)

Theorem shared_observer_shared_cause : forall t1 t2 : Triple,
  depth_val (observer_depth t1) = depth_val (observer_depth t2) ->
  depth_val (cause_ceiling t1) = depth_val (cause_ceiling t2).
Proof.
  intros t1 t2 H.
  rewrite (cause_shares_boundary t1).
  rewrite (cause_shares_boundary t2).
  exact H.
Qed.
