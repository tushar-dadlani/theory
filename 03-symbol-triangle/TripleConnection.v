(** * Corollary 3: Triple.v Connections to the Proof Tower *)

(** Triple.v defines a Cause/Observer/Effect primitive over (0,1]
    using Depth (rationals in (0,1]) and zone partitioning.

    This file bridges Triple.v to the tower:
    - Depth → q_in_interval (QInterval.v)
    - Depth → affine_interval via Q2R (GeometryInterval.v)
    - tower(n) → vanishing point (VanishingPoint.v)
    - Effect zone → affine interval
    - Ground (depth → 0 limit) = vanishing point *)

From Stdlib Require Import QArith.
From Stdlib Require Import Reals.
From Stdlib Require Import Qreals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
Require Import IntervalEquiv.
Require Import QInterval.
Require Import RInterval.
Require Import GeometryInterval.
Require Import VanishingPoint.
Require Import Triple.

Open Scope R_scope.

(* ================================================================= *)
(** ** Bridge 1: Depth → q_in_interval (QInterval.v)                 *)
(* ================================================================= *)

(** Every Depth value satisfies the (0,1] predicate from QInterval.v.
    The Depth record encodes the same constraints constructively. *)

Theorem depth_satisfies_q_in_interval :
  forall d : Depth, q_in_interval (depth_val d).
Proof.
  intro d. unfold q_in_interval. split.
  - exact (depth_pos d).
  - exact (depth_le1 d).
Qed.

(** Canonical depths are in (0,1] *)
Corollary disc_point_in_interval : q_in_interval (depth_val disc_point).
Proof. apply depth_satisfies_q_in_interval. Qed.

Corollary clifford_in_interval : q_in_interval (depth_val clifford_t).
Proof. apply depth_satisfies_q_in_interval. Qed.

Corollary gauge_in_interval : q_in_interval (depth_val gauge_circ).
Proof. apply depth_satisfies_q_in_interval. Qed.

(* ================================================================= *)
(** ** Bridge 2: Depth → affine_interval via Q2R (GeometryInterval.v)*)
(* ================================================================= *)

(** Every Depth embeds into R and lands in the affine interval (0,1].
    This connects the constructive Q world of Triple.v to the
    geometric R world of affine/projective intervals. *)

Theorem depth_embeds_in_affine :
  forall d : Depth, affine_interval (Q2R (depth_val d)).
Proof.
  intro d.
  unfold affine_interval.
  apply q_real_interval_agree.
  exact (depth_satisfies_q_in_interval d).
Qed.

(** No Depth value can be the vanishing point *)
Corollary depth_is_never_vanishing :
  forall d : Depth, Q2R (depth_val d) <> vanishing_point.
Proof.
  intros d Heq.
  assert (Haff : affine_interval (Q2R (depth_val d)))
    by (apply depth_embeds_in_affine).
  rewrite Heq in Haff.
  exact (affine_no_witness Haff).
Qed.

(* ================================================================= *)
(** ** Bridge 3: tower(n) → vanishing point (VanishingPoint.v)       *)
(* ================================================================= *)

(** The tower function tower(n) = 1/(n+1) produces Depth values
    that approach the vanishing point 0 as n grows.
    This is the (0,1] approach sequence from the tower, now
    connected to VanishingPoint.v's vanishing_point = 0. *)

Lemma Q2R_tower_pos : forall n : positive,
  Q2R (depth_val (tower n)) > 0.
Proof.
  intro n.
  assert (H := depth_embeds_in_affine (tower n)).
  unfold affine_interval in H. lra.
Qed.

Theorem tower_approaches_vanishing :
  forall eps : R, eps > 0 ->
    exists n : positive, Q2R (depth_val (tower n)) < eps.
Proof.
  intros eps Heps.
  (* Strategy: use Qlt_Rlt to work in Q, where 1#(n+1) < eps
     reduces to integer arithmetic via the Archimedean property *)
  destruct (archimed (/ eps)) as [Harch _].
  (* up(/eps) > /eps > 0, so up(/eps) >= 1 as an integer *)
  assert (Hup_pos : (0 < up (/ eps))%Z).
  { apply lt_IZR. simpl.
    apply Rlt_trans with (/ eps).
    - apply Rinv_0_lt_compat. exact Heps.
    - exact Harch. }
  (* Pick n such that n+1 > up(/eps), ensuring 1/(n+1) < eps *)
  exists (Z.to_pos (up (/ eps))).
  set (m := Z.to_pos (up (/ eps))).
  (* depth_val (tower m) = 1 # (m + 1) *)
  simpl depth_val.
  (* Use Qlt_Rlt: it suffices to show the Q inequality,
     then lift to R. But we need to go the other way:
     show the R inequality directly. *)
  assert (Haff := depth_embeds_in_affine (tower m)).
  unfold affine_interval in Haff. destruct Haff as [Hpos Hle1].
  (* Q2R (1 # (m+1)) = IZR 1 * / IZR (Zpos (m+1)) = / IZR (Zpos (m+1)) *)
  assert (Hm1_val : Q2R (1 # (m + 1))%Q = / IZR (Z.pos (m + 1))).
  { unfold Q2R. simpl Qnum. rewrite Rmult_1_l. reflexivity. }
  rewrite Hm1_val.
  assert (Hm1_pos : IZR (Z.pos (m + 1)) > 0) by (apply IZR_lt; lia).
  assert (Hm1_big : IZR (Z.pos (m + 1)) > / eps).
  { apply Rlt_trans with (IZR (up (/ eps))).
    - exact Harch.
    - apply IZR_lt. unfold m. lia. }
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat.
    + apply Rinv_0_lt_compat. exact Heps.
    + exact Hm1_pos.
  - exact Hm1_big.
Qed.

(** The tower never reaches the vanishing point *)
Corollary tower_never_reaches_vanishing :
  forall n : positive, Q2R (depth_val (tower n)) <> vanishing_point.
Proof.
  intro n. apply depth_is_never_vanishing.
Qed.

(* ================================================================= *)
(** ** Bridge 4: Effect zone → affine interval                       *)
(* ================================================================= *)

(** Every Depth in the effect zone of a Triple embeds into the
    affine interval. The effect zone is "above" the observer,
    which is always positive — so all effect zone elements
    are well within (0,1]. *)

Theorem effect_zone_is_affine :
  forall (t : Triple) (d : Depth),
    in_effect_zone d (observer_depth t) ->
    affine_interval (Q2R (depth_val d)).
Proof.
  intros t d _.
  (* The zone constraint is irrelevant — ALL Depths are affine *)
  apply depth_embeds_in_affine.
Qed.

(** The cause zone elements are also affine (they are still Depths) *)
Theorem cause_zone_is_affine :
  forall (t : Triple) (d : Depth),
    in_cause_zone d (observer_depth t) ->
    affine_interval (Q2R (depth_val d)).
Proof.
  intros t d _.
  apply depth_embeds_in_affine.
Qed.

(** Both zones embed in affine — the ENTIRE Depth type is affine.
    The projective extension (adding the vanishing point 0) is
    what lies OUTSIDE the Depth type. *)
Theorem all_depths_are_affine_not_projective_boundary :
  (forall d : Depth, affine_interval (Q2R (depth_val d))) /\
  ~ affine_interval vanishing_point /\
  projective_interval vanishing_point.
Proof.
  split; [| split].
  - exact depth_embeds_in_affine.
  - exact affine_no_witness.
  - exact projective_witness_exists.
Qed.

(* ================================================================= *)
(** ** Bridge 5: Ground = Vanishing Point                            *)
(* ================================================================= *)

(** The "ground" in Triple.v is the unreachable limit as depth → 0.
    We prove: this ground IS the vanishing point from the tower.

    Three facts combined:
    1. The vanishing point is 0
    2. The tower sequence converges to 0
    3. 0 is not in the affine interval (not a Depth)

    This is the formal statement that the ground of the Triple
    framework is the same vanishing point that emerged from
    geometry, category theory, and G = Hom(G,G). *)

Theorem ground_is_vanishing :
  (** The vanishing point is 0 *)
  vanishing_point = 0 /\
  (** The tower sequence approaches it *)
  (forall eps, eps > 0 ->
    exists n : positive, Q2R (depth_val (tower n)) < eps) /\
  (** It is not a valid Depth (not in affine interval) *)
  ~ affine_interval vanishing_point.
Proof.
  split; [| split].
  - reflexivity.
  - exact tower_approaches_vanishing.
  - exact affine_no_witness.
Qed.

(** The Observer boundary approaches the vanishing point as depth → 0.
    In the limit, the Observer IS the vanishing point — the boundary
    between affine and projective, between Effect and Cause,
    between computable and divergent. *)
Theorem observer_limit_is_vanishing :
  forall eps : R, eps > 0 ->
    exists n : positive,
      let t := canonical_triple n in
      Q2R (depth_val (observer_depth t)) < eps /\
      Q2R (depth_val (observer_depth t)) > 0.
Proof.
  intros eps Heps.
  destruct (tower_approaches_vanishing eps Heps) as [n Hn].
  exists n. simpl. split.
  - exact Hn.
  - apply Q2R_tower_pos.
Qed.
