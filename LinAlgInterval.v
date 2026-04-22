(** * Linear Algebra over R and Bounded (0,1] *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Require Import IntervalEquiv.
Require Import RInterval.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: R as a 1-Dimensional Vector Space                     *)
(* ================================================================= *)

(** The vector space operations on R are just the standard ones:
    - vector addition = real addition
    - scalar multiplication = real multiplication
    - zero vector = 0
    We record the axioms explicitly to show (0,1] lives inside
    a well-defined algebraic structure. *)

(** Vector space axioms for R over itself *)
Lemma vs_add_comm : forall x y : R, x + y = y + x.
Proof. intros. lra. Qed.

Lemma vs_add_assoc : forall x y z : R, x + (y + z) = (x + y) + z.
Proof. intros. lra. Qed.

Lemma vs_add_zero : forall x : R, x + 0 = x.
Proof. intros. lra. Qed.

Lemma vs_add_inv : forall x : R, x + (- x) = 0.
Proof. intros. lra. Qed.

Lemma vs_scale_assoc : forall a b x : R, a * (b * x) = (a * b) * x.
Proof. intros. lra. Qed.

Lemma vs_scale_one : forall x : R, 1 * x = x.
Proof. intros. lra. Qed.

Lemma vs_scale_dist_add : forall a x y : R, a * (x + y) = a * x + a * y.
Proof. intros. lra. Qed.

Lemma vs_scale_dist_scalar : forall a b x : R, (a + b) * x = a * x + b * x.
Proof. intros. lra. Qed.

(* ================================================================= *)
(** ** Part 2: Bounded-Above Property of (0,1]                       *)
(* ================================================================= *)

(** A subset S of R is bounded above if there exists an upper bound *)
Definition bounded_above (S : R -> Prop) : Prop :=
  exists M : R, forall x, S x -> x <= M.

(** A subset S of R is bounded below if there exists a lower bound *)
Definition bounded_below (S : R -> Prop) : Prop :=
  exists m : R, forall x, S x -> m <= x.

(** A subset is bounded if it is bounded above and below *)
Definition bounded (S : R -> Prop) : Prop :=
  bounded_above S /\ bounded_below S.

(** (0,1] is bounded above by 1 *)
Theorem interval_bounded_above : bounded_above in_interval_conj.
Proof.
  exists 1. intros x [_ Hle]. exact Hle.
Qed.

(** 1 is the tightest (least) upper bound *)
Theorem interval_sup_is_1 : is_lub in_interval_conj 1.
Proof.
  split.
  - intros x [_ Hle]. exact Hle.
  - intros b Hb.
    apply Hb. unfold in_interval_conj. lra.
Qed.

(** (0,1] is bounded below by 0 (though 0 is not attained) *)
Theorem interval_bounded_below : bounded_below in_interval_conj.
Proof.
  exists 0. intros x [Hpos _]. lra.
Qed.

(** Therefore (0,1] is bounded (both sides) *)
Theorem interval_bounded : bounded in_interval_conj.
Proof.
  split.
  - exact interval_bounded_above.
  - exact interval_bounded_below.
Qed.

(* ================================================================= *)
(** ** The Witness Problem: (0,1] vs [0,1]                           *)
(* ================================================================= *)

(** A "witness" for a predicate is a concrete element that satisfies it.
    For (0,1], we can always produce a witness ABOVE any point in the
    interval (just pick 1), but producing a witness BELOW a given
    point is the challenge — there is no smallest element. *)

(** Witness above: 1 is always a witness for (0,1] *)
Theorem witness_above : in_interval_conj 1.
Proof. unfold in_interval_conj. lra. Qed.

(** Witness below: for any x in (0,1], x/2 is also in (0,1] and
    strictly smaller. This is what makes (0,1] open on the left —
    you can always go closer to 0 but never reach it. *)
Theorem witness_below : forall x : R,
  in_interval_conj x -> in_interval_conj (x / 2) /\ x / 2 < x.
Proof.
  intros x [Hpos Hle]. unfold in_interval_conj. split; [split|]; lra.
Qed.

(** The infimum witness: for any proposed lower bound lb > 0,
    we can produce a witness in (0,1] that is BELOW lb.
    This is the constructive content of "0 is the inf." *)
Theorem inf_witness : forall lb : R,
  lb > 0 ->
  exists x, in_interval_conj x /\ x < lb.
Proof.
  intros lb Hlb.
  (* The witness: pick min(lb/2, 1/2) — always in (0,1] and < lb *)
  exists (Rmin (lb / 2) (1 / 2)).
  split.
  - unfold in_interval_conj. split.
    + apply Rlt_le_trans with (Rmin (lb / 2) (1 / 2)).
      * apply Rmin_pos; lra.   (* Rmin of two positives is positive *)
      * lra.
    + apply Rle_trans with (1 / 2).
      * apply Rmin_r.
      * lra.
  - apply Rle_lt_trans with (lb / 2).
    + apply Rmin_l.
    + lra.
Qed.

(** 0 is the greatest lower bound (infimum), not attained *)
Theorem interval_inf_is_0 :
  (forall x, in_interval_conj x -> 0 <= x) /\
  (forall lb, (forall x, in_interval_conj x -> lb <= x) -> lb <= 0).
Proof.
  split.
  - intros x [Hpos _]. lra.
  - intros lb Hlb.
    destruct (Rle_dec lb 0) as [H | H].
    + exact H.
    + exfalso.
      assert (Hlb_pos : lb > 0) by lra.
      destruct (inf_witness lb Hlb_pos) as [x [Hx Hlt]].
      assert (lb <= x) by (apply Hlb; exact Hx).
      lra.
Qed.

(** The key asymmetry: sup IS attained, inf is NOT *)

(** 1 is in (0,1] — the sup is attained *)
Theorem sup_attained : in_interval_conj 1.
Proof. unfold in_interval_conj. lra. Qed.

(** 0 is NOT in (0,1] — the inf is not attained *)
Theorem inf_not_attained : ~ in_interval_conj 0.
Proof. unfold in_interval_conj. lra. Qed.

(** This asymmetry is exactly what makes (0,1] half-open:
    - The right side is closed: sup = max = 1, WITNESSED by 1 itself
    - The left side is open: inf = 0, NO witness (0 is not a member)
    Instead, we have an infinite chain of witnesses approaching 0:
    1, 1/2, 1/4, 1/8, ... each in (0,1] but never reaching 0 *)

(* ================================================================= *)
(** ** Part 3: How Linear Operations Interact with the Bound         *)
(* ================================================================= *)

(** Scaling (0,1] by a positive constant c gives (0, c] *)
Definition scaled_interval (c : R) (x : R) : Prop :=
  exists y, in_interval_conj y /\ x = c * y.

(** If c > 0, the scaled interval is bounded above by c *)
Theorem scaled_bounded_above : forall c : R,
  c > 0 -> bounded_above (scaled_interval c).
Proof.
  intros c Hc. exists c.
  intros x [y [[Hy_pos Hy_le] Heq]].
  rewrite Heq. nra.
Qed.

(** The sup of the scaled interval is c *)
Theorem scaled_sup : forall c : R,
  c > 0 -> is_lub (scaled_interval c) c.
Proof.
  intros c Hc. split.
  - intros x [y [[Hy_pos Hy_le] Heq]].
    rewrite Heq.
    nra.
  - intros b Hb.
    apply Hb. exists 1. split.
    + unfold in_interval_conj. lra.
    + lra.
Qed.

(** Scaling preserves boundedness *)
Theorem scaled_bounded : forall c : R,
  c > 0 -> bounded (scaled_interval c).
Proof.
  intros c Hc. split.
  - exact (scaled_bounded_above c Hc).
  - exists 0. intros x [y [[Hy_pos Hy_le] Heq]].
    rewrite Heq. nra.
Qed.

(** Scaling by 0 collapses to {0} — bounded but degenerate *)
Theorem scaled_zero :
  forall x, scaled_interval 0 x -> x = 0.
Proof.
  intros x [y [_ Heq]]. lra.
Qed.

(** Scaling by a negative constant c < 0 flips the interval to [c, 0) *)
Theorem scaled_neg_bounded_above : forall c : R,
  c < 0 -> bounded_above (scaled_interval c).
Proof.
  intros c Hc. exists 0.
  intros x [y [[Hy_pos Hy_le] Heq]].
  rewrite Heq. nra.
Qed.

(* ================================================================= *)
(** ** Part 4: Translation and Affine Maps                           *)
(* ================================================================= *)

(** Translating (0,1] by t gives (t, 1+t] *)
Definition translated_interval (t : R) (x : R) : Prop :=
  exists y, in_interval_conj y /\ x = y + t.

(** Translated interval is bounded above by 1 + t *)
Theorem translated_bounded_above : forall t : R,
  bounded_above (translated_interval t).
Proof.
  intro t. exists (1 + t).
  intros x [y [[Hy_pos Hy_le] Heq]]. lra.
Qed.

(** The sup of the translated interval is 1 + t *)
Theorem translated_sup : forall t : R,
  is_lub (translated_interval t) (1 + t).
Proof.
  intro t. split.
  - intros x [y [[_ Hy_le] Heq]]. lra.
  - intros b Hb.
    assert (H : translated_interval t (1 + t)).
    { exists 1. split.
      - unfold in_interval_conj. lra.
      - lra. }
    exact (Hb (1 + t) H).
Qed.

(** General affine map: x ↦ a*x + b applied to (0,1] *)
Definition affine_image (a b : R) (x : R) : Prop :=
  exists y, in_interval_conj y /\ x = a * y + b.

(** Affine images of (0,1] are always bounded above *)
Theorem affine_bounded_above : forall a b : R,
  bounded_above (affine_image a b).
Proof.
  intros a b.
  destruct (Rle_dec 0 a) as [Ha | Ha].
  - (* a >= 0: image is bounded above by a + b *)
    exists (a + b). intros x [y [[_ Hy_le] Heq]].
    rewrite Heq. nra.
  - (* a < 0: image is bounded above by b *)
    exists b. intros x [y [[Hy_pos _] Heq]].
    rewrite Heq. nra.
Qed.

(** The sup of the affine image depends on the sign of a *)
Theorem affine_sup_positive : forall a b : R,
  a > 0 -> is_lub (affine_image a b) (a + b).
Proof.
  intros a b Ha. split.
  - intros x [y [[_ Hy_le] Heq]]. rewrite Heq. nra.
  - intros m Hm.
    assert (H : affine_image a b (a * 1 + b)).
    { exists 1. split.
      - unfold in_interval_conj. lra.
      - reflexivity. }
    assert (Hle : a * 1 + b <= m) by (apply Hm; exact H).
    lra.
Qed.

(* ================================================================= *)
(** ** Part 5: Convexity of (0,1]                                    *)
(* ================================================================= *)

(** (0,1] is convex: for any x, y in (0,1] and t in [0,1],
    the convex combination t*x + (1-t)*y is in (0,1] *)
Theorem interval_convex : forall x y t : R,
  in_interval_conj x -> in_interval_conj y ->
  0 <= t -> t <= 1 ->
  in_interval_conj (t * x + (1 - t) * y).
Proof.
  intros x y t [Hx_pos Hx_le] [Hy_pos Hy_le] Ht0 Ht1.
  unfold in_interval_conj. split; nra.
Qed.

(** Convexity + bounded above implies the sup is preserved:
    if S ⊆ (0,1] is convex and non-empty, its sup is at most 1 *)
Theorem convex_subset_bounded : forall S : R -> Prop,
  (forall x, S x -> in_interval_conj x) ->
  bounded_above S.
Proof.
  intros S Hsub. exists 1.
  intros x Hx. destruct (Hsub x Hx) as [_ Hle]. exact Hle.
Qed.

(* ================================================================= *)
(** ** Part 6: Connection to Predicate Algebra                       *)
(* ================================================================= *)

(** Using derived predicate extensionality from RInterval.v,
    we can show that the bounded-above property is invariant
    under predicate equivalence *)

Theorem bounded_above_ext : forall P Q : R -> Prop,
  (forall x, P x <-> Q x) ->
  bounded_above P -> bounded_above Q.
Proof.
  intros P Q Hext [M HM].
  exists M. intros x Hx.
  apply HM. apply Hext. exact Hx.
Qed.

(** The two (0,1] predicates have the same bounded-above property *)
Theorem both_intervals_bounded :
  bounded_above in_interval_conj /\ bounded_above in_interval_alt.
Proof.
  split.
  - exact interval_bounded_above.
  - apply (bounded_above_ext in_interval_conj in_interval_alt).
    exact interval_predicates_equiv.
    exact interval_bounded_above.
Qed.

(** Using predicate equality (from derived extensionality),
    we can substitute freely in boundedness statements *)
Theorem boundedness_invariant :
  forall P Q : R -> Prop,
    P = Q -> bounded_above P -> bounded_above Q.
Proof.
  intros P Q Heq Hb. rewrite <- Heq. exact Hb.
Qed.

(** The full chain: derived extensionality → predicate equality →
    boundedness transfers between equivalent (0,1] definitions *)
Theorem interval_alt_bounded_via_extensionality :
  bounded_above in_interval_alt.
Proof.
  apply (boundedness_invariant in_interval_conj in_interval_alt).
  - exact interval_predicates_eq_derived.
  - exact interval_bounded_above.
Qed.
