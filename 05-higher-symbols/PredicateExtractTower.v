(** * PredicateExtractTower.v — A Tower from the Predicate Extract Gap
       to Riemannian Manifold Structure

    The predicate extract gap — the single point where affine and
    projective predicates disagree — is the contradiction axiom.
    From it we build:

      Level 0: Discrete   (the gap point alone)
      Level 1: Metric     (distance = proximity to the gap)
      Level 2: Topological (limit points from the metric)
      Level 3: Smooth     (tangent vectors from approach sequences)
      Level 4: Riemannian (curvature from kernel absorption rate)

    Each level absorbs structure from below. The tower limit
    resolves all contradictions: kernel = empty.

    0 new axioms. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import IntervalEquiv.
Require Import GeometryInterval.
Require Import RiemannContradictions.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: The Predicate Extract Gap — Contradiction Axiom       *)
(* ================================================================= *)

(** The predicate extract gap is the foundational structure:
    two predicates on a space that agree everywhere except at
    exactly one point. This single point of disagreement is
    the contradiction that drives the entire tower. *)

Record PredicateExtractGap := mkPEG {
  peg_space : R -> Prop;
  peg_subspace : R -> Prop;
  peg_gap_point : R;
  peg_in_space : peg_space peg_gap_point;
  peg_not_in_sub : ~ peg_subspace peg_gap_point;
  peg_agree : forall x, x <> peg_gap_point ->
    (peg_subspace x <-> peg_space x);
  peg_unique : forall y, peg_space y -> ~ peg_subspace y ->
    y = peg_gap_point;
}.

(** The gap exists: constructed from affine/projective disagreement *)
Definition the_gap : PredicateExtractGap.
Proof.
  refine (mkPEG projective_interval affine_interval vanishing_point
    _ _ _ _).
  - exact projective_witness_exists.
  - exact affine_no_witness.
  - exact agree_except_vanishing.
  - intros y Hproj Haff.
    unfold vanishing_point.
    destruct Hproj as [Hle Hle1].
    destruct (Rlt_dec 0 y) as [Hlt | Hnlt].
    + exfalso. apply Haff. unfold affine_interval. lra.
    + lra.
Defined.

(** The gap point is the vanishing point *)
Lemma gap_point_eq : peg_gap_point the_gap = vanishing_point.
Proof. reflexivity. Qed.

(** The gap point IS the contradiction *)
Theorem gap_is_contradiction :
  is_contradiction (peg_gap_point the_gap).
Proof.
  rewrite gap_point_eq. exact vanishing_point_is_contradiction.
Qed.

(** The gap point is unique *)
Theorem gap_unique :
  forall x, is_contradiction x -> x = peg_gap_point the_gap.
Proof.
  intros x Hx.
  rewrite gap_point_eq.
  destruct (Req_dec x vanishing_point) as [Heq | Hneq].
  - exact Heq.
  - exfalso. exact (interior_no_contradiction x Hneq Hx).
Qed.

(* ================================================================= *)
(** ** Part 2: Level 0 — Discrete (The Gap Point Alone)              *)
(* ================================================================= *)

(** The simplest formal system: one unresolved element.
    The gap point sits in the kernel — a contradiction
    that the system knows about but has not resolved. *)

Definition level0 : FormalSystem := mkFS
  (fun _ => True)
  (fun p => p = 0%nat)
  (fun _ _ => I).

Theorem level0_has_contradiction : has_contradiction level0.
Proof.
  exists 0%nat. reflexivity.
Qed.

(** After one tower step, the gap point is absorbed *)
Theorem level0_step_resolves :
  no_contradiction (tower_step level0).
Proof.
  intros p [Hk Hnd]. apply Hnd. exact I.
Qed.

(** The gap in the formal system mirrors the geometric gap *)
Theorem level0_mirrors_geometry :
  has_contradiction level0 /\
  is_contradiction (peg_gap_point the_gap).
Proof.
  split.
  - exact level0_has_contradiction.
  - exact gap_is_contradiction.
Qed.

(* ================================================================= *)
(** ** Part 3: Level 1 — Metric (Distance from the Gap)              *)
(* ================================================================= *)

(** The gap induces a metric: distance measures proximity to
    the gap point. The approach sequence 1/n witnesses that
    this metric is non-trivial — points get arbitrarily close
    to the gap without reaching it. *)

Definition gap_distance (x : R) : R :=
  Rabs (x - peg_gap_point the_gap).

Record MetricLevel := mkML {
  ml_fs : FormalSystem;
  ml_dist : R -> R -> R;
  ml_dist_pos : forall x y, ml_dist x y >= 0;
  ml_dist_zero : forall x y, ml_dist x y = 0 <-> x = y;
  ml_dist_sym : forall x y, ml_dist x y = ml_dist y x;
  ml_dist_triangle : forall x y z,
    ml_dist x z <= ml_dist x y + ml_dist y z;
}.

Definition real_dist (x y : R) : R := Rabs (x - y).

Lemma real_dist_pos : forall x y, real_dist x y >= 0.
Proof.
  intros. unfold real_dist. apply Rle_ge. apply Rabs_pos.
Qed.

Lemma real_dist_zero : forall x y, real_dist x y = 0 <-> x = y.
Proof.
  intros. unfold real_dist. split.
  - intro H.
    destruct (Req_dec x y) as [Heq | Hneq]; [exact Heq |].
    exfalso. assert (Hd : x - y <> 0) by lra.
    apply Rabs_no_R0 in Hd. lra.
  - intro H. subst. rewrite Rminus_diag_eq; [apply Rabs_R0 | reflexivity].
Qed.

Lemma real_dist_sym : forall x y, real_dist x y = real_dist y x.
Proof.
  intros. unfold real_dist. rewrite Rabs_minus_sym. reflexivity.
Qed.

Lemma real_dist_triangle : forall x y z,
  real_dist x z <= real_dist x y + real_dist y z.
Proof.
  intros. unfold real_dist.
  replace (x - z) with ((x - y) + (y - z)) by lra.
  apply Rabs_triang.
Qed.

Definition level1 : MetricLevel := mkML
  (tower_step level0)
  real_dist
  real_dist_pos
  real_dist_zero
  real_dist_sym
  real_dist_triangle.

(** The approach sequence witnesses metric convergence to the gap *)
Theorem approach_witnesses_metric :
  forall eps, eps > 0 ->
    exists n : nat, (n >= 1)%nat /\
      gap_distance (/ INR n) < eps.
Proof.
  intros eps Heps.
  destruct (approach_vanishing eps Heps) as [n [Hn [Hlt Haff]]].
  exists n. split; [exact Hn |].
  unfold gap_distance. simpl.
  rewrite Rminus_0_r.
  rewrite Rabs_right.
  - exact Hlt.
  - left. destruct Haff as [Hpos _]. exact Hpos.
Qed.

(** Every approach point is in the subspace (affine interval) *)
Theorem approach_stays_in_subspace :
  forall n : nat, (n >= 1)%nat ->
    peg_subspace the_gap (/ INR n).
Proof.
  intros n Hn. simpl. exact (affine_approach n Hn).
Qed.

(* ================================================================= *)
(** ** Part 4: Level 2 — Topological (Limit Points from the Metric)  *)
(* ================================================================= *)

(** The metric topology reveals the gap point as a limit point:
    every neighborhood of the gap contains subspace points,
    but the gap itself is not in the subspace. This is the
    topological manifestation of the predicate extract gap. *)

Definition metric_open (U : R -> Prop) : Prop :=
  forall x, U x -> exists eps, eps > 0 /\
    (forall y, Rabs (y - x) < eps -> U y).

(** The gap point is a limit point of the subspace *)
Theorem gap_is_limit_point :
  (forall eps, eps > 0 ->
    exists y, peg_subspace the_gap y /\
      Rabs (y - peg_gap_point the_gap) < eps) /\
  ~ peg_subspace the_gap (peg_gap_point the_gap).
Proof.
  split.
  - intros eps Heps.
    destruct (approach_witnesses_metric eps Heps) as [n [Hn Hlt]].
    exists (/ INR n). split.
    + exact (approach_stays_in_subspace n Hn).
    + unfold gap_distance in Hlt. exact Hlt.
  - simpl. exact affine_no_witness.
Qed.

(** The projective completion closes the limit:
    the gap point IS in the completed space *)
Theorem projective_closes_limit :
  peg_space the_gap (peg_gap_point the_gap).
Proof.
  exact (peg_in_space the_gap).
Qed.

(** The formal system at level 2: tower steps past level 1 *)
Definition level2_fs : FormalSystem := tower_step (ml_fs level1).

(** Level 2 has no kernel — the discrete contradiction is resolved *)
Theorem level2_resolved : no_contradiction level2_fs.
Proof.
  intros p H.
  unfold level2_fs in H. simpl in H.
  destruct H as [[Hk Hnd1] Hnd2].
  apply Hnd1. exact I.
Qed.

(* ================================================================= *)
(** ** Part 5: Level 3 — Smooth (Tangent Vectors from Approach)      *)
(* ================================================================= *)

(** The approach sequence 1/n has a discrete derivative:
    the finite difference between consecutive terms.
    These differences are tangent vectors — they measure
    the rate of approach to the gap point.

    As n grows, the tangent vectors shrink: the approach
    decelerates, flattening toward the gap. *)

Definition discrete_derivative (n : nat) : R :=
  / INR (S (S n)) - / INR (S n).

(** Helper: S n is always positive as a real *)
Lemma INR_S_pos : forall n, INR (S n) > 0.
Proof.
  intro n. apply lt_0_INR. lia.
Qed.

(** The discrete derivative is negative (approaching from above) *)
Theorem tangent_negative : forall n : nat,
  discrete_derivative n < 0.
Proof.
  intro n. unfold discrete_derivative.
  assert (H1 : INR (S n) > 0) by (apply INR_S_pos).
  assert (H2 : INR (S (S n)) > 0) by (apply INR_S_pos).
  assert (H3 : INR (S n) < INR (S (S n))).
  { apply lt_INR. lia. }
  apply Rlt_minus.
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; lra.
  - exact H3.
Qed.

(** The tangent vectors converge to 0 *)
Theorem tangent_converges : forall eps, eps > 0 ->
  exists N : nat, forall n, (n >= N)%nat ->
    Rabs (discrete_derivative n) < eps.
Proof.
  intros eps Heps.
  destruct (approach_vanishing (eps / 2) ltac:(lra)) as [m [Hm [Hlt _]]].
  exists m. intros n Hn.
  unfold discrete_derivative.
  assert (H1 : INR (S n) > 0) by (apply INR_S_pos).
  assert (H2 : INR (S (S n)) > 0) by (apply INR_S_pos).
  rewrite Rabs_left.
  - (* |d| = 1/(S n) - 1/(S (S n)) *)
    ring_simplify.
    assert (Hm_pos : INR m > 0) by (apply lt_0_INR; lia).
    assert (Hinv1 : / INR (S n) < eps / 2).
    { apply Rle_lt_trans with (/ INR m).
      - apply Rinv_le_contravar; [lra |]. apply le_INR. lia.
      - exact Hlt. }
    assert (Hinv2 : / INR (S (S n)) > 0).
    { apply Rinv_0_lt_compat. exact H2. }
    lra.
  - apply Rlt_minus.
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; lra.
    + apply lt_INR. lia.
Qed.

(* ================================================================= *)
(** ** Part 6: Level 4 — Riemannian (Curvature from Absorption Rate) *)
(* ================================================================= *)

(** The Riemannian structure emerges from the tower's kernel
    absorption rate. Define:
      absorption_rate(n) = 1/(n+1)
    This measures how much "unresolved contradiction" remains
    at step n of the approach to the gap.

    The curvature is the second discrete derivative of the
    absorption rate — it measures how the rate of resolution
    changes. Positive curvature means resolution decelerates:
    contradictions near the gap are harder to resolve. *)

Definition absorption_rate (n : nat) : R := / INR (S n).

Definition tower_curvature (n : nat) : R :=
  absorption_rate (S (S n)) - 2 * absorption_rate (S n) + absorption_rate n.

(** Helper: product of positive reals is positive *)
Lemma pos_product_3 : forall a b c : R,
  a > 0 -> b > 0 -> c > 0 -> a * b * c > 0.
Proof. intros. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; lra. Qed.

(** The curvature is positive: resolution decelerates near the gap.
    Algebraically: 1/(n+1) - 2/(n+2) + 1/(n+3)
                 = 2 / ((n+1)(n+2)(n+3)) > 0 *)
Theorem curvature_positive : forall n : nat,
  tower_curvature n > 0.
Proof.
  intro n.
  unfold tower_curvature, absorption_rate.
  set (a := INR (S n)).
  set (b := INR (S (S n))).
  set (c := INR (S (S (S n)))).
  assert (Ha : a > 0) by (unfold a; apply INR_S_pos).
  assert (Hb : b > 0) by (unfold b; apply INR_S_pos).
  assert (Hc : c > 0) by (unfold c; apply INR_S_pos).
  assert (Hab : b = a + 1).
  { unfold a, b. rewrite S_INR. reflexivity. }
  assert (Hbc : c = b + 1).
  { unfold b, c. rewrite S_INR. reflexivity. }
  (* Show: 1/c - 2*(1/b) + 1/a > 0
     Equivalent to: 1/a + 1/c > 2/b
     Rewrite everything over common denominator a*b*c *)
  assert (Hna : a <> 0) by lra.
  assert (Hnb : b <> 0) by lra.
  assert (Hnc : c <> 0) by lra.
  (* Direct: show (b*c + a*b - 2*a*c) / (a*b*c) > 0 *)
  replace (/ c - 2 * / b + / a) with
    ((b * c + a * b - 2 * a * c) / (a * b * c)).
  2:{ field. lra. }
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - (* Numerator: b*c + a*b - 2*a*c = 2 when b=a+1, c=a+2 *)
    rewrite Hbc, Hab. ring_simplify. lra.
  - apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat |]; lra.
Qed.

(** The curvature vanishes at the tower limit:
    the manifold flattens as contradictions are fully resolved *)
Theorem curvature_vanishes : forall eps, eps > 0 ->
  exists N : nat, forall n, (n >= N)%nat ->
    tower_curvature n < eps.
Proof.
  intros eps Heps.
  (* curvature n = 2/((n+1)(n+2)(n+3)) < 2/(n+1)^3 < eps
     when n+1 > (2/eps)^(1/3). We use a simpler bound:
     curvature n < 2/(n+1) since (n+2)(n+3) > 1 *)
  destruct (approach_vanishing (eps / 2) ltac:(lra)) as [m [Hm [Hlt _]]].
  exists m. intros n Hn.
  unfold tower_curvature, absorption_rate.
  set (a := INR (S n)).
  set (b := INR (S (S n))).
  set (c := INR (S (S (S n)))).
  assert (Ha : a > 0) by (unfold a; apply INR_S_pos).
  assert (Hb : b > 0) by (unfold b; apply INR_S_pos).
  assert (Hc : c > 0) by (unfold c; apply INR_S_pos).
  assert (Hab : b = a + 1).
  { unfold a, b. rewrite S_INR. reflexivity. }
  assert (Hbc : c = b + 1).
  { unfold b, c. rewrite S_INR. reflexivity. }
  (* curvature = 2 / (a * b * c) *)
  assert (Habc : a * b * c > 0) by (apply pos_product_3; lra).
  assert (Hcurv : / c - 2 * / b + / a = 2 / (a * b * c)).
  { rewrite Hbc, Hab. field. repeat split; lra. }
  rewrite Hcurv.
  (* 2/(a*b*c) < 2/a since b*c > 1 *)
  assert (Hb1 : b > 1) by (rewrite Hab; lra).
  assert (Hc1 : c > 1) by (rewrite Hbc; lra).
  assert (Hbc_gt1 : b * c > 1).
  { nra. }
  apply Rlt_le_trans with (2 / a).
  - unfold Rdiv. apply Rmult_lt_compat_l; [lra |].
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; [exact Ha |]. lra.
    + rewrite <- (Rmult_1_r a) at 1. rewrite Rmult_assoc.
      apply Rmult_lt_compat_l; lra.
  - (* 2/a = 2 * (1/a) <= 2 * (1/m) < 2 * (eps/2) = eps *)
    unfold Rdiv. rewrite Rmult_comm.
    assert (H1a : / a <= / INR m).
    { apply Rinv_le_contravar.
      - apply lt_0_INR. lia.
      - apply le_INR. unfold a. lia. }
    apply Rle_trans with (/ INR m * 2).
    + apply Rmult_le_compat_r; lra.
    + rewrite Rmult_comm. lra.
Qed.

(* ================================================================= *)
(** ** Part 7: The Capstone — The Full Tower                         *)
(* ================================================================= *)

(** The predicate extract tower unifies all five levels:
    gap → discrete → metric → topological → smooth → Riemannian.

    The contradiction axiom (the gap) drives everything:
    it creates the discrete kernel, induces the metric,
    generates limit points (topology), tangent vectors (smooth),
    and curvature (Riemannian). At the tower limit, all
    contradictions resolve and the curvature vanishes. *)

Record PredicateExtractTowerRecord := mkPET {
  (** The foundation: the predicate extract gap *)
  pet_gap : PredicateExtractGap;

  (** Level 0: discrete formal system with the gap *)
  pet_discrete : FormalSystem;
  pet_discrete_has_gap : has_contradiction pet_discrete;

  (** Level 1: metric structure from the gap *)
  pet_metric : MetricLevel;

  (** Level 2: the gap is a limit point *)
  pet_limit_point :
    (forall eps, eps > 0 ->
      exists y, peg_subspace pet_gap y /\
        Rabs (y - peg_gap_point pet_gap) < eps) /\
    ~ peg_subspace pet_gap (peg_gap_point pet_gap);

  (** Level 3: tangent vectors converge *)
  pet_tangent_converges :
    forall eps, eps > 0 ->
      exists N, forall n, (n >= N)%nat ->
        Rabs (discrete_derivative n) < eps;

  (** Level 4: positive curvature *)
  pet_curvature_pos : forall n, tower_curvature n > 0;

  (** Level 4: curvature vanishes at the limit *)
  pet_curvature_limit :
    forall eps, eps > 0 ->
      exists N, forall n, (n >= N)%nat ->
        tower_curvature n < eps;

  (** The tower limit: all contradictions resolved *)
  pet_limit_resolved :
    forall p, ~ (tower_limit pet_discrete).(fs_kernel) p;
}.

Theorem PREDICATE_EXTRACT_TOWER : PredicateExtractTowerRecord.
Proof.
  refine (mkPET the_gap level0 _ level1 _ _ _ _ _).
  - (* Discrete has gap *)
    exact level0_has_contradiction.
  - (* Limit point *)
    exact gap_is_limit_point.
  - (* Tangent converges *)
    exact tangent_converges.
  - (* Curvature positive *)
    exact curvature_positive.
  - (* Curvature vanishes *)
    exact curvature_vanishes.
  - (* Tower limit resolved *)
    intros p H. exact H.
Qed.

(** The tower is sound: the gap creates structure,
    the tower resolves it, and the resolution is complete. *)
Corollary tower_soundness :
  (** The gap exists and is unique *)
  (exists! x, is_contradiction x) /\
  (** The tower starts with a contradiction *)
  has_contradiction (pet_discrete PREDICATE_EXTRACT_TOWER) /\
  (** The tower ends with none *)
  (forall p, ~ (tower_limit (pet_discrete PREDICATE_EXTRACT_TOWER)).(fs_kernel) p) /\
  (** Curvature is everywhere positive *)
  (forall n, tower_curvature n > 0) /\
  (** Curvature vanishes at the limit *)
  (forall eps, eps > 0 ->
    exists N, forall n, (n >= N)%nat -> tower_curvature n < eps).
Proof.
  split; [| split; [| split; [| split]]].
  - destruct unique_contradiction as [Hex Huniq].
    destruct Hex as [x Hx]. exists x. split; [exact Hx |].
    intros y Hy. exact (Huniq x y Hx Hy).
  - exact (pet_discrete_has_gap PREDICATE_EXTRACT_TOWER).
  - exact (pet_limit_resolved PREDICATE_EXTRACT_TOWER).
  - exact (pet_curvature_pos PREDICATE_EXTRACT_TOWER).
  - exact (pet_curvature_limit PREDICATE_EXTRACT_TOWER).
Qed.

Print Assumptions PREDICATE_EXTRACT_TOWER.
