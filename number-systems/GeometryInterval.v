(** * Geometry, the Vanishing Point, and the (0,1] Witness *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
From Stdlib Require Import ZArith.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Require Import IntervalEquiv.
Require Import LinAlgInterval.
Require Import RInterval.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: The Affine Line — (0,1] Without a Witness             *)
(* ================================================================= *)

(** In affine geometry, points are real numbers. The interval (0,1]
    is an affine set: it lives in R but is missing its left boundary.
    This is like parallel lines in Euclidean geometry — they approach
    but never meet. *)

(** The affine interval: (0,1] — open on the left *)
Definition affine_interval (x : R) : Prop :=
  0 < x /\ x <= 1.

(** The vanishing point candidate: 0 *)
Definition vanishing_point : R := 0.

(** THEOREM (Affine): The vanishing point is NOT in the affine interval.
    This is the affine "parallel postulate" — the boundary point
    that the interval approaches but never contains. *)
Theorem affine_no_witness :
  ~ affine_interval vanishing_point.
Proof.
  unfold affine_interval, vanishing_point. lra.
Qed.

(** Every approach toward the vanishing point stays inside (0,1]
    but never reaches it — like parallel lines converging toward
    a meeting point that doesn't exist in affine space *)
Theorem affine_approach : forall n : nat,
  (n >= 1)%nat -> affine_interval (/ INR n).
Proof.
  intros n Hn. unfold affine_interval.
  assert (Hn_pos : INR n > 0).
  { apply lt_0_INR. lia. }
  split.
  - apply Rinv_0_lt_compat. exact Hn_pos.
  - assert (H1 : 1 <= INR n).
    { replace 1 with (INR 1) by (simpl; lra).
      apply le_INR. lia. }
    rewrite <- Rinv_1.
    apply Rinv_le_contravar; lra.
Qed.

(** The sequence 1/n approaches the vanishing point *)
Theorem approach_vanishing : forall eps : R,
  eps > 0 -> exists n : nat, (n >= 1)%nat /\
    / INR n < eps /\ affine_interval (/ INR n).
Proof.
  intros eps Heps.
  destruct (archimed (/ eps)) as [Harch _].
  assert (Hup_pos : (0 < up (/ eps))%Z).
  { apply lt_IZR. apply Rlt_trans with (/ eps).
    - apply Rinv_0_lt_compat. exact Heps.
    - exact Harch. }
  set (n := Z.to_nat (up (/ eps))).
  assert (Hn_eq : INR n = IZR (up (/ eps))).
  { unfold n. rewrite INR_IZR_INZ.
    f_equal. rewrite Z2Nat.id; [reflexivity | lia]. }
  assert (Hn_ge : (n >= 1)%nat).
  { unfold n. lia. }
  assert (Hn_pos : INR n > 0) by (apply lt_0_INR; lia).
  exists n. split; [exact Hn_ge |]. split.
  - (* 1/n < eps because n > 1/eps *)
    assert (Hn_gt : INR n > / eps) by lra.
    assert (Hinv_n : / INR n < / (/ eps)).
    { apply Rinv_lt_contravar.
      - apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat |]; lra.
      - exact Hn_gt. }
    rewrite Rinv_inv in Hinv_n. exact Hinv_n.
  - apply affine_approach. exact Hn_ge.
Qed.

(* ================================================================= *)
(** ** Part 2: The Projective Line — Adding the Vanishing Point      *)
(* ================================================================= *)

(** The projective completion adds a "point at infinity" to the line.
    In our case, this means adding 0 to (0,1] to get [0,1].
    Euclid's parallel postulate breaks: the vanishing point now
    exists as a genuine element. *)

(** Points on the projective line: either a finite real or infinity *)
Inductive projective_point : Type :=
  | Finite : R -> projective_point
  | Infinity : projective_point.

(** The projective interval: [0,1] — closed on both sides *)
Definition projective_interval (x : R) : Prop :=
  0 <= x /\ x <= 1.

(** THEOREM (Projective): The vanishing point IS in the projective interval.
    The "parallel lines" now meet — the witness exists. *)
Theorem projective_witness_exists :
  projective_interval vanishing_point.
Proof.
  unfold projective_interval, vanishing_point. lra.
Qed.

(** The projective interval extends the affine interval *)
Theorem affine_subset_projective : forall x : R,
  affine_interval x -> projective_interval x.
Proof.
  intros x [Hlt Hle]. unfold projective_interval. lra.
Qed.

(** The projective interval adds exactly one point: the vanishing point *)
Theorem projective_extension : forall x : R,
  projective_interval x <-> (affine_interval x \/ x = vanishing_point).
Proof.
  intro x. unfold affine_interval, projective_interval, vanishing_point.
  split.
  - intros [Hle Hle1].
    destruct (Rlt_dec 0 x) as [Hlt | Hnlt].
    + left. split; assumption.
    + right. lra.
  - intros [H | H].
    + destruct H as [Hlt Hle]. lra.
    + rewrite H. lra.
Qed.

(* ================================================================= *)
(** ** Part 3: The Contradiction — Same Point, Two Truths            *)
(* ================================================================= *)

(** The fundamental contradiction between affine and projective:
    the vanishing point is simultaneously excluded and included,
    depending on which geometry you work in. *)

(** Statement 1 (Affine): 0 is not a member *)
Definition affine_excludes_zero : Prop :=
  ~ affine_interval vanishing_point.

(** Statement 2 (Projective): 0 is a member *)
Definition projective_includes_zero : Prop :=
  projective_interval vanishing_point.

(** Both statements are provable — in their respective systems *)
Theorem contradiction_both_hold :
  affine_excludes_zero /\ projective_includes_zero.
Proof.
  split.
  - exact affine_no_witness.
  - exact projective_witness_exists.
Qed.

(** This is not a logical contradiction! The predicates are different:
    affine_interval uses strict < , projective_interval uses <= .
    The "contradiction" is geometric: the same point (0) has different
    status depending on whether you work in affine or projective space. *)

(** Formally: the two predicates are NOT equal *)
Theorem affine_neq_projective :
  affine_interval <> projective_interval.
Proof.
  intro Heq.
  assert (H : affine_interval vanishing_point).
  { rewrite Heq. exact projective_witness_exists. }
  exact (affine_no_witness H).
Qed.

(** But they agree on all points EXCEPT the vanishing point *)
Theorem agree_except_vanishing : forall x : R,
  x <> vanishing_point ->
  (affine_interval x <-> projective_interval x).
Proof.
  intros x Hneq. unfold affine_interval, projective_interval, vanishing_point.
  split.
  - intros [Hlt Hle]. lra.
  - intros [Hle Hle1]. split; [|exact Hle1].
    destruct (Rlt_dec 0 x) as [Hlt | Hnlt].
    + exact Hlt.
    + exfalso. apply Hnlt. destruct Hle as [Hlt' | Heq'].
      * exact Hlt'.
      * exfalso. apply Hneq. unfold vanishing_point. lra.
Qed.

(* ================================================================= *)
(** ** Part 4: The Vanishing Point as Geometric Witness              *)
(* ================================================================= *)

(** In LinAlgInterval.v we proved:
    - sup_attained: 1 is in (0,1] — the upper bound has a witness
    - inf_not_attained: 0 is NOT in (0,1] — the lower bound has no witness

    The projective completion resolves the missing witness: *)

(** The projective interval has BOTH witnesses *)
Theorem projective_sup_attained : projective_interval 1.
Proof. unfold projective_interval. lra. Qed.

Theorem projective_inf_attained : projective_interval 0.
Proof. unfold projective_interval. lra. Qed.

(** The affine interval is missing exactly one witness *)
Theorem affine_one_witness_missing :
  affine_interval 1 /\ ~ affine_interval 0.
Proof.
  split.
  - unfold affine_interval. lra.
  - exact affine_no_witness.
Qed.

(** The projective completion "heals" the asymmetry *)
Theorem projective_symmetric_witnesses :
  projective_interval 0 /\ projective_interval 1.
Proof.
  split; unfold projective_interval; lra.
Qed.

(* ================================================================= *)
(** ** Part 5: Projective Completeness — The Sup/Inf Are Both In     *)
(* ================================================================= *)

(** The projective interval is complete in a stronger sense:
    both the sup AND inf are members *)

Theorem projective_lub : is_lub projective_interval 1.
Proof.
  split.
  - intros x [_ Hle]. exact Hle.
  - intros b Hb. apply Hb. unfold projective_interval. lra.
Qed.

(** The greatest lower bound of [0,1] is 0, and it IS attained *)
Theorem projective_glb :
  (forall x, projective_interval x -> 0 <= x) /\
  (forall lb, (forall x, projective_interval x -> lb <= x) -> lb <= 0) /\
  projective_interval 0.
Proof.
  split; [| split].
  - intros x [Hle _]. exact Hle.
  - intros lb Hlb. apply Hlb. unfold projective_interval. lra.
  - exact projective_inf_attained.
Qed.

(* ================================================================= *)
(** ** Part 6: Predicate Algebra — Affine vs Projective              *)
(* ================================================================= *)

(** The projective interval is the predicate-algebraic CLOSURE of
    the affine interval: it is the smallest closed predicate
    containing the affine interval plus the vanishing point *)

Definition pred_add_point (P : R -> Prop) (p : R) : R -> Prop :=
  fun x => P x \/ x = p.

(** Adding the vanishing point to (0,1] gives [0,1] *)
Theorem closure_is_projective :
  pred_add_point affine_interval vanishing_point = projective_interval.
Proof.
  apply r_pred_extensionality.
  intro x. unfold pred_add_point.
  symmetry. exact (projective_extension x).
Qed.

(** The vanishing point is the UNIQUE point that distinguishes
    the affine from the projective interval *)
Theorem unique_vanishing_point : forall p : R,
  pred_add_point affine_interval p = projective_interval ->
  p = vanishing_point.
Proof.
  intros p Heq.
  assert (H : projective_interval p).
  { rewrite <- Heq. unfold pred_add_point. right. reflexivity. }
  assert (H2 : pred_add_point affine_interval p p) by
    (unfold pred_add_point; right; reflexivity).
  rewrite Heq in H2.
  (* p must be in [0,1] but not in (0,1] *)
  destruct (Rlt_dec 0 p) as [Hlt | Hnlt].
  - (* If 0 < p, then p is in (0,1] already *)
    assert (Haffine : affine_interval p).
    { unfold affine_interval. destruct H as [H0 H1]. lra. }
    (* Adding p doesn't change anything — but it must change
       the predicate to include 0, which means p = 0 *)
    exfalso.
    assert (Hno0 : ~ pred_add_point affine_interval p vanishing_point ->
                    ~ projective_interval vanishing_point).
    { rewrite Heq. auto. }
    apply Hno0.
    + unfold pred_add_point, vanishing_point.
      intros [Haff | Hp0].
      * exact (affine_no_witness Haff).
      * lra.
    + exact projective_witness_exists.
  - unfold vanishing_point. destruct H as [H0 H1]. lra.
Qed.

(* ================================================================= *)
(** ** Part 7: The Grand Analogy — Parallel Lines and (0,1]          *)
(* ================================================================= *)

(** We model "parallel lines" as sequences that approach the
    vanishing point but never reach it — exactly like the
    sequence 1/n approaches 0 in (0,1] *)

(** A "parallel family" is a sequence of points in (0,1] that
    converges toward the vanishing point *)
Definition parallel_family (f : nat -> R) : Prop :=
  (forall n, (n >= 1)%nat -> affine_interval (f n)) /\
  (forall eps, eps > 0 -> exists N, forall n, (n >= N)%nat -> f n < eps).

(** The canonical parallel family: 1/n *)
Theorem inv_nat_parallel : parallel_family (fun n => / INR n).
Proof.
  split.
  - intros n Hn. exact (affine_approach n Hn).
  - intros eps Heps.
    destruct (approach_vanishing eps Heps) as [n [Hn [Hlt _]]].
    exists n. intros m Hm.
    assert (Hm_pos : INR m > 0) by (apply lt_0_INR; lia).
    assert (Hn_le_m : INR n <= INR m) by (apply le_INR; lia).
    apply Rle_lt_trans with (/ INR n); [| exact Hlt].
    assert (Hn_pos2 : INR n > 0) by (apply lt_0_INR; lia).
    apply Rinv_le_contravar; lra.
Qed.

(** In affine geometry: the parallel family has no limit point in (0,1] *)
Theorem affine_parallels_dont_meet :
  forall f, parallel_family f ->
    ~ exists p, affine_interval p /\
      (forall eps, eps > 0 -> exists N, forall n, (n >= N)%nat ->
        Rabs (f n - p) < eps).
Proof.
  intros f [Hin Hconv] [p [[Hp_pos Hp_le] Hlim]].
  (* p > 0, but the sequence converges below any eps,
     so it can't stay near p > 0 *)
  destruct (Hlim (p / 2) ltac:(lra)) as [N1 HN1].
  destruct (Hconv (p / 2) ltac:(lra)) as [N2 HN2].
  set (N := Nat.max N1 (Nat.max N2 1)).
  assert (HN_ge1 : (N >= 1)%nat) by (unfold N; lia).
  assert (HN_ge_N1 : (N >= N1)%nat) by (unfold N; lia).
  assert (HN_ge_N2 : (N >= N2)%nat) by (unfold N; lia).
  assert (H1 : Rabs (f N - p) < p / 2) by (apply HN1; lia).
  assert (H2 : f N < p / 2) by (apply HN2; lia).
  assert (H3 : affine_interval (f N)) by (apply Hin; lia).
  destruct H3 as [Hfn_pos _].
  apply Rabs_def2 in H1. lra.
Qed.

(** In projective geometry: the parallel family DOES have a limit
    point — the vanishing point 0, which is now in [0,1] *)
Theorem projective_parallels_meet :
  forall f, parallel_family f ->
    exists p, projective_interval p /\
      (forall eps, eps > 0 -> exists N, forall n, (n >= N)%nat ->
        Rabs (f n - p) < eps).
Proof.
  intros f [Hin Hconv].
  exists vanishing_point. split.
  - exact projective_witness_exists.
  - intros eps Heps.
    destruct (Hconv eps Heps) as [N HN].
    exists (Nat.max N 1). intros n Hn.
    unfold vanishing_point. rewrite Rminus_0_r.
    rewrite Rabs_right.
    + apply HN. lia.
    + left. destruct (Hin n ltac:(lia)) as [Hpos _]. exact Hpos.
Qed.
