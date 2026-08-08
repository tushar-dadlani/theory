(* ================================================================= *)
(*  CGoursatGeom.v  —  Milestone C, brick C2a-4b (geometry): the four   *)
(*  medial sub-triangles each have half the diameter, and their corner   *)
(*  vertices sit within half a diameter of the parent corner.  These are *)
(*  the shrinking facts driving the nested-triangle limit.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSegInt CGoursatML.
Open Scope R_scope.

Lemma Cmod_scal_half : forall z, Cmod (Cmul (RtoC (/ 2)) z) = / 2 * Cmod z.
Proof.
  intro z; rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq (/ 2)) by lra; reflexivity.
Qed.

Lemma Cmod_Cminus_sym : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof.
  intros a b; replace (Cminus a b) with (Copp (Cminus b a)) by ring; apply Cmod_opp.
Qed.

Lemma diam_e1 : forall v0 v1 v2, Cmod (Cminus v1 v0) <= diam v0 v1 v2.
Proof. intros; unfold diam; apply Rmax_l. Qed.
Lemma diam_e2 : forall v0 v1 v2, Cmod (Cminus v2 v1) <= diam v0 v1 v2.
Proof. intros; unfold diam; eapply Rle_trans; [ apply Rmax_l | apply Rmax_r ]. Qed.
Lemma diam_e3 : forall v0 v1 v2, Cmod (Cminus v0 v2) <= diam v0 v1 v2.
Proof. intros; unfold diam; eapply Rle_trans; [ apply Rmax_r | apply Rmax_r ]. Qed.

(* generic: an edge that is half of E, with |E| <= d, has length <= d/2 *)
Lemma edge_bound : forall X Y E d,
  Cminus X Y = Cmul (RtoC (/ 2)) E -> Cmod E <= d -> Cmod (Cminus X Y) <= / 2 * d.
Proof.
  intros X Y E d Heq HE; rewrite Heq, Cmod_scal_half.
  apply Rmult_le_compat_l; [ lra | exact HE ].
Qed.

Ltac mid_id := unfold mid, Cmul, RtoC, Cadd, Cminus; apply Ceq; cbn; field.

(* ---- the four sub-triangle diameters ---- *)
Lemma diam_sub0 : forall v0 v1 v2,
  diam v0 (mid v0 v1) (mid v2 v0) <= / 2 * diam v0 v1 v2.
Proof.
  intros v0 v1 v2; unfold diam at 1; apply Rmax_lub; [ | apply Rmax_lub ].
  - apply (edge_bound _ _ (Cminus v1 v0)); [ mid_id | apply diam_e1 ].
  - apply (edge_bound _ _ (Cminus v2 v1)); [ mid_id | apply diam_e2 ].
  - apply (edge_bound _ _ (Cminus v0 v2)); [ mid_id | apply diam_e3 ].
Qed.

Lemma diam_sub1 : forall v0 v1 v2,
  diam (mid v0 v1) v1 (mid v1 v2) <= / 2 * diam v0 v1 v2.
Proof.
  intros v0 v1 v2; unfold diam at 1; apply Rmax_lub; [ | apply Rmax_lub ].
  - apply (edge_bound _ _ (Cminus v1 v0)); [ mid_id | apply diam_e1 ].
  - apply (edge_bound _ _ (Cminus v2 v1)); [ mid_id | apply diam_e2 ].
  - apply (edge_bound _ _ (Cminus v0 v2)); [ mid_id | apply diam_e3 ].
Qed.

Lemma diam_sub2 : forall v0 v1 v2,
  diam (mid v2 v0) (mid v1 v2) v2 <= / 2 * diam v0 v1 v2.
Proof.
  intros v0 v1 v2; unfold diam at 1; apply Rmax_lub; [ | apply Rmax_lub ].
  - apply (edge_bound _ _ (Cminus v1 v0)); [ mid_id | apply diam_e1 ].
  - apply (edge_bound _ _ (Cminus v2 v1)); [ mid_id | apply diam_e2 ].
  - apply (edge_bound _ _ (Cminus v0 v2)); [ mid_id | apply diam_e3 ].
Qed.

Lemma diam_sub3 : forall v0 v1 v2,
  diam (mid v0 v1) (mid v1 v2) (mid v2 v0) <= / 2 * diam v0 v1 v2.
Proof.
  intros v0 v1 v2; unfold diam at 1; apply Rmax_lub; [ | apply Rmax_lub ].
  - apply (edge_bound _ _ (Cminus v2 v0));
      [ mid_id | rewrite Cmod_Cminus_sym; apply diam_e3 ].
  - apply (edge_bound _ _ (Cminus v0 v1));
      [ mid_id | rewrite Cmod_Cminus_sym; apply diam_e1 ].
  - apply (edge_bound _ _ (Cminus v1 v2));
      [ mid_id | rewrite Cmod_Cminus_sym; apply diam_e2 ].
Qed.

(* ---- corner-vertex moves ---- *)
Lemma vmove_m01 : forall v0 v1 v2,
  Cmod (Cminus (mid v0 v1) v0) <= / 2 * diam v0 v1 v2.
Proof.
  intros v0 v1 v2; apply (edge_bound _ _ (Cminus v1 v0)); [ mid_id | apply diam_e1 ].
Qed.

Lemma vmove_m20 : forall v0 v1 v2,
  Cmod (Cminus (mid v2 v0) v0) <= / 2 * diam v0 v1 v2.
Proof.
  intros v0 v1 v2; apply (edge_bound _ _ (Cminus v2 v0));
    [ mid_id | rewrite Cmod_Cminus_sym; apply diam_e3 ].
Qed.

Print Assumptions diam_sub3.

(* ================================================================= *)
(*  END CGoursatGeom.v  —  sub-triangle shrinking geometry (C2a-4b).    *)
(* ================================================================= *)
