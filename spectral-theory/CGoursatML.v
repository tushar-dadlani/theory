(* ================================================================= *)
(*  CGoursatML.v  —  Milestone C, brick C2a-3c: perimeter, diameter,    *)
(*  and the triangle ML (length × sup) estimate.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral CSegInt CTriangle.
Open Scope R_scope.

Definition perim (v0 v1 v2 : C) : R :=
  Cmod (Cminus v1 v0) + Cmod (Cminus v2 v1) + Cmod (Cminus v0 v2).

Definition diam (v0 v1 v2 : C) : R :=
  Rmax (Cmod (Cminus v1 v0)) (Rmax (Cmod (Cminus v2 v1)) (Cmod (Cminus v0 v2))).

Lemma perim_nonneg : forall v0 v1 v2, 0 <= perim v0 v1 v2.
Proof.
  intros; unfold perim; pose proof (Cmod_nonneg (Cminus v1 v0));
    pose proof (Cmod_nonneg (Cminus v2 v1)); pose proof (Cmod_nonneg (Cminus v0 v2)); lra.
Qed.

(* ---- ML for one segment ---- *)
Lemma seg_int_ML : forall f (Hf : CcontC f) a b M,
  (forall s, 0 <= s <= 1 -> Cmod (f (seg a b s)) <= M) ->
  Cmod (seg_int f Hf a b) <= 2 * M * Cmod (Cminus b a).
Proof.
  intros f Hf a b M HM; unfold seg_int.
  apply Rle_trans with (2 * (M * Cmod (Cminus b a)) * (1 - 0)).
  - apply Cintf_ML; [ lra | intros u Hu; rewrite Cmod_mul; unfold seg';
      apply Rmult_le_compat_r; [ apply Cmod_nonneg | apply HM; exact Hu ] ].
  - apply Req_le; ring.
Qed.

(* ---- ML for the triangle boundary ---- *)
Lemma tri_int_ML : forall f (Hf : CcontC f) v0 v1 v2 M,
  (forall s, 0 <= s <= 1 -> Cmod (f (seg v0 v1 s)) <= M) ->
  (forall s, 0 <= s <= 1 -> Cmod (f (seg v1 v2 s)) <= M) ->
  (forall s, 0 <= s <= 1 -> Cmod (f (seg v2 v0 s)) <= M) ->
  Cmod (tri_int f Hf v0 v1 v2) <= 2 * M * perim v0 v1 v2.
Proof.
  intros f Hf v0 v1 v2 M H01 H12 H20; unfold tri_int, perim.
  apply Rle_trans with (2 * M * Cmod (Cminus v1 v0)
    + (2 * M * Cmod (Cminus v2 v1) + 2 * M * Cmod (Cminus v0 v2))).
  - eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat; [ apply seg_int_ML; exact H01 | ].
    eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat; [ apply seg_int_ML; exact H12 | apply seg_int_ML; exact H20 ].
  - apply Req_le; ring.
Qed.

Print Assumptions tri_int_ML.

(* ================================================================= *)
(*  END CGoursatML.v  —  perimeter/diameter + triangle ML (C2a-3c).     *)
(* ================================================================= *)
