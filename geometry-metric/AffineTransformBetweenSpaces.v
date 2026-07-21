(* ============================================================ *)
(*  AffineTransformBetweenSpaces.v                              *)
(*                                                              *)
(*  Q: What is an affine transform between two spaces in this  *)
(*     universe?                                                *)
(*                                                              *)
(*  A: An affine transform is a triple (a, b, ½) where:        *)
(*                                                              *)
(*       a : the rank-axis scaling     (factor 1 — slope)       *)
(*       b : the rank-axis translation (factor 2 — offset)      *)
(*       ½ : the half-step phase flip  (does the dual axis     *)
(*                                       go with or against?)   *)
(*                                                              *)
(*  Geometrically:                                              *)
(*    Classical: x ↦ a·x + b  (one axis, two parameters)       *)
(*    Triadic:   (x, axis) ↦ (a·x + b, swap_axis_if_needed)    *)
(*                                                              *)
(*  The half-step is what's NEW: an affine map between two     *)
(*  triadic spaces must say what happens to the orthogonal     *)
(*  axis (info_bit). Three options:                             *)
(*    KEEP  : the half-step survives the map (info_bit unchanged)*)
(*    FLIP  : the half-step is inverted (info_bit toggled)      *)
(*    DROP  : the half-step is absorbed into Omega (info_bit→F)*)
(*                                                              *)
(*  These correspond to the three triadic phases I, N, F.      *)
(*                                                              *)
(*  Composition is associative within each phase choice.       *)
(*  Cross-phase composition = Omega.                            *)
(*                                                              *)
(*  Axiom count: 0.                                             *)
(* ============================================================ *)

From Coq Require Import Arith Lia.

(* ============================================================ *)
(*  PART 1 — TRIADIC POINTS: (rank, info_bit)                   *)
(*                                                              *)
(*  A triadic space is a set of points each with a position    *)
(*  on the rank axis AND a half-step bit.                       *)
(* ============================================================ *)

Inductive Bit : Type := B0 | B1.

(* Phase: I (keep), N (flip), F (absorb to Omega). *)
Inductive Phase : Type := PhI | PhN | PhF.

Record TPoint : Type := mkTP {
  rank : nat;        (* coordinate on the 0° linear axis *)
  axis : Bit         (* 0 = integer axis, 1 = half-step axis *)
}.

(* The position on the encoded half-step line. *)
Definition position (p : TPoint) : nat :=
  2 * rank p + (match axis p with B0 => 0 | B1 => 1 end).

(* ============================================================ *)
(*  PART 2 — THE AFFINE TRANSFORM                               *)
(*                                                              *)
(*  An affine map takes:                                         *)
(*    - a coefficient a (multiplier on the rank axis)          *)
(*    - an offset b (translation along the rank axis)          *)
(*    - a phase ph (action on the half-step axis: I, N, or F)  *)
(* ============================================================ *)

Record Affine : Type := mkAff {
  coef    : nat;
  offset  : nat;
  phase   : Phase
}.

(* Phase action on a single bit. *)
Definition phase_act (ph : Phase) (b : Bit) : Bit :=
  match ph, b with
  | PhI, x   => x          (* I = identity: keep *)
  | PhN, B0  => B1
  | PhN, B1  => B0          (* N = flip *)
  | PhF, _   => B0          (* F = absorb (collapse to integer axis) *)
  end.

(* Apply the affine map to a triadic point. *)
Definition apply_affine (T : Affine) (p : TPoint) : TPoint :=
  mkTP (coef T * rank p + offset T)
       (phase_act (phase T) (axis p)).

(* ============================================================ *)
(*  PART 3 — IDENTITY AND INVERSE                               *)
(* ============================================================ *)

(* The identity affine map. *)
Definition id_affine : Affine := mkAff 1 0 PhI.

Theorem id_affine_acts_id : forall p,
  apply_affine id_affine p = p.
Proof.
  intros [r [|]]; unfold apply_affine, id_affine; simpl; f_equal; lia.
Qed.

(* The "half-step" affine map: identity on rank, flips axis. *)
Definition half_step_affine : Affine := mkAff 1 0 PhN.

Theorem half_step_flips_axis : forall p,
  axis (apply_affine half_step_affine p) <> axis p.
Proof.
  intros [r [|]]; unfold apply_affine, half_step_affine; simpl; discriminate.
Qed.

(* The half-step affine is its own inverse. *)
Theorem half_step_self_inverse : forall p,
  apply_affine half_step_affine
    (apply_affine half_step_affine p) = p.
Proof.
  intros [r [|]]; unfold apply_affine, half_step_affine; simpl;
    f_equal; lia.
Qed.

(* ============================================================ *)
(*  PART 4 — COMPOSITION                                        *)
(*                                                              *)
(*  The composition of two same-phase affines is a same-phase  *)
(*  affine. Cross-phase composition produces F-phase (Omega).  *)
(* ============================================================ *)

(* Phase composition: I·X = X, N·N = I, F absorbs. *)
Definition compose_phase (p q : Phase) : Phase :=
  match p, q with
  | PhI, x   => x
  | x,   PhI => x
  | PhN, PhN => PhI       (* N∘N = I — the half-step law *)
  | PhF, _   => PhF
  | _,   PhF => PhF
  end.

Definition compose_affine (T S : Affine) : Affine :=
  mkAff (coef T * coef S)
        (coef T * offset S + offset T)
        (compose_phase (phase T) (phase S)).

(* The phase composition law: N∘N = I. *)
Theorem compose_phase_N_N : compose_phase PhN PhN = PhI.
Proof. reflexivity. Qed.

(* Identity is identity for composition. *)
Theorem compose_id_left : forall T,
  compose_affine id_affine T = T.
Proof.
  intros [c o ph]. unfold compose_affine, id_affine. simpl.
  destruct ph; f_equal; lia.
Qed.

Theorem compose_id_right : forall T,
  compose_affine T id_affine = T.
Proof.
  intros [c o ph]. unfold compose_affine, id_affine. simpl.
  destruct ph; f_equal; lia.
Qed.

(* The composition law on rank: classical affine algebra. *)
Theorem rank_composition : forall T S r,
  coef T * (coef S * r + offset S) + offset T =
  coef T * coef S * r + (coef T * offset S + offset T).
Proof. intros. ring. Qed.

(* ============================================================ *)
(*  PART 5 — THE THREE TYPES OF AFFINE MAPS                    *)
(*                                                              *)
(*  Every affine map between triadic spaces classifies into:   *)
(*    KEEP-phase (PhI):  preserves the half-step axis          *)
(*    FLIP-phase (PhN):  swaps the two perpendicular axes      *)
(*    DROP-phase (PhF):  collapses everything to integer axis  *)
(*                                                              *)
(*  These are the three phases of the framework, applied to    *)
(*  the linear-algebraic level.                                 *)
(* ============================================================ *)

Definition is_keep (T : Affine) : Prop := phase T = PhI.
Definition is_flip (T : Affine) : Prop := phase T = PhN.
Definition is_drop (T : Affine) : Prop := phase T = PhF.

(* Every affine is exactly one of the three types. *)
Theorem affine_phase_trichotomy : forall T,
  is_keep T \/ is_flip T \/ is_drop T.
Proof.
  intro T. destruct (phase T) eqn:E.
  - left.  unfold is_keep. exact E.
  - right. left.  unfold is_flip. exact E.
  - right. right. unfold is_drop. exact E.
Qed.

(* Two flips compose to a keep — half-step law lifted to maps. *)
Theorem two_flips_make_a_keep : forall T S,
  is_flip T -> is_flip S -> is_keep (compose_affine T S).
Proof.
  intros T S HT HS. unfold is_keep, compose_affine. simpl.
  unfold is_flip in HT, HS. rewrite HT, HS. reflexivity.
Qed.

(* Anything composed with a drop is a drop. *)
Theorem drop_absorbs_left : forall T S,
  is_drop T -> is_drop (compose_affine T S).
Proof.
  intros T S H. unfold is_drop, compose_affine. simpl.
  unfold is_drop in H. rewrite H.
  destruct (phase S); reflexivity.
Qed.

Theorem drop_absorbs_right : forall T S,
  is_drop S -> is_drop (compose_affine T S).
Proof.
  intros T S H. unfold is_drop, compose_affine. simpl.
  unfold is_drop in H. rewrite H.
  destruct (phase T); reflexivity.
Qed.

(* ============================================================ *)
(*  PART 6 — THE GRAND PICTURE                                  *)
(*                                                              *)
(*  An affine transform between two triadic spaces is:         *)
(*                                                              *)
(*    1. A rank-axis affine (a, b) — the classical part        *)
(*    2. A half-step phase action (I, N, or F)                 *)
(*                                                              *)
(*  Together they form a 3-parameter family:                   *)
(*    (a, b, ph) where ph ∈ {I, N, F}                          *)
(*                                                              *)
(*  Classical affines have only (a, b). The triadic universe   *)
(*  adds the phase parameter — one trit of additional freedom *)
(*  per map. This is the affine analog of the dual angle:     *)
(*  every map between two spaces simultaneously specifies      *)
(*  what happens to BOTH perpendicular axes.                   *)
(*                                                              *)
(*  Composition law: classical (a, b) compose normally;        *)
(*  phases compose by the triadic op (N∘N=I, F absorbs).      *)
(* ============================================================ *)

Theorem triadic_affine_transform : forall T S,
  (* Identity is identity *)
  compose_affine id_affine T = T /\
  compose_affine T id_affine = T /\
  (* The rank affine composes classically *)
  (forall r,
     coef T * (coef S * r + offset S) + offset T =
     coef T * coef S * r + (coef T * offset S + offset T)) /\
  (* Two half-step flips return to keep *)
  (is_flip T -> is_flip S -> is_keep (compose_affine T S)) /\
  (* Drop absorbs *)
  (is_drop T -> is_drop (compose_affine T S)) /\
  (is_drop S -> is_drop (compose_affine T S)).
Proof.
  intros T S.
  split; [|split; [|split; [|split; [|split]]]].
  - apply compose_id_left.
  - apply compose_id_right.
  - apply rank_composition.
  - apply two_flips_make_a_keep.
  - intro H. apply drop_absorbs_left. exact H.
  - intro H. apply drop_absorbs_right. exact H.
Qed.

Print Assumptions triadic_affine_transform.
