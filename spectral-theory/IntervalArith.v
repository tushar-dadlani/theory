(* ================================================================= *)
(*  IntervalArith.v  —  Stage 3, brick 1: computable rational intervals. *)
(*                                                                    *)
(*  The foundation of the verified-quadrature subsystem (Stage 3-4 of   *)
(*  exhibiting the first zeta zero).  A rigorous interval is a pair of   *)
(*  rationals (Q) enclosing a real:                                     *)
(*                                                                    *)
(*    Icontains i x := Q2R (ilo i) <= x <= Q2R (ihi i).                 *)
(*                                                                    *)
(*  Sound, COMPUTABLE (vm_compute-able) arithmetic: Iconst, Iadd, Ineg, *)
(*  Isub, Imul.  Everything is over Q so hundreds of panel evaluations  *)
(*  reduce by vm_compute; soundness bridges each Q op to its R op via   *)
(*  the Q2R ring homomorphism (Qreals).  Interval multiplication uses   *)
(*  the min/max of the four corner products (the standard robust rule). *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (Q is constructive).         *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra.
Local Open Scope R_scope.

Record Itv := mkI { ilo : Q ; ihi : Q }.

Definition Icontains (i : Itv) (x : R) : Prop :=
  Q2R (ilo i) <= x <= Q2R (ihi i).

(* ---- computable min/max on Q, matched to Rmin/Rmax through Q2R ---- *)
Definition Qmin2 (a b : Q) : Q := if Qle_bool a b then a else b.
Definition Qmax2 (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma Qle_bool_false : forall a b, Qle_bool a b = false -> (b <= a)%Q.
Proof.
  intros a b E. apply Qlt_le_weak. apply Qnot_le_lt. intro Hc.
  apply Qle_bool_iff in Hc. rewrite E in Hc. discriminate.
Qed.

Lemma Q2R_Qmin2 : forall a b, Q2R (Qmin2 a b) = Rmin (Q2R a) (Q2R b).
Proof.
  intros a b. unfold Qmin2. destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff in E. rewrite Rmin_left; [ reflexivity | apply Qle_Rle; exact E ].
  - apply Qle_bool_false in E. rewrite Rmin_right; [ reflexivity | apply Qle_Rle; exact E ].
Qed.

Lemma Q2R_Qmax2 : forall a b, Q2R (Qmax2 a b) = Rmax (Q2R a) (Q2R b).
Proof.
  intros a b. unfold Qmax2. destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff in E. rewrite Rmax_right; [ reflexivity | apply Qle_Rle; exact E ].
  - apply Qle_bool_false in E. rewrite Rmax_left; [ reflexivity | apply Qle_Rle; exact E ].
Qed.

(* ---- constant, add, neg, sub ---- *)
Definition Iconst (q : Q) : Itv := mkI q q.
Definition Iadd (i j : Itv) : Itv := mkI (ilo i + ilo j) (ihi i + ihi j).
Definition Ineg (i : Itv) : Itv := mkI (- ihi i) (- ilo i).
Definition Isub (i j : Itv) : Itv := Iadd i (Ineg j).

Lemma Iconst_sound : forall q, Icontains (Iconst q) (Q2R q).
Proof. intro q; unfold Icontains, Iconst; simpl; lra. Qed.

Lemma Iadd_sound : forall i j x y,
  Icontains i x -> Icontains j y -> Icontains (Iadd i j) (x + y).
Proof.
  intros i j x y [Hx1 Hx2] [Hy1 Hy2]. unfold Icontains, Iadd; simpl.
  rewrite !Q2R_plus. lra.
Qed.

Lemma Ineg_sound : forall i x, Icontains i x -> Icontains (Ineg i) (- x).
Proof.
  intros i x [Hx1 Hx2]. unfold Icontains, Ineg; simpl. rewrite !Q2R_opp. lra.
Qed.

Lemma Isub_sound : forall i j x y,
  Icontains i x -> Icontains j y -> Icontains (Isub i j) (x - y).
Proof.
  intros i j x y Hx Hy. unfold Isub.
  replace (x - y) with (x + - y) by ring.
  apply Iadd_sound; [ exact Hx | apply Ineg_sound; exact Hy ].
Qed.

(* ---- interval multiplication via the four corner products ---- *)
Lemma mul_le_max2 : forall x c d y, c <= y <= d -> x * y <= Rmax (x * c) (x * d).
Proof.
  intros x c d y [Hc Hd]. destruct (Rle_dec 0 x) as [Hx | Hx].
  - apply Rle_trans with (x * d); [ nra | apply Rmax_r ].
  - apply Rle_trans with (x * c); [ nra | apply Rmax_l ].
Qed.

Lemma min_le_mul2 : forall x c d y, c <= y <= d -> Rmin (x * c) (x * d) <= x * y.
Proof.
  intros x c d y [Hc Hd]. destruct (Rle_dec 0 x) as [Hx | Hx].
  - apply Rle_trans with (x * c); [ apply Rmin_l | nra ].
  - apply Rle_trans with (x * d); [ apply Rmin_r | nra ].
Qed.

Lemma mul_le_max1 : forall a b x c, a <= x <= b -> x * c <= Rmax (a * c) (b * c).
Proof.
  intros a b x c [Ha Hb]. destruct (Rle_dec 0 c) as [Hcp | Hcp].
  - apply Rle_trans with (b * c); [ nra | apply Rmax_r ].
  - apply Rle_trans with (a * c); [ nra | apply Rmax_l ].
Qed.

Lemma min_le_mul1 : forall a b x c, a <= x <= b -> Rmin (a * c) (b * c) <= x * c.
Proof.
  intros a b x c [Ha Hb]. destruct (Rle_dec 0 c) as [Hcp | Hcp].
  - apply Rle_trans with (a * c); [ apply Rmin_l | nra ].
  - apply Rle_trans with (b * c); [ apply Rmin_r | nra ].
Qed.

Definition Imul (i j : Itv) : Itv :=
  let a := ilo i in let b := ihi i in let c := ilo j in let d := ihi j in
  mkI (Qmin2 (Qmin2 (a * c) (a * d)) (Qmin2 (b * c) (b * d)))
      (Qmax2 (Qmax2 (a * c) (a * d)) (Qmax2 (b * c) (b * d))).

Lemma Imul_sound : forall i j x y,
  Icontains i x -> Icontains j y -> Icontains (Imul i j) (x * y).
Proof.
  intros i j x y [Hx1 Hx2] [Hy1 Hy2]. unfold Icontains, Imul; simpl.
  set (a := Q2R (ilo i)) in *. set (b := Q2R (ihi i)) in *.
  set (c := Q2R (ilo j)) in *. set (d := Q2R (ihi j)) in *.
  rewrite !Q2R_Qmin2, !Q2R_Qmax2, !Q2R_mult. split.
  - (* min-of-4 <= x*y *)
    apply Rle_trans with (Rmin (x * c) (x * d)); [ | apply min_le_mul2; lra ].
    apply Rmin_glb.
    + apply Rle_trans with (Rmin (a * c) (b * c)); [ | apply min_le_mul1; lra ].
      apply Rmin_glb.
      * apply Rle_trans with (Rmin (a * c) (a * d)); [ apply Rmin_l | apply Rmin_l ].
      * apply Rle_trans with (Rmin (b * c) (b * d)); [ apply Rmin_r | apply Rmin_l ].
    + apply Rle_trans with (Rmin (a * d) (b * d)); [ | apply min_le_mul1; lra ].
      apply Rmin_glb.
      * apply Rle_trans with (Rmin (a * c) (a * d)); [ apply Rmin_l | apply Rmin_r ].
      * apply Rle_trans with (Rmin (b * c) (b * d)); [ apply Rmin_r | apply Rmin_r ].
  - (* x*y <= max-of-4 *)
    apply Rle_trans with (Rmax (x * c) (x * d)); [ apply mul_le_max2; lra | ].
    apply Rmax_lub.
    + apply Rle_trans with (Rmax (a * c) (b * c)); [ apply mul_le_max1; lra | ].
      apply Rmax_lub.
      * apply Rle_trans with (Rmax (a * c) (a * d)); [ apply Rmax_l | apply Rmax_l ].
      * apply Rle_trans with (Rmax (b * c) (b * d)); [ apply Rmax_l | apply Rmax_r ].
    + apply Rle_trans with (Rmax (a * d) (b * d)); [ apply mul_le_max1; lra | ].
      apply Rmax_lub.
      * apply Rle_trans with (Rmax (a * c) (a * d)); [ apply Rmax_r | apply Rmax_l ].
      * apply Rle_trans with (Rmax (b * c) (b * d)); [ apply Rmax_r | apply Rmax_r ].
Qed.

Print Assumptions Imul_sound.
