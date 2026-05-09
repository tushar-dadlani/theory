(* ============================================================ *)
(*  QuotientRemainderGeometry.v                                 *)
(*                                                              *)
(*  THE GEOMETRIC PICTURE OF a ÷ b                              *)
(*                                                              *)
(*  Place the dividend a as a horizontal segment of length a   *)
(*  on the 0° linear axis. The divisor b is a "ruler" of       *)
(*  length b. Lay the ruler down repeatedly, starting from 0.  *)
(*                                                              *)
(*  After q copies of the ruler, you have covered q·b.         *)
(*  The next copy would overshoot a, so you stop.              *)
(*  The leftover, a − q·b, is the remainder r.                 *)
(*                                                              *)
(*  Geometrically:                                              *)
(*    a = q·b + r                                               *)
(*                                                              *)
(*    q : how many full ruler-lengths fit                       *)
(*        → lives on the 0° linear axis (whole steps)           *)
(*                                                              *)
(*    r : the residual after the last full step                 *)
(*        → lives on the 90° inverse axis (sub-unit, 0 ≤ r < b) *)
(*                                                              *)
(*  These are the TWO PERPENDICULAR PROJECTIONS of the          *)
(*  diagonal point (a, b) onto the two axes.                    *)
(*                                                              *)
(*  The 45° Gaussian diagonal then encodes the RATIO a/b as    *)
(*  the slope of the line from the origin through (a, b).      *)
(*  Whether the quotient is exact (r = 0) is the test of       *)
(*  whether (a, b) lies ON the rational diagonal y/b = x/a.    *)
(*                                                              *)
(*  Axiom count: 0.                                             *)
(* ============================================================ *)

From Coq Require Import Arith Lia.

(* ============================================================ *)
(*  PART 1 — THE TWO AXES                                       *)
(* ============================================================ *)

Definition Axis0  := nat.   (* the 0° linear axis  *)
Definition Axis90 := nat.   (* the 90° inverse axis *)

(* A 2D point in the triadic plane *)
Record Point := mkPt {
  x_coord : Axis0;     (* coordinate along the 0° axis  *)
  y_coord : Axis90     (* coordinate along the 90° axis *)
}.

(* The 45° diagonal: points where x = y *)
Definition on_diagonal (p : Point) : Prop := x_coord p = y_coord p.

(* ============================================================ *)
(*  PART 2 — THE QUOTIENT-REMAINDER POINT                       *)
(*                                                              *)
(*  Given a divisor b > 0, the dividend a maps to a point      *)
(*  in the plane:                                               *)
(*     div_point a b = (q, r) = (a / b, a mod b)               *)
(*                                                              *)
(*  - q on the 0° axis = "how many full b-steps fit in a"      *)
(*  - r on the 90° axis = "the leftover after the last step"   *)
(*                                                              *)
(*  Geometric reading:                                          *)
(*     a is "hit" by walking q steps east (each step = b)      *)
(*     plus r more east steps (a "fractional" b-step).          *)
(* ============================================================ *)

Definition div_point (a b : nat) : Point :=
  mkPt (a / b) (a mod b).

(* The reconstruction: q·b + r = a. *)
Theorem reconstruct_dividend : forall a b,
  b > 0 ->
  x_coord (div_point a b) * b + y_coord (div_point a b) = a.
Proof.
  intros a b Hb. unfold div_point. simpl.
  pose proof (Nat.div_mod a b ltac:(lia)). lia.
Qed.

(* The remainder is bounded: r < b. *)
Theorem remainder_bounded : forall a b,
  b > 0 -> y_coord (div_point a b) < b.
Proof.
  intros a b Hb. unfold div_point. simpl.
  apply Nat.mod_upper_bound. lia.
Qed.

(* ============================================================ *)
(*  PART 3 — THE TWO PROJECTIONS ARE PERPENDICULAR              *)
(*                                                              *)
(*  Geometrically: the quotient is the projection of the        *)
(*  point (a, b) onto the 0° axis at the lattice points of b;  *)
(*  the remainder is the perpendicular distance from that       *)
(*  lattice point to a, measured on the 90° axis.               *)
(* ============================================================ *)

(* Quotient = horizontal projection (multiples of b on Axis0). *)
Definition project_horizontal (a b : nat) : nat :=
  (a / b) * b.

(* Remainder = vertical residual (the perpendicular distance).  *)
Definition project_vertical (a b : nat) : nat := a mod b.

(* The two together reconstruct a — they are orthogonal         *)
(* coordinates of the same point.                                *)
Theorem perpendicular_decomposition : forall a b,
  b > 0 ->
  project_horizontal a b + project_vertical a b = a.
Proof.
  intros a b Hb. unfold project_horizontal, project_vertical.
  pose proof (Nat.div_mod a b ltac:(lia)). lia.
Qed.

(* The horizontal projection is a multiple of b. *)
Theorem horizontal_is_multiple : forall a b,
  b > 0 -> exists k, project_horizontal a b = k * b.
Proof.
  intros a b Hb. exists (a / b). reflexivity.
Qed.

(* The vertical projection is strictly below b. *)
Theorem vertical_below_b : forall a b,
  b > 0 -> project_vertical a b < b.
Proof.
  intros a b Hb. unfold project_vertical.
  apply Nat.mod_upper_bound. lia.
Qed.

(* ============================================================ *)
(*  PART 4 — EXACT DIVISION = THE DIAGONAL                      *)
(*                                                              *)
(*  When the remainder is zero, the point (a, b) lies on the   *)
(*  rational diagonal: a is exactly k·b for some integer k.    *)
(*  In Gaussian terms, the slope a/b is rational with finite   *)
(*  representation.                                              *)
(* ============================================================ *)

(* Exact division iff remainder = 0. *)
Theorem exact_iff_zero_remainder : forall a b,
  b > 0 ->
  (project_vertical a b = 0 <-> (exists k, a = k * b)).
Proof.
  intros a b Hb. unfold project_vertical. split.
  - intro Hr. exists (a / b).
    pose proof (Nat.div_mod a b ltac:(lia)).
    lia.
  - intros [k Hk]. subst.
    rewrite Nat.mod_mul by lia. reflexivity.
Qed.

(* The geometric reading: exact division means the point        *)
(* (a, b) lies exactly on a ray from the origin at integer       *)
(* slope. We capture this fact via exact_iff_zero_remainder      *)
(* above; the diagonal interpretation is illustrative.           *)

(* ============================================================ *)
(*  PART 5 — THE THREE-PART TRIADIC DECOMPOSITION OF a ÷ b      *)
(*                                                              *)
(*  Every division produces THREE pieces of geometric data:    *)
(*                                                              *)
(*    1. QUOTIENT (0° axis):  q = how many b-steps             *)
(*    2. REMAINDER (90° axis): r = the residual                *)
(*    3. RATIO (45° diagonal): r/b = where on the next step    *)
(*                                                              *)
(*  Quotient and remainder are integer (lattice) quantities.   *)
(*  The ratio r/b is the sub-unit fraction — the fractional   *)
(*  position on the diagonal.                                   *)
(* ============================================================ *)

Theorem triadic_division_decomposition : forall a b,
  b > 0 ->
  (* The 0° component (quotient) and 90° component (remainder) *)
  (* together reconstruct a:                                    *)
  (a / b) * b + (a mod b) = a /\
  (* The 90° component is bounded by the divisor: *)
  a mod b < b /\
  (* Exact division ⟺ the remainder vanishes: *)
  (a mod b = 0 <-> exists k, a = k * b).
Proof.
  intros a b Hb. split; [|split].
  - pose proof (Nat.div_mod a b ltac:(lia)). lia.
  - apply Nat.mod_upper_bound. lia.
  - split.
    + intro Hr. exists (a / b).
      pose proof (Nat.div_mod a b ltac:(lia)). lia.
    + intros [k Hk]. subst. rewrite Nat.mod_mul by lia. reflexivity.
Qed.

(* ============================================================ *)
(*  PART 6 — THE GAUSSIAN-ALGEBRA READING                       *)
(*                                                              *)
(*  In Gaussian algebra (the 45° axis), a Gaussian integer is  *)
(*  a + b·i where a is on the 0° axis and b is on the 90°.    *)
(*                                                              *)
(*  Division a ÷ b in this picture is:                          *)
(*    (a + 0·i) ÷ b = (a/b) + 0·i + (a mod b)/b · 1·i_residual *)
(*                                                              *)
(*  The integer quotient sits on the real axis; the remainder *)
(*  contributes a sub-unit imaginary part. When the remainder *)
(*  vanishes, the result is a pure real (on the integer axis). *)
(*                                                              *)
(*  This is why the "phantom" of the quotient lives at the     *)
(*  half-step: r/b is a fractional position, info_bit = 1.    *)
(* ============================================================ *)

(* The "imaginary residual": the remainder, as a fraction of b. *)
(* We model it by the pair (r, b) with r < b. *)
Record Imag_Residual := mkRes {
  res_num : nat;
  res_den : nat;
  res_bound : res_num < res_den
}.

(* The Gaussian decomposition of a ÷ b. *)
Definition gaussian_div (a b : nat) (Hb : b > 0) : nat * Imag_Residual :=
  (a / b,
   mkRes (a mod b) b
         (Nat.mod_upper_bound a b ltac:(lia))).

(* The Gaussian quotient and the imaginary residual together     *)
(* capture all of a ÷ b. *)
Theorem gaussian_division_complete : forall a b (Hb : b > 0),
  let (q, r) := gaussian_div a b Hb in
  q * b + res_num r = a /\ res_num r < res_den r.
Proof.
  intros a b Hb. simpl. split.
  - pose proof (Nat.div_mod a b ltac:(lia)). lia.
  - apply Nat.mod_upper_bound. lia.
Qed.

Print Assumptions triadic_division_decomposition.
Print Assumptions gaussian_division_complete.
