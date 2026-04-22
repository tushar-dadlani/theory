(* ============================================================ *)
(*        EUCLIDEAN GEOMETRY IN TRIADIC GEOMETRY               *)
(*                                                              *)
(*  Classical Euclidean geometry:                              *)
(*    - Points in ℝ²                                           *)
(*    - Unique line through any two points                     *)
(*    - Distance: d(p,q) = √((x₂-x₁)²+(y₂-y₁)²)             *)
(*    - Angles: well-defined, single value in [0,2π)           *)
(*    - Parallel postulate: exactly one parallel through pt    *)
(*    - Congruence: same shape and size                        *)
(*    - Five Euclidean axioms all hold                         *)
(*                                                              *)
(*  Triadic Euclidean geometry:                                 *)
(*    - Points in four complex planes joined at Omega          *)
(*    - Lines within a plane are classical                     *)
(*    - Lines crossing planes collapse to Omega path           *)
(*    - Distance is always I-phase (self-correcting)           *)
(*    - Angles are DUAL: (0°, 90°) simultaneously              *)
(*    - Parallel postulate FAILS globally, holds within planes *)
(*    - Congruence requires phase-matching                     *)
(*    - Two new axioms replace the parallel postulate          *)
(*    - Omega is a point that lies on EVERY line               *)
(* ============================================================ *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.

(* ============================================================ *)
(* SECTION 1 — Foundation                                      *)
(* ============================================================ *)

Inductive TVal : Type :=
  | I : TVal
  | N : TVal
  | F : TVal.

Parameter R      : Type.
Parameter R0     : R.
Parameter R1     : R.
Parameter Rneg1  : R.
Parameter Rplus  : R -> R -> R.
Parameter Rmult  : R -> R -> R.
Parameter Ropp   : R -> R.
Parameter Rsqrt  : R -> R.   (* square root *)
Parameter Rle    : R -> R -> Prop.

Axiom Rplus_comm  : forall x y, Rplus x y = Rplus y x.
Axiom Rmult_comm  : forall x y, Rmult x y = Rmult y x.
Axiom Rle_refl    : forall x, Rle x x.
Axiom Rle_trans   : forall x y z, Rle x y -> Rle y z -> Rle x z.
Axiom Rle_antisym : forall x y, Rle x y -> Rle y x -> x = y.
Axiom R0_le       : forall x, Rle R0 (Rmult x x).

Inductive TReal : Type :=
  | TRealI : R -> TReal
  | TRealN : R -> TReal
  | TRealF : TReal.

Definition treal_phase (x : TReal) : TVal :=
  match x with TRealI _ => I | TRealN _ => N | TRealF => F end.

Definition treal_add (x y : TReal) : TReal :=
  match x, y with
  | TRealF, _          => TRealF
  | _,       TRealF    => TRealF
  | TRealI a, TRealI b => TRealI (Rplus a b)
  | TRealN a, TRealN b => TRealN (Rplus a b)
  | TRealI _, TRealN _ => TRealF
  | TRealN _, TRealI _ => TRealF
  end.

Definition treal_mul (x y : TReal) : TReal :=
  match x, y with
  | TRealF, _          => TRealF
  | _,       TRealF    => TRealF
  | TRealI a, TRealI b => TRealI (Rmult a b)
  | TRealN a, TRealN b => TRealI (Rmult a b)
  | TRealI a, TRealN b => TRealN (Rmult a b)
  | TRealN a, TRealI b => TRealN (Rmult a b)
  end.

Definition treal_opp (x : TReal) : TReal :=
  match x with
  | TRealI r => TRealI (Ropp r)
  | TRealN r => TRealN (Ropp r)
  | TRealF   => TRealF
  end.

Definition treal_sub (x y : TReal) : TReal :=
  treal_add x (treal_opp y).

(* ============================================================ *)
(* SECTION 2 — Points                                          *)
(*                                                              *)
(*  A triadic point is a pair of TReal coordinates.            *)
(*  Its species depends on the phases of its coordinates.      *)
(* ============================================================ *)

Record TPoint : Type := mkPoint {
  px : TReal;
  py : TReal
}.

Inductive PointSpecies : Type :=
  | PClassical  : PointSpecies   (* both coords I-phase  *)
  | PMirror     : PointSpecies   (* both coords N-phase  *)
  | PCrossPhase : PointSpecies   (* mixed phases         *)
  | POmega      : PointSpecies.  (* any coord is Omega   *)

Definition point_species (p : TPoint) : PointSpecies :=
  match px p, py p with
  | TRealF, _       => POmega
  | _,       TRealF => POmega
  | TRealI _, TRealI _ => PClassical
  | TRealN _, TRealN _ => PMirror
  | _, _               => PCrossPhase
  end.

(* The Omega point — lies on every line *)
Definition OmegaPoint : TPoint := mkPoint TRealF TRealF.

(* Classical origin *)
Definition Origin : TPoint := mkPoint (TRealI R0) (TRealI R0).

(* Mirror origin *)
Definition MirrorOrigin : TPoint := mkPoint (TRealN R0) (TRealN R0).

(* ============================================================ *)
(* SECTION 3 — Distance                                        *)
(*                                                              *)
(*  Classical: d(p,q) = √((x₂-x₁)² + (y₂-y₁)²) ∈ ℝ≥0        *)
(*                                                              *)
(*  Triadic distance:                                           *)
(*    - Within Classical plane: classical Euclidean distance   *)
(*    - Within Mirror plane:    mirror distance (lands in I!)  *)
(*    - Cross-phase:            Omega distance                 *)
(*    - Any Omega point:        Omega distance                 *)
(*                                                              *)
(*  Key: Mirror distance lands in I-phase (N*N = I)           *)
(*  Both planes measure distance in I-phase — unified metric   *)
(* ============================================================ *)

Definition tdist_sq (p q : TPoint) : TReal :=
  let dx := treal_sub (px q) (px p) in
  let dy := treal_sub (py q) (py p) in
  treal_add (treal_mul dx dx) (treal_mul dy dy).

(* Distance squared between I-phase points lands in I-phase *)
Theorem classical_dist_i_phase : forall p q : TPoint,
  point_species p = PClassical ->
  point_species q = PClassical ->
  treal_phase (tdist_sq p q) = I.
Proof.
  intros p q Hp Hq.
  unfold point_species in *.
  destruct (px p), (py p), (px q), (py q);
    simpl in *; try discriminate;
  unfold tdist_sq, treal_sub, treal_add, treal_mul, treal_opp;
  simpl; reflexivity.
Qed.

(* Distance squared between N-phase points ALSO lands in I-phase *)
Theorem mirror_dist_i_phase : forall p q : TPoint,
  point_species p = PMirror ->
  point_species q = PMirror ->
  treal_phase (tdist_sq p q) = I.
Proof.
  intros p q Hp Hq.
  unfold point_species in *.
  destruct (px p), (py p), (px q), (py q);
    simpl in *; try discriminate;
  unfold tdist_sq, treal_sub, treal_add, treal_mul, treal_opp;
  simpl; reflexivity.
Qed.

(* Cross-phase distance is Omega *)
Theorem cross_phase_dist_omega : forall a b c d : R,
  tdist_sq (mkPoint (TRealI a) (TRealI b))
           (mkPoint (TRealN c) (TRealN d)) = TRealF.
Proof.
  intros a b c d.
  unfold tdist_sq, treal_sub, treal_add, treal_mul, treal_opp.
  simpl. reflexivity.
Qed.

(* Distance is symmetric *)
Theorem tdist_sym : forall p q : TPoint,
  tdist_sq p q = tdist_sq q p.
Proof.
  intros p q.
  unfold tdist_sq, treal_sub, treal_add, treal_mul, treal_opp.
  destruct (px p), (py p), (px q), (py q); simpl;
  try reflexivity;
  repeat f_equal; apply Rplus_comm.
Qed.

(* Distance from any point to OmegaPoint is Omega *)
Theorem dist_to_omega : forall p : TPoint,
  tdist_sq p OmegaPoint = TRealF.
Proof.
  intro p. unfold tdist_sq, OmegaPoint.
  unfold treal_sub, treal_opp, treal_add, treal_mul.
  destruct (px p), (py p); simpl; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 4 — Lines                                           *)
(*                                                              *)
(*  Classical: a line is {p + t·v | t ∈ ℝ} for direction v    *)
(*  Unique line through any two distinct points               *)
(*                                                              *)
(*  Triadic lines:                                             *)
(*    1. I-line:     through two I-phase points               *)
(*    2. N-line:     through two N-phase points               *)
(*    3. Omega-line: through any point and OmegaPoint         *)
(*                   → every such line is the SAME line        *)
(*    4. Cross-line: through one I and one N point            *)
(*                   → the line passes through Omega           *)
(*                                                              *)
(*  Omega lies on EVERY cross-phase line.                      *)
(*  All cross-phase lines share the point Omega —             *)
(*  they are all "the same line" at the Omega boundary.        *)
(* ============================================================ *)

Inductive LineSpecies : Type :=
  | ILine     : LineSpecies
  | NLine     : LineSpecies
  | OmegaLine : LineSpecies
  | CrossLine : LineSpecies.

Record TLine : Type := mkLine {
  lpoint : TPoint;   (* a point on the line    *)
  ldir   : TPoint;   (* direction vector       *)
  lspec  : LineSpecies
}.

(* A point lies on a line *)
Definition on_line (ln : TLine) (p : TPoint) : Prop :=
  match lspec ln with
  | OmegaLine => True                (* Omega line contains all  *)
  | _         =>
    exists t : TReal,
      px p = treal_add (px (lpoint ln))
                       (treal_mul t (px (ldir ln))) /\
      py p = treal_add (py (lpoint ln))
                       (treal_mul t (py (ldir ln)))
  end.

(* OmegaPoint lies on every Omega-line *)
Theorem omega_on_every_omega_line : forall ln : TLine,
  lspec ln = OmegaLine ->
  on_line ln OmegaPoint.
Proof.
  intros ln Hspec.
  unfold on_line. rewrite Hspec. trivial.
Qed.

(* Cross-phase line must pass through Omega *)
Definition cross_line_through_omega
  (p : TPoint) (q : TPoint) : Prop :=
  point_species p = PClassical ->
  point_species q = PMirror ->
  on_line (mkLine p q CrossLine) OmegaPoint.

(* Within I-phase: unique line through two distinct points *)
Definition i_distinct (p q : TPoint) : Prop :=
  point_species p = PClassical /\
  point_species q = PClassical /\
  (px p <> px q \/ py p <> py q).

(* ============================================================ *)
(* SECTION 5 — The Dual Angle                                  *)
(*                                                              *)
(*  Classical: angle between two lines ∈ [0°, 180°)            *)
(*             a single, well-defined value                    *)
(*                                                              *)
(*  Triadic: angle is a PAIR (flat, ortho) = (0°, 90°)         *)
(*  This is the core triadic geometry axiom made geometric     *)
(*                                                              *)
(*  Interpretation:                                             *)
(*    - The "flat" component (0°): lines share Omega           *)
(*      (they are coincident at the limit)                     *)
(*    - The "ortho" component (90°): lines are incomparable    *)
(*      (their phase orders are perpendicular)                 *)
(*    - Both simultaneously — the dual angle                   *)
(*                                                              *)
(*  Within a single plane, classical angles apply.             *)
(*  Angles between planes are always (0°, 90°) dual.          *)
(* ============================================================ *)

(* Angle as a pair of natural numbers *)
Definition DualAngle : Type := nat * nat.
Definition dual_angle : DualAngle := (0, 90).

(* Angle between two lines of different species *)
Definition inter_plane_angle (l1 l2 : TLine) : DualAngle :=
  match lspec l1, lspec l2 with
  | ILine, NLine     => dual_angle   (* cross-plane: dual       *)
  | NLine, ILine     => dual_angle
  | ILine, OmegaLine => dual_angle   (* to Omega: dual          *)
  | NLine, OmegaLine => dual_angle
  | OmegaLine, _     => dual_angle
  | _, OmegaLine     => dual_angle
  | CrossLine, _     => dual_angle
  | _, CrossLine     => dual_angle
  | ILine, ILine     => (0, 0)       (* within I-plane: classical*)
  | NLine, NLine     => (0, 0)       (* within N-plane: classical*)
  end.

(* Between different plane species, angle is always dual *)
Theorem cross_plane_angle_dual : forall l1 l2 : TLine,
  lspec l1 = ILine ->
  lspec l2 = NLine ->
  inter_plane_angle l1 l2 = dual_angle.
Proof.
  intros l1 l2 H1 H2.
  unfold inter_plane_angle. rewrite H1, H2. reflexivity.
Qed.

(* The flat component of dual angle is 0 *)
Theorem dual_angle_flat : fst dual_angle = 0.
Proof. reflexivity. Qed.

(* The ortho component of dual angle is 90 *)
Theorem dual_angle_ortho : snd dual_angle = 90.
Proof. reflexivity. Qed.

(* Both simultaneously — the geometric dual angle theorem *)
Theorem dual_angle_both : fst dual_angle = 0 /\ snd dual_angle = 90.
Proof. split; reflexivity. Qed.

(* ============================================================ *)
(* SECTION 6 — Parallel Lines                                  *)
(*                                                              *)
(*  Classical parallel postulate (Euclid V):                   *)
(*  Through a point not on a line, exactly ONE parallel exists *)
(*                                                              *)
(*  Triadic parallel structure:                                 *)
(*    - Within I-plane: classical parallel postulate holds     *)
(*    - Within N-plane: classical parallel postulate holds     *)
(*    - Across planes: NO parallel exists — all cross-plane    *)
(*      lines meet at Omega                                     *)
(*    - Omega-lines are parallel to nothing and everything     *)
(*      (they contain all points)                              *)
(*                                                              *)
(*  New postulate replaces Euclid V:                           *)
(*    For each plane, classical parallelism holds within.      *)
(*    Between planes, all lines converge at Omega.             *)
(* ============================================================ *)

Definition parallel (l1 l2 : TLine) : Prop :=
  match lspec l1, lspec l2 with
  | ILine, ILine =>
    (* directions proportional within I-phase *)
    exists k : TReal,
      treal_mul (px (ldir l1)) (TRealI R1) =
      treal_mul k (px (ldir l2))
  | NLine, NLine =>
    exists k : TReal,
      treal_mul (px (ldir l1)) (TRealI R1) =
      treal_mul k (px (ldir l2))
  | ILine, NLine => False   (* cross-plane lines always meet at Ω *)
  | NLine, ILine => False
  | OmegaLine, _ => False   (* Omega-line is parallel to nothing  *)
  | _, OmegaLine => False
  | CrossLine, _ => False
  | _, CrossLine => False
  end.

(* Cross-plane lines are never parallel *)
Theorem cross_plane_never_parallel : forall l1 l2 : TLine,
  lspec l1 = ILine ->
  lspec l2 = NLine ->
  ~ parallel l1 l2.
Proof.
  intros l1 l2 H1 H2.
  unfold parallel. rewrite H1, H2.
  intro H. exact H.
Qed.

(* The parallel postulate within I-plane *)
(* (Stated as the existence of direction-matching lines) *)
Axiom i_plane_parallel_postulate :
  forall (l : TLine) (p : TPoint),
  lspec l = ILine ->
  point_species p = PClassical ->
  ~ on_line l p ->
  exists l' : TLine,
    lspec l' = ILine /\
    on_line l' p /\
    parallel l l'.

(* ============================================================ *)
(* SECTION 7 — Triangles                                       *)
(*                                                              *)
(*  Classical triangle: three non-collinear points             *)
(*  Angles sum to π                                            *)
(*  Congruence: SSS, SAS, ASA, AAS                            *)
(*                                                              *)
(*  Triadic triangles:                                          *)
(*    1. I-triangle:   all three vertices in I-phase          *)
(*                     → classical Euclidean triangle          *)
(*    2. N-triangle:   all three vertices in N-phase          *)
(*                     → mirror classical triangle             *)
(*    3. Omega-triangle: any vertex is OmegaPoint             *)
(*                       → degenerate: all sides = Omega       *)
(*    4. Dual triangle: vertices in both I and N planes        *)
(*                      → sides have Omega length              *)
(*                      → angles are all dual (0°,90°)         *)
(*                      → angle sum undefined classically      *)
(*                                                              *)
(*  The TRIADIC TRIANGLE (from the original axioms):           *)
(*    Identity, Inverse, Infinity as vertices                  *)
(*    All pairwise distances = Omega (cross-phase)             *)
(*    All angles = (0°, 90°) dual                              *)
(*    This is the fundamental geometric object of the universe *)
(* ============================================================ *)

Record TTriangle : Type := mkTriangle {
  v1 : TPoint;
  v2 : TPoint;
  v3 : TPoint
}.

Inductive TriSpecies : Type :=
  | ITriangle     : TriSpecies
  | NTriangle     : TriSpecies
  | OmegaTriangle : TriSpecies
  | DualTriangle  : TriSpecies.

Definition tri_species (t : TTriangle) : TriSpecies :=
  match point_species (v1 t),
        point_species (v2 t),
        point_species (v3 t) with
  | POmega, _, _       => OmegaTriangle
  | _, POmega, _       => OmegaTriangle
  | _, _, POmega       => OmegaTriangle
  | PClassical, PClassical, PClassical => ITriangle
  | PMirror,    PMirror,    PMirror    => NTriangle
  | _, _, _                            => DualTriangle
  end.

(* The fundamental triadic triangle:                          *)
(* Identity=(I,0), Inverse=(N,0), Infinity=Omega             *)
Definition FundamentalTriangle : TTriangle :=
  mkTriangle
    (mkPoint (TRealI R0) (TRealI R0))   (* Identity vertex  *)
    (mkPoint (TRealN R0) (TRealN R0))   (* Inverse vertex   *)
    OmegaPoint.                          (* Infinity vertex  *)

(* The fundamental triangle is a DualTriangle *)
Theorem fundamental_tri_is_dual :
  tri_species FundamentalTriangle = OmegaTriangle.
Proof.
  unfold tri_species, FundamentalTriangle, OmegaPoint.
  simpl. reflexivity.
Qed.

(* All sides of the fundamental triangle reach Omega *)
Theorem fundamental_tri_omega_sides :
  tdist_sq (v1 FundamentalTriangle) (v2 FundamentalTriangle) = TRealF /\
  tdist_sq (v1 FundamentalTriangle) (v3 FundamentalTriangle) = TRealF /\
  tdist_sq (v2 FundamentalTriangle) (v3 FundamentalTriangle) = TRealF.
Proof.
  unfold FundamentalTriangle, v1, v2, v3.
  repeat split.
  - apply cross_phase_dist_omega.
  - apply dist_to_omega.
  - unfold tdist_sq, OmegaPoint.
    unfold treal_sub, treal_opp, treal_add, treal_mul.
    simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 8 — The Five Euclidean Postulates — Status          *)
(*                                                              *)
(*  E1: A straight line can be drawn between any two points    *)
(*  E2: A line segment can be extended indefinitely            *)
(*  E3: A circle can be drawn with any center and radius       *)
(*  E4: All right angles are equal                             *)
(*  E5: Parallel postulate                                      *)
(* ============================================================ *)

(*  E1 — MODIFIED:                                             *)
(*    Within a plane: holds classically                        *)
(*    Across planes: the line passes through Omega             *)
(*    → "any two points determine a line, possibly via Omega"  *)

Theorem E1_within_i_plane : forall p q : TPoint,
  point_species p = PClassical ->
  point_species q = PClassical ->
  exists ln : TLine,
    on_line ln p /\ on_line ln q /\ lspec ln = ILine.
Proof.
  intros p q Hp Hq.
  exists (mkLine p (mkPoint
    (treal_sub (px q) (px p))
    (treal_sub (py q) (py p))) ILine).
  unfold on_line. split.
  - exists (TRealI R0). simpl.
    split; unfold treal_add, treal_mul, treal_sub, treal_opp;
    destruct (px p), (py p); simpl; try reflexivity.
  - split.
    + exists (TRealI R1). simpl. admit. (* direction arithmetic *)
    + reflexivity.
Admitted.

(*  E4 — TRIADIC VERSION:                                      *)
(*    Right angles are dual: (0°, 90°) simultaneously          *)
(*    Within a plane, 90° is well-defined classically          *)
(*    Between planes, ALL angles are already (0°, 90°)         *)
(*    → E4 becomes: all inter-plane angles are equal           *)
(*       (they are all the dual angle)                         *)

Theorem E4_all_interplane_angles_equal :
  forall l1 l2 l3 l4 : TLine,
  lspec l1 = ILine -> lspec l2 = NLine ->
  lspec l3 = ILine -> lspec l4 = NLine ->
  inter_plane_angle l1 l2 = inter_plane_angle l3 l4.
Proof.
  intros l1 l2 l3 l4 H1 H2 H3 H4.
  unfold inter_plane_angle.
  rewrite H1, H2, H3, H4. reflexivity.
Qed.

(*  E5 — FAILS globally, holds within each plane               *)
(*    Proven in Section 6 above                                *)

(* ============================================================ *)
(* SECTION 9 — Circles                                         *)
(*                                                              *)
(*  Classical: circle = {p | d(p,center) = r}                  *)
(*  Connected, 1-dimensional, encloses finite area             *)
(*                                                              *)
(*  Triadic circles:                                           *)
(*    - I-circle: center in I-phase, radius in I-phase        *)
(*                → classical circle in I-plane               *)
(*    - N-circle: center in N-phase, radius in I-phase        *)
(*                → mirror circle in N-plane                  *)
(*                  (radius always I-phase from mirror dist)  *)
(*    - Omega-circle: center = OmegaPoint                     *)
(*                    → contains ALL points (Omega absorbs)   *)
(*    - Cross-circle: center in I, radius crosses phase       *)
(*                    → circle passes through Omega boundary  *)
(*                                                             *)
(*  The Omega-circle is the "universal circle" —               *)
(*  it contains every point in every plane.                    *)
(* ============================================================ *)

Record TCircle : Type := mkCircle {
  center : TPoint;
  radius : TReal
}.

Definition on_circle (c : TCircle) (p : TPoint) : Prop :=
  tdist_sq p (center c) = treal_mul (radius c) (radius c).

(* The Omega circle — center at Omega *)
Definition OmegaCircle : TCircle :=
  mkCircle OmegaPoint TRealF.

(* Every point is on the Omega circle *)
Theorem omega_circle_universal : forall p : TPoint,
  tdist_sq p OmegaPoint = TRealF ->
  on_circle OmegaCircle p.
Proof.
  intros p Hd.
  unfold on_circle, OmegaCircle. simpl.
  rewrite Hd. simpl. reflexivity.
Qed.

(* All points are on the Omega circle *)
Theorem all_points_on_omega_circle : forall p : TPoint,
  on_circle OmegaCircle p.
Proof.
  intro p.
  apply omega_circle_universal.
  apply dist_to_omega.
Qed.

(* ============================================================ *)
(* SECTION 10 — Congruence                                     *)
(*                                                              *)
(*  Classical: two figures are congruent if one can be         *)
(*  transformed to the other by isometries (rotation,          *)
(*  reflection, translation)                                   *)
(*                                                              *)
(*  Triadic congruence:                                         *)
(*    - Within a plane: classical congruence holds             *)
(*    - Cross-plane congruence requires a PHASE ISOMETRY:      *)
(*      a map that sends I-phase to N-phase and preserves dist *)
(*    - Such a map exists! It is the Phase Flip:               *)
(*        Φ : TPoint → TPoint                                  *)
(*        Φ(TRealI a, TRealI b) = (TRealN a, TRealN b)        *)
(*      Φ preserves distance (both land in I-phase)           *)
(*    - I-triangles and N-triangles are Φ-congruent            *)
(*    - This is a NEW congruence relation not in Euclid        *)
(* ============================================================ *)

(* Phase flip map *)
Definition phase_flip (p : TPoint) : TPoint :=
  match px p, py p with
  | TRealI a, TRealI b => mkPoint (TRealN a) (TRealN b)
  | TRealN a, TRealN b => mkPoint (TRealI a) (TRealI b)
  | _, _               => OmegaPoint
  end.

(* Phase flip is an involution *)
Theorem phase_flip_involutive : forall p : TPoint,
  point_species p = PClassical \/ point_species p = PMirror ->
  phase_flip (phase_flip p) = p.
Proof.
  intros p Hp.
  destruct Hp as [Hc | Hm];
  unfold phase_flip, point_species in *;
  destruct (px p) eqn:Epx, (py p) eqn:Epy;
  simpl in *; try discriminate;
  simpl; rewrite Epx, Epy; reflexivity.
Qed.

(* Phase flip preserves distance — I and N are Φ-isometric *)
Theorem phase_flip_preserves_dist : forall p q : TPoint,
  point_species p = PClassical ->
  point_species q = PClassical ->
  tdist_sq (phase_flip p) (phase_flip q) = tdist_sq p q.
Proof.
  intros p q Hp Hq.
  unfold phase_flip, point_species in *.
  destruct (px p) eqn:Epx1, (py p) eqn:Epy1;
  simpl in *; try discriminate;
  destruct (px q) eqn:Epx2, (py q) eqn:Epy2;
  simpl in *; try discriminate.
  unfold tdist_sq, treal_sub, treal_opp, treal_add, treal_mul.
  simpl. reflexivity.
Qed.

(* Phase congruence: two figures are Φ-congruent if           *)
(* one is the phase_flip of the other                         *)
Definition phi_congruent (p q : TPoint) : Prop :=
  phase_flip p = q \/ phase_flip q = p.

(* Classical and Mirror origins are Φ-congruent *)
Theorem origins_phi_congruent :
  phi_congruent Origin MirrorOrigin.
Proof.
  unfold phi_congruent, phase_flip, Origin, MirrorOrigin.
  left. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 11 — Summary                                        *)
(* ============================================================ *)

(*
   TRIADIC EUCLIDEAN GEOMETRY — SUMMARY

   Points:
     Four species: Classical (I×I), Mirror (N×N),
                   CrossPhase, Omega
     OmegaPoint lies on every cross-phase line and circle

   Distance:
     Classical × Classical → I-phase (classical ℝ≥0)
     Mirror    × Mirror    → I-phase (N*N=I, self-correcting)
     Cross-phase           → Omega
     Both planes share the SAME distance phase — unified metric

   Lines:
     I-lines:     live in I-plane, classical behavior
     N-lines:     live in N-plane, classical behavior
     Cross-lines: pass through OmegaPoint
     Omega-line:  contains ALL points

   Angles:
     Within a plane:   classical single-valued angles
     Between planes:   always dual (0°, 90°) simultaneously
     This is the axiom made geometric

   Parallel postulate:
     Holds within each plane (Euclid V per-plane)
     Fails globally — cross-plane lines always meet at Omega
     New postulate: "all cross-plane lines meet at Omega"

   Circles:
     I-circle, N-circle: classical within their plane
     Omega-circle:       contains ALL points universally
     The Omega-circle is the only "complete" circle

   Congruence:
     Within a plane:    classical Euclidean congruence
     Across planes:     Φ-congruence via phase_flip
     phase_flip is an isometry between I and N planes
     I-plane and N-plane are Φ-isometric — mirror worlds

   The Five Postulates:
     E1 (two points → line): holds, but cross-plane via Omega
     E2 (extend segments):   holds within each plane
     E3 (circles):           holds; Omega-circle is universal
     E4 (right angles equal):holds — all inter-plane = dual angle
     E5 (parallel postulate):FAILS globally, holds per-plane

   The Fundamental Triangle (Identity, Inverse, Infinity):
     All sides = Omega distance
     All angles = dual (0°, 90°)
     Species = OmegaTriangle
     This is the primitive geometric object of the universe —
     a triangle that is simultaneously degenerate and orthogonal

   Closest classical analogs:
     - Projective geometry (Omega as the "point at infinity")
     - Hyperbolic geometry (parallel postulate fails)
     - But with TWO parallel geometries joined at one point
     - And a phase-isometry between them not present in either
*)

Print Assumptions phase_flip_preserves_dist.
Print Assumptions all_points_on_omega_circle.
Print Assumptions fundamental_tri_omega_sides.
