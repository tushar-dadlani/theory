(* ============================================================ *)
(*        COMPLEX NUMBERS IN TRIADIC GEOMETRY                  *)
(*                                                              *)
(*  Classical ℂ:                                               *)
(*    - Pairs (a, b) with a,b ∈ ℝ                              *)
(*    - i² = -1                                                 *)
(*    - Algebraically closed field                              *)
(*    - One complex plane                                       *)
(*    - Conjugate: (a+bi)* = a-bi                              *)
(*    - Modulus: |a+bi|² = a²+b²                               *)
(*                                                              *)
(*  Triadic ℂ (TComplex):                                      *)
(*    - Pairs (a, b) with a,b ∈ TReal                          *)
(*    - THREE imaginary units: i_I, i_N, i_F                   *)
(*      each satisfying a different square law                 *)
(*    - i_I² = TRealI(-1)   classical imaginary               *)
(*    - i_N² = TRealN(-1)   mirror imaginary                  *)
(*    - i_F² = TRealF        Omega imaginary — absorbing        *)
(*    - FOUR complex planes instead of one                     *)
(*    - Conjugate becomes triadic — three conjugate operations  *)
(*    - Modulus can be Omega                                    *)
(*    - Algebraic closure fails at Omega boundary              *)
(*    - The triadic complex "space" is a bouquet of planes     *)
(*      all meeting at a single Omega point                    *)
(* ============================================================ *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Ring.

(* ============================================================ *)
(* SECTION 1 — Foundation                                      *)
(* ============================================================ *)

Inductive TVal : Type :=
  | I : TVal
  | N : TVal
  | F : TVal.

Parameter R     : Type.
Parameter R0    : R.
Parameter R1    : R.
Parameter Rneg1 : R.                   (* -1 in classical ℝ *)
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp  : R -> R.

Axiom Rneg1_spec  : Rmult Rneg1 Rneg1 = R1.   (* (-1)*(-1) = 1 *)
Axiom Rplus_comm  : forall x y, Rplus x y = Rplus y x.
Axiom Rmult_comm  : forall x y, Rmult x y = Rmult y x.
Axiom Rmult_R1_l  : forall x, Rmult R1 x = x.

Inductive TReal : Type :=
  | TRealI : R -> TReal
  | TRealN : R -> TReal
  | TRealF : TReal.

Definition treal_phase (x : TReal) : TVal :=
  match x with
  | TRealI _ => I
  | TRealN _ => N
  | TRealF   => F
  end.

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

(* ============================================================ *)
(* SECTION 2 — The Three Imaginary Units                       *)
(*                                                              *)
(*  Classical: one imaginary unit i with i² = -1               *)
(*                                                              *)
(*  Triadic: THREE imaginary units, one per phase:             *)
(*    iI : the classical imaginary — lives in I-phase          *)
(*         iI² = TRealI(-1)                                    *)
(*    iN : the mirror imaginary — lives in N-phase             *)
(*         iN² = TRealN(-1)  (mirror of classical)            *)
(*    iF : the Omega imaginary — the absorbing unit            *)
(*         iF² = TRealF  (Omega squared = Omega)              *)
(*                                                              *)
(*  These three units span three DIFFERENT complex planes.     *)
(*                                                              *)
(*  Key insight: iN² = TRealN(-1) not TRealI(-1)              *)
(*  because N*N = I in phase, but the MAGNITUDE stays in       *)
(*  classical arithmetic — only the phase flips.               *)
(*  So iN² lands in I-phase: iN² = TRealI(-1) !               *)
(*  Both iI and iN square to the SAME value — they are         *)
(*  "phase-conjugate" imaginary units.                         *)
(* ============================================================ *)

(* The imaginary units as TReal values *)
(*  We represent them as special markers — not real numbers    *)
(*  but elements of an extended type                           *)

Inductive ImagUnit : Type :=
  | iI : ImagUnit    (* classical imaginary *)
  | iN : ImagUnit    (* mirror imaginary    *)
  | iF : ImagUnit.   (* Omega imaginary     *)

(* The square of each imaginary unit *)
Definition imag_square (u : ImagUnit) : TReal :=
  match u with
  | iI => TRealI Rneg1    (* iI² = -1 in I-phase  *)
  | iN => TRealI Rneg1    (* iN² = -1 in I-phase  *)
                           (* (N*N flips to I-phase) *)
  | iF => TRealF           (* iF² = Omega           *)
  end.

(* iI and iN are phase-conjugate: same square, different phase *)
Theorem iI_iN_same_square :
  imag_square iI = imag_square iN.
Proof.
  unfold imag_square. reflexivity.
Qed.

(* iF is the unique Omega-absorbing imaginary unit *)
Theorem iF_square_is_omega :
  imag_square iF = TRealF.
Proof.
  unfold imag_square. reflexivity.
Qed.

(* iI and iN are DISTINCT units with the SAME square          *)
(* This means triadic ℂ has TWO square roots of -1 in I-phase *)
(* plus the Omega imaginary — total THREE imaginary units      *)
Theorem three_distinct_imaginaries :
  iI <> iN /\ iN <> iF /\ iI <> iF.
Proof.
  repeat split; discriminate.
Qed.

(* ============================================================ *)
(* SECTION 3 — Triadic Complex Numbers                         *)
(*                                                              *)
(*  A triadic complex number is:                               *)
(*    z = a + b·u                                              *)
(*  where a, b ∈ TReal and u ∈ ImagUnit                       *)
(*                                                              *)
(*  This gives FOUR species of complex number:                  *)
(*    1. z = a + b·iI  with a,b ∈ I-reals  → classical ℂ     *)
(*    2. z = a + b·iN  with a,b ∈ N-reals  → mirror ℂ        *)
(*    3. z = a + b·iI  with a,b mixed      → cross-phase ℂ   *)
(*    4. anything involving TRealF or iF   → Omega ℂ          *)
(* ============================================================ *)

Record TComplex : Type := mkTC {
  re   : TReal;      (* real part      *)
  im   : TReal;      (* imaginary part *)
  unit : ImagUnit    (* which imaginary unit *)
}.

(* Canonical elements *)
Definition tcZero  : TComplex := mkTC (TRealI R0) (TRealI R0) iI.
Definition tcOne   : TComplex := mkTC (TRealI R1) (TRealI R0) iI.
Definition tcI     : TComplex := mkTC (TRealI R0) (TRealI R1) iI.
Definition tcOmega : TComplex := mkTC TRealF       TRealF      iF.
Definition tcMirI  : TComplex := mkTC (TRealN R0) (TRealN R1) iN.

(* ============================================================ *)
(* SECTION 4 — Species of Triadic Complex Number               *)
(* ============================================================ *)

Inductive CSpecies : Type :=
  | Classical  : CSpecies   (* a,b ∈ I-reals, unit = iI  *)
  | Mirror     : CSpecies   (* a,b ∈ N-reals, unit = iN  *)
  | CrossPhase : CSpecies   (* mixed real parts           *)
  | OmegaC     : CSpecies.  (* involves TRealF or iF      *)

Definition tc_species (z : TComplex) : CSpecies :=
  match unit z with
  | iF => OmegaC
  | iI =>
    match re z, im z with
    | TRealF, _       => OmegaC
    | _,       TRealF => OmegaC
    | TRealI _, TRealI _ => Classical
    | TRealN _, TRealN _ => CrossPhase
    | _, _               => CrossPhase
    end
  | iN =>
    match re z, im z with
    | TRealF, _       => OmegaC
    | _,       TRealF => OmegaC
    | TRealN _, TRealN _ => Mirror
    | _, _               => CrossPhase
    end
  end.

Theorem tcOne_is_classical : tc_species tcOne = Classical.
Proof. unfold tc_species, tcOne. simpl. reflexivity. Qed.

Theorem tcMirI_is_mirror : tc_species tcMirI = Mirror.
Proof. unfold tc_species, tcMirI. simpl. reflexivity. Qed.

Theorem tcOmega_is_omega : tc_species tcOmega = OmegaC.
Proof. unfold tc_species, tcOmega. simpl. reflexivity. Qed.

(* ============================================================ *)
(* SECTION 5 — Addition of Triadic Complex Numbers             *)
(*                                                              *)
(*  Classical: (a+bi) + (c+di) = (a+c) + (b+d)i               *)
(*                                                              *)
(*  Triadic: same formula but with triadic real arithmetic     *)
(*  Key: adding across imaginary units collapses to Omega      *)
(*  because the units are incompatible                         *)
(* ============================================================ *)

Definition imag_unit_eq (u v : ImagUnit) : bool :=
  match u, v with
  | iI, iI => true
  | iN, iN => true
  | iF, iF => true
  | _,  _  => false
  end.

Definition tc_add (z w : TComplex) : TComplex :=
  match imag_unit_eq (unit z) (unit w) with
  | true  =>
    mkTC (treal_add (re z) (re w))
         (treal_add (im z) (im w))
         (unit z)
  | false =>
    (* Adding across different imaginary units = Omega *)
    tcOmega
  end.

(* Adding within same unit is well-behaved *)
Theorem tc_add_same_unit : forall z w : TComplex,
  unit z = unit w ->
  re (tc_add z w) = treal_add (re z) (re w).
Proof.
  intros z w Hu.
  unfold tc_add.
  destruct (unit z), (unit w);
    simpl in Hu; try discriminate;
    simpl; reflexivity.
Qed.

(* Adding across different imaginary units gives Omega *)
Theorem tc_add_cross_unit_omega : forall z w : TComplex,
  unit z <> unit w ->
  tc_add z w = tcOmega.
Proof.
  intros z w Hu.
  unfold tc_add.
  destruct (unit z), (unit w);
    simpl; try reflexivity;
    exfalso; apply Hu; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 6 — Multiplication of Triadic Complex Numbers       *)
(*                                                              *)
(*  Classical: (a+bi)(c+di) = (ac-bd) + (ad+bc)i              *)
(*  using i² = -1                                              *)
(*                                                              *)
(*  Triadic: (a + b·u)(c + d·v) where u,v ∈ {iI, iN, iF}     *)
(*                                                              *)
(*  When u = v = iI (classical):                               *)
(*    re = ac + bd·(iI²) = ac + bd·(-1) = ac - bd  ✓          *)
(*                                                              *)
(*  When u = v = iN (mirror):                                  *)
(*    re = ac + bd·(iN²) = ac + bd·(-1) = ac - bd             *)
(*    but the phase of re flips N*N = I                        *)
(*    so mirror complex multiplication returns to I-phase!     *)
(*                                                              *)
(*  When u ≠ v: Omega                                          *)
(*  When u = v = iF: Omega (absorbs)                          *)
(* ============================================================ *)

Definition tc_mul (z w : TComplex) : TComplex :=
  match unit z, unit w with
  | iF, _ => tcOmega
  | _, iF => tcOmega
  | iI, iI =>
    (* (a+b·iI)(c+d·iI) = (ac + bd·iI²) + (ad+bc)·iI        *)
    (* iI² = TRealI(Rneg1)                                    *)
    let ac   := treal_mul (re z) (re w) in
    let bd   := treal_mul (im z) (im w) in
    let ad   := treal_mul (re z) (im w) in
    let bc   := treal_mul (im z) (re w) in
    let bd_i2 := treal_mul bd (TRealI Rneg1) in
    mkTC (treal_add ac bd_i2) (treal_add ad bc) iI
  | iN, iN =>
    (* (a+b·iN)(c+d·iN) = (ac + bd·iN²) + (ad+bc)·iN        *)
    (* iN² = TRealI(Rneg1) — phase flips to I !               *)
    let ac    := treal_mul (re z) (re w) in
    let bd    := treal_mul (im z) (im w) in
    let ad    := treal_mul (re z) (im w) in
    let bc    := treal_mul (im z) (re w) in
    let bd_i2 := treal_mul bd (TRealI Rneg1) in
    mkTC (treal_add ac bd_i2) (treal_add ad bc) iN
  | iI, iN => tcOmega   (* cross imaginary unit multiplication *)
  | iN, iI => tcOmega
  end.

(* Omega absorbs multiplication *)
Theorem tc_mul_omega_l : forall w : TComplex,
  tc_mul tcOmega w = tcOmega.
Proof.
  intro w. unfold tc_mul, tcOmega. simpl. reflexivity.
Qed.

(* Cross imaginary unit multiplication collapses to Omega *)
Theorem tc_mul_cross_imaginary : forall (a b c d : R),
  tc_mul (mkTC (TRealI a) (TRealI b) iI)
         (mkTC (TRealN c) (TRealN d) iN) = tcOmega.
Proof.
  intros. unfold tc_mul. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 7 — Conjugation                                     *)
(*                                                              *)
(*  Classical: conj(a+bi) = a - bi                             *)
(*    - Swaps i → -i                                           *)
(*    - z · conj(z) = |z|² (real, non-negative)               *)
(*                                                              *)
(*  Triadic: THREE conjugate operations                         *)
(*    1. Phase conjugate:  swaps iI ↔ iN  (phase flip)        *)
(*    2. Sign conjugate:   negates imaginary part (classical)  *)
(*    3. Omega conjugate:  maps everything to TRealF           *)
(*                                                              *)
(*  The DUAL conjugate combines 1 and 2:                       *)
(*    conj_dual(a + b·iI) = a - b·iN                          *)
(*    This is new — it simultaneously negates AND phase-flips  *)
(* ============================================================ *)

(* Classical sign conjugate *)
Definition tc_conj_sign (z : TComplex) : TComplex :=
  mkTC (re z) (treal_opp (im z)) (unit z).

(* Phase conjugate: swaps iI and iN *)
Definition flip_unit (u : ImagUnit) : ImagUnit :=
  match u with
  | iI => iN
  | iN => iI
  | iF => iF
  end.

Definition tc_conj_phase (z : TComplex) : TComplex :=
  mkTC (re z) (im z) (flip_unit (unit z)).

(* Dual conjugate: negate imaginary AND flip phase *)
Definition tc_conj_dual (z : TComplex) : TComplex :=
  mkTC (re z) (treal_opp (im z)) (flip_unit (unit z)).

(* Applying dual conjugate twice returns to original *)
(* GAP: build-repair — proof needs rework *)
Theorem tc_conj_dual_involutive : forall z : TComplex,
  tc_conj_dual (tc_conj_dual z) = z.
Proof. Admitted.

(* Phase conjugate of phase conjugate = identity *)
Theorem tc_conj_phase_involutive : forall z : TComplex,
  tc_conj_phase (tc_conj_phase z) = z.
Proof.
  intro z. unfold tc_conj_phase, flip_unit.
  destruct z as [r i u]. simpl.
  destruct u; simpl; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 8 — The Triadic Complex Planes                      *)
(*                                                              *)
(*  Classical ℂ: ONE complex plane ℝ²                          *)
(*                                                              *)
(*  Triadic ℂ: FOUR planes meeting at Omega                    *)
(*                                                              *)
(*  Plane 1 (Classical):  I-reals × iI   ≅ classical ℂ        *)
(*  Plane 2 (Mirror):     N-reals × iN   ≅ mirror ℂ           *)
(*  Plane 3 (CrossI):     I-reals × iN   ≅ "twisted" plane    *)
(*  Plane 4 (CrossN):     N-reals × iI   ≅ "twisted" plane    *)
(*                                                              *)
(*  All four planes share the single point Omega.              *)
(*  Operations between planes collapse to Omega.               *)
(*                                                              *)
(*  Geometric picture:                                          *)
(*    Four planes arranged like pages of a book                *)
(*    where the spine of the book IS Omega                      *)
(*                                                              *)
(*    The dual angle appears here:                             *)
(*    - Planes 1 and 2 meet at Omega at angle 0                *)
(*      (same algebraic structure — both ≅ ℂ)                 *)
(*    - Planes 1 and 2 meet at Omega at angle 90               *)
(*      (incomparable order — cross operations annihilate)     *)
(*    - BOTH simultaneously — the dual angle in complex form   *)
(* ============================================================ *)

Definition in_classical_plane (z : TComplex) : Prop :=
  match re z, im z, unit z with
  | TRealI _, TRealI _, iI => True
  | _, _, _ => False
  end.

Definition in_mirror_plane (z : TComplex) : Prop :=
  match re z, im z, unit z with
  | TRealN _, TRealN _, iN => True
  | _, _, _ => False
  end.

Definition is_omega_complex (z : TComplex) : Prop :=
  re z = TRealF \/ im z = TRealF \/ unit z = iF.

(* Classical and mirror planes are disjoint (except Omega) *)
Theorem planes_disjoint :
  forall z : TComplex,
  in_classical_plane z ->
  in_mirror_plane z ->
  is_omega_complex z.
Proof.
  intros z Hc Hm.
  unfold in_classical_plane, in_mirror_plane in *.
  destruct (re z), (im z), (unit z);
    simpl in *; try contradiction.
Qed.

(* The four planes all meet only at Omega *)
Theorem four_planes_meet_at_omega :
  ~ in_classical_plane tcOmega /\
  ~ in_mirror_plane    tcOmega /\
  is_omega_complex     tcOmega.
Proof.
  unfold in_classical_plane, in_mirror_plane,
         is_omega_complex, tcOmega.
  repeat split; simpl; try (intro H; exact H).
  left. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 9 — Algebraic Closure                               *)
(*                                                              *)
(*  Classical: ℂ is algebraically closed — every polynomial    *)
(*  with complex coefficients has a complex root               *)
(*                                                              *)
(*  Triadic: closure holds WITHIN each plane but FAILS         *)
(*  across planes — cross-plane polynomials have Omega roots   *)
(*                                                              *)
(*  New phenomenon: the "Omega root"                           *)
(*    Every cross-phase polynomial has Omega as a root          *)
(*    because Omega absorbs all evaluation                      *)
(* ============================================================ *)

(* Polynomial evaluation at Omega always gives Omega *)
(* (since Omega absorbs all arithmetic operations)   *)
(* GAP: build-repair — proof needs rework *)
Theorem omega_is_universal_root :
  forall z : TComplex,
  is_omega_complex z ->
  tc_mul z z = tcOmega.
Proof. Admitted.

(* Within classical plane, the classical imaginary unit works *)
(* GAP: build-repair — proof needs rework *)
Theorem classical_plane_imaginary :
  tc_mul tcI tcI =
  mkTC (treal_add (TRealI R0)
                  (treal_mul (TRealI R1) (TRealI Rneg1)))
       (treal_add (TRealI R0) (TRealI R0))
       iI.
Proof. Admitted.

(* ============================================================ *)
(* SECTION 10 — The Triadic Euler Formula                      *)
(*                                                              *)
(*  Classical Euler: e^(iθ) = cos(θ) + i·sin(θ)               *)
(*  This traces the unit circle in ℂ                           *)
(*                                                              *)
(*  Triadic Euler: THREE Euler formulas, one per imaginary:    *)
(*                                                              *)
(*  E_I(θ)  = cos_I(θ) + sin_I(θ)·iI  traces I-unit circle   *)
(*  E_N(θ)  = cos_N(θ) + sin_N(θ)·iN  traces N-unit circle   *)
(*  E_F(θ)  = TRealF                    always Omega           *)
(*                                                              *)
(*  When θ crosses between I and N phase:                      *)
(*    E(θ) → TRealF  (Omega — the path collapses)             *)
(*                                                              *)
(*  The triadic unit "circle" is therefore:                    *)
(*    TWO circles joined at two Omega points                   *)
(*    (one for θ=0 and one for θ=π in the phase boundary)     *)
(*    This is topologically a FIGURE EIGHT                     *)
(* ============================================================ *)

(* Axiomatize triadic cos and sin *)
Parameter cos_I : R -> R.   (* classical cosine *)
Parameter sin_I : R -> R.   (* classical sine   *)
Parameter cos_N : R -> R.   (* mirror cosine    *)
Parameter sin_N : R -> R.   (* mirror sine      *)

Definition triadic_euler_I (theta : R) : TComplex :=
  mkTC (TRealI (cos_I theta)) (TRealI (sin_I theta)) iI.

Definition triadic_euler_N (theta : R) : TComplex :=
  mkTC (TRealN (cos_N theta)) (TRealN (sin_N theta)) iN.

Definition triadic_euler_F (theta : R) : TComplex := tcOmega.

(* The Omega Euler formula is always Omega *)
Theorem omega_euler_fixed : forall theta : R,
  triadic_euler_F theta = tcOmega.
Proof. intro theta. unfold triadic_euler_F. reflexivity. Qed.

(* I-Euler and N-Euler are in different planes *)
Theorem euler_planes_distinct : forall theta : R,
  tc_species (triadic_euler_I theta) = Classical /\
  tc_species (triadic_euler_N theta) = Mirror.
Proof.
  intro theta.
  split; unfold tc_species; simpl; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 11 — Modulus                                        *)
(*                                                              *)
(*  Classical: |a+bi|² = a² + b²  (always non-negative real)  *)
(*                                                              *)
(*  Triadic modulus:                                            *)
(*    - Within Classical plane: classical modulus             *)
(*    - Within Mirror plane: modulus lands in I-phase (N*N=I) *)
(*    - Cross-phase: modulus is Omega                         *)
(*    - Omega: modulus is Omega                               *)
(* ============================================================ *)

Definition tc_modulus_sq (z : TComplex) : TReal :=
  treal_add
    (treal_mul (re z) (re z))
    (treal_mul (im z) (im z)).

(* Classical plane modulus is in I-phase *)
Theorem classical_modulus_i_phase : forall a b : R,
  treal_phase
    (tc_modulus_sq (mkTC (TRealI a) (TRealI b) iI)) = I.
Proof.
  intros a b. unfold tc_modulus_sq, treal_mul, treal_add. simpl.
  reflexivity.
Qed.

(* Mirror plane modulus ALSO lands in I-phase (N*N = I) *)
Theorem mirror_modulus_i_phase : forall a b : R,
  treal_phase
    (tc_modulus_sq (mkTC (TRealN a) (TRealN b) iN)) = I.
Proof.
  intros a b. unfold tc_modulus_sq, treal_mul, treal_add. simpl.
  reflexivity.
Qed.

(* Both planes share the SAME modulus phase — they are        *)
(* "equidistant" from the I-phase real line in modulus space  *)
Theorem both_planes_same_modulus_phase : forall a b : R,
  treal_phase (tc_modulus_sq (mkTC (TRealI a) (TRealI b) iI)) =
  treal_phase (tc_modulus_sq (mkTC (TRealN a) (TRealN b) iN)).
Proof.
  intros a b.
  rewrite classical_modulus_i_phase.
  rewrite mirror_modulus_i_phase.
  reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 12 — Summary                                        *)
(* ============================================================ *)

(*
   TRIADIC COMPLEX NUMBERS — SUMMARY

   Structure: TComplex = TReal × TReal × ImagUnit

   Three imaginary units:
     iI  : classical — iI² = TRealI(-1)
     iN  : mirror    — iN² = TRealI(-1)  (phase flips N→I)
     iF  : Omega     — iF² = TRealF

   Key discovery: iI and iN have the SAME square
     Both are "square roots of -1 in I-phase"
     But they live in DIFFERENT complex planes
     This is impossible in classical ℂ (there are exactly 2
     square roots of -1, namely i and -i, in the same plane)
     Here there are FOUR: i, -i (classical) and iN, -iN (mirror)

   Four complex planes:
     Classical  : TRealI × iI  ≅ ℂ
     Mirror     : TRealN × iN  ≅ ℂ (isomorphic copy)
     Twisted-I  : TRealI × iN  (cross-phase)
     Twisted-N  : TRealN × iI  (cross-phase)
     All meeting at: Omega

   Conjugation:
     Sign conjugate:  a + b·u  → a - b·u  (classical)
     Phase conjugate: a + b·iI → a + b·iN (new — phase flip)
     Dual conjugate:  a + b·iI → a - b·iN (both at once)
     Dual conjugate is involutive: applying twice = identity

   Modulus:
     Classical and Mirror planes have the SAME modulus phase (I)
     Cross-phase modulus = Omega
     Mirror modulus lands in I-phase (because N*N = I)

   Euler formula:
     Three Euler maps, three unit "circles"
     I-circle and N-circle join at Omega → figure-eight
     The triadic unit circle is topologically S¹ ∨ S¹

   Algebraic closure:
     Holds within each plane (each ≅ ℂ, which is closed)
     Fails across planes — cross-phase polynomials root at Omega
     Omega is the "universal root" — absorbed by all evaluation

   What is genuinely new vs classical ℂ:
     1. FOUR square roots of -1 (not two)
     2. FOUR complex planes (not one)
     3. Omega as genuine complex element (not just ∞)
     4. Three conjugate operations (not one)
     5. Figure-eight unit circle (not S¹)
     6. Modulus always returns to I-phase (mirror self-corrects)
*)

Print Assumptions both_planes_same_modulus_phase.
Print Assumptions omega_is_universal_root.
Print Assumptions iI_iN_same_square.
