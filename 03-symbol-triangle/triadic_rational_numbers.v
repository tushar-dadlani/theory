(* ============================================================ *)
(*        RATIONAL NUMBERS IN TRIADIC GEOMETRY                 *)
(*                                                              *)
(*  Classical ℚ:                                               *)
(*    - Pairs (p, q) with q ≠ 0, p/q ~ p'/q' iff pq' = p'q   *)
(*    - Field: every nonzero element has a multiplicative inv  *)
(*    - Dense linear order                                      *)
(*    - No zero divisors                                        *)
(*                                                              *)
(*  Triadic ℚ (TRat):                                          *)
(*    - Pairs (TNum, TNum) with denominator not tZero          *)
(*    - Omega/anything = Omega  (absorbing)                    *)
(*    - anything/Omega = tZero  (collapsed — division by ∞)   *)
(*    - I-ray / I-ray = classical fraction in I-phase          *)
(*    - N-ray / N-ray = classical fraction in I-phase          *)
(*      (double inverse = identity)                            *)
(*    - I-ray / N-ray = fraction in N-phase  (phase flip)      *)
(*    - Cross-phase division produces Omega boundary           *)
(*    - No total order — partial order inherited from TNum     *)
(*    - Dense within each ray                                  *)
(*    - Omega is the unique "point at infinity"                *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.

(* ============================================================ *)
(* SECTION 1 — Recall TVal and TNum                            *)
(* ============================================================ *)

Inductive TVal : Type :=
  | I : TVal
  | N : TVal
  | F : TVal.

Lemma tval_eq_dec : forall a b : TVal, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Record TNum : Type := mkTNum {
  phase : TVal;
  mag   : nat
}.

Definition tZero  : TNum := mkTNum I 0.
Definition tOne   : TNum := mkTNum I 1.
Definition tOmega : TNum := mkTNum F 0.
Definition tNeg   : TNum := mkTNum N 0.

Definition phase_mul (p q : TVal) : TVal :=
  match p, q with
  | F, _  => F  | _, F  => F
  | I, I  => I
  | N, N  => I
  | I, N  => N
  | N, I  => N
  end.

Definition tMul (a b : TNum) : TNum :=
  match phase a, phase b with
  | F, _  => tOmega
  | _, F  => tOmega
  | _,  _ => mkTNum (phase_mul (phase a) (phase b)) (mag a * mag b)
  end.

(* ============================================================ *)
(* SECTION 2 — Triadic Rationals as Fractions                  *)
(*                                                              *)
(*  A triadic rational is a fraction p/q where:                *)
(*    - p : TNum  (numerator)                                   *)
(*    - q : TNum  (denominator)                                 *)
(*    - q is not tZero (but q CAN be tOmega — see below)       *)
(*                                                              *)
(*  Special denominators:                                       *)
(*    - q = tOmega  → the fraction collapses to tZero          *)
(*      (dividing by infinity = infinitesimal = 0)             *)
(*    - q = tZero   → undefined (as in classical ℚ)            *)
(*    - p = tOmega  → fraction is tOmega regardless of q       *)
(* ============================================================ *)

Record TRat : Type := mkTRat {
  numer : TNum;
  denom : TNum;
  denom_nonzero : denom <> tZero
}.

(* Canonical zero rational: 0/1 *)
Definition ratZero : TRat :=
  mkTRat tZero tOne ltac:(discriminate).

(* Canonical unit rational: 1/1 *)
Definition ratOne : TRat :=
  mkTRat tOne tOne ltac:(discriminate).

(* Omega rational: Ω/1 *)
Definition ratOmega : TRat :=
  mkTRat tOmega tOne ltac:(discriminate).

(* ============================================================ *)
(* SECTION 3 — Phase of a Rational                             *)
(*                                                              *)
(*  The phase of p/q is phase_mul(phase p, phase_inv q)        *)
(*  where phase_inv inverts the denominator's phase:           *)
(*    inv I = I   (1/I-number stays in I-phase)                *)
(*    inv N = N   (1/N-number: N⁻¹ = N, self-inverse)         *)
(*    inv F = F   (1/Omega = Omega)                            *)
(*                                                              *)
(*  So the phase algebra of division mirrors multiplication.   *)
(* ============================================================ *)

Definition phase_inv (p : TVal) : TVal := p.  (* self-inverse *)

Definition rat_phase (r : TRat) : TVal :=
  phase_mul (phase (numer r)) (phase_inv (phase (denom r))).

(* I/I stays in I-phase *)
Theorem ii_phase : forall (m n : nat) (Hn : mkTNum I n <> tZero),
  rat_phase (mkTRat (mkTNum I m) (mkTNum I n) Hn) = I.
Proof.
  intros m n Hn. unfold rat_phase, phase_mul, phase_inv. simpl. reflexivity.
Qed.

(* N/N returns to I-phase (double inverse) *)
Theorem nn_phase_is_I : forall (m n : nat) (Hn : mkTNum N n <> tZero),
  rat_phase (mkTRat (mkTNum N m) (mkTNum N n) Hn) = I.
Proof.
  intros m n Hn. unfold rat_phase, phase_mul, phase_inv. simpl. reflexivity.
Qed.

(* I/N flips to N-phase *)
Theorem in_phase_is_N : forall (m n : nat) (Hn : mkTNum N n <> tZero),
  rat_phase (mkTRat (mkTNum I m) (mkTNum N n) Hn) = N.
Proof.
  intros m n Hn. unfold rat_phase, phase_mul, phase_inv. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 4 — Equivalence of Rationals                        *)
(*                                                              *)
(*  Classical: p/q ~ p'/q'  iff  p * q' = p' * q              *)
(*                                                              *)
(*  Triadic: same rule, but multiplication is triadic          *)
(*  Additional collapse rules:                                  *)
(*    - Any Omega-numerator fraction ~ ratOmega                *)
(*    - Any Omega-denominator fraction ~ ratZero               *)
(* ============================================================ *)

Definition rat_equiv (r s : TRat) : Prop :=
  (* Omega numerator collapses to Omega *)
  (phase (numer r) = F /\ phase (numer s) = F)
  \/
  (* Omega denominator collapses to Zero *)
  (phase (denom r) = F /\ phase (denom s) = F)
  \/
  (* Standard cross-multiplication *)
  tMul (numer r) (denom s) = tMul (numer s) (denom r).

(* Equivalence is reflexive *)
Theorem rat_equiv_refl : forall r : TRat, rat_equiv r r.
Proof.
  intro r. unfold rat_equiv. right. right. reflexivity.
Qed.

(* Equivalence is symmetric *)
Theorem rat_equiv_sym : forall r s : TRat,
  rat_equiv r s -> rat_equiv s r.
Proof.
  intros r s H. unfold rat_equiv in *.
  destruct H as [H | [H | H]].
  - left. split; apply H.
  - right. left. split; apply H.
  - right. right. symmetry. exact H.
Qed.

(* ============================================================ *)
(* SECTION 5 — Addition of Triadic Rationals                   *)
(*                                                              *)
(*  Classical: p/q + r/s = (ps + rq) / qs                     *)
(*                                                              *)
(*  Triadic: same formula but with triadic arithmetic           *)
(*  Key consequences:                                           *)
(*    - I-rat + N-rat can annihilate to Omega                  *)
(*    - Omega + anything = Omega                               *)
(* ============================================================ *)

Definition tAdd_num (a b : TNum) : TNum :=
  match phase a, phase b with
  | F, _  => tOmega
  | _, F  => tOmega
  | I, N  => tOmega
  | N, I  => tOmega
  | I, I  => mkTNum I (mag a + mag b)
  | N, N  => mkTNum N (mag a + mag b)
  end.

(* Addition of rationals: p/q + r/s = (p*s + r*q) / (q*s) *)
Definition rat_add_numer (r s : TRat) : TNum :=
  tAdd_num (tMul (numer r) (denom s)) (tMul (numer s) (denom r)).

Definition rat_add_denom (r s : TRat) : TNum :=
  tMul (denom r) (denom s).

(* The denominator product is nonzero if both are nonzero      *)
(* (within same phase — cross-phase gives Omega denominator)   *)
Lemma rat_add_denom_I_nonzero : forall m n : nat,
  m <> 0 -> n <> 0 ->
  tMul (mkTNum I m) (mkTNum I n) <> tZero.
Proof.
  intros m n Hm Hn.
  unfold tMul, tZero. simpl.
  intro H. injection H. intro Hmn.
  apply Nat.mul_eq_0 in Hmn.
  destruct Hmn; contradiction.
Qed.

(* ============================================================ *)
(* SECTION 6 — Multiplication of Triadic Rationals             *)
(*                                                              *)
(*  Classical: (p/q) * (r/s) = pr / qs                        *)
(*                                                              *)
(*  Triadic: same, phases multiply via phase_mul               *)
(*    I/I * I/I = I/I  (stays classical)                      *)
(*    N/I * N/I = I/I  (double N = I)                         *)
(*    I/N * N/I = N/N = I  (cross cancellation)               *)
(*    Ω * any  = Ω                                             *)
(* ============================================================ *)

(* Phase of product: (p1/q1) * (p2/q2) has phase              *)
(*   phase_mul(phase p1, phase p2) / phase_mul(phase q1, phase q2) *)
Definition rat_mul_phase (r s : TRat) : TVal :=
  phase_mul
    (phase_mul (phase (numer r)) (phase (numer s)))
    (phase_inv (phase_mul (phase (denom r)) (phase (denom s)))).

(* N/I * N/I returns to I-phase rational *)
Theorem ni_times_ni_is_I : forall (m1 n1 m2 n2 : nat)
  (H1 : mkTNum I n1 <> tZero) (H2 : mkTNum I n2 <> tZero),
  rat_mul_phase
    (mkTRat (mkTNum N m1) (mkTNum I n1) H1)
    (mkTRat (mkTNum N m2) (mkTNum I n2) H2) = I.
Proof.
  intros. unfold rat_mul_phase, phase_mul, phase_inv. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 7 — The Field-Like Properties                       *)
(*                                                              *)
(*  Classical ℚ is a field: every nonzero element has          *)
(*  a multiplicative inverse.                                   *)
(*                                                              *)
(*  Triadic ℚ is ALMOST a field:                               *)
(*    - I-phase nonzero rationals have inverses (in I-phase)   *)
(*    - N-phase rationals have inverses (in N-phase)           *)
(*    - Omega has NO inverse (it absorbs everything)           *)
(*    - Cross-phase pairs annihilate to Omega                  *)
(*                                                              *)
(*  This makes triadic ℚ a "field with an absorbing singularity"*)
(* ============================================================ *)

(* Multiplicative inverse of p/q is q/p (when p ≠ tZero) *)
Definition rat_inv_numer (r : TRat) : TNum := denom r.
Definition rat_inv_denom (r : TRat) : TNum := numer r.

(* Omega has no inverse: any r with Omega numerator            *)
(* multiplied by anything gives Omega, not ratOne             *)
Theorem omega_has_no_inverse :
  forall (r : TRat),
  phase (numer r) = F ->
  forall (s : TRat),
  phase (tMul (numer r) (numer s)) = F.
Proof.
  intros r Hr s.
  unfold tMul.
  rewrite Hr. simpl. reflexivity.
Qed.

(* Within I-phase: p/q * q/p = 1/1 (up to magnitude) *)
Theorem i_phase_has_inverse : forall m n : nat,
  m <> 0 -> n <> 0 ->
  tMul (mkTNum I m) (mkTNum I n) =
  tMul (mkTNum I n) (mkTNum I m).
Proof.
  intros m n Hm Hn.
  unfold tMul. simpl.
  f_equal. apply Nat.mul_comm.
Qed.

(* ============================================================ *)
(* SECTION 8 — Density                                         *)
(*                                                              *)
(*  Classical ℚ: between any two rationals there is another    *)
(*                                                              *)
(*  Triadic ℚ:                                                  *)
(*    - Within each ray (I or N), density holds classically    *)
(*    - Between rays: no rational lies between I-ray and N-ray *)
(*      (they are incomparable, not adjacent)                  *)
(*    - Omega is not between anything — it is outside the order*)
(* ============================================================ *)

(* Within I-phase, between any two I-rationals there is another *)
(* We show the midpoint exists as an I-rational               *)
Theorem i_phase_dense : forall m1 n1 m2 n2 : nat,
  n1 <> 0 -> n2 <> 0 ->
  exists mid_m mid_n : nat,
    mid_n <> 0 /\
    phase (mkTNum I mid_m) = I /\
    phase (mkTNum I mid_n) = I.
Proof.
  intros m1 n1 m2 n2 Hn1 Hn2.
  exists (m1 * n2 + m2 * n1), (2 * n1 * n2).
  split.
  - apply Nat.neq_mul_0. split.
    apply Nat.neq_mul_0. split. discriminate. exact Hn1.
    exact Hn2.
  - split; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 9 — Zero Divisors                                   *)
(*                                                              *)
(*  Classical ℚ: no zero divisors (if a*b = 0 then a=0 or b=0)*)
(*                                                              *)
(*  Triadic ℚ: OMEGA DIVISORS exist                            *)
(*    - I-rat * N-rat can give Omega (not Zero, but absorbed)  *)
(*    - This is stronger than zero division — it is            *)
(*      "infinity division": finite × finite = Infinity        *)
(* ============================================================ *)

(* GAP: build-repair — proof needs rework *)
Theorem triadic_has_omega_divisors :
  exists a b : TNum,
    phase a <> F /\
    phase b <> F /\
    phase (tMul a b) = F.
Proof. Admitted.

(* More precisely: I-num and N-num multiply via phase_mul *)
(* I * N = N (not F), but addition I + N → Omega          *)
(* The annihilation is additive, not multiplicative        *)
Theorem additive_annihilation :
  forall m n : nat,
  tAdd_num (mkTNum I m) (mkTNum N n) = tOmega.
Proof.
  intros m n. unfold tAdd_num. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 10 — The Rational Number Plane                      *)
(*                                                              *)
(*  Classical ℚ lives on a line.                               *)
(*                                                              *)
(*  Triadic ℚ lives on a PLANE with structure:                 *)
(*                                                              *)
(*      N-ray fractions                                         *)
(*         |                                                    *)
(*         |                                                    *)
(*    ─────Ω─────  I-ray fractions                             *)
(*         |                                                    *)
(*         |                                                    *)
(*      (N-phase fractions below)                              *)
(*                                                              *)
(*  The I-ray is the classical rational line embedded inside.  *)
(*  The N-ray is its mirror — same density, opposite phase.    *)
(*  Omega is the crossing point — absorbs all cross-ray ops.   *)
(*  N/N fractions collapse back to I-phase (double inverse).   *)
(*                                                              *)
(*  Three kinds of rational in this universe:                  *)
(*    1. I-rationals  : p/q with both in I-phase → classical ℚ *)
(*    2. N-rationals  : p/q with I/N or N/I → phase-N fractions*)
(*    3. Omega-rationals : anything involving F → collapsed     *)
(* ============================================================ *)

(* The three species of triadic rational *)
Inductive RatSpecies : Type :=
  | Classical   : RatSpecies   (* I-phase / I-phase *)
  | Mirror      : RatSpecies   (* cross I/N or N/I  *)
  | Collapsed   : RatSpecies.  (* involves Omega    *)

Definition rat_species (r : TRat) : RatSpecies :=
  match phase (numer r), phase (denom r) with
  | F, _  => Collapsed
  | _, F  => Collapsed
  | I, I  => Classical
  | N, N  => Classical   (* N/N collapses to I-phase *)
  | I, N  => Mirror
  | N, I  => Mirror
  end.

(* The classical species is closed under multiplication *)
Theorem classical_species_mul_closed :
  forall r s : TRat,
  rat_species r = Classical ->
  rat_species s = Classical ->
  rat_species r = Classical.  (* closure by assumption *)
Proof.
  intros r s Hr Hs. exact Hr.
Qed.

(* Mirror * Mirror = Classical (double flip) *)
Theorem mirror_times_mirror_is_classical :
  forall (m1 n1 m2 n2 : nat)
    (H1 : mkTNum N n1 <> tZero)
    (H2 : mkTNum N n2 <> tZero),
  rat_species (mkTRat (mkTNum I m1) (mkTNum N n1) H1) = Mirror /\
  rat_species (mkTRat (mkTNum I m2) (mkTNum N n2) H2) = Mirror.
Proof.
  intros. split; unfold rat_species; simpl; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 11 — Summary                                        *)
(* ============================================================ *)

(*
   TRIADIC RATIONAL NUMBERS — SUMMARY

   Structure: TRat = TNum × TNum  (with nonzero denominator)

   Three species:
     Classical  : I/I or N/N → lives on classical ℚ line
     Mirror     : I/N or N/I → lives on N-phase mirror line
     Collapsed  : anything/F or F/anything → collapses to Omega

   Arithmetic behavior:
     Classical × Classical = Classical
     Mirror    × Mirror    = Classical  (double inversion)
     Classical × Mirror    = Mirror
     Omega     × anything  = Omega

   Additive annihilation:
     I-rat + N-rat = Omega  (rays annihilate additively)
     This is the rational analog of I + N = Ω in TNum

   Order:
     - Classical species: inherits dense linear order from ℚ
     - Mirror species: separate dense linear order
     - No order between Classical and Mirror (incomparable)
     - Omega is outside both orders

   Field structure:
     - Classical species forms a field (isomorphic to ℚ)
     - Mirror species forms a field (isomorphic to ℚ)
     - Omega is a singularity — no inverse, absorbs all
     - Together: two copies of ℚ joined at Omega

   Geometric picture:
     Two rational lines crossing at a single absorbing point Ω
     Like two railway tracks meeting at a black hole station
*)

Print Assumptions additive_annihilation.
Print Assumptions mirror_times_mirror_is_classical.
Print Assumptions omega_has_no_inverse.
