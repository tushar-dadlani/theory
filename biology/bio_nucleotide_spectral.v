(* ============================================================ *)
(*  Nucleotide Spectral Triple — Level -1 of the Dirac Tower    *)
(*                                                                *)
(*  The 4 nucleotides {A, T, C, G} are GENERATED as the          *)
(*  eigenvalues of a 2-dimensional spectral decomposition:        *)
(*                                                                *)
(*    Dimension 1: Ring class                                     *)
(*      Purine (+1):    A, G  (double ring)                       *)
(*      Pyrimidine (-1): C, T  (single ring)                     *)
(*                                                                *)
(*    Dimension 2: Bond strength                                  *)
(*      Strong (+): G, C  (3 hydrogen bonds with complement)     *)
(*      Weak (-):   A, T  (2 hydrogen bonds with complement)     *)
(*                                                                *)
(*    Combined spectral weight:                                   *)
(*      h(n) = ring_sign × bond_count (milli-units × 1000)       *)
(*      G = +3000,  A = +2000,  T = -2000,  C = -3000            *)
(*                                                                *)
(*  Sign class (nucleotide-level BioProt):                        *)
(*    Ordered:    purines  (A, G) with h > 0                      *)
(*    Transition: pyrimidines (C, T) with h < 0                   *)
(*                                                                *)
(*  Base editors are sign-preserving morphisms:                   *)
(*    CBE (C→T): -3000 → -2000  (Transition → Transition)        *)
(*    ABE (A→G): +2000 → +3000  (Ordered → Ordered)              *)
(*                                                                *)
(*  Tower connection:                                             *)
(*    Level -1: Nucleotide → spectral weight → nucleotide sign   *)
(*    Level  0: Codon → amino acid → KD → protein stability      *)
(*    Level  1: Stability → sign pattern → BioProt object         *)
(*    Level  2: D(End(G)) = G  (fixed point, bio_dirac_tower.v)  *)
(*                                                                *)
(*  Rocq/Coq 9.x compatible (uses Stdlib, lia).                  *)
(* ============================================================ *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.

Open Scope Z_scope.

(* ------------------------------------------------------------ *)
(* SECTION 1: NUCLEOTIDE TYPE AND SPECTRAL WEIGHT                *)
(* ------------------------------------------------------------ *)

(** The 4 nucleotides. *)
Inductive Nucleotide : Type :=
  | G   (* Guanine:  purine, 3 H-bonds *)
  | A   (* Adenine:  purine, 2 H-bonds *)
  | T   (* Thymine:  pyrimidine, 2 H-bonds *)
  | C.  (* Cytosine: pyrimidine, 3 H-bonds *)

(** Ring class: the first generator of Z/2 × Z/2. *)
Inductive RingClass : Type :=
  | Purine     (* double ring: A, G *)
  | Pyrimidine (* single ring: C, T *).

(** Bond strength: the second generator of Z/2 × Z/2. *)
Inductive BondStrength : Type :=
  | Strong  (* 3 hydrogen bonds: G, C *)
  | Weak.   (* 2 hydrogen bonds: A, T *)

(** Extract ring class from nucleotide. *)
Definition ring_class (n : Nucleotide) : RingClass :=
  match n with
  | G => Purine
  | A => Purine
  | T => Pyrimidine
  | C => Pyrimidine
  end.

(** Extract bond strength from nucleotide. *)
Definition bond_strength (n : Nucleotide) : BondStrength :=
  match n with
  | G => Strong
  | A => Weak
  | T => Weak
  | C => Strong
  end.

(** Spectral weight: h(n) = ring_sign × bond_count × 1000.
    This is the diagonal entry of the nucleotide Dirac operator. *)
Definition spectral_weight (n : Nucleotide) : Z :=
  match n with
  | G =>  3000
  | A =>  2000
  | T => -2000
  | C => -3000
  end.

(* ------------------------------------------------------------ *)
(* SECTION 2: GENERATION THEOREM                                 *)
(*                                                                *)
(* The 4 nucleotides are uniquely determined by two binary        *)
(* predicates: ring_class and bond_strength.                      *)
(* This is the Z/2 × Z/2 structure of the DNA alphabet.         *)
(* ------------------------------------------------------------ *)

(** T1. NucleotideGeneration:
    Each combination of (RingClass, BondStrength) uniquely
    determines a nucleotide.  The DNA alphabet is generated
    by two binary observables. *)
Theorem NucleotideGeneration :
  forall n : Nucleotide,
  (ring_class n = Purine     /\ bond_strength n = Strong -> n = G) /\
  (ring_class n = Purine     /\ bond_strength n = Weak   -> n = A) /\
  (ring_class n = Pyrimidine /\ bond_strength n = Weak   -> n = T) /\
  (ring_class n = Pyrimidine /\ bond_strength n = Strong -> n = C).
Proof.
  destruct n; repeat split; intros [H1 H2]; simpl in *;
  try reflexivity; try discriminate.
Qed.

(** T1a. InjectiveGeneration:
    Different nucleotides have different (ring, bond) pairs.
    The generation is injective. *)
Theorem InjectiveGeneration :
  forall n m : Nucleotide,
  ring_class n = ring_class m ->
  bond_strength n = bond_strength m ->
  n = m.
Proof.
  destruct n, m; simpl; intros H1 H2;
  try reflexivity; try discriminate.
Qed.

(** T1b. SpectralWeightDistinct:
    All 4 nucleotides have distinct spectral weights. *)
Theorem SpectralWeightDistinct :
  spectral_weight G <> spectral_weight A /\
  spectral_weight G <> spectral_weight T /\
  spectral_weight G <> spectral_weight C /\
  spectral_weight A <> spectral_weight T /\
  spectral_weight A <> spectral_weight C /\
  spectral_weight T <> spectral_weight C.
Proof.
  unfold spectral_weight.
  repeat split; intro H; lia.
Qed.

(* ------------------------------------------------------------ *)
(* SECTION 3: SIGN CLASSIFICATION                                *)
(*                                                                *)
(* Purines have positive spectral weight (Ordered).              *)
(* Pyrimidines have negative spectral weight (Transition).       *)
(* This is the nucleotide-level BioProt sign class.              *)
(* ------------------------------------------------------------ *)

Inductive NucSignClass : Type :=
  | NucOrdered    (* spectral weight > 0, i.e. purine *)
  | NucTransition (* spectral weight < 0, i.e. pyrimidine *).

Definition nuc_sign (n : Nucleotide) : NucSignClass :=
  if Z.ltb 0 (spectral_weight n) then NucOrdered
  else NucTransition.

(** T2a. Purines are Ordered. *)
Theorem PurineIsOrdered_G : nuc_sign G = NucOrdered.
Proof. reflexivity. Qed.

Theorem PurineIsOrdered_A : nuc_sign A = NucOrdered.
Proof. reflexivity. Qed.

(** T2b. Pyrimidines are Transition. *)
Theorem PyrimidineIsTransition_T : nuc_sign T = NucTransition.
Proof. reflexivity. Qed.

Theorem PyrimidineIsTransition_C : nuc_sign C = NucTransition.
Proof. reflexivity. Qed.

(** T2c. Sign class equals ring class (isomorphism). *)
Theorem SignEqualsRingClass :
  forall n : Nucleotide,
  (ring_class n = Purine <-> nuc_sign n = NucOrdered) /\
  (ring_class n = Pyrimidine <-> nuc_sign n = NucTransition).
Proof.
  destruct n; simpl; split; split; intros; try reflexivity; try discriminate.
Qed.

(** T2d. Spectral weight ordering matches sign class. *)
Theorem SpectralWeightPositive_Purine :
  forall n : Nucleotide,
  ring_class n = Purine -> spectral_weight n > 0.
Proof.
  destruct n; simpl; intros; try lia; discriminate.
Qed.

Theorem SpectralWeightNegative_Pyrimidine :
  forall n : Nucleotide,
  ring_class n = Pyrimidine -> spectral_weight n < 0.
Proof.
  destruct n; simpl; intros; try lia; discriminate.
Qed.

(* ------------------------------------------------------------ *)
(* SECTION 4: BASE EDITING AS SIGN-PRESERVING MORPHISM           *)
(*                                                                *)
(* CBE (C→T) and ABE (A→G) are the two base editors.            *)
(* Both preserve the ring class (= sign class).                  *)
(* They only change the bond strength dimension.                  *)
(* ------------------------------------------------------------ *)

(** CBE target: cytosine. *)
Definition is_cbe_target (n : Nucleotide) : bool :=
  match n with C => true | _ => false end.

(** ABE target: adenine. *)
Definition is_abe_target (n : Nucleotide) : bool :=
  match n with A => true | _ => false end.

(** CBE edit: C → T. *)
Definition cbe_edit (n : Nucleotide) : Nucleotide :=
  match n with C => T | x => x end.

(** ABE edit: A → G. *)
Definition abe_edit (n : Nucleotide) : Nucleotide :=
  match n with A => G | x => x end.

(** T3a. CBE preserves ring class (sign class). *)
Theorem CBE_preserves_ring_class :
  forall n : Nucleotide,
  ring_class (cbe_edit n) = ring_class n.
Proof.
  destruct n; reflexivity.
Qed.

(** T3b. ABE preserves ring class (sign class). *)
Theorem ABE_preserves_ring_class :
  forall n : Nucleotide,
  ring_class (abe_edit n) = ring_class n.
Proof.
  destruct n; reflexivity.
Qed.

(** T3c. CBE preserves sign class. *)
Theorem CBE_preserves_sign :
  forall n : Nucleotide,
  nuc_sign (cbe_edit n) = nuc_sign n.
Proof.
  destruct n; reflexivity.
Qed.

(** T3d. ABE preserves sign class. *)
Theorem ABE_preserves_sign :
  forall n : Nucleotide,
  nuc_sign (abe_edit n) = nuc_sign n.
Proof.
  destruct n; reflexivity.
Qed.

(** T3e. CBE changes bond strength on C (strong→weak). *)
Theorem CBE_flips_bond_on_C :
  bond_strength (cbe_edit C) = Weak.
Proof. reflexivity. Qed.

(** T3f. ABE changes bond strength on A (weak→strong). *)
Theorem ABE_flips_bond_on_A :
  bond_strength (abe_edit A) = Strong.
Proof. reflexivity. Qed.

(** T3g. CBE leaves non-C nucleotides unchanged. *)
Theorem CBE_identity_non_C :
  forall n : Nucleotide,
  is_cbe_target n = false -> cbe_edit n = n.
Proof.
  destruct n; simpl; intro H; try reflexivity; discriminate.
Qed.

(** T3h. ABE leaves non-A nucleotides unchanged. *)
Theorem ABE_identity_non_A :
  forall n : Nucleotide,
  is_abe_target n = false -> abe_edit n = n.
Proof.
  destruct n; simpl; intro H; try reflexivity; discriminate.
Qed.

(* ------------------------------------------------------------ *)
(* SECTION 5: SPECTRAL WEIGHT MONOTONICITY                       *)
(*                                                                *)
(* Within each sign class, the spectral weight is ordered:       *)
(*   Purines:    A < G  (2000 < 3000)                             *)
(*   Pyrimidines: C < T  (-3000 < -2000)                         *)
(*                                                                *)
(* Base editors move "up" within each class:                     *)
(*   CBE: C → T  (weight increases: -3000 → -2000)               *)
(*   ABE: A → G  (weight increases: +2000 → +3000)               *)
(* Both editors INCREASE spectral weight.                        *)
(* ------------------------------------------------------------ *)

(** T4a. CBE increases spectral weight (C→T). *)
Theorem CBE_increases_weight :
  spectral_weight (cbe_edit C) > spectral_weight C.
Proof. simpl. lia. Qed.

(** T4b. ABE increases spectral weight (A→G). *)
Theorem ABE_increases_weight :
  spectral_weight (abe_edit A) > spectral_weight A.
Proof. simpl. lia. Qed.

(** T4c. General: base editors never decrease spectral weight. *)
Theorem BaseEdit_nondecreasing :
  forall n : Nucleotide,
  spectral_weight (cbe_edit n) >= spectral_weight n /\
  spectral_weight (abe_edit n) >= spectral_weight n.
Proof.
  destruct n; simpl; split; lia.
Qed.

(** T4d. The spectral weight delta for CBE on C is exactly +1000. *)
Theorem CBE_delta :
  spectral_weight (cbe_edit C) - spectral_weight C = 1000.
Proof. simpl. lia. Qed.

(** T4e. The spectral weight delta for ABE on A is exactly +1000. *)
Theorem ABE_delta :
  spectral_weight (abe_edit A) - spectral_weight A = 1000.
Proof. simpl. lia. Qed.

(** T4f. Both editors have the SAME delta magnitude.
    CBE and ABE are the SAME operation (flip bond strength)
    restricted to different ring classes. *)
Theorem Editors_same_delta :
  spectral_weight (cbe_edit C) - spectral_weight C =
  spectral_weight (abe_edit A) - spectral_weight A.
Proof. simpl. lia. Qed.

(* ------------------------------------------------------------ *)
(* SECTION 6: COMPLEMENTARITY                                    *)
(*                                                                *)
(* Watson-Crick pairing: A↔T and G↔C.                           *)
(* Complement negates the spectral weight: h(n') = -h(n).       *)
(* The double strand is a Z/2 involution on the spectrum.         *)
(* ------------------------------------------------------------ *)

Definition complement (n : Nucleotide) : Nucleotide :=
  match n with
  | A => T
  | T => A
  | G => C
  | C => G
  end.

(** T5a. Complement is an involution: n'' = n. *)
Theorem complement_involution :
  forall n : Nucleotide,
  complement (complement n) = n.
Proof.
  destruct n; reflexivity.
Qed.

(** T5b. Complement negates spectral weight: h(n') = -h(n). *)
Theorem complement_negates_weight :
  forall n : Nucleotide,
  spectral_weight (complement n) = - spectral_weight n.
Proof.
  destruct n; simpl; lia.
Qed.

(** T5c. Complement swaps ring class. *)
Theorem complement_swaps_ring :
  forall n : Nucleotide,
  (ring_class n = Purine -> ring_class (complement n) = Pyrimidine) /\
  (ring_class n = Pyrimidine -> ring_class (complement n) = Purine).
Proof.
  destruct n; simpl; split; intros; try reflexivity; discriminate.
Qed.

(** T5d. Complement preserves bond strength. *)
Theorem complement_preserves_bonds :
  forall n : Nucleotide,
  bond_strength (complement n) = bond_strength n.
Proof.
  destruct n; reflexivity.
Qed.

(** T5e. Complement swaps sign class. *)
Theorem complement_swaps_sign :
  forall n : Nucleotide,
  (nuc_sign n = NucOrdered -> nuc_sign (complement n) = NucTransition) /\
  (nuc_sign n = NucTransition -> nuc_sign (complement n) = NucOrdered).
Proof.
  destruct n; simpl; split; intros; try reflexivity; discriminate.
Qed.

(* ------------------------------------------------------------ *)
(* SECTION 7: SUMMARY                                            *)
(* ------------------------------------------------------------ *)

(*
  ── PROVED (all formal, zero admitted) ─────────────────────

  T1. NucleotideGeneration + InjectiveGeneration:
      The 4 nucleotides are generated by Z/2 × Z/2 =
      (RingClass, BondStrength).  The generation is bijective.

  T2. SignEqualsRingClass:
      Nucleotide sign class = ring class.
      Purines are Ordered, Pyrimidines are Transition.
      Spectral weight is positive for purines, negative for pyrimidines.

  T3. CBE/ABE preserve sign class:
      Both base editors preserve the ring class (= sign class).
      They are sign-preserving morphisms at the nucleotide level.
      They only change the bond strength dimension (Z/2 flip).

  T4. Spectral weight monotonicity:
      CBE increases weight by +1000 (C→T: -3000 → -2000).
      ABE increases weight by +1000 (A→G: +2000 → +3000).
      SAME delta: base editors are the SAME operation on
      different ring classes.  Never decreases weight.

  T5. Complementarity:
      Watson-Crick complement is an involution (n'' = n).
      Complement NEGATES spectral weight: h(n') = -h(n).
      Complement SWAPS ring class (purine ↔ pyrimidine).
      Complement PRESERVES bond strength.
      The double strand is a Z/2 spectral involution.

  ── TOWER CONNECTION ──────────────────────────────────────

  Level -1 (this file):
    Nucleotides → spectral weight → sign class
    Base editors = sign-preserving morphisms
    Complement = sign-SWAPPING involution

  Level 0 (bio_spectral_axioms.v):
    3 nucleotides → codon → amino acid → KD scale → stability

  Level 1 (bio_bioproto_category.v):
    Stability → sign pattern → BioProt category

  Level 2 (bio_dirac_tower.v):
    D(End(G)) ≅ G  (category fixed point)

  The full tower:
    ATCG → codons → amino acids → stability → sign → D(End(G)) = G
    Each level is a spectral triple.
    Each level's sign-preserving morphisms are the valid
    transformations at that level.
    The tower stabilises at level 2.
*)
