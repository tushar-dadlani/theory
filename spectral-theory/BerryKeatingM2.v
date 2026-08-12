(* ================================================================= *)
(*  BerryKeatingM2.v                                                  *)
(*                                                                    *)
(*  A CONCRETE NON-COMMUTATIVE dagger algebra: 2x2 complex matrices   *)
(*  M2(C) with the conjugate-transpose as adjoint.  Instantiating     *)
(*  BerryKeating.DagAlg, the Pauli matrices                           *)
(*     X = [[0,1],[1,0]]      Z = [[1,0],[0,-1]]                       *)
(*  are self-adjoint with  [X,Z] <> 0, so (BerryKeating results):      *)
(*     - X Z is NOT self-adjoint          (XZ_not_selfadj),           *)
(*     - X Z + Z X IS self-adjoint        (symmetrised_selfadj).      *)
(*  This makes the "why symmetrise" point concrete: the bare product  *)
(*  genuinely fails Hermiticity, the anticommutator restores it.      *)
(*                                                                    *)
(*  Axiom-free (finite algebra over C; standard classical-Reals       *)
(*  axioms only).                                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField BerryKeating.
Open Scope R_scope.

Record M2 : Type := mkM2 { m11 : C; m12 : C; m21 : C; m22 : C }.

Definition M2add (A B : M2) : M2 :=
  mkM2 (Cadd (m11 A) (m11 B)) (Cadd (m12 A) (m12 B))
       (Cadd (m21 A) (m21 B)) (Cadd (m22 A) (m22 B)).

Definition M2mul (A B : M2) : M2 :=
  mkM2 (Cadd (Cmul (m11 A) (m11 B)) (Cmul (m12 A) (m21 B)))
       (Cadd (Cmul (m11 A) (m12 B)) (Cmul (m12 A) (m22 B)))
       (Cadd (Cmul (m21 A) (m11 B)) (Cmul (m22 A) (m21 B)))
       (Cadd (Cmul (m21 A) (m12 B)) (Cmul (m22 A) (m22 B))).

(* conjugate transpose: (A^dag)_ij = conj (A_ji) *)
Definition M2dag (A : M2) : M2 :=
  mkM2 (Cconj (m11 A)) (Cconj (m21 A)) (Cconj (m12 A)) (Cconj (m22 A)).

Ltac m2 := intros; repeat (match goal with [ H : M2 |- _ ] => destruct H end);
           unfold M2add, M2mul, M2dag; f_equal; apply Ceq; simpl; ring.

Lemma M2add_comm  : forall A B, M2add A B = M2add B A.
Proof. m2. Qed.
Lemma M2dag_add   : forall A B, M2dag (M2add A B) = M2add (M2dag A) (M2dag B).
Proof. m2. Qed.
Lemma M2dag_comp  : forall A B, M2dag (M2mul A B) = M2mul (M2dag B) (M2dag A).
Proof. m2. Qed.
Lemma M2dag_invol : forall A, M2dag (M2dag A) = A.
Proof. m2. Qed.

Definition M2_DagAlg : DagAlg :=
  {| Op := M2; Oadd := M2add; Ocomp := M2mul; Odag := M2dag;
     Oadd_comm := M2add_comm; Odag_add := M2dag_add;
     Odag_comp := M2dag_comp; Odag_invol := M2dag_invol |}.

(* the two non-commuting self-adjoint Pauli matrices *)
Definition X : M2 := mkM2 C0 C1 C1 C0.
Definition Z : M2 := mkM2 C1 C0 C0 (Copp C1).

Lemma X_selfadj : SelfAdj M2_DagAlg X.
Proof. unfold SelfAdj, X; simpl; unfold M2dag; simpl; f_equal; apply Ceq; simpl; ring. Qed.
Lemma Z_selfadj : SelfAdj M2_DagAlg Z.
Proof. unfold SelfAdj, Z; simpl; unfold M2dag; simpl; f_equal; apply Ceq; simpl; ring. Qed.

(* [X,Z] <> 0 : the off-diagonal entry of XZ and ZX differ (-1 vs 1) *)
Lemma XZ_ne_ZX : M2mul X Z <> M2mul Z X.
Proof.
  intro H. apply (f_equal m12) in H.
  unfold M2mul, X, Z in H; simpl in H.
  apply (f_equal Re) in H; unfold Cadd, Cmul, C0, C1, Copp in H; simpl in H. lra.
Qed.

(* HENCE the bare product X Z is genuinely NOT self-adjoint. *)
Theorem XZ_not_selfadj : ~ SelfAdj M2_DagAlg (Ocomp M2_DagAlg X Z).
Proof.
  intro H. apply XZ_ne_ZX.
  exact (proj1 (xp_selfadj_iff_commute M2_DagAlg X Z X_selfadj Z_selfadj) H).
Qed.

(* ... while the SYMMETRISED product X Z + Z X IS self-adjoint. *)
Theorem symmetrised_selfadj :
  SelfAdj M2_DagAlg (Oadd M2_DagAlg (Ocomp M2_DagAlg X Z) (Ocomp M2_DagAlg Z X)).
Proof. apply anticomm_selfadj; [ exact X_selfadj | exact Z_selfadj ]. Qed.

Print Assumptions XZ_not_selfadj.
Print Assumptions symmetrised_selfadj.
