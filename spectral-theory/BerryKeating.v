(* ================================================================= *)
(*  BerryKeating.v                                                    *)
(*                                                                    *)
(*  THE xp + px REALITY CONDITION.                                    *)
(*                                                                    *)
(*  Berry-Keating conjecture the Riemann zero ordinates are the       *)
(*  eigenvalues of a self-adjoint quantisation of the classical       *)
(*  dilation Hamiltonian  H = x p.  But x p is NOT self-adjoint:      *)
(*  with the adjoint (dagger) an anti-homomorphism, (x p)† = p x.     *)
(*  Hence one must SYMMETRISE:  H = (x p + p x)/2, which IS            *)
(*  self-adjoint, and self-adjointness forces the spectrum REAL.      *)
(*                                                                    *)
(*  This file isolates that reality condition as a purely algebraic   *)
(*  fact in a *-("dagger")-algebra, plus the state form "expectation  *)
(*  of a self-adjoint element is real".  It is the operator-side twin *)
(*  of CoherenceSingularity.coherence_line (XiC real on the seam):    *)
(*  both are the SAME reality condition -- self-adjointness -- one on  *)
(*  the arithmetic operator, one on the completed zeta.               *)
(*                                                                    *)
(*  Axiom-free: the algebra laws are record fields (hypotheses), not  *)
(*  global axioms.                                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField.
Open Scope R_scope.

(* An involutive ("dagger") operator algebra: an adjoint that reverses  *)
(* products, distributes over sums, and is an involution.              *)
Record DagAlg : Type := {
  Op    : Type;
  Oadd  : Op -> Op -> Op;
  Ocomp : Op -> Op -> Op;
  Odag  : Op -> Op;
  Oadd_comm  : forall a b, Oadd a b = Oadd b a;
  Odag_add   : forall a b, Odag (Oadd a b) = Oadd (Odag a) (Odag b);
  Odag_comp  : forall a b, Odag (Ocomp a b) = Ocomp (Odag b) (Odag a);
  Odag_invol : forall a, Odag (Odag a) = a
}.

Definition SelfAdj (A : DagAlg) (a : Op A) : Prop := Odag A a = a.

Section Reality.
  Context (A : DagAlg).

  (* The bare product x p is NOT self-adjoint: (x p)† = p x. *)
  Lemma xp_dag : forall x p, SelfAdj A x -> SelfAdj A p ->
    Odag A (Ocomp A x p) = Ocomp A p x.
  Proof. intros x p Hx Hp; rewrite Odag_comp, Hx, Hp; reflexivity. Qed.

  (* ... so x p is self-adjoint iff x and p COMMUTE (they do not: [x,p]<>0). *)
  Theorem xp_selfadj_iff_commute : forall x p, SelfAdj A x -> SelfAdj A p ->
    (SelfAdj A (Ocomp A x p) <-> Ocomp A x p = Ocomp A p x).
  Proof.
    intros x p Hx Hp; unfold SelfAdj; rewrite (xp_dag x p Hx Hp).
    split; intro H; symmetry; exact H.
  Qed.

  (* The SYMMETRISED product x p + p x IS self-adjoint -- this is why    *)
  (* Berry-Keating take H = (x p + p x)/2.                              *)
  Theorem anticomm_selfadj : forall x p, SelfAdj A x -> SelfAdj A p ->
    SelfAdj A (Oadd A (Ocomp A x p) (Ocomp A p x)).
  Proof.
    intros x p Hx Hp; unfold SelfAdj.
    rewrite Odag_add, (xp_dag x p Hx Hp), (xp_dag p x Hp Hx); apply Oadd_comm.
  Qed.

  (* A state / expectation functional with the Hermitian property        *)
  (* <a†> = conj <a>  (physical measurement).                           *)
  Context (omega : Op A -> C)
          (omega_dag : forall a, omega (Odag A a) = Cconj (omega a)).

  (* REALITY: the expectation of any self-adjoint element is real.       *)
  Theorem selfadj_real : forall a, SelfAdj A a -> Im (omega a) = 0.
  Proof.
    intros a Ha; pose proof (omega_dag a) as H; unfold SelfAdj in Ha.
    rewrite Ha in H. destruct (omega a) as [x y]; unfold Cconj in H.
    apply (f_equal Im) in H; simpl in H |- *; lra.
  Qed.

  (* THE BERRY-KEATING REALITY CONDITION.  For self-adjoint x, p the      *)
  (* symmetrised H = x p + p x has REAL expectation (a real would-be      *)
  (* spectrum), whereas the bare x p does not, unless x, p commute.       *)
  Corollary BK_reality : forall x p, SelfAdj A x -> SelfAdj A p ->
    Im (omega (Oadd A (Ocomp A x p) (Ocomp A p x))) = 0.
  Proof. intros x p Hx Hp; apply selfadj_real, anticomm_selfadj; assumption. Qed.

End Reality.

(* The record is inhabited (so the theorems are not vacuous): C itself   *)
(* with conjugation is a (commutative) dagger algebra.  The intended     *)
(* NON-commutative models -- matrix / operator algebras where x p <> p x *)
(* -- are where the symmetrisation is genuinely needed.                  *)
Lemma Cadd_comm' : forall a b, Cadd a b = Cadd b a.
Proof. intros; unfold Cadd; apply Ceq; simpl; ring. Qed.
Lemma Cmul_comm' : forall a b, Cmul a b = Cmul b a.
Proof. intros; unfold Cmul; apply Ceq; simpl; ring. Qed.

Definition C_DagAlg : DagAlg :=
  {| Op := C; Oadd := Cadd; Ocomp := Cmul; Odag := Cconj;
     Oadd_comm := Cadd_comm';
     Odag_add := Cconj_add;
     Odag_comp := fun a b => eq_trans (Cconj_mul a b) (Cmul_comm' (Cconj a) (Cconj b));
     Odag_invol := Cconj_involutive |}.

Print Assumptions BK_reality.
