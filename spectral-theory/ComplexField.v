(* ================================================================= *)
(*  ComplexField.v                                                   *)
(*                                                                    *)
(*  A CUSTOM COMPLEX FIELD C = R[i] = R x R, under the repo's axiom    *)
(*  discipline: instead of importing an opaque / external C (which     *)
(*  would inject its own axioms and break the ledger), we DEFINE C as  *)
(*  ordered pairs over the repo's classical R and PROVE every complex- *)
(*  number axiom as a theorem.  The axiom footprint is therefore       *)
(*  EXACTLY the quarantined classical R axioms -- nothing new is added; *)
(*  the "complex axioms" are Qed lemmas, not assumptions.             *)
(*                                                                    *)
(*  What is proved (complex_field_axioms bundles them):               *)
(*    * commutative field: +/*/-/inv with all ring + field laws        *)
(*      (C_ring_theory, C_field_theory, registered for `ring`/`field`);*)
(*    * i^2 = -1               (Ci_sq);                               *)
(*    * every c = Re c + i*Im c   (C_decompose; 2-dimensional over R);  *)
(*    * R ↪ C is an injective ring homomorphism (subfield);           *)
(*    * conjugation is an involution and a ring homomorphism, with      *)
(*      c * conj c = |c|^2 = Cnorm2 c (real, >= 0).                    *)
(*                                                                    *)
(*  So C here is the genuine field R[i]; downstream files can use       *)
(*  `ring`/`field` on it and rely on i^2=-1, conjugation, modulus --    *)
(*  the machinery needed for roots of unity / a bona fide DFT / zeta    *)
(*  work -- WITHOUT importing any new axiom.                          *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via R).             *)
(* ================================================================= *)

From Stdlib Require Import Reals Field Ring Lra.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The carrier and operations (projection-style, so `simpl` reduces   *)
(*  Re/Im through them even on abstract arguments)                    *)
(* ----------------------------------------------------------------- *)

Record C : Set := mkC { Re : R; Im : R }.

Definition Cadd   (a b : C) : C := mkC (Re a + Re b) (Im a + Im b).
Definition Copp   (a : C)   : C := mkC (- Re a) (- Im a).
Definition Cminus (a b : C) : C := mkC (Re a - Re b) (Im a - Im b).
Definition Cmul   (a b : C) : C := mkC (Re a * Re b - Im a * Im b) (Re a * Im b + Im a * Re b).
Definition C0 : C := mkC 0 0.
Definition C1 : C := mkC 1 0.
Definition Ci : C := mkC 0 1.
Definition Cconj  (a : C)   : C := mkC (Re a) (- Im a).
Definition RtoC   (r : R)   : C := mkC r 0.
Definition Cnorm2 (a : C)   : R := Re a * Re a + Im a * Im a.
Definition Cinv   (a : C)   : C := mkC (Re a / Cnorm2 a) (- Im a / Cnorm2 a).
Definition Cdiv   (a b : C) : C := Cmul a (Cinv b).

(* extensionality: a complex number is determined by its two reals *)
Lemma Ceq : forall a b : C, Re a = Re b -> Im a = Im b -> a = b.
Proof. intros [ar ai] [br bi]; simpl; intros -> ->; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  COMMUTATIVE RING and FIELD structure                             *)
(* ----------------------------------------------------------------- *)

Lemma C_ring_theory : ring_theory C0 C1 Cadd Cmul Cminus Copp (@eq C).
Proof. constructor; intros; apply Ceq; simpl; ring. Qed.

Add Ring CRing : C_ring_theory.

Lemma C1_neq_C0 : C1 <> C0.
Proof. intro H; apply R1_neq_R0; exact (f_equal Re H). Qed.

(* the squared modulus is nonzero exactly when the number is nonzero *)
Lemma Cnorm2_neq_0 : forall a, a <> C0 -> Re a * Re a + Im a * Im a <> 0.
Proof. intros a Ha H; apply Ha; apply Ceq; simpl; nra. Qed.

Lemma Cinv_l : forall a, a <> C0 -> Cmul (Cinv a) a = C1.
Proof.
  intros a Ha.
  pose proof (Cnorm2_neq_0 a Ha) as Hd.
  apply Ceq; unfold Cmul, Cinv, Cnorm2; simpl; field; exact Hd.
Qed.

Lemma C_field_theory :
  field_theory C0 C1 Cadd Cmul Cminus Copp Cdiv Cinv (@eq C).
Proof.
  apply mk_field.
  - exact C_ring_theory.
  - exact C1_neq_C0.
  - intros p q; reflexivity.
  - exact Cinv_l.
Qed.

Add Field CField : C_field_theory.

(* ----------------------------------------------------------------- *)
(*  THE DEFINING COMPLEX-NUMBER FACTS (all Qed, via `ring`)           *)
(* ----------------------------------------------------------------- *)

(* i^2 = -1 *)
Lemma Ci_sq : Cmul Ci Ci = Copp C1.
Proof. apply Ceq; simpl; ring. Qed.

(* every complex number is Re + i * Im : C is 2-dimensional over R *)
Lemma C_decompose : forall a, a = Cadd (RtoC (Re a)) (Cmul Ci (RtoC (Im a))).
Proof. intro a; apply Ceq; simpl; ring. Qed.

(* R ↪ C is an injective ring homomorphism (R is a subfield) *)
Lemma RtoC_add : forall r s, RtoC (r + s) = Cadd (RtoC r) (RtoC s).
Proof. intros; apply Ceq; simpl; ring. Qed.

Lemma RtoC_mul : forall r s, RtoC (r * s) = Cmul (RtoC r) (RtoC s).
Proof. intros; apply Ceq; simpl; ring. Qed.

Lemma RtoC_inj : forall r s, RtoC r = RtoC s -> r = s.
Proof. intros r s H; exact (f_equal Re H). Qed.

(* conjugation: involution + ring homomorphism *)
Lemma Cconj_involutive : forall a, Cconj (Cconj a) = a.
Proof. intro a; apply Ceq; simpl; ring. Qed.

Lemma Cconj_add : forall a b, Cconj (Cadd a b) = Cadd (Cconj a) (Cconj b).
Proof. intros; apply Ceq; simpl; ring. Qed.

Lemma Cconj_mul : forall a b, Cconj (Cmul a b) = Cmul (Cconj a) (Cconj b).
Proof. intros; apply Ceq; simpl; ring. Qed.

(* c * conj c = |c|^2 (a nonnegative real) *)
Lemma Cmul_conj : forall a, Cmul a (Cconj a) = RtoC (Cnorm2 a).
Proof. intro a; apply Ceq; unfold Cnorm2; simpl; ring. Qed.

Lemma Cnorm2_nonneg : forall a, 0 <= Cnorm2 a.
Proof. intro a; unfold Cnorm2; nra. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM: C satisfies all the complex-number axioms         *)
(* ----------------------------------------------------------------- *)

Theorem complex_field_axioms :
  (* commutative field *)
     (forall a b c, Cadd a (Cadd b c) = Cadd (Cadd a b) c)
  /\ (forall a b, Cadd a b = Cadd b a)
  /\ (forall a, Cadd C0 a = a)
  /\ (forall a, Cadd a (Copp a) = C0)
  /\ (forall a b c, Cmul a (Cmul b c) = Cmul (Cmul a b) c)
  /\ (forall a b, Cmul a b = Cmul b a)
  /\ (forall a, Cmul C1 a = a)
  /\ (forall a b c, Cmul (Cadd a b) c = Cadd (Cmul a c) (Cmul b c))
  /\ (forall a, a <> C0 -> Cmul (Cinv a) a = C1)
  /\ C1 <> C0
  (* i^2 = -1 *)
  /\ Cmul Ci Ci = Copp C1
  (* 2-dimensional over R: c = Re + i*Im *)
  /\ (forall a, a = Cadd (RtoC (Re a)) (Cmul Ci (RtoC (Im a))))
  (* R ↪ C : injective ring homomorphism (subfield) *)
  /\ (forall r s, RtoC (r + s) = Cadd (RtoC r) (RtoC s))
  /\ (forall r s, RtoC (r * s) = Cmul (RtoC r) (RtoC s))
  /\ (forall r s, RtoC r = RtoC s -> r = s)
  (* conjugation: involution, ring hom, and c*conj c = |c|^2 >= 0 *)
  /\ (forall a, Cconj (Cconj a) = a)
  /\ (forall a b, Cconj (Cadd a b) = Cadd (Cconj a) (Cconj b))
  /\ (forall a b, Cconj (Cmul a b) = Cmul (Cconj a) (Cconj b))
  /\ (forall a, Cmul a (Cconj a) = RtoC (Cnorm2 a))
  /\ (forall a, 0 <= Cnorm2 a).
Proof.
  repeat split; intros;
    solve [ apply Ceq; simpl; ring
          | exact C1_neq_C0
          | apply Cinv_l; assumption
          | exact Ci_sq
          | apply C_decompose
          | apply RtoC_add | apply RtoC_mul | apply RtoC_inj; assumption
          | apply Cconj_involutive | apply Cconj_add | apply Cconj_mul
          | apply Cmul_conj | apply Cnorm2_nonneg ].
Qed.

Print Assumptions complex_field_axioms.

(* ================================================================= *)
(*  END ComplexField.v                                               *)
(*  C = R[i] built as R x R over the repo's classical R, with EVERY    *)
(*  complex-number axiom proved as a theorem (field laws, i^2 = -1,    *)
(*  the R-subfield, conjugation involution/hom, modulus).  `ring` and   *)
(*  `field` are registered for C.  Axiom footprint = the quarantined    *)
(*  classical R axioms only -- no new axiom is introduced by C.        *)
(* ================================================================= *)
