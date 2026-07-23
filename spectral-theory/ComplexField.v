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
(*  LAYERING (the weak / strong split of the real<->imaginary coupling)*)
(*  --------------------------------------------------------------     *)
(*  The only place the value -1 is baked into the product is the term   *)
(*  Im*Im.  We make that a PARAMETER d (the square of the generator,    *)
(*  i^2 = d) and split the structure into two honest layers:           *)
(*                                                                    *)
(*    * RING CORE (weak).  The product Cmulg d and the whole           *)
(*      commutative-ring structure hold for EVERY real d               *)
(*      (Cring_theory_g) -- the ring never uses i^2 = -1.  Our Cmul is  *)
(*      exactly the d = -1 instance (Cmul_is_gen), and the generator     *)
(*      squares to the parameter, e^2 = d (Cig_sq).  So R[e]/(e^2 = d)  *)
(*      is a commutative R-algebra for any d (d<0: complex; d=0: dual   *)
(*      numbers; d>0: split-complex).                                  *)
(*    * i^2 = -1 (Ci_sq) is then just the d = -1 evaluation -- a        *)
(*      DOWNSTREAM lemma, not a foundation.                            *)
(*    * FIELD CAP (strong).  Invertibility needs the norm-form          *)
(*      Re^2 - d*Im^2 to be nonzero off 0, which holds EXACTLY when      *)
(*      d < 0 (no real square root of d): Cnorm2g_pos.  That single      *)
(*      hypothesis d<0 is the entire gap between "commutative ring for   *)
(*      all d" and "field".  Our C takes d = -1 < 0, so it is a field.   *)
(*                                                                    *)
(*  What is proved (complex_field_axioms bundles the field facts;       *)
(*  ring_core_generalization bundles the weak/strong layering):        *)
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

(* ================================================================= *)
(*  §1  THE RING CORE  (WEAK LAYER: the generator squares to any d)   *)
(* ================================================================= *)

(* The generalized product of R[e]/(e^2 = d): the ONLY change from    *)
(* Cmul is that the Im*Im coupling is scaled by the parameter d        *)
(* instead of being fixed at -1.                                       *)
Definition Cmulg (d : R) (a b : C) : C :=
  mkC (Re a * Re b + d * (Im a * Im b)) (Re a * Im b + Im a * Re b).

(* THE CORE FACT: for EVERY real d, (C, +, Cmulg d) is a commutative   *)
(* ring.  The proof never mentions i, and never uses any property of   *)
(* the specific value -1 -- the ring core is genuinely d-agnostic.     *)
Lemma Cring_theory_g : forall d,
  ring_theory C0 C1 Cadd (Cmulg d) Cminus Copp (@eq C).
Proof. intro d; constructor; intros; apply Ceq; simpl; ring. Qed.

(* our concrete product is exactly the d = -1 instance *)
Lemma Cmul_is_gen : forall a b, Cmul a b = Cmulg (-1) a b.
Proof. intros a b; apply Ceq; simpl; ring. Qed.

(* hence the ring structure of our C is the d = -1 point of the core;  *)
(* we state it under the public name Cmul (proved directly, so the     *)
(* footprint stays the two classical-R axioms -- no functional          *)
(* extensionality needed to pass between Cmul and Cmulg (-1)).          *)
Lemma C_ring_theory : ring_theory C0 C1 Cadd Cmul Cminus Copp (@eq C).
Proof. constructor; intros; apply Ceq; simpl; ring. Qed.

Add Ring CRing : C_ring_theory.

(* the generator squares to the parameter: e^2 = d  (RtoC d).          *)
(* This is the single identity that carries all the "root" content.    *)
Lemma Cig_sq : forall d, Cmulg d Ci Ci = RtoC d.
Proof. intro d; apply Ceq; simpl; ring. Qed.

(* ================================================================= *)
(*  §2  i^2 = -1  :  A DOWNSTREAM CONSEQUENCE, NOT A FOUNDATION       *)
(* ================================================================= *)

(* i^2 = -1 is just Cig_sq at the field parameter d = -1, transported   *)
(* through Cmul_is_gen: nothing about -1 was assumed to get the ring.   *)
Lemma Ci_sq : Cmul Ci Ci = Copp C1.
Proof. rewrite Cmul_is_gen, (Cig_sq (-1)); apply Ceq; simpl; ring. Qed.

(* every complex number is Re + i * Im : C is 2-dimensional over R *)
Lemma C_decompose : forall a, a = Cadd (RtoC (Re a)) (Cmul Ci (RtoC (Im a))).
Proof. intro a; apply Ceq; simpl; ring. Qed.

(* ================================================================= *)
(*  §3  THE FIELD CAP  (STRONG LAYER: invertibility needs d < 0)      *)
(* ================================================================= *)

(* the norm-form of R[e]/(e^2 = d): N_d(a) = Re^2 - d*Im^2.  Its         *)
(* vanishing is what an inverse must divide by.                         *)
Definition Cnorm2g (d : R) (a : C) : R := Re a * Re a - d * (Im a * Im a).

(* our |a|^2 = Re^2 + Im^2 is the d = -1 norm-form *)
Lemma Cnorm2_is_gen : forall a, Cnorm2 a = Cnorm2g (-1) a.
Proof. intro a; unfold Cnorm2, Cnorm2g; ring. Qed.

(* THE FIELD-CAP HYPOTHESIS, isolated: for d < 0 the norm-form is        *)
(* nonzero off the origin (Re^2 + |d|*Im^2 > 0) -- so, and ONLY so,      *)
(* every nonzero element is invertible.  d >= 0 fails: d = 0 has         *)
(* nilpotents (e^2 = 0), d > 0 has zero divisors ((sqrt d + e) etc.).    *)
Lemma Cnorm2g_pos : forall d a, d < 0 -> a <> C0 -> Cnorm2g d a <> 0.
Proof.
  intros d a Hd Ha.
  assert (Hsq : 0 < Re a * Re a \/ 0 < Im a * Im a).
  { destruct (Rtotal_order (Re a) 0) as [h|[h|h]].
    - left; nra.
    - destruct (Rtotal_order (Im a) 0) as [k|[k|k]].
      + right; nra.
      + exfalso; apply Ha; apply Ceq; simpl; [ exact h | exact k ].
      + right; nra.
    - left; nra. }
  unfold Cnorm2g; intro H.
  assert (HR : 0 <= Re a * Re a) by nra.
  assert (HI : 0 <= Im a * Im a) by nra.
  destruct Hsq as [Hs|Hs]; nra.
Qed.

Lemma C1_neq_C0 : C1 <> C0.
Proof. intro H; apply R1_neq_R0; exact (f_equal Re H). Qed.

(* the squared modulus is nonzero exactly when the number is nonzero;   *)
(* this is precisely the d = -1 instance of the field-cap hypothesis.   *)
Lemma Cnorm2_neq_0 : forall a, a <> C0 -> Re a * Re a + Im a * Im a <> 0.
Proof.
  intros a Ha H; apply (Cnorm2g_pos (-1) a ltac:(lra) Ha).
  unfold Cnorm2g; nra.
Qed.

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

(* ================================================================= *)
(*  §4  THE R-SUBFIELD AND CONJUGATION                               *)
(* ================================================================= *)

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

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM: the weak/strong layering (ring core vs field cap)  *)
(* ----------------------------------------------------------------- *)

Theorem ring_core_generalization :
  (* WEAK: R[e]/(e^2 = d) is a commutative ring for EVERY real d *)
     (forall d, ring_theory C0 C1 Cadd (Cmulg d) Cminus Copp (@eq C))
  (* the generator squares to the parameter: e^2 = d *)
  /\ (forall d, Cmulg d Ci Ci = RtoC d)
  (* our field C is exactly the d = -1 instance ... *)
  /\ (forall a b, Cmul a b = Cmulg (-1) a b)
  (* ... and i^2 = -1 is the d = -1 evaluation *)
  /\ Cmul Ci Ci = Copp C1
  (* STRONG: the field cap is nonzero-norm off 0, which needs d < 0 *)
  /\ (forall d a, d < 0 -> a <> C0 -> Cnorm2g d a <> 0).
Proof.
  split; [ exact Cring_theory_g | ].
  split; [ exact Cig_sq | ].
  split; [ exact Cmul_is_gen | ].
  split; [ exact Ci_sq | ].
  exact Cnorm2g_pos.
Qed.

Print Assumptions ring_core_generalization.

(* ================================================================= *)
(*  END ComplexField.v                                               *)
(*  C = R[i] built as R x R over the repo's classical R, with EVERY    *)
(*  complex-number axiom proved as a theorem (field laws, i^2 = -1,    *)
(*  the R-subfield, conjugation involution/hom, modulus).  `ring` and   *)
(*  `field` are registered for C.  Axiom footprint = the quarantined    *)
(*  classical R axioms only -- no new axiom is introduced by C.        *)
(*                                                                    *)
(*  The real<->imaginary coupling is layered: a WEAK ring core         *)
(*  R[e]/(e^2 = d) that holds for every real d (Cring_theory_g, the     *)
(*  ring never uses i^2 = -1), i^2 = -1 as a DOWNSTREAM d = -1 fact     *)
(*  (Ci_sq via Cig_sq), and a STRONG field cap whose sole extra          *)
(*  hypothesis is d < 0 (Cnorm2g_pos).  ring_core_generalization        *)
(*  bundles the layering; d<0/=0/>0 = complex/dual/split-complex.       *)
(* ================================================================= *)
