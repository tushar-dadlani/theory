(* ================================================================= *)
(*  CexpFull.v  —  the full complex exponential Cexpf : C -> C and the *)
(*  complex power Cpw c w = c^w of a positive real base c.            *)
(*                                                                    *)
(*  Cexpf w := exp(Re w) · (cos(Im w), sin(Im w)), built on the       *)
(*  unit-circle EulerFormula.Cexp.  Key facts: homomorphism, modulus  *)
(*  = exp(Re w), and Cpw_mod : |c^w| = c^{Re w}.  Axiom-clean.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField EulerFormula Cmodulus.
Open Scope R_scope.

Definition Cexpf (w : C) : C := Cmul (RtoC (exp (Re w))) (Cexp (Im w)).

Lemma Cexpf_RtoC : forall r, Cexpf (RtoC r) = RtoC (exp r).
Proof. intro r; unfold Cexpf, RtoC; simpl; rewrite Cexp_0; ring. Qed.

Lemma Cexpf_add : forall a b, Cexpf (Cadd a b) = Cmul (Cexpf a) (Cexpf b).
Proof.
  intros a b; unfold Cexpf; simpl.
  rewrite exp_plus, RtoC_mul, Cexp_add; ring.
Qed.

Lemma Cmod_Cexpf : forall w, Cmod (Cexpf w) = exp (Re w).
Proof.
  intro w; unfold Cexpf; rewrite Cmod_mul, Cmod_RtoC.
  rewrite Rabs_right by (left; apply exp_pos).
  unfold Cmod; rewrite Cnorm2_Cexp, sqrt_1; ring.
Qed.

Lemma Cexpf_ne0 : forall w, Cexpf w <> C0.
Proof.
  intro w; intro H. pose proof (Cmod_Cexpf w) as HM. rewrite H in HM.
  assert (Hc0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
  rewrite Hc0 in HM. pose proof (exp_pos (Re w)); lra.
Qed.

(* --- complex power of a positive real base --- *)

Definition Cpw (c : R) (w : C) : C := Cexpf (Cmul w (RtoC (ln c))).

Lemma Cpw_split : forall c w1 w2, Cpw c (Cadd w1 w2) = Cmul (Cpw c w1) (Cpw c w2).
Proof.
  intros c w1 w2; unfold Cpw.
  replace (Cmul (Cadd w1 w2) (RtoC (ln c)))
    with (Cadd (Cmul w1 (RtoC (ln c))) (Cmul w2 (RtoC (ln c)))) by ring.
  apply Cexpf_add.
Qed.

Lemma Cpw_RtoC : forall c a, Cpw c (RtoC a) = RtoC (Rpower c a).
Proof.
  intros c a; unfold Cpw. rewrite <- RtoC_mul, Cexpf_RtoC. unfold Rpower. reflexivity.
Qed.

Lemma Cpw_mod : forall c w, Cmod (Cpw c w) = Rpower c (Re w).
Proof.
  intros c w; unfold Cpw. rewrite Cmod_Cexpf. unfold Rpower. f_equal.
  unfold Cmul, RtoC; simpl; ring.
Qed.

Print Assumptions Cpw_mod.

(* ================================================================= *)
(*  END CexpFull.v.                                                   *)
(* ================================================================= *)
