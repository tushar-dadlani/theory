(* ================================================================= *)
(*  EulerFormula.v                                                   *)
(*                                                                    *)
(*  LEVERAGING TRIG: Euler's formula and the CIRCLE GROUP.           *)
(*                                                                    *)
(*  Over the custom field C = R[i], define                           *)
(*                                                                    *)
(*      Cexp t := cos t + i sin t                                     *)
(*                                                                    *)
(*  and prove it is a GROUP HOMOMORPHISM  (R,+) -> (C*, x)  landing    *)
(*  on the unit circle:                                              *)
(*                                                                    *)
(*    Cexp_0    : Cexp 0 = 1                    (identity)            *)
(*    Cexp_add  : Cexp(a+b) = Cexp a * Cexp b   (homomorphism)        *)
(*    Cnorm2_.. : |Cexp t|^2 = 1                (image = unit circle) *)
(*    Cinv_Cexp : (Cexp t)^-1 = Cexp(-t) = conj(Cexp t)              *)
(*    Cpow_Cexp : (Cexp t)^n = Cexp (n t)       (de Moivre)          *)
(*    Cexp_2PI  : Cexp (2 pi) = 1                                    *)
(*    w_is_Cexp : w N = Cexp (2 pi / N)          grounds RootsOfUnity *)
(*                                                                    *)
(*  This is the analytic backbone the ENTIRE character/DFT/Dirichlet   *)
(*  layer rests on: `AlgebraicOrthogonality` showed the orthogonality  *)
(*  is axiom-free field algebra given a root of unity, and Cexp is     *)
(*  precisely the trig machine that MANUFACTURES that root.  A single  *)
(*  complex identity Cexp_add packs BOTH real angle-addition formulas  *)
(*  (cos_plus and sin_plus) at once -- that is what "leveraging trig"   *)
(*  buys: additive angles become multiplicative rotations.            *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via cos/sin).       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField RootsOfUnity.
Open Scope R_scope.

Definition Cexp (t : R) : C := mkC (cos t) (sin t).

(* ----------------------------------------------------------------- *)
(*  The homomorphism (R,+) -> (C*, x)                                *)
(* ----------------------------------------------------------------- *)

Lemma Cexp_0 : Cexp 0 = C1.
Proof. unfold Cexp; apply Ceq; simpl; [ apply cos_0 | apply sin_0 ]. Qed.

(* Cexp(a+b) = Cexp a * Cexp b  --  ONE complex identity that is BOTH *)
(* cos_plus and sin_plus simultaneously.                             *)
Lemma Cexp_add : forall a b, Cexp (a + b) = Cmul (Cexp a) (Cexp b).
Proof.
  intros a b; unfold Cexp, Cmul; apply Ceq; simpl.
  - rewrite cos_plus; ring.
  - rewrite sin_plus; ring.
Qed.

Lemma Cexp_neg : forall t, Cexp (- t) = Cconj (Cexp t).
Proof.
  intro t; unfold Cexp, Cconj; apply Ceq; simpl; [ apply cos_neg | apply sin_neg ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The image lies on the unit circle:  |Cexp t|^2 = 1               *)
(* ----------------------------------------------------------------- *)

Lemma Cnorm2_Cexp : forall t, Cnorm2 (Cexp t) = 1.
Proof.
  intro t; unfold Cnorm2, Cexp; simpl.
  pose proof (sin2_cos2 t) as H; unfold Rsqr in H; lra.
Qed.

Lemma Cexp_neq_0 : forall t, Cexp t <> C0.
Proof.
  intros t H; pose proof (Cnorm2_Cexp t) as HN.
  rewrite H in HN; unfold Cnorm2, C0 in HN; simpl in HN; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Inverses:  conjugation = reciprocal = negated angle              *)
(* ----------------------------------------------------------------- *)

(* Cexp t * Cexp(-t) = 1, directly from the homomorphism *)
Lemma Cexp_mul_neg : forall t, Cmul (Cexp t) (Cexp (- t)) = C1.
Proof.
  intro t; rewrite <- Cexp_add; replace (t + - t) with 0 by ring; apply Cexp_0.
Qed.

(* on the unit circle the field inverse is just the conjugate *)
Lemma Cinv_Cexp : forall t, Cinv (Cexp t) = Cexp (- t).
Proof.
  intro t; unfold Cinv; rewrite (Cnorm2_Cexp t).
  apply Ceq; unfold Cexp; simpl.
  - rewrite cos_neg; field.
  - rewrite sin_neg; field.
Qed.

Lemma Cconj_Cexp_is_inv : forall t, Cconj (Cexp t) = Cinv (Cexp t).
Proof. intro t; rewrite <- Cexp_neg, Cinv_Cexp; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  De Moivre, restated as the power law of the homomorphism         *)
(* ----------------------------------------------------------------- *)

Lemma Cpow_Cexp : forall t n, Cpow (Cexp t) n = Cexp (INR n * t).
Proof. intros t n; unfold Cexp; rewrite de_moivre; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  The full turn, and the bridge to RootsOfUnity.w                  *)
(* ----------------------------------------------------------------- *)

Lemma Cexp_2PI : Cexp (2 * PI) = C1.
Proof. unfold Cexp; apply Ceq; simpl; [ apply cos_2PI | apply sin_2PI ]. Qed.

Lemma w_is_Cexp : forall N, w N = Cexp (2 * PI / INR N).
Proof. intro N; unfold w, Cexp; reflexivity. Qed.

(* w_pow_N re-derived from Euler: the root of unity is Cexp of one N-th *)
(* of a full turn, so its N-th power is Cexp of a full turn = 1.        *)
Lemma w_pow_N_via_euler : forall N, (0 < N)%nat -> Cpow (w N) N = C1.
Proof.
  intros N HN; rewrite w_is_Cexp, Cpow_Cexp.
  replace (INR N * (2 * PI / INR N)) with (2 * PI)
    by (field; apply not_0_INR; lia).
  apply Cexp_2PI.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER: Cexp is a homomorphism (R,+) -> (unit circle, x)          *)
(* ----------------------------------------------------------------- *)

Theorem euler_circle_group :
     Cexp 0 = C1
  /\ (forall a b, Cexp (a + b) = Cmul (Cexp a) (Cexp b))
  /\ (forall t, Cnorm2 (Cexp t) = 1)
  /\ (forall t, Cinv (Cexp t) = Cexp (- t))
  /\ (forall t, Cconj (Cexp t) = Cinv (Cexp t))
  /\ (forall t n, Cpow (Cexp t) n = Cexp (INR n * t))
  /\ Cexp (2 * PI) = C1
  /\ (forall N, w N = Cexp (2 * PI / INR N)).
Proof.
  split; [ exact Cexp_0 | ].
  split; [ exact Cexp_add | ].
  split; [ exact Cnorm2_Cexp | ].
  split; [ exact Cinv_Cexp | ].
  split; [ exact Cconj_Cexp_is_inv | ].
  split; [ exact Cpow_Cexp | ].
  split; [ exact Cexp_2PI | exact w_is_Cexp ].
Qed.

Print Assumptions euler_circle_group.

(* ================================================================= *)
(*  END EulerFormula.v                                               *)
(*  Euler's formula Cexp t = cos t + i sin t as the group homomorphism *)
(*  (R,+) -> (unit circle in C, x): identity, additivity (= cos_plus  *)
(*  & sin_plus at once), unit modulus, conjugate = reciprocal = Cexp   *)
(*  of the negated angle, de Moivre as the power law, and w N =        *)
(*  Cexp(2 pi/N) grounding RootsOfUnity.  This is the trig engine that  *)
(*  manufactures the roots of unity the (otherwise axiom-free)         *)
(*  orthogonality consumes.  Uses the quarantined classical R axioms.  *)
(* ================================================================= *)
