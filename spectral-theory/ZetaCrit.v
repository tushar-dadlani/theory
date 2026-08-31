(* ================================================================= *)
(*  ZetaCrit.v  --  Re and Im of the trapezoid ingredients on the      *)
(*  critical line, as explicit real expressions.                      *)
(*                                                                    *)
(*    g(x) = x^{-s} = x^{-1/2} (cos(t ln x) - i sin(t ln x))          *)
(*    G(x) = x^{1-s}/(1-s) = x^{1/2}(cos - i sin) . (1/2 + it)/D      *)
(*                                                                    *)
(*  with D = 1/4 + t^2.  Everything on the right is built from exp,    *)
(*  ln, cos and sin of REAL arguments, so the interval evaluation      *)
(*  needs no complex interval type -- just Iexp_itv, Ilntab,           *)
(*  Icos_itv and Isin_itv.                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPowBase EulerFormula
        CZetaTerm CoherenceSingularity.
Open Scope R_scope.

Definition Dt (t : R) : R := / 4 + t ^ 2.

Lemma Dt_pos : forall t, 0 < Dt t.
Proof. intro t. unfold Dt. nra. Qed.

Lemma Re_gC_crit : forall t x,
  Re (gC (crit t) x) = exp (- (/ 2) * ln x) * cos (t * ln x).
Proof.
  intros t x. unfold gC, Cpw, Cexpf, Cexp, crit, Copp, Cmul, RtoC.
  cbn [Re Im].
  replace (- / 2 * 0 + - t * ln x) with (- (t * ln x)) by ring.
  rewrite cos_neg.
  replace (- / 2 * ln x - - t * 0) with (- (/ 2) * ln x) by ring.
  ring.
Qed.

Lemma Im_gC_crit : forall t x,
  Im (gC (crit t) x) = - (exp (- (/ 2) * ln x) * sin (t * ln x)).
Proof.
  intros t x. unfold gC, Cpw, Cexpf, Cexp, crit, Copp, Cmul, RtoC.
  cbn [Re Im].
  replace (- / 2 * 0 + - t * ln x) with (- (t * ln x)) by ring.
  rewrite sin_neg.
  replace (- / 2 * ln x - - t * 0) with (- (/ 2) * ln x) by ring.
  ring.
Qed.

Lemma Re_GC_crit : forall t x,
  Re (GC (crit t) x)
  = exp (/ 2 * ln x)
    * (cos (t * ln x) * (/ 2 / Dt t) + sin (t * ln x) * (t / Dt t)).
Proof.
  intros t x. pose proof (Dt_pos t) as HD.
  unfold GC, Cpw, Cexpf, Cexp, crit, Cminus, Cadd, Copp, Cmul, Cinv,
    Cnorm2, RtoC, C1.
  cbn [Re Im].
  replace ((1 - / 2) * 0 + (0 - t) * ln x) with (- (t * ln x)) by ring.
  rewrite cos_neg, sin_neg.
  replace ((1 - / 2) * ln x - (0 - t) * 0) with (/ 2 * ln x) by field.
  unfold Dt.
  assert (H1 : (1 - / 2) * (1 - / 2) + (0 - t) * (0 - t) <> 0)
    by (apply Rgt_not_eq; nra).
  assert (H2 : / 4 + t ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  field; repeat split; apply Rgt_not_eq; nra.
Qed.

Lemma Im_GC_crit : forall t x,
  Im (GC (crit t) x)
  = exp (/ 2 * ln x)
    * (cos (t * ln x) * (t / Dt t) - sin (t * ln x) * (/ 2 / Dt t)).
Proof.
  intros t x. pose proof (Dt_pos t) as HD.
  unfold GC, Cpw, Cexpf, Cexp, crit, Cminus, Cadd, Copp, Cmul, Cinv,
    Cnorm2, RtoC, C1.
  cbn [Re Im].
  replace ((1 - / 2) * 0 + (0 - t) * ln x) with (- (t * ln x)) by ring.
  rewrite cos_neg, sin_neg.
  replace ((1 - / 2) * ln x - (0 - t) * 0) with (/ 2 * ln x) by field.
  unfold Dt.
  assert (H1 : (1 - / 2) * (1 - / 2) + (0 - t) * (0 - t) <> 0)
    by (apply Rgt_not_eq; nra).
  assert (H2 : / 4 + t ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  field; repeat split; apply Rgt_not_eq; nra.
Qed.
