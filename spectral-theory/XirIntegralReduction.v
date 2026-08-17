(* ================================================================= *)
(*  XirIntegralReduction.v  —  Stage 2, brick 1: xir as (1/4+t^2).Re TC.  *)
(*                                                                    *)
(*  Bridges the ABSTRACT boundary value  xir t = Re XiC(1/2+it)         *)
(*  (CoherenceSingularity) to the theta-tail integral TC, by evaluating *)
(*  XiC on the line.  On z = 1/2 + it one has z(z-1) = -(1/4 + t^2), a  *)
(*  NEGATIVE REAL, so the completed xi collapses to                     *)
(*                                                                    *)
(*    xir t = 1/2 - (1/4 + t^2)/2 . ( Re TC(1/2+it) + Re TC(1/2-it) ).  *)
(*                                                                    *)
(*  This is the algebraic step of the reduction; the next brick writes  *)
(*  Re TC(1/2 +- it) as the real improper integral                      *)
(*     int Psi(clamp u) (clamp u)^{-3/4} cos((t/2) ln(clamp u)) du      *)
(*  (via TC_spec / CImp), on which the Stage-1 Psi enclosure and the    *)
(*  verified quadrature then act.                                       *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity ThetaTailEntire.
Open Scope R_scope.

(* z(z-1) = -(1/4 + t^2) on the critical line z = 1/2 + it *)
Lemma crit_quad : forall t, Cmul (crit t) (Cminus (crit t) C1) = RtoC (- (/ 4 + t ^ 2)).
Proof.
  intro t. unfold crit, Cmul, Cminus, RtoC, C1, Copp, Cadd; apply Ceq; cbn [Re Im]; field.
Qed.

(* THE ALGEBRAIC REDUCTION *)
Theorem xir_reduction : forall t,
  xir t = / 2 - (/ 4 + t ^ 2) / 2
                * (Re (TC (crit t)) + Re (TC (Cminus C1 (crit t)))).
Proof.
  intro t. unfold xir. set (z := crit t). unfold XiC.
  assert (HA : Cadd (Cmul C0 z) (RtoC (/ 2)) = RtoC (/ 2))
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  assert (HB : Cadd (Cmul C1 z) C0 = z) by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  assert (HD : Cadd (Cmul C1 z) (Copp C1) = Cminus z C1)
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  assert (HE : Cadd (Cmul (Copp C1) z) C1 = Cminus C1 z)
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  rewrite HA, HB, HD, HE.
  set (W := Cadd (TC z) (TC (Cminus C1 z))).
  assert (Hzd : Cmul z (Cminus z C1) = RtoC (- (/ 4 + t ^ 2)))
    by (unfold z; apply crit_quad).
  assert (Hbig : Cmul z (Cmul (Cminus z C1) W) = Cmul (RtoC (- (/ 4 + t ^ 2))) W)
    by (rewrite <- Hzd; ring).
  rewrite Hbig. unfold W.
  cbn [Re Im Cadd Cmul RtoC Copp]. field.
Qed.

Print Assumptions xir_reduction.
