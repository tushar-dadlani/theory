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
Require Import ComplexField RiemannXiEntire CoherenceSingularity ThetaTailEntire
        RiemannPsi CPowBase CBaseDeriv2 MellinElem CImproperIntegral.
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

(* ===== the two Re TC terms coincide (cos is even in t) ===== *)
(* Re(wkerC z u) = Psi(clamp u) . (clamp u)^{Re(z/2-1)} . cos(Im(z/2-1) ln(clamp u));
   z = 1/2+it and z = 1/2-it share Re(z/2-1) = -3/4 and opposite Im, so the cos
   (even) makes the integrands equal pointwise. *)
Lemma Re_wkerC_mirror : forall t u,
  Re (wkerC (Cminus C1 (crit t)) u) = Re (wkerC (crit t) u).
Proof.
  intros t u. unfold wkerC. rewrite !Re_RtoC_mul, !Re_Cpw.
  set (W1 := Cminus (Cmul (Cminus C1 (crit t)) (RtoC (/ 2))) C1).
  set (W2 := Cminus (Cmul (crit t) (RtoC (/ 2))) C1).
  assert (HRe : Re W1 = Re W2)
    by (unfold W1, W2, crit; cbn [Re Im Cmul Cminus Cadd Copp RtoC C1]; lra).
  assert (HIm : Im W1 = - Im W2)
    by (unfold W1, W2, crit; cbn [Re Im Cmul Cminus Cadd Copp RtoC C1]; lra).
  rewrite HRe.
  replace (Im W1 * ln (clamp u)) with (- (Im W2 * ln (clamp u)))
    by (rewrite HIm; ring).
  rewrite cos_neg. reflexivity.
Qed.

Lemma ReTC_mirror : forall t, Re (TC (Cminus C1 (crit t))) = Re (TC (crit t)).
Proof.
  intro t.
  destruct (TC_spec (Cminus C1 (crit t))) as [H1 _].
  destruct (TC_spec (crit t)) as [H2 _].
  apply (improper_unique
           (fun u => Re (wkerC (Cminus C1 (crit t)) u))
             (cont_RI _ (cont_wkerC_re (Cminus C1 (crit t))))
           (fun u => Re (wkerC (crit t) u)) (cont_RI _ (cont_wkerC_re (crit t)))
           (Re (TC (Cminus C1 (crit t)))) (Re (TC (crit t)))).
  - intros u _. apply Re_wkerC_mirror.
  - exact H1.
  - exact H2.
Qed.

(* the halved reduction: xir t = 1/2 - (1/4+t^2) . Re TC(1/2+it) *)
Theorem xir_reduction' : forall t,
  xir t = / 2 - (/ 4 + t ^ 2) * Re (TC (crit t)).
Proof.
  intro t. rewrite xir_reduction, ReTC_mirror. field.
Qed.

Print Assumptions xir_reduction'.
