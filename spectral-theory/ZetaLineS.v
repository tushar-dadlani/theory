(* ================================================================= *)
(*  ZetaLineS.v  --  Re and Im of the trapezoid ingredients on ANY    *)
(*  vertical line Re s = sg, as explicit real expressions.            *)
(*                                                                    *)
(*  ZetaCrit.v does this at sg = 1/2 only.  The counting contour of    *)
(*  the RH programme needs zeta OFF the critical line, so the four     *)
(*  lemmas are re-proved with sg as a variable:                        *)
(*                                                                    *)
(*    g(x) = x^{-s} = x^{-sg} (cos(t ln x) - i sin(t ln x))            *)
(*    G(x) = x^{1-s}/(1-s) = x^{1-sg}(cos - i sin) . ((1-sg) + it)/D   *)
(*                                                                    *)
(*  with D = (1-sg)^2 + t^2.  As at sg = 1/2, everything on the right  *)
(*  is exp, ln, cos, sin of REAL arguments, so no complex interval     *)
(*  type is needed.                                                    *)
(*                                                                    *)
(*  TWO THINGS THAT ARE NOT COSMETIC.                                  *)
(*                                                                    *)
(*  (a) D can VANISH.  At sg = 1/2 it is 1/4 + t^2 > 0 outright; in    *)
(*      general (1-sg)^2 + t^2 is zero exactly at s = 1.  So Dts_pos   *)
(*      becomes a hypothesis, and it is precisely the condition        *)
(*      zetaC's own H1 : Cminus C1 s <> C0 already demands.            *)
(*                                                                    *)
(*  (b) THE SIGN.  D serves both |s-1|^2 and |1-s|^2 -- the same       *)
(*      number -- but the NUMERATORS differ in sign: the head term     *)
(*      1/(s-1) carries (sg-1)/D while the G term carries (1-sg)/D.    *)
(*      At sg = 1/2 those are -1/2 and +1/2, which is why ZetaEnclose  *)
(*      uses uq bare in Iquad' and negated in Izeta2.  Get this        *)
(*      backwards and the result type-checks and is false.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPowBase EulerFormula
        CZetaTerm CoherenceSingularity.
Open Scope R_scope.

Definition lineC (sg t : R) : C := mkC sg t.

Definition Dts (sg t : R) : R := (1 - sg) ^ 2 + t ^ 2.

(* D vanishes exactly at s = 1, which is also where zetaC is undefined *)
Lemma Dts_pos_iff : forall sg t, 0 < Dts sg t <-> (sg <> 1 \/ t <> 0).
Proof.
  intros sg t; unfold Dts; split.
  - intro H; destruct (Req_dec sg 1) as [Hs | Hs]; [ | left; exact Hs ].
    right; intro Ht; rewrite Hs, Ht in H; nra.
  - intros [Hs | Ht].
    + assert (Hne : 1 - sg <> 0) by (intro Hc; apply Hs; lra).
      pose proof (Rlt_0_sqr (1 - sg) Hne) as Hq; unfold Rsqr in Hq.
      pose proof (Rle_0_sqr t) as Hq2; unfold Rsqr in Hq2. nra.
    + pose proof (Rlt_0_sqr t Ht) as Hq; unfold Rsqr in Hq.
      pose proof (Rle_0_sqr (1 - sg)) as Hq2; unfold Rsqr in Hq2. nra.
Qed.

Lemma Dts_crit : forall t, Dts (/ 2) t = / 4 + t ^ 2.
Proof. intro t; unfold Dts; field. Qed.

Lemma lineC_crit : forall t, lineC (/ 2) t = crit t.
Proof. intro t; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  g(x) = x^{-s}                                                     *)
(* ----------------------------------------------------------------- *)

Lemma Re_gC_line : forall sg t x,
  Re (gC (lineC sg t) x) = exp (- sg * ln x) * cos (t * ln x).
Proof.
  intros sg t x. unfold gC, Cpw, Cexpf, Cexp, lineC, Copp, Cmul, RtoC.
  cbn [Re Im].
  replace (- sg * 0 + - t * ln x) with (- (t * ln x)) by ring.
  rewrite cos_neg.
  replace (- sg * ln x - - t * 0) with (- sg * ln x) by ring.
  ring.
Qed.

Lemma Im_gC_line : forall sg t x,
  Im (gC (lineC sg t) x) = - (exp (- sg * ln x) * sin (t * ln x)).
Proof.
  intros sg t x. unfold gC, Cpw, Cexpf, Cexp, lineC, Copp, Cmul, RtoC.
  cbn [Re Im].
  replace (- sg * 0 + - t * ln x) with (- (t * ln x)) by ring.
  rewrite sin_neg.
  replace (- sg * ln x - - t * 0) with (- sg * ln x) by ring.
  ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  G(x) = x^{1-s}/(1-s)                                              *)
(* ----------------------------------------------------------------- *)

Lemma Re_GC_line : forall sg t x, 0 < Dts sg t ->
  Re (GC (lineC sg t) x)
  = exp ((1 - sg) * ln x)
    * (cos (t * ln x) * ((1 - sg) / Dts sg t)
       + sin (t * ln x) * (t / Dts sg t)).
Proof.
  intros sg t x HD.
  unfold GC, Cpw, Cexpf, Cexp, lineC, Cminus, Cadd, Copp, Cmul, Cinv,
    Cnorm2, RtoC, C1.
  cbn [Re Im].
  replace ((1 - sg) * 0 + (0 - t) * ln x) with (- (t * ln x)) by ring.
  rewrite cos_neg, sin_neg.
  replace ((1 - sg) * ln x - (0 - t) * 0) with ((1 - sg) * ln x) by ring.
  unfold Dts in *.
  assert (H1 : (1 - sg) * (1 - sg) + (0 - t) * (0 - t) <> 0)
    by (apply Rgt_not_eq; nra).
  assert (H2 : (1 - sg) ^ 2 + t ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  field; repeat split; assumption.
Qed.

Lemma Im_GC_line : forall sg t x, 0 < Dts sg t ->
  Im (GC (lineC sg t) x)
  = exp ((1 - sg) * ln x)
    * (cos (t * ln x) * (t / Dts sg t)
       - sin (t * ln x) * ((1 - sg) / Dts sg t)).
Proof.
  intros sg t x HD.
  unfold GC, Cpw, Cexpf, Cexp, lineC, Cminus, Cadd, Copp, Cmul, Cinv,
    Cnorm2, RtoC, C1.
  cbn [Re Im].
  replace ((1 - sg) * 0 + (0 - t) * ln x) with (- (t * ln x)) by ring.
  rewrite cos_neg, sin_neg.
  replace ((1 - sg) * ln x - (0 - t) * 0) with ((1 - sg) * ln x) by ring.
  unfold Dts in *.
  assert (H1 : (1 - sg) * (1 - sg) + (0 - t) * (0 - t) <> 0)
    by (apply Rgt_not_eq; nra).
  assert (H2 : (1 - sg) ^ 2 + t ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  field; repeat split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  The head term 1/(s-1).  NOTE THE SIGN: (sg-1)/D, not (1-sg)/D.    *)
(* ----------------------------------------------------------------- *)

Lemma Re_Cinv_line : forall sg t, 0 < Dts sg t ->
  Re (Cinv (Cminus (lineC sg t) C1)) = - ((1 - sg) / Dts sg t).
Proof.
  intros sg t HD.
  unfold Cinv, Cminus, lineC, C1, Cnorm2; cbn [Re Im]. unfold Dts in *.
  assert (H1 : (sg - 1) * (sg - 1) + (t - 0) * (t - 0) <> 0)
    by (apply Rgt_not_eq; nra).
  assert (H2 : (1 - sg) ^ 2 + t ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  field; repeat split; assumption.
Qed.

Lemma Im_Cinv_line : forall sg t, 0 < Dts sg t ->
  Im (Cinv (Cminus (lineC sg t) C1)) = - (t / Dts sg t).
Proof.
  intros sg t HD.
  unfold Cinv, Cminus, lineC, C1, Cnorm2; cbn [Re Im]. unfold Dts in *.
  assert (H1 : (sg - 1) * (sg - 1) + (t - 0) * (t - 0) <> 0)
    by (apply Rgt_not_eq; nra).
  assert (H2 : (1 - sg) ^ 2 + t ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  field; repeat split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  Agreement with the critical-line originals -- a check that the     *)
(*  generalisation did not silently flip a sign.                       *)
(* ----------------------------------------------------------------- *)

Lemma Re_gC_line_crit : forall t x,
  Re (gC (lineC (/ 2) t) x) = Re (gC (crit t) x).
Proof. intros t x; rewrite lineC_crit; reflexivity. Qed.

Lemma Re_Cinv_line_crit : forall t,
  Re (Cinv (Cminus (lineC (/ 2) t) C1)) = - (/ 2 / (/ 4 + t ^ 2)).
Proof.
  intro t.
  assert (HD : 0 < Dts (/ 2) t) by (unfold Dts; nra).
  rewrite (Re_Cinv_line (/ 2) t HD), Dts_crit.
  replace (1 - / 2) with (/ 2) by field; reflexivity.
Qed.

Print Assumptions Re_GC_line.
Print Assumptions Re_Cinv_line.

(* ================================================================= *)
(*  END ZetaLineS.v -- the trapezoid ingredients on any vertical line. *)
(* ================================================================= *)
