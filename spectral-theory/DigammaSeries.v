(* ================================================================= *)
(*  DigammaSeries.v  --  the digamma partial-fraction series.          *)
(*                                                                    *)
(*     psi(z) = Gamma'/Gamma (z) = - gamma - 1/z                       *)
(*                                 - sum_{k>=1} [ 1/(k+z) - 1/k ]      *)
(*                                                                    *)
(*  on Re z > 0.  This is the one identity that turns the repo's       *)
(*  ExplicitFormulaDigamma.digamma -- which is defined as the opaque   *)
(*  quotient  dG * /GammaC z  and carries no information at all --     *)
(*  into something one can BOUND.  The bound itself is DigammaBound.v. *)
(*                                                                    *)
(*  Nothing analytic is proved here.  Every ingredient already exists; *)
(*  they had simply never been multiplied together:                    *)
(*                                                                    *)
(*    GammaArg.GammaC_PcW    Gamma(z) * Pc(z) = 1 on Re z > 0          *)
(*    GammaExpLog.Cexpf_Lf   e^{Lf z} = Wc z, the two forms of Pc       *)
(*    GammaCLogSum.L_holo    is_Cderiv Lf z (Sderiv z)                 *)
(*    GammaCLogSum.Sderiv_series                                       *)
(*                           Sderiv z = sum_k [1/(k+z) - 1/k]          *)
(*                                                                    *)
(*  The derivation is the classical one: differentiate Gamma . Pc = 1. *)
(*  Because the product is CONSTANT on an open set its derivative is 0,*)
(*  so  Gamma' Pc + Gamma Pc' = 0, and dividing by Gamma . Pc = 1 turns *)
(*  that into  Gamma'/Gamma = - Pc'/Pc.  Since                          *)
(*     Pc z = z e^{gamma z} e^{Lf z},                                  *)
(*  the logarithmic derivative of Pc is 1/z + gamma + Lf'(z), and       *)
(*  Lf' = Sderiv is exactly the series.                                 *)
(*                                                                    *)
(*  The 1/Gamma step needs no division lemma: Gamma . Pc = 1 says Pc   *)
(*  IS 1/Gamma, so  digamma z dG = dG * /Gamma z = dG * Pc z.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull Holomorphic CDeriv CHoloCalculus
        CAnalyticTower CDerivUnique CexpfDeriv CZetaDeriv2 PerronRemovable
        CSeries CDerivLine EulerMascheroni
        GammaC GammaCNe0 GammaCLogSum GammaCLogTerm GammaCWeierstrass
        GammaExpLog GammaArg CZetaXiComplex ExplicitFormulaDigamma.
Open Scope R_scope.

(* the exponential form of the reciprocal Weierstrass factor *)
Notation PcL := (GammaCNe0.Pc GammaCLogSum.Lf).

(* ----------------------------------------------------------------- *)
(*  Part A -- Gamma . PcL = 1, and PcL = 1/Gamma.                      *)
(* ----------------------------------------------------------------- *)

Lemma GammaC_PcL : forall z, 0 < Re z -> Cmul (GammaC z) (PcL z) = C1.
Proof.
  intros z Hz.
  assert (HP : GammaCNe0.Pc GammaCLogSum.Lf z = GammaCWeierstrass.Pc z).
  { unfold GammaCWeierstrass.Pc, GammaCNe0.Pc.
    rewrite (Cexpf_Lf z Hz). reflexivity. }
  rewrite HP. apply GammaC_PcW; exact Hz.
Qed.

Lemma PcL_is_inv : forall z, 0 < Re z -> Cinv (GammaC z) = PcL z.
Proof.
  intros z Hz.
  assert (HG : GammaC z <> C0) by (apply GammaC_ne0_final; exact Hz).
  transitivity (Cmul (Cinv (GammaC z)) C1); [ ring | ].
  rewrite <- (GammaC_PcL z Hz). field. exact HG.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the derivative of PcL.                                   *)
(* ----------------------------------------------------------------- *)

Lemma Re_pos_ne0 : forall z, 0 < Re z -> z <> C0.
Proof.
  intros z Hz Hc. rewrite Hc in Hz. unfold C0 in Hz; cbn [Re] in Hz; lra.
Qed.

Lemma PcL_deriv : forall z, 0 < Re z ->
  is_Cderiv PcL z
    (Cmul (PcL z) (Cadd (Cadd (Cinv z) (RtoC gamma)) (Sderiv z))).
Proof.
  intros z Hz.
  assert (Hz0 : z <> C0) by (apply Re_pos_ne0; exact Hz).
  (* d/dz (gamma z) = gamma *)
  pose proof (Cderiv_scal (RtoC gamma) (fun w => w) z C1 (Cderiv_id z)) as h1.
  (* d/dz e^{gamma z} *)
  pose proof (Cexpf_comp_deriv (fun w => Cmul (RtoC gamma) w) z
                (Cmul (RtoC gamma) C1) h1) as h2.
  (* d/dz (z e^{gamma z}) *)
  pose proof (Cderiv_mul (fun w => w) (fun w => Cexpf (Cmul (RtoC gamma) w))
                z C1 _ (Cderiv_id z) h2) as h3.
  (* d/dz e^{Lf z} = e^{Lf z} . Sderiv z *)
  pose proof (Cexpf_comp_deriv GammaCLogSum.Lf z (Sderiv z) (L_holo z Hz)) as h4.
  (* product *)
  pose proof (Cderiv_mul (fun w => Cmul w (Cexpf (Cmul (RtoC gamma) w)))
                (fun w => Cexpf (GammaCLogSum.Lf w)) z _ _ h3 h4) as h5.
  eapply is_Cderiv_eq; [ exact h5 | ].
  unfold GammaCNe0.Pc. field. exact Hz0.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the product is locally constant, so its derivative is 0. *)
(* ----------------------------------------------------------------- *)

Lemma prod_deriv_zero : forall z, 0 < Re z ->
  is_Cderiv (fun w => Cmul (GammaC w) (PcL w)) z C0.
Proof.
  intros z Hz.
  apply (is_Cderiv_congr (fun w => Cmul (GammaC w) (PcL w))
           (fun _ : C => C1) z C0 (Re z)).
  - exact Hz.
  - intros w Hw. apply GammaC_PcL.
    pose proof (Cmod_Re_le (Cminus w z)) as HR.
    rewrite CDerivLine.Re_Cminus in HR.
    assert (Hd : Rabs (Re w - Re z) < Re z) by lra.
    apply Rabs_def2 in Hd. lra.
  - apply Cderiv_const.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part D -- the identity.                                            *)
(* ----------------------------------------------------------------- *)

Theorem digamma_series : forall z dG, 0 < Re z -> is_Cderiv GammaC z dG ->
  digamma z dG = Copp (Cadd (Cadd (Cinv z) (RtoC gamma)) (Sderiv z)).
Proof.
  intros z dG Hz HdG.
  set (S := Cadd (Cadd (Cinv z) (RtoC gamma)) (Sderiv z)).
  pose proof (Cderiv_mul GammaC PcL z dG (Cmul (PcL z) S) HdG
                (PcL_deriv z Hz)) as Hm.
  pose proof (is_Cderiv_unique _ _ _ _ Hm (prod_deriv_zero z Hz)) as Heq.
  (* Heq : dG * PcL z + GammaC z * (PcL z * S) = C0 *)
  assert (Hs : Cmul (GammaC z) (Cmul (PcL z) S) = S).
  { transitivity (Cmul (Cmul (GammaC z) (PcL z)) S);
      [ ring | rewrite (GammaC_PcL z Hz); ring ]. }
  rewrite Hs in Heq.
  unfold digamma. rewrite (PcL_is_inv z Hz).
  transitivity (Cminus (Cadd (Cmul dG (PcL z)) S) S); [ ring | ].
  rewrite Heq. ring.
Qed.

Print Assumptions digamma_series.

(* ----------------------------------------------------------------- *)
(*  Part E -- the same, with the series spelled out termwise.          *)
(*  gterm n z = 1/((n+1)+z) - 1/(n+1)  (GammaCLogTerm.v:54)            *)
(* ----------------------------------------------------------------- *)

Corollary digamma_series_explicit : forall z dG,
  0 < Re z -> is_Cderiv GammaC z dG ->
  exists Sv, Cseries_cv (fun k => gterm k z) Sv
             /\ digamma z dG = Copp (Cadd (Cadd (Cinv z) (RtoC gamma)) Sv).
Proof.
  intros z dG Hz HdG. exists (Sderiv z).
  split; [ apply Sderiv_series; exact Hz | apply digamma_series; assumption ].
Qed.

Print Assumptions digamma_series_explicit.

(* ================================================================= *)
(*  END DigammaSeries.v                                               *)
(* ================================================================= *)
