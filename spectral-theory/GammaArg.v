(* ================================================================= *)
(*  GammaArg.v  --  Stage 3 payoff: the direction of Gamma on the      *)
(*  critical line, as an explicit convergent arctan series.           *)
(*                                                                    *)
(*  Combining the exp/log bridge (GammaExpLog) with the product's      *)
(*  angle (GammaDir) and the strip factorisation (XirSignZ):          *)
(*                                                                    *)
(*     Uvec t = Cexp (theta t),                                        *)
(*     theta t = -(t/2) ln pi - Pang (1/4 + i t/2),                    *)
(*     Pang z = atan(Im z/Re z) + gamma Im z                           *)
(*              + sum_{k>=1} [ atan(Im z/(k+Re z)) - Im z/k ],         *)
(*                                                                    *)
(*  hence  Z(t) = cos(theta t) Re zeta - sin(theta t) Im zeta,         *)
(*  and    xir t = -c(t) Z(t)  with c(t) > 0  (XirSignZ).             *)
(*                                                                    *)
(*  Nothing here computes |Gamma|.  The modulus of the Weierstrass     *)
(*  product converges only like |z|^2/N, the angle like Im z/N, and    *)
(*  only the angle is needed -- which is the whole reason the sign of  *)
(*  Z is cheap to certify where the sign of xir is not.                *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra.
Require Import ComplexField Cmodulus EulerFormula CexpFull Holomorphic
        GammaC ZetaFn CZetaXiComplex CoherenceSingularity XirSignZ
        CPolarDir GammaDir GammaExpLog GammaCWeierstrass GammaCNe0
        EulerMascheroni CWalk.
Open Scope R_scope.

(* ---- Gamma * Pc = 1 for the PRODUCT form of Pc ---- *)

Theorem GammaC_PcW : forall z, 0 < Re z ->
  Cmul (GammaC z) (GammaCWeierstrass.Pc z) = C1.
Proof.
  intros z Hz.
  assert (HP : GammaCWeierstrass.Pc z = GammaCNe0.Pc GammaCLogSum.Lf z).
  { unfold GammaCWeierstrass.Pc, GammaCNe0.Pc.
    rewrite (Cexpf_Lf z Hz). reflexivity. }
  rewrite HP.
  pose proof (CWalk.reach (GammaCNe0.Fc GammaCLogSum.Lf)
                (GammaCNe0.Fc_ptc GammaCLogSum.Lf GammaCLogSum.Lf_holo)
                (GammaCNe0.Fc_holo GammaCLogSum.Lf GammaCLogSum.Lf_holo)
                (GammaCNe0.Fc_ray GammaCLogSum.Lf GammaCLogSum.Lf_agree) z Hz) as HF.
  unfold GammaCNe0.Fc in HF.
  transitivity (Cadd (Cminus (Cmul (GammaC z) (GammaCNe0.Pc GammaCLogSum.Lf z)) C1) C1);
    [ ring | rewrite HF; ring ].
Qed.

Theorem dir_GammaC : forall z, 0 < Re z -> 0 <= Im z ->
  PosDir (- Pang z) (GammaC z).
Proof.
  intros z Hx Hy.
  assert (Hne : GammaCWeierstrass.Pc z <> C0).
  { intro E. pose proof (GammaC_PcW z Hx) as H. rewrite E in H.
    assert (Hz0 : Cmul (GammaC z) C0 = C0) by ring. rewrite Hz0 in H.
    symmetry in H. exact (C1_neq_C0 H). }
  assert (HG : GammaC z = Cinv (GammaCWeierstrass.Pc z)).
  { transitivity (Cmul (Cmul (GammaC z) (GammaCWeierstrass.Pc z))
                    (Cinv (GammaCWeierstrass.Pc z)));
      [ field; exact Hne | rewrite (GammaC_PcW z Hx); ring ]. }
  rewrite HG. apply PosDir_inv.
  apply dir_Pc; [ exact Hx | exact Hy | apply Wc_ne0; exact Hx ].
Qed.

(* ---- the critical line ---- *)

Definition theta (t : R) : R :=
  - (t / 2) * ln PI + - Pang (mkC (/ 4) (t / 2)).

Theorem Uvec_eq : forall t, 0 <= t -> Uvec t = Cexp (theta t).
Proof.
  intros t Ht.
  assert (Hdir : PosDir (theta t) (Afac t)).
  { unfold Afac, theta. apply PosDir_mul.
    - assert (E : Im (Cmul (mhalfz (crit t)) (RtoC (ln PI))) = - (t / 2) * ln PI)
        by (unfold mhalfz, crit, Cmul, Cadd, RtoC, C0; cbn [Re Im]; field).
      unfold archexp, Cpw. rewrite <- E. apply dir_Cexpf.
    - rewrite halfz_crit. apply dir_GammaC; cbn [Re Im]; lra. }
  unfold Uvec, Amod. apply PosDir_unit. exact Hdir.
Qed.

Theorem Zfun_polar : forall t, 0 <= t ->
  Zfun t = cos (theta t) * Re (zF (crit t)) - sin (theta t) * Im (zF (crit t)).
Proof.
  intros t Ht. unfold Zfun. rewrite (Uvec_eq t Ht).
  unfold Cexp, Cmul; cbn [Re Im]. ring.
Qed.

(* the whole Stage 1-3 chain in one statement *)
Corollary xir_polar : forall t, 0 <= t ->
  xir t = - cpos t *
    (cos (theta t) * Re (zF (crit t)) - sin (theta t) * Im (zF (crit t))).
Proof.
  intros t Ht. rewrite (xir_sign_Z t), (Zfun_polar t Ht). reflexivity.
Qed.
