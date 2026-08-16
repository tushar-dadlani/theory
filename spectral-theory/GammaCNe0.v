(* ================================================================= *)
(*  GammaCNe0.v   (GammaC != 0 on {Re>0}; the reach glue, C.3.3)          *)
(*                                                                    *)
(*  Route B, file 3/3.  Parametrised by the file-2 deliverable: the       *)
(*  complex log-sum  Lf = L = Sum_k (log(1+z/k) - z/k),  holomorphic on    *)
(*  {Re>0} and agreeing on the real axis with the real  Winf.  From this   *)
(*  the reciprocal Weierstrass factor  Pc z = z e^{gamma z} e^{L z}  is     *)
(*  holomorphic and satisfies  Pc(RtoC s) = RtoC(Pval s).  Then             *)
(*  F = GammaC.Pc - 1  is holomorphic, continuous, and vanishes on R+       *)
(*  (GammaC_agree + Pc_agree + real_weierstrass), so CWalk.reach gives       *)
(*  GammaC.Pc = 1 on {Re>0}, hence GammaC != 0, discharging the strip        *)
(*  hypothesis of CZetaStripId.XiC_zero_iff_zetaC_zero.                       *)
(*                                                                    *)
(*  Once file 2 (GammaCLogSum) provides Lf/Lf_holo/Lf_agree, GammaC_ne0     *)
(*  and the strip equivalence become UNCONDITIONAL.                        *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull Holomorphic CDeriv CHoloCalculus CAnalyticTower
        CWalk GammaC GammaReal GammaWeierstrass EulerMascheroni CexpfDeriv
        CZetaXiComplex CZetaStripId CZetaDeriv2 RiemannXiEntire CZeta.
Open Scope R_scope.

Section GammaCNe0.
Variable Lf : C -> C.
Hypothesis Lf_holo : forall z, 0 < Re z -> exists d, is_Cderiv Lf z d.
Hypothesis Lf_agree : forall s (Hs : 0 < s), Lf (RtoC s) = RtoC (Winf s Hs).

(* the reciprocal Weierstrass factor  Pc z = z * e^{gamma z} * e^{L z} *)
Definition Pc (z : C) : C := Cmul (Cmul z (Cexpf (Cmul (RtoC gamma) z))) (Cexpf (Lf z)).

Lemma egz_holo : forall z, exists d, is_Cderiv (fun w => Cexpf (Cmul (RtoC gamma) w)) z d.
Proof.
  intro z. eexists.
  apply (Cexpf_comp_deriv (fun w => Cmul (RtoC gamma) w) z (RtoC gamma)).
  apply (is_Cderiv_eq _ _ (Cmul (RtoC gamma) C1)); [ apply Cderiv_scal, Cderiv_id | ring ].
Qed.

Lemma Pc_holo : forall z, 0 < Re z -> exists d, is_Cderiv Pc z d.
Proof.
  intros z Hz. unfold Pc.
  destruct (egz_holo z) as [d1 Hd1]. destruct (Lf_holo z Hz) as [dL HdL].
  eexists. apply Cderiv_mul.
  - apply Cderiv_mul; [ apply Cderiv_id | exact Hd1 ].
  - apply (Cexpf_comp_deriv Lf z dL HdL).
Qed.

Lemma Pc_agree : forall s (Hs : 0 < s), Pc (RtoC s) = RtoC (Pval s Hs).
Proof.
  intros s Hs. unfold Pc. rewrite (Lf_agree s Hs), Cexpf_RtoC.
  replace (Cmul (RtoC gamma) (RtoC s)) with (RtoC (gamma * s))
    by (rewrite <- RtoC_mul; reflexivity).
  rewrite Cexpf_RtoC, <- RtoC_mul, <- RtoC_mul.
  unfold Pval. f_equal. replace (gamma * s) with (s * gamma) by ring. ring.
Qed.

(* F = GammaC * Pc - 1 *)
Definition Fc (z : C) : C := Cminus (Cmul (GammaC z) (Pc z)) C1.

Lemma Fc_holo : forall z, 0 < Re z -> exists d, is_Cderiv Fc z d.
Proof.
  intros z Hz. unfold Fc. destruct (Pc_holo z Hz) as [dP HdP].
  eexists. apply Cderiv_minus.
  - apply Cderiv_mul; [ apply (GammaC_entire z Hz) | exact HdP ].
  - apply Cderiv_const.
Qed.

Lemma Fc_ptc : forall z, 0 < Re z -> forall e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Fc z') (Fc z)) < e.
Proof.
  intros z Hz e He. destruct (Fc_holo z Hz) as [d Hd].
  destruct (is_Cderiv_cont Fc z d Hd e He) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ]. intros z' Hz'.
  pose proof (Hc (Cminus z' z) Hz') as HH.
  replace (Cadd z (Cminus z' z)) with z' in HH by ring. exact HH.
Qed.

Lemma Fc_ray : forall s, 0 < s -> Fc (mkC s 0) = C0.
Proof.
  intros s Hs. unfold Fc.
  replace (mkC s 0) with (RtoC s) by reflexivity.
  rewrite (GammaC_agree s Hs), (Pc_agree s Hs), <- RtoC_mul, (real_weierstrass s Hs).
  apply Ceq; unfold RtoC, C1, Cminus, C0; cbn [Re Im]; ring.
Qed.

Theorem GammaC_ne0 : forall w, 0 < Re w -> GammaC w <> C0.
Proof.
  intros w Hw Hc.
  pose proof (reach Fc Fc_ptc Fc_holo Fc_ray w Hw) as HF.
  unfold Fc in HF. rewrite Hc in HF.
  assert (Hz0 : Cmul C0 (Pc w) = C0) by ring. rewrite Hz0 in HF.
  apply (f_equal Re) in HF. unfold Cminus, C0, C1 in HF; cbn [Re] in HF; lra.
Qed.

(* discharge the strip hypothesis of CZetaStripId.XiC_zero_iff_zetaC_zero *)
Theorem XiC_zero_iff_zetaC_zero_uncond :
  forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
    Re z < 1 -> (XiC z = C0 <-> zetaC z H0 H1 = C0).
Proof.
  intros z H0 H1 Hlt.
  apply (XiC_zero_iff_zetaC_zero z H0 H1 Hlt).
  apply GammaC_ne0.
  assert (HRe : Re (halfz z) = / 2 * Re z)
    by (unfold halfz, Cadd, Cmul, RtoC, C0; cbn [Re Im]; ring).
  rewrite HRe; lra.
Qed.

End GammaCNe0.

Print Assumptions GammaC_ne0.
