(* ================================================================= *)
(*  ExplicitFormulaXiLogDeriv.v  —  Stage C core, brick 3 (capstone):    *)
(*  the assembled  xi'/xi <-> zeta'/zeta  BRIDGE IDENTITY.               *)
(*                                                                    *)
(*  From the completed-xi product  XiC = prefac . archexp . GammaC(z/2) .  *)
(*  zF  (XiC_completed_complex, on Re z > 1) and the four factors' log-    *)
(*  derivatives (bricks 1-2 of this Stage-C core), the product rule gives  *)
(*  the master bridge identity:                                           *)
(*                                                                    *)
(*   XiC_logderiv :  xi'(z) = xi(z) . [ (1/z + 1/(z-1))                    *)
(*                                    + (-1/2 ln pi)                       *)
(*                                    + (1/2 digamma(z/2))                 *)
(*                                    + (zF'/zF) ]     (on Re z > 1)       *)
(*                                                                    *)
(*  equivalently  xi'/xi = zeta'/zeta + 1/z + 1/(z-1) - 1/2 ln pi          *)
(*                         + 1/2 (Gamma'/Gamma)(z/2),  i.e.                *)
(*     zeta'/zeta = xi'/xi - 1/z - 1/(z-1) + 1/2 ln pi                     *)
(*                  - 1/2 (Gamma'/Gamma)(z/2).                            *)
(*                                                                    *)
(*  This is THE identity carrying the zeros side (xi'/xi, poles = the      *)
(*  nontrivial zeros) to the prime side (zeta'/zeta = sum Lam(n) n^{-s}).  *)
(*  Assembled via a generic log-derivative product rule (mul_logderiv,     *)
(*  f'=a.f & g'=b.g => (fg)'=(a+b).fg) over the four factors, transferred  *)
(*  from RHSz to XiC by is_Cderiv_congr on the open half-plane Re > 1      *)
(*  (where XiC = RHSz).  zF (the bare holomorphic zeta, ZetaFn) supplies   *)
(*  a clean is_Cderiv, and zF <> 0 on Re > 1 comes from zetaC_nonzero.     *)
(*  Parametrised on the GammaC- and zF-derivative witnesses (dG, dz).      *)
(*                                                                    *)
(*  This completes the ARCHIMEDEAN bridge.  The one remaining Stage-C      *)
(*  input is xi'/xi itself as a sum over zeros -- the HADAMARD PRODUCT for  *)
(*  xi -- the deep, RH-adjacent piece (also the source of the growth       *)
(*  bounds vanishing the far contour edges of the explicit formula).       *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv CHoloCalculus
        CZetaDeriv2 CDerivLine CSeries PerronRemovable GammaC GammaCNe0 RiemannXiEntire CZetaXiComplex ZetaFn
        CEulerProductZeta CDirichlet
        ExplicitFormulaXiZetaBridge ExplicitFormulaDigamma.
Open Scope R_scope.

(* product rule in log-derivative form:  f'=a.f, g'=b.g  =>  (fg)'=(a+b).fg *)
Lemma mul_logderiv : forall f g z a b,
  is_Cderiv f z (Cmul a (f z)) -> is_Cderiv g z (Cmul b (g z)) ->
  is_Cderiv (fun w => Cmul (f w) (g w)) z (Cmul (Cadd a b) (Cmul (f z) (g z))).
Proof.
  intros f g z a b Hf Hg.
  apply (is_Cderiv_eq _ _ (Cadd (Cmul (Cmul a (f z)) (g z)) (Cmul (f z) (Cmul b (g z))))).
  - apply Cderiv_mul; assumption.
  - ring.
Qed.

Lemma C1_minus_ne0 : forall z, 1 < Re z -> Cminus C1 z <> C0.
Proof.
  intros z Hz Hc. apply (f_equal Re) in Hc.
  unfold Cminus, C1, C0 in Hc; cbn [Re] in Hc. lra.
Qed.

Lemma prefac_logform : forall z, z <> C0 -> Cminus z C1 <> C0 ->
  is_Cderiv prefac z (Cmul (Cadd (Cinv z) (Cinv (Cminus z C1))) (prefac z)).
Proof.
  intros z Hz Hz1.
  apply (is_Cderiv_eq _ _ (dprefac z)); [ apply prefac_deriv | ].
  unfold dprefac, prefac. field. split; assumption.
Qed.

Lemma zF_logform : forall z dz, is_Cderiv zF z dz -> zF z <> C0 ->
  is_Cderiv zF z (Cmul (Cmul dz (Cinv (zF z))) (zF z)).
Proof.
  intros z dz Hdz Hne.
  apply (is_Cderiv_eq _ _ dz); [ exact Hdz | ].
  field. exact Hne.
Qed.

Lemma zF_ne0_gt1 : forall z, 1 < Re z -> zF z <> C0.
Proof.
  intros z Hz.
  assert (H0 : 0 < Re z) by lra.
  assert (H1 : Cminus C1 z <> C0) by (apply C1_minus_ne0; exact Hz).
  rewrite (zF_eq z H0 H1). apply (zetaC_nonzero z Hz H0 H1).
Qed.

(* THE BRIDGE IDENTITY:  xi' = xi * [ (1/z+1/(z-1)) + (-1/2 ln pi)
                                     + (1/2 digamma(z/2)) + (zF'/zF) ] *)
Theorem XiC_logderiv : forall z (Hz : 1 < Re z) dG dz,
  is_Cderiv GammaC (halfz z) dG -> is_Cderiv zF z dz ->
  is_Cderiv XiC z
    (Cmul (Cadd (Cadd (Cinv z) (Cinv (Cminus z C1)))
                (Cadd (RtoC (- / 2 * ln PI))
                      (Cadd (Cmul (RtoC (/ 2)) (digamma (halfz z) dG))
                            (Cmul dz (Cinv (zF z))))))
          (XiC z)).
Proof.
  intros z Hz dG dz HdG Hdz.
  assert (Hz0 : 0 < Re z) by lra.
  assert (Hz1 : z <> C0) by (intro E; apply (f_equal Re) in E; unfold C0 in E; cbn [Re] in E; lra).
  assert (Hz1' : Cminus z C1 <> C0)
    by (intro E; apply (f_equal Re) in E; unfold Cminus, C1, C0 in E; cbn [Re] in E; lra).
  (* factor log-derivatives *)
  pose proof (prefac_logform z Hz1 Hz1') as Hp.
  pose proof (archexp_deriv z) as Ha; unfold darchexp in Ha.
  pose proof (gammahalf_deriv_logform z Hz0 dG HdG) as Hg.
  pose proof (zF_logform z dz Hdz (zF_ne0_gt1 z Hz)) as Hz'.
  (* assemble  archexp * GammaC(z/2) *)
  pose proof (mul_logderiv archexp (fun w => GammaC (halfz w)) z
                (RtoC (- / 2 * ln PI)) (Cmul (RtoC (/ 2)) (digamma (halfz z) dG))
                Ha Hg) as Hag.
  (* prefac * (archexp * GammaC(z/2)) *)
  pose proof (mul_logderiv prefac (fun w => Cmul (archexp w) (GammaC (halfz w))) z
                (Cadd (Cinv z) (Cinv (Cminus z C1)))
                (Cadd (RtoC (- / 2 * ln PI)) (Cmul (RtoC (/ 2)) (digamma (halfz z) dG)))
                Hp Hag) as Hpag.
  (* ... * zF *)
  pose proof (mul_logderiv (fun w => Cmul (prefac w) (Cmul (archexp w) (GammaC (halfz w)))) zF z
                (Cadd (Cadd (Cinv z) (Cinv (Cminus z C1)))
                      (Cadd (RtoC (- / 2 * ln PI)) (Cmul (RtoC (/ 2)) (digamma (halfz z) dG))))
                (Cmul dz (Cinv (zF z))) Hpag Hz') as Hfull.
  cbn beta in Hfull.
  (* Hfull : is_Cderiv RHSz z ( LD * RHSz z ) *)
  (* transfer to XiC via XiC = RHSz on Re>1 *)
  assert (Hcongr : is_Cderiv XiC z
    (Cmul (Cadd (Cadd (Cinv z) (Cinv (Cminus z C1)))
                (Cadd (RtoC (- / 2 * ln PI))
                      (Cadd (Cmul (RtoC (/ 2)) (digamma (halfz z) dG))
                            (Cmul dz (Cinv (zF z))))))
          (RHSz z))).
  { apply (is_Cderiv_congr XiC RHSz z _ (Re z - 1)); [ lra | | ].
    - intros w Hw. apply XiC_completed_complex.
      pose proof (Cmod_Re_le (Cminus w z)) as HR. rewrite Re_Cminus in HR.
      assert (Rabs (Re w - Re z) < Re z - 1) by lra.
      apply Rabs_def2 in H. lra.
    - unfold RHSz. eapply is_Cderiv_eq; [ exact Hfull | ring ]. }
  rewrite (XiC_completed_complex z Hz). exact Hcongr.
Qed.

Print Assumptions XiC_logderiv.
