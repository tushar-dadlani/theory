(* ================================================================= *)
(*  CAnalyticTowerF.v  (identity-theorem plan, FE chain brick 3/4)      *)
(*                                                                    *)
(*  The derivative tower, specialised to a holomorphic F on the         *)
(*  |z| < Rr+1 disk.  The defining property: fseq 0 = F, i.e. the        *)
(*  Cauchy representation  (1/2 pi i) oint F(z)/(z-w) dz = F(w)          *)
(*  (cauchy_interior_dom), packaged through the origin clamp.  With      *)
(*  fseq_chain (fseq (S k) = (fseq k)') this exhibits F's all-orders     *)
(*  holomorphic derivative tower -- the holomorphic => analytic step.    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Factorial FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral CLeibniz RootsOfUnity CWindingOffCenter CCauchyAnalytic
        CRemovableExtDom CAnalyticTower.
Open Scope R_scope.

Lemma Cpow1 : forall x : C, Cpow x 1 = x.
Proof. intro x; cbn; ring. Qed.

Theorem fseq0_eq :
  forall (F : C -> C) (Rr : R) (HR : 0 < Rr) (HFc : CcontC F)
    (HFptc : forall z eps, 0 < eps -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps)
    (HFhol : forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv F z d),
  forall w, Cmod w < Rr / 2 -> fseq F Rr HR HFc 0 w = F w.
Proof.
  intros F Rr HR HFc HFptc HFhol w Hw.
  pose proof (Cmod_nonneg w) as Hcw.
  assert (HwR : Cmod w < Rr) by lra.
  assert (Harc : forall u, Cminus (arc Rr u) w <> C0)
    by (apply arc_ne_pt; [ exact HR | exact HwR ]).
  assert (Hcl : clampw Rr C0 w = w).
  { apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
    replace (Cminus w C0) with w by ring. lra. }
  assert (Hpc : Ccont (fun u => Cmul (Cmul (F (arc Rr u))
                        (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))).
  { assert (Hfe : (fun u => Cmul (Cmul (F (arc Rr u))
                        (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))
                  = Kwn F Rr 1 w).
    { apply functional_extensionality; intro u; unfold Kwn; rewrite Cpow1; reflexivity. }
    rewrite Hfe. apply (Kwn_cont F Rr 1 HFc w Harc). }
  assert (HPsi : Psi F Rr HR HFc 1 w = Cmul (mkC 0 (2 * PI)) (F w)).
  { unfold Psi, PhiN.
    transitivity (Cintf (fun u => Cmul (Cmul (F (arc Rr u))
                    (Cinv (Cminus (arc Rr u) w))) (arc' Rr u)) Hpc 0 (2 * PI)).
    - apply Cintf_ext. intro u. unfold Kwn. rewrite Hcl, Cpow1. reflexivity.
    - change (Cintf (fun u => Cmul (Cmul (F (arc Rr u))
                (Cinv (Cminus (arc Rr u) w))) (arc' Rr u)) Hpc 0 (2 * PI))
        with (pathint (arc Rr) (arc' Rr)
                (fun z => Cmul (F z) (Cinv (Cminus z w))) Hpc 0 (2 * PI)).
      destruct (HFhol w ltac:(lra)) as [dw Hdw].
      apply (cauchy_interior_dom F Rr w dw HR HwR Hdw HFptc
               (fun z Hz (_ : z <> w) => HFhol z Hz)). }
  unfold fseq.
  assert (H1 : RtoC (INR (fact 0)) = C1)
    by (change (fact 0) with 1%nat; rewrite INR_1; apply Ceq; reflexivity).
  rewrite H1, Cmul_1_l.
  change (Psi F Rr HR HFc (S 0)) with (Psi F Rr HR HFc 1).
  rewrite HPsi.
  assert (HXne : mkC 0 (2 * PI) <> C0)
    by (intro Hc; apply (f_equal Im) in Hc; cbn in Hc; generalize PI_RGT_0; lra).
  unfold cc. field. exact HXne.
Qed.

Print Assumptions fseq0_eq.
