(* ================================================================= *)
(*  CLogFExpEntire.v  —  Hadamard keystone, brick 3 piece (a):          *)
(*  the complex logarithm of an ENTIRE zero-free function, globally.    *)
(*                                                                    *)
(*    logF_exp_entire : F entire, F' entire, F zero-free everywhere,    *)
(*    F'/F path-continuous ==>                                         *)
(*      exists G Cc, (forall z, is_Cderiv G z (F'/F z)) /\             *)
(*                   (forall z, F z = Cc . Cexpf (G z)).               *)
(*                                                                    *)
(*  The entire analogue of CLogFExp.logF_exp: G = Log F is now entire   *)
(*  (via CPrimitiveEntire.primitive_entire), so the ENTIRE-function     *)
(*  mean value property (CCauchyFormula.M_const/meanval0) will apply    *)
(*  to it -- the remaining step toward the zero-free MVP (brick 3).     *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CexpfDeriv CSine EulerFormula CSegInt
        CPrimitiveDisk CDerivConst CPrimitiveEntire.
Open Scope R_scope.

Theorem logF_exp_entire : forall (F Fp : C -> C),
  (forall z, is_Cderiv F z (Fp z)) ->
  (forall z, exists d, is_Cderiv Fp z d) ->
  (forall z, F z <> C0) ->
  CcontC (fun w => Cmul (Fp w) (Cinv (F w))) ->
  exists (G : C -> C) (Cc : C),
    (forall z, is_Cderiv G z (Cmul (Fp z) (Cinv (F z)))) /\
    (forall z, F z = Cmul Cc (Cexpf (G z))).
Proof.
  intros F Fp HFhol HFphol HFne0 HcontG.
  set (g := fun w : C => Cmul (Fp w) (Cinv (F w))).
  assert (Hghol : forall z, exists d, is_Cderiv g z d).
  { intros z. destruct (HFphol z) as [dFp HdFp]. unfold g. eexists.
    apply Cderiv_div; [ exact HdFp | apply HFhol | apply HFne0 ]. }
  destruct (primitive_entire g HcontG Hghol) as [G HG].
  set (Hexp := fun w : C => Cmul (F w) (Cexpf (Copp (G w)))).
  assert (Hexp_deriv : forall z, is_Cderiv Hexp z C0).
  { intros z.
    assert (HGz : is_Cderiv G z (g z)) by (apply HG).
    assert (Hexpder : is_Cderiv (fun w => Cexpf (Copp (G w))) z
                        (Cmul (Cexpf (Copp (G z))) (Copp (g z))))
      by (apply (Cexpf_comp_deriv (fun w => Copp (G w)) z (Copp (g z)));
          apply Cderiv_opp; exact HGz).
    pose proof (Cderiv_mul F (fun w => Cexpf (Copp (G w))) z (Fp z)
                  (Cmul (Cexpf (Copp (G z))) (Copp (g z)))
                  (HFhol z) Hexpder) as Hprod.
    cbv beta in Hprod.
    assert (HFg : Cmul (F z) (g z) = Fp z).
    { unfold g.
      assert (HinvF : Cmul (F z) (Cinv (F z)) = C1)
        by (rewrite <- (Cinv_l (F z) (HFne0 z)); ring).
      transitivity (Cmul (Fp z) (Cmul (F z) (Cinv (F z)))); [ ring | ].
      rewrite HinvF; ring. }
    assert (Hgcontrib : Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Copp (g z)))
                        = Copp (Cmul (Fp z) (Cexpf (Copp (G z))))).
    { transitivity (Cmul (Cexpf (Copp (G z))) (Copp (Cmul (F z) (g z)))); [ ring | ].
      rewrite HFg. ring. }
    replace (Cadd (Cmul (Fp z) (Cexpf (Copp (G z))))
                  (Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Copp (g z)))))
       with C0 in Hprod by (rewrite Hgcontrib; ring).
    exact Hprod. }
  exists G, (Cmul (F C0) (Cexpf (Copp (G C0)))). split.
  - intros z. exact (HG z).
  - intros z.
    set (Rr := Cmod z + 1).
    assert (HR : 0 < Rr) by (unfold Rr; pose proof (Cmod_nonneg z); lra).
    assert (HzD : disk Rr z) by (unfold disk, Rr; lra).
    assert (HCm0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
    assert (HC0D : disk Rr C0)
      by (unfold disk, Rr; rewrite HCm0; pose proof (Cmod_nonneg z); lra).
    assert (Hc : Cmul (F z) (Cexpf (Copp (G z))) = Cmul (F C0) (Cexpf (Copp (G C0))))
      by exact (Cderiv0_const (disk Rr) (disk_convex Rr) Hexp
                  (fun w _ => Hexp_deriv w) z C0 HzD HC0D).
    rewrite <- Hc.
    replace (Cmul (Cmul (F z) (Cexpf (Copp (G z)))) (Cexpf (G z)))
       with (Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Cexpf (G z)))) by ring.
    rewrite <- Cexpf_add.
    replace (Cadd (Copp (G z)) (G z)) with C0 by ring.
    rewrite Cexpf_C0. ring.
Qed.

Print Assumptions logF_exp_entire.
