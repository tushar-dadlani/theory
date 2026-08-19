(* ================================================================= *)
(*  CLogFExp.v  —  Hadamard keystone, brick B (full):                   *)
(*  the holomorphic complex logarithm, in exponential form.             *)
(*                                                                    *)
(*    logF_exp : F holomorphic and zero-free on a disk (with F'         *)
(*    holomorphic and F'/F path-continuous) ==>                        *)
(*      exists G Cc, (G is a primitive of F'/F on the disk) /\          *)
(*                   (forall z in the disk, F z = Cc . Cexpf (G z)).    *)
(*                                                                    *)
(*  G = Log F (up to the additive constant folded into Cc = F(0).      *)
(*  e^{-G(0)}).  This is exactly what the zero-free MEAN VALUE PROPERTY *)
(*  (brick 3's other half) needs: |F| = |Cc|.e^{Re G}, so              *)
(*  ln|F| = ln|Cc| + Re G with Re G harmonic; and the constant Cc      *)
(*  cancels in ln|F(0)| = mean of ln|F| (so we never need G(0)=0).      *)
(*                                                                    *)
(*  Construction: G = primitive of g := F'/F (brick A,                 *)
(*  CPrimitiveDisk.primitive_on_disk); then H := F.e^{-G} has          *)
(*  is_Cderiv H z C0 (product rule + chain rule + F.(F'/F)=F'), so by   *)
(*  CDerivConst.Cderiv0_const it is CONSTANT = F(0).e^{-G(0)} =: Cc,    *)
(*  giving F = Cc.e^{G}.                                               *)
(*                                                                    *)
(*  Axiom-clean.  This closes brick B.                                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CexpfDeriv CSine EulerFormula CSegInt
        CPrimitiveDisk CDerivConst.
Open Scope R_scope.

Theorem logF_exp : forall (Rr : R) (F Fp : C -> C),
  0 < Rr ->
  (forall z, disk Rr z -> is_Cderiv F z (Fp z)) ->
  (forall z, disk Rr z -> exists d, is_Cderiv Fp z d) ->
  (forall z, disk Rr z -> F z <> C0) ->
  CcontC (fun w => Cmul (Fp w) (Cinv (F w))) ->
  exists (G : C -> C) (Cc : C),
    (forall z, disk Rr z -> is_Cderiv G z (Cmul (Fp z) (Cinv (F z)))) /\
    (forall z, disk Rr z -> F z = Cmul Cc (Cexpf (G z))).
Proof.
  intros Rr F Fp HR HFhol HFphol HFne0 HcontG.
  set (g := fun w : C => Cmul (Fp w) (Cinv (F w))).
  (* g = F'/F is holomorphic on the disk (quotient rule) *)
  assert (Hghol : forall z, disk Rr z -> exists d, is_Cderiv g z d).
  { intros z Hz. destruct (HFphol z Hz) as [dFp HdFp]. unfold g. eexists.
    apply Cderiv_div; [ exact HdFp | apply HFhol; exact Hz | apply HFne0; exact Hz ]. }
  destruct (primitive_on_disk Rr g HcontG HR Hghol) as [G HG].
  assert (HdiskC0 : disk Rr C0).
  { unfold disk. assert (Cmod C0 = 0) as H0 by (apply (proj2 (Cmod0 C0)); reflexivity).
    rewrite H0; exact HR. }
  (* H := F . e^{-G} has derivative 0 on the disk *)
  set (Hexp := fun w : C => Cmul (F w) (Cexpf (Copp (G w)))).
  assert (Hexp_deriv : forall z, disk Rr z -> is_Cderiv Hexp z C0).
  { intros z Hz.
    assert (HGz : is_Cderiv G z (g z)) by (apply HG; exact Hz).
    assert (Hexpder : is_Cderiv (fun w => Cexpf (Copp (G w))) z
                        (Cmul (Cexpf (Copp (G z))) (Copp (g z))))
      by (apply (Cexpf_comp_deriv (fun w => Copp (G w)) z (Copp (g z)));
          apply Cderiv_opp; exact HGz).
    pose proof (Cderiv_mul F (fun w => Cexpf (Copp (G w))) z (Fp z)
                  (Cmul (Cexpf (Copp (G z))) (Copp (g z)))
                  (HFhol z Hz) Hexpder) as Hprod.
    cbv beta in Hprod.
    assert (HFg : Cmul (F z) (g z) = Fp z).
    { unfold g.
      assert (HinvF : Cmul (F z) (Cinv (F z)) = C1)
        by (rewrite <- (Cinv_l (F z) (HFne0 z Hz)); ring).
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
  - intros z Hz. exact (HG z Hz).
  - intros z Hz.
    assert (Hc : Cmul (F z) (Cexpf (Copp (G z))) = Cmul (F C0) (Cexpf (Copp (G C0))))
      by exact (Cderiv0_const (disk Rr) (disk_convex Rr) Hexp Hexp_deriv z C0 Hz HdiskC0).
    rewrite <- Hc.
    replace (Cmul (Cmul (F z) (Cexpf (Copp (G z)))) (Cexpf (G z)))
       with (Cmul (F z) (Cmul (Cexpf (Copp (G z))) (Cexpf (G z)))) by ring.
    rewrite <- Cexpf_add.
    replace (Cadd (Copp (G z)) (G z)) with C0 by ring.
    rewrite Cexpf_C0. ring.
Qed.

Print Assumptions logF_exp.
