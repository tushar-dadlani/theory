(* ================================================================= *)
(*  CZetaStripId.v   (Phase C2: the strip identity + zero link)         *)
(*                                                                    *)
(*  XiC z = (1/2) z . pi^{-z/2} . GammaC(z/2) . BfnT z   on all {Re>0}, *)
(*  where BfnT z = (z-1) zetaC z is the REGULAR completed factor.       *)
(*  Proved by continuing the Re>1 identity (Phase A) across the strip   *)
(*  via the from-region identity theorem region_reach (Phase C1):       *)
(*  both sides are holomorphic on {Re>0} (BfnT holo at z=1!) and agree   *)
(*  on {Re>1}.                                                          *)
(*                                                                    *)
(*  Corollary (no nonvanishing needed):                                *)
(*    zetaC z = 0  ==>  XiC z = 0   in the strip.                       *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CPower GammaC RiemannXiEntire ZetaFn CZeta
        CZetaXiComplex CZetaRegular6 CZetaMarchH.
Open Scope R_scope.

(* the regular completed right-hand side  (1/2) z pi^{-z/2} GammaC(z/2) BfnT z *)
Definition RHSc (z : C) : C :=
  Cmul (Cmul (Cmul (RtoC (/ 2)) z) (Cmul (archexp z) (GammaC (halfz z)))) (BfnT z).
Definition Dc (z : C) : C := Cminus (XiC z) (RHSc z).

Lemma RHSc_holo : forall z, 0 < Re z -> exists d, is_Cderiv RHSc z d.
Proof.
  intros z Hz. unfold RHSc.
  destruct (archexp_holo z) as [d2 H2].
  destruct (gammahalf_holo z Hz) as [d3 H3].
  destruct (BfnT_holo z Hz) as [d4 H4].
  eexists.
  apply (Cderiv_mul (fun w => Cmul (Cmul (RtoC (/ 2)) w) (Cmul (archexp w) (GammaC (halfz w))))
                    BfnT).
  - apply (Cderiv_mul (fun w => Cmul (RtoC (/ 2)) w)
                      (fun w => Cmul (archexp w) (GammaC (halfz w)))).
    + apply (Cderiv_mul (fun _ => RtoC (/ 2)) (fun w => w));
        [ apply Cderiv_const | apply Cderiv_id ].
    + apply (Cderiv_mul archexp (fun w => GammaC (halfz w))); [ exact H2 | exact H3 ].
  - exact H4.
Qed.

Lemma Dc_holo : forall z, 0 < Re z -> exists d, is_Cderiv Dc z d.
Proof.
  intros z Hz. unfold Dc.
  destruct (XiC_entire z I) as [dx Hx].
  destruct (RHSc_holo z Hz) as [dr Hr].
  eexists. apply (Cderiv_minus XiC RHSc); [ exact Hx | exact Hr ].
Qed.

Lemma Dc_ptc : forall z, 0 < Re z -> forall e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Dc z') (Dc z)) < e.
Proof.
  intros z Hz e He.
  destruct (Dc_holo z Hz) as [d Hd].
  destruct (is_Cderiv_cont Dc z d Hd e He) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros z' Hz'. pose proof (Hc (Cminus z' z) Hz') as Hcc.
  replace (Cadd z (Cminus z' z)) with z' in Hcc by ring. exact Hcc.
Qed.

Lemma Dc_vanish1 : forall z, 1 < Re z -> Dc z = C0.
Proof.
  intros z Hz. unfold Dc.
  assert (H0 : 0 < Re z) by lra.
  assert (Hne : Cminus C1 z <> C0)
    by (intro Hc; apply (f_equal Re) in Hc; unfold Cminus, Cadd, Copp, C1, C0 in Hc;
        cbn [Re Im] in Hc; lra).
  rewrite (XiC_completed_complex z Hz).
  assert (Heq : RHSz z = RHSc z).
  { unfold RHSz, RHSc, prefac. rewrite (BfnT_eq z H0 Hne). ring. }
  rewrite Heq. replace (Cminus (RHSc z) (RHSc z)) with C0 by ring. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE STRIP IDENTITY on all of {Re > 0}                            *)
(* ----------------------------------------------------------------- *)
Theorem XiC_completed_strip : forall z, 0 < Re z -> XiC z = RHSc z.
Proof.
  intros z Hz.
  assert (HD : Dc z = C0)
    by (apply (region_reach Dc Dc_ptc Dc_holo Dc_vanish1 z Hz)).
  unfold Dc in HD.
  transitivity (Cadd (Cminus (XiC z) (RHSc z)) (RHSc z)); [ ring | rewrite HD; ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  zeta zero  ==>  XiC zero   (no nonvanishing needed)              *)
(* ----------------------------------------------------------------- *)
Theorem zetaC_zero_implies_XiC_zero :
  forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
    zetaC z H0 H1 = C0 -> XiC z = C0.
Proof.
  intros z H0 H1 Hz0.
  rewrite (XiC_completed_strip z H0). unfold RHSc.
  assert (HB : BfnT z = C0).
  { rewrite (BfnT_eq z H0 H1), (zF_eq z H0 H1), Hz0. ring. }
  rewrite HB. ring.
Qed.

Print Assumptions XiC_completed_strip.
Print Assumptions zetaC_zero_implies_XiC_zero.
