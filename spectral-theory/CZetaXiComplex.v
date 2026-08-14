(* ================================================================= *)
(*  CZetaXiComplex.v   (closing the zetaC <-> XiC continuation gap)     *)
(*                                                                    *)
(*  PHASE A: the COMPLEX completed-zeta identity on Re z > 1.          *)
(*                                                                    *)
(*    XiC z = (1/2) z (z-1) . pi^{-z/2} . GammaC(z/2) . zF z           *)
(*                                                for all Re z > 1.     *)
(*                                                                    *)
(*  Currently only the REAL (s>1) version (ZetaXiLink.XiC_is_completed *)
(*  _zeta) exists.  We lift it to complex z via the half-plane         *)
(*  identity theorem CWalk.reach (shifted to Re>1): both sides are      *)
(*  holomorphic there (no pole, z<>1 automatic) and agree on the real   *)
(*  ray (1,oo).  This de-risks the reach-application + RHS-holomorphy   *)
(*  machinery reused by Phases B/C (the strip / zero-set closure).      *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CPower GammaC GammaCFE RiemannXiEntire ZetaXiLink ZetaFn CZeta
        Ell2ZetaCont GammaReal CWalk.
Open Scope R_scope.

(* affine building blocks, so Cderiv_comp_affine applies verbatim *)
Definition halfz (z : C) : C := Cadd (Cmul (RtoC (/ 2)) z) C0.          (* z/2   *)
Definition mhalfz (z : C) : C := Cadd (Cmul (RtoC (- / 2)) z) C0.       (* -z/2  *)

Definition archexp (z : C) : C := Cpw PI (mhalfz z).                    (* pi^{-z/2} *)
Definition prefac (z : C) : C := Cmul (RtoC (/ 2)) (Cmul z (Cminus z C1)). (* 1/2 z(z-1) *)
Definition RHSz (z : C) : C :=
  Cmul (Cmul (prefac z) (Cmul (archexp z) (GammaC (halfz z)))) (zF z).
Definition Dz (z : C) : C := Cminus (XiC z) (RHSz z).

(* ----------------------------------------------------------------- *)
(*  holomorphy of the RHS on Re z > 1                                *)
(* ----------------------------------------------------------------- *)

Lemma archexp_holo : forall z, exists d, is_Cderiv archexp z d.
Proof.
  intro z. unfold archexp, mhalfz.
  eexists. apply (Cderiv_comp_affine (fun v => Cpw PI v) (RtoC (- / 2)) C0 z).
  apply Cpw_deriv. exact PI_RGT_0.
Qed.

Lemma prefac_holo : forall z, exists d, is_Cderiv prefac z d.
Proof.
  intro z. unfold prefac. eexists.
  apply (Cderiv_mul (fun _ => RtoC (/ 2)) (fun w => Cmul w (Cminus w C1))).
  - apply Cderiv_const.
  - apply (Cderiv_mul (fun w => w) (fun w => Cminus w C1)).
    + apply Cderiv_id.
    + apply (Cderiv_minus (fun w => w) (fun _ => C1)); [ apply Cderiv_id | apply Cderiv_const ].
Qed.

Lemma gammahalf_holo : forall z, 0 < Re z -> exists d, is_Cderiv (fun w => GammaC (halfz w)) z d.
Proof.
  intros z Hz. unfold halfz.
  assert (Hh : 0 < Re (Cadd (Cmul (RtoC (/ 2)) z) C0))
    by (unfold Cadd, Cmul, RtoC, C0; cbn [Re Im]; lra).
  eexists. apply (Cderiv_comp_affine GammaC (RtoC (/ 2)) C0 z).
  apply (GammaC_entire (Cadd (Cmul (RtoC (/ 2)) z) C0) Hh).
Qed.

Lemma RHSz_holo : forall z, 1 < Re z -> exists d, is_Cderiv RHSz z d.
Proof.
  intros z Hz. unfold RHSz.
  destruct (prefac_holo z) as [d1 H1].
  destruct (archexp_holo z) as [d2 H2].
  destruct (gammahalf_holo z ltac:(lra)) as [d3 H3].
  assert (HinD : inDom z).
  { split; [ lra | intro Hc; apply (f_equal Re) in Hc;
             unfold Cminus, Cadd, Copp, C1, C0 in Hc; cbn [Re Im] in Hc; lra ]. }
  destruct (zF_holo z HinD) as [d4 H4].
  eexists.
  apply (Cderiv_mul (fun w => Cmul (prefac w) (Cmul (archexp w) (GammaC (halfz w)))) zF).
  - apply (Cderiv_mul prefac (fun w => Cmul (archexp w) (GammaC (halfz w)))).
    + exact H1.
    + apply (Cderiv_mul archexp (fun w => GammaC (halfz w))); [ exact H2 | exact H3 ].
  - exact H4.
Qed.

Lemma Dz_holo : forall z, 1 < Re z -> exists d, is_Cderiv Dz z d.
Proof.
  intros z Hz. unfold Dz.
  destruct (XiC_entire z I) as [dx Hx].
  destruct (RHSz_holo z Hz) as [dr Hr].
  eexists. apply (Cderiv_minus XiC RHSz); [ exact Hx | exact Hr ].
Qed.

(* ----------------------------------------------------------------- *)
(*  shift to the standard half-plane:  F z := Dz (z+1)                *)
(* ----------------------------------------------------------------- *)
Definition Fsh (z : C) : C := Dz (Cadd (Cmul C1 z) C1).

Lemma Fsh_holo : forall z, 0 < Re z -> exists d, is_Cderiv Fsh z d.
Proof.
  intros z Hz. unfold Fsh.
  assert (Hz1 : 1 < Re (Cadd (Cmul C1 z) C1))
    by (unfold Cadd, Cmul, C1; cbn [Re Im]; lra).
  destruct (Dz_holo (Cadd (Cmul C1 z) C1) Hz1) as [d Hd].
  eexists. apply (Cderiv_comp_affine Dz C1 C1 z). exact Hd.
Qed.

Lemma Fsh_ptcont : forall z, 0 < Re z -> forall e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Fsh z') (Fsh z)) < e.
Proof.
  intros z Hz e He.
  destruct (Fsh_holo z Hz) as [d Hd].
  destruct (is_Cderiv_cont Fsh z d Hd e He) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros z' Hz'. pose proof (Hc (Cminus z' z) Hz') as Hcc.
  replace (Cadd z (Cminus z' z)) with z' in Hcc by ring. exact Hcc.
Qed.

(* ----------------------------------------------------------------- *)
(*  the RHS agrees with XiC on the real ray  s > 1                    *)
(* ----------------------------------------------------------------- *)
Lemma Fsh_ray : forall s, 0 < s -> Fsh (mkC s 0) = C0.
Proof.
  intros s Hs. unfold Fsh.
  replace (Cadd (Cmul C1 (mkC s 0)) C1) with (RtoC (s + 1))
    by (apply Ceq; unfold Cadd, Cmul, C1, RtoC; cbn [Re Im]; ring).
  unfold Dz. set (t := s + 1).
  assert (Ht0 : 0 < t) by (unfold t; lra).
  assert (Ht1 : t <> 1) by (unfold t; lra).
  assert (Ht2 : 0 < t / 2) by (unfold t; lra).
  assert (Htg : 1 < t) by (unfold t; lra).
  (* XiC (RtoC t) via XiC_is_completed_zeta *)
  rewrite (XiC_is_completed_zeta t Ht0 Ht1 Ht2 Htg).
  (* RHSz (RtoC t) = RtoC (same product) *)
  assert (HR : RHSz (RtoC t) =
    RtoC (/ 2 * t * ((t - 1)
          * (Rpower PI (- (t / 2)) * Gam (t / 2) Ht2 * zeta_cont t Ht0 Ht1)))).
  { unfold RHSz, prefac, archexp, mhalfz, halfz.
    assert (H0t : 0 < Re (RtoC t)) by (unfold RtoC; cbn [Re]; exact Ht0).
    assert (H1t : Cminus C1 (RtoC t) <> C0)
      by (unfold Cminus, C1, RtoC, C0, Copp; intro Hc; apply (f_equal Re) in Hc;
          cbn [Re Im] in Hc; lra).
    (* archexp factor *)
    replace (Cadd (Cmul (RtoC (- / 2)) (RtoC t)) C0) with (RtoC (- (t / 2)))
      by (apply Ceq; unfold Cadd, Cmul, RtoC, C0; cbn [Re Im]; field).
    rewrite Cpw_RtoC.
    (* GammaC factor *)
    replace (Cadd (Cmul (RtoC (/ 2)) (RtoC t)) C0) with (RtoC (t / 2))
      by (apply Ceq; unfold Cadd, Cmul, RtoC, C0; cbn [Re Im]; field).
    rewrite (GammaC_agree (t / 2) Ht2).
    (* zF factor *)
    rewrite (zF_eq (RtoC t) H0t H1t), (zetaC_agree t Ht0 Ht1 H0t H1t).
    (* now all RtoC; collapse via the ring hom *)
    unfold Cminus, Cmul, Cadd, RtoC, Copp, C1; apply Ceq; cbn [Re Im]; field. }
  rewrite HR. unfold Cminus, Cadd, Copp, RtoC, C0; apply Ceq; cbn [Re Im]; field.
Qed.

(* ----------------------------------------------------------------- *)
(*  the identity, complex, on Re z > 1                               *)
(* ----------------------------------------------------------------- *)
Theorem XiC_completed_complex : forall z, 1 < Re z ->
  XiC z = RHSz z.
Proof.
  intros z Hz.
  assert (Hshift : Fsh (Cminus z C1) = C0).
  { apply (reach Fsh Fsh_ptcont Fsh_holo Fsh_ray).
    unfold Cminus, C1, Copp; cbn [Re Im]; lra. }
  unfold Fsh in Hshift.
  replace (Cadd (Cmul C1 (Cminus z C1)) C1) with z in Hshift
    by (apply Ceq; unfold Cadd, Cmul, Cminus, C1, Copp; cbn [Re Im]; ring).
  unfold Dz in Hshift.
  transitivity (Cadd (Cminus (XiC z) (RHSz z)) (RHSz z)); [ ring | ].
  rewrite Hshift. ring.
Qed.

Print Assumptions XiC_completed_complex.
