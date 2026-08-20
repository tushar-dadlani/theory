(* ================================================================= *)
(*  CMorera.v  —  two halves of the Weierstrass convergence theorem.   *)
(*                                                                    *)
(*    Cintf_unif_limit : the COMPLEX integral of a uniform limit is    *)
(*      the limit of the integrals;                                    *)
(*    MPrim_deriv     : MORERA's primitive -- a continuous function     *)
(*      whose triangle integrals vanish on a convex open set has a      *)
(*      primitive there.                                               *)
(*                                                                    *)
(*  WHY.  Piece 2b of the Hadamard programme needs the entire          *)
(*  cofactors Hcof N to have an ENTIRE limit -- Weierstrass's          *)
(*  convergence theorem, which this repo lacks.  The Morera route is   *)
(*  the one already used for the removable singularity in              *)
(*  CZeroFactorDisk: vanishing triangle integrals give a primitive,    *)
(*  and CDerivHoloDisk.deriv_holo_radius turns that primitive's        *)
(*  derivative back into a holomorphic function.                       *)
(*                                                                    *)
(*  CPrimConv.PrimC_deriv already proves the primitive statement, but  *)
(*  from HFhol -- the function being HOLOMORPHIC -- which is exactly   *)
(*  what one is trying to conclude.  Inspecting that proof, HFhol is   *)
(*  used only twice: via Fcont_pt_conv (pointwise continuity) and via  *)
(*  PrimC_diff (which only needs the triangle integrals to vanish).    *)
(*  MPrim_deriv takes those two as hypotheses instead -- the same move *)
(*  as CInfProdUnif.tail_bound_gen, and CPrimConv.v stays untouched.   *)
(*                                                                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CSeries CImproperIntegral
        CIntegral2 CPathIntegral CSegInt CTriangle CGoursatML CGoursatLin
        CPrimitive CPrimConv CDerivConst UniformIntegralSwap.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the complex integral of a uniform limit                        *)
(* ----------------------------------------------------------------- *)
Theorem Cintf_unif_limit : forall (fn : nat -> R -> C) (g : R -> C)
  (Hfn : forall n, Ccont (fn n)) (Hg : Ccont g) (a b : R),
  a <= b ->
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
     forall t, a <= t <= b -> Cmod (Cminus (fn n t) (g t)) <= eps) ->
  CUn_cv (fun n => Cintf (fn n) (Hfn n) a b) (Cintf g Hg a b).
Proof.
  intros fn g Hfn Hg a b Hab Hunif.
  apply CUn_cv_comp. split.
  - apply (RiemannInt_unif_limit (fun n u => Re (fn n u)) (fun u => Re (g u))
             a b Hab (fun n => cont_RI _ (proj1 (Hfn n)) a b)
             (cont_RI _ (proj1 Hg) a b)).
    intros eps Heps. destruct (Hunif eps Heps) as [N HN].
    exists N. intros n Hn t Ht.
    eapply Rle_trans; [ | apply (HN n Hn t Ht) ].
    rewrite <- ReCm. apply Cmod_Re_le.
  - apply (RiemannInt_unif_limit (fun n u => Im (fn n u)) (fun u => Im (g u))
             a b Hab (fun n => cont_RI _ (proj2 (Hfn n)) a b)
             (cont_RI _ (proj2 Hg) a b)).
    intros eps Heps. destruct (Hunif eps Heps) as [N HN].
    exists N. intros n Hn t Ht.
    eapply Rle_trans; [ | apply (HN n Hn t Ht) ].
    rewrite <- ImCm. apply Cmod_Im_le.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  MORERA: a primitive from vanishing triangle integrals          *)
(* ----------------------------------------------------------------- *)
Section MoreraPrim.

Variable U : C -> Prop.
Hypothesis HU : Convex U.
Hypothesis HO : Open U.
Variable F : C -> C.
Variable HF : CcontC F.
(* the two things PrimC_deriv actually uses, in place of HFhol *)
Hypothesis Hvan : forall a b c, U a -> U b -> U c -> tri_int F HF a b c = C0.
Hypothesis Hptc : forall z, U z -> forall eps, 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps.
Variable z0 : C.
Hypothesis HUz0 : U z0.

Definition MPrim (z : C) : C := seg_int F HF z0 z.

Lemma MPrim_diff : forall z k, U z -> U (Cadd z k) ->
  seg_int F HF z (Cadd z k) = Cminus (MPrim (Cadd z k)) (MPrim z).
Proof.
  intros z k HUz HUzk; unfold MPrim.
  pose proof (Hvan z0 z (Cadd z k) HUz0 HUz HUzk) as HG.
  unfold tri_int in HG; rewrite (seg_reverse F HF z0 (Cadd z k)) in HG.
  assert (HR := f_equal Re HG); assert (HI := f_equal Im HG).
  apply Ceq; unfold Cadd, Copp, Cminus, C0 in *; cbn in *; lra.
Qed.

Theorem MPrim_deriv : forall z, U z -> is_Cderiv MPrim z (F z).
Proof.
  intros z HUz eps Heps.
  destruct (Hptc z HUz (eps / 2) ltac:(lra)) as [del1 [Hdel1 Hc]].
  destruct (HO z HUz) as [r [Hr Hball]].
  exists (Rmin del1 r); split; [ apply Rmin_pos; lra | ]; intros k Hk.
  assert (HUzk : U (Cadd z k)).
  { apply Hball; replace (Cminus (Cadd z k) z) with k by ring;
      eapply Rlt_le_trans; [ exact Hk | apply Rmin_r ]. }
  rewrite <- (MPrim_diff z k HUz HUzk).
  assert (HFk : Cmul (F z) k = seg_int (fun _ => F z) (CcontC_const (F z)) z (Cadd z k))
    by (rewrite seg_int_const; replace (Cminus (Cadd z k) z) with k by ring; reflexivity).
  rewrite HFk.
  rewrite <- (seg_int_sub F (fun _ => F z) HF (CcontC_const (F z))
              (CcontC_add F (fun _ => Copp (F z)) HF (CcontC_const (Copp (F z))))
              z (Cadd z k)).
  eapply Rle_trans.
  { apply (seg_int_ML (fun w => Cminus (F w) (F z)) _ z (Cadd z k) (eps / 2)).
    intros s Hs.
    assert (Hws : Cmod (Cminus (seg z (Cadd z k) s) z) <= Cmod k).
    { replace (Cminus (seg z (Cadd z k) s) z) with (Cmul (RtoC s) k)
        by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
      rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq s) by lra.
      apply Rle_trans with (1 * Cmod k);
        [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ] | lra ]. }
    apply Rlt_le, Hc; eapply Rle_lt_trans;
      [ exact Hws | eapply Rlt_le_trans; [ exact Hk | apply Rmin_l ] ]. }
  replace (Cminus (Cadd z k) z) with k by ring.
  apply Req_le; lra.
Qed.

End MoreraPrim.

Print Assumptions Cintf_unif_limit.
Print Assumptions MPrim_deriv.
