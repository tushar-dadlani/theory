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
        CIntegral2 CPathIntegral CSegInt CSegIntCont CTriangle CGoursatML
        CGoursatLin CPrimitive CPrimConv CPrimitiveDisk CDerivConst
        CDerivHoloDisk UniformIntegralSwap.
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

(* ----------------------------------------------------------------- *)
(*  C.  segment and triangle integrals of a uniform limit             *)
(* ----------------------------------------------------------------- *)
Lemma CUn_cv_add2 : forall (u v : nat -> C) (a b : C),
  CUn_cv u a -> CUn_cv v b -> CUn_cv (fun n => Cadd (u n) (v n)) (Cadd a b).
Proof.
  intros u v a b Hu Hv eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2). intros n Hn.
  pose proof (H1 n ltac:(lia)) as Ha. pose proof (H2 n ltac:(lia)) as Hb.
  replace (Cminus (Cadd (u n) (v n)) (Cadd a b))
    with (Cadd (Cminus (u n) a) (Cminus (v n) b)) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ]. lra.
Qed.

Lemma CUn_cv_C0 : CUn_cv (fun _ : nat => C0) C0.
Proof.
  intros eps Heps. exists 0%nat. intros n _.
  replace (Cminus C0 C0) with C0 by ring.
  rewrite (proj2 (Cmod0 C0) eq_refl). exact Heps.
Qed.

Lemma CUn_cv_ext2 : forall (u v : nat -> C) (l : C),
  (forall n, u n = v n) -> CUn_cv u l -> CUn_cv v l.
Proof.
  intros u v l Heq Hcv eps Heps. destruct (Hcv eps Heps) as [N HN].
  exists N. intros n Hn. rewrite <- (Heq n). apply HN; exact Hn.
Qed.

Lemma seg_int_unif_limit : forall (Fn : nat -> C -> C) (G : C -> C)
  (HFn : forall n, CcontC (Fn n)) (HG : CcontC G) (U : C -> Prop) (a b : C),
  Convex U -> U a -> U b ->
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
     forall w, U w -> Cmod (Cminus (Fn n w) (G w)) <= eps) ->
  CUn_cv (fun n => seg_int (Fn n) (HFn n) a b) (seg_int G HG a b).
Proof.
  intros Fn G HFn HG U a b HU Ha Hb Hunif.
  unfold seg_int.
  apply (Cintf_unif_limit
           (fun n u => Cmul (Fn n (seg a b u)) (seg' a b u))
           (fun u => Cmul (G (seg a b u)) (seg' a b u))
           (fun n => seg_ig_cont (Fn n) (HFn n) a b)
           (seg_ig_cont G HG a b) 0 1 ltac:(lra)).
  intros eps Heps.
  set (M := Cmod (Cminus b a) + 1).
  assert (Hm0 : 0 <= Cmod (Cminus b a)) by apply Cmod_nonneg.
  assert (HM : 0 < M) by (unfold M; lra).
  destruct (Hunif (eps / M) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  exists N. intros n Hn t Ht.
  replace (Cminus (Cmul (Fn n (seg a b t)) (seg' a b t))
                  (Cmul (G (seg a b t)) (seg' a b t)))
    with (Cmul (Cminus (Fn n (seg a b t)) (G (seg a b t))) (seg' a b t)) by ring.
  rewrite Cmod_mul. unfold seg'.
  assert (HUs : U (seg a b t)) by (apply HU; [ exact Ha | exact Hb | exact Ht ]).
  pose proof (HN n Hn (seg a b t) HUs) as Hd.
  assert (Hle : Cmod (Cminus (Fn n (seg a b t)) (G (seg a b t))) * Cmod (Cminus b a)
                <= eps / M * M).
  { apply Rle_trans with (eps / M * Cmod (Cminus b a)).
    - apply Rmult_le_compat_r; [ exact Hm0 | exact Hd ].
    - apply Rmult_le_compat_l;
        [ left; apply Rdiv_lt_0_compat; lra | unfold M; lra ]. }
  replace (eps / M * M) with eps in Hle by (field; lra). exact Hle.
Qed.

Lemma tri_int_unif_limit : forall (Fn : nat -> C -> C) (G : C -> C)
  (HFn : forall n, CcontC (Fn n)) (HG : CcontC G) (U : C -> Prop) (a b c : C),
  Convex U -> U a -> U b -> U c ->
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
     forall w, U w -> Cmod (Cminus (Fn n w) (G w)) <= eps) ->
  CUn_cv (fun n => tri_int (Fn n) (HFn n) a b c) (tri_int G HG a b c).
Proof.
  intros Fn G HFn HG U a b c HU Ha Hb Hc Hunif. unfold tri_int.
  apply CUn_cv_add2;
    [ apply (seg_int_unif_limit Fn G HFn HG U a b HU Ha Hb Hunif) | ].
  apply CUn_cv_add2;
    [ apply (seg_int_unif_limit Fn G HFn HG U b c HU Hb Hc Hunif)
    | apply (seg_int_unif_limit Fn G HFn HG U c a HU Hc Ha Hunif) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C'. a LOCALLY uniform limit of continuous functions is continuous.  *)
(*                                                                    *)
(*  unif_limit_holo assumes its limit continuous, and nothing supplied  *)
(*  that.  This does, and it is the form the application needs: the     *)
(*  hypothesis is uniformity only on SOME neighbourhood of each point,  *)
(*  which is exactly what locally uniform convergence gives, and the    *)
(*  conclusion is global pointwise continuity -- from which            *)
(*  PerronRemovable.ptcont_CcontC yields the global CcontC that the     *)
(*  seg_int API demands.                                               *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_minus_sym0 : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof. intros a b. rewrite <- (Cmod_opp (Cminus a b)). f_equal. ring. Qed.

Theorem unif_limit_ptcont : forall (fn : nat -> C -> C) (g : C -> C),
  (forall n z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (fn n z') (fn n z)) < eps) ->
  (forall z0 : C, exists r, 0 < r /\ forall eps, 0 < eps -> exists N,
     forall n, (N <= n)%nat -> forall w, Cmod (Cminus w z0) < r ->
       Cmod (Cminus (fn n w) (g w)) <= eps) ->
  forall z eps, 0 < eps -> exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (g z') (g z)) < eps.
Proof.
  intros fn g Hptc Hunif z eps Heps.
  destruct (Hunif z) as [r [Hr Hu]].
  destruct (Hu (eps / 4) ltac:(lra)) as [N HN].
  destruct (Hptc N z (eps / 4) ltac:(lra)) as [del0 [Hdel0 Hc]].
  exists (Rmin del0 r). split; [ apply Rmin_pos; lra | ].
  intros z' Hz'.
  assert (Hz'r : Cmod (Cminus z' z) < r)
    by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_r ]).
  assert (Hz'd : Cmod (Cminus z' z) < del0)
    by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_l ]).
  assert (H1 : Cmod (Cminus (fn N z') (g z')) <= eps / 4)
    by (apply HN; [ lia | exact Hz'r ]).
  assert (H2 : Cmod (Cminus (fn N z) (g z)) <= eps / 4).
  { apply HN; [ lia | ].
    replace (Cminus z z) with C0 by ring.
    rewrite (proj2 (Cmod0 C0) eq_refl). exact Hr. }
  assert (H3 : Cmod (Cminus (fn N z') (fn N z)) < eps / 4)
    by (apply Hc; exact Hz'd).
  replace (Cminus (g z') (g z))
    with (Cadd (Cminus (g z') (fn N z'))
               (Cadd (Cminus (fn N z') (fn N z)) (Cminus (fn N z) (g z)))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  assert (Hin : Cmod (Cadd (Cminus (fn N z') (fn N z)) (Cminus (fn N z) (g z)))
                <= Cmod (Cminus (fn N z') (fn N z)) + Cmod (Cminus (fn N z) (g z)))
    by apply Cmod_triangle.
  rewrite (Cmod_minus_sym0 (g z') (fn N z')) in *.
  lra.
Qed.

(* ================================================================= *)
(*  D.  WEIERSTRASS'S CONVERGENCE THEOREM                              *)
(*                                                                    *)
(*  A uniform limit of holomorphic functions is holomorphic.  Morera    *)
(*  in three moves: the fn have vanishing triangle integrals            *)
(*  (tri_int_conv_all), those pass to the limit (tri_int_unif_limit),   *)
(*  so MPrim_deriv gives g a primitive -- and a primitive's derivative  *)
(*  is holomorphic (CDerivHoloDisk.deriv_holo_radius).  The Rr -> Rr/2  *)
(*  style shrink is the tower's, inherited through deriv_holo_radius.   *)
(* ================================================================= *)
Theorem unif_limit_holo : forall (fn : nat -> C -> C) (g : C -> C) (Rr : R),
  1 < Rr ->
  (forall n, CcontC (fn n)) ->
  (forall n z, exists d, is_Cderiv (fn n) z d) ->
  CcontC g ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (g z') (g z)) < eps) ->
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
     forall w, Cmod w < Rr -> Cmod (Cminus (fn n w) (g w)) <= eps) ->
  forall z, Cmod z < (Rr - 1) / 2 -> exists d, is_Cderiv g z d.
Proof.
  intros fn g Rr HR Hfnc Hfnh Hgc Hgptc Hunif z Hz.
  assert (HU : Convex (disk Rr)) by apply disk_convex.
  assert (HO : Open (disk Rr)) by apply disk_open.
  (* the limit's triangle integrals vanish *)
  assert (Hvan : forall a b c, disk Rr a -> disk Rr b -> disk Rr c ->
                   tri_int g Hgc a b c = C0).
  { intros a b c Ha Hb Hc.
    assert (Hcv : CUn_cv (fun n => tri_int (fn n) (Hfnc n) a b c)
                         (tri_int g Hgc a b c)).
    { apply (tri_int_unif_limit fn g Hfnc Hgc (disk Rr) a b c HU Ha Hb Hc).
      intros eps Heps. destruct (Hunif eps Heps) as [N HN].
      exists N. intros n Hn w Hw. apply HN; [ exact Hn | exact Hw ]. }
    assert (Hzero : forall n, tri_int (fn n) (Hfnc n) a b c = C0).
    { intro n. apply (tri_int_conv_all (disk Rr) HU HO (fn n) (Hfnc n) a b c
                        Ha Hb Hc). intros w _. apply Hfnh. }
    assert (Hc0 : CUn_cv (fun n => tri_int (fn n) (Hfnc n) a b c) C0).
    { apply (CUn_cv_ext2 (fun _ : nat => C0));
        [ intro n; symmetry; apply Hzero | apply CUn_cv_C0 ]. }
    exact (CUn_cv_unique _ _ _ Hcv Hc0). }
  (* Morera gives a primitive *)
  assert (HUz0 : disk Rr C0)
    by (unfold disk; rewrite (proj2 (Cmod0 C0) eq_refl); lra).
  pose proof (MPrim_deriv (disk Rr) HO g Hgc Hvan
                (fun w _ eps He => Hgptc w eps He) C0 HUz0) as HPd.
  (* the primitive is pointwise continuous *)
  assert (HPptc : forall w eps, 0 < eps -> exists del, 0 < del /\
             forall v, Cmod (Cminus v w) < del ->
               Cmod (Cminus (MPrim g Hgc C0 v) (MPrim g Hgc C0 w)) < eps)
    by (intros w eps He; exact (seg_int_cmod_cont g Hgc C0 Hgptc w eps He)).
  (* and a primitive's derivative is holomorphic *)
  apply (deriv_holo_radius (MPrim g Hgc C0) g ((Rr - 1) / 2) ltac:(lra) HPptc).
  - intros w Hw. apply HPd. unfold disk. lra.
  - exact Hz.
Qed.

Print Assumptions Cintf_unif_limit.
Print Assumptions MPrim_deriv.
Print Assumptions tri_int_unif_limit.
Print Assumptions unif_limit_holo.
Print Assumptions unif_limit_ptcont.
