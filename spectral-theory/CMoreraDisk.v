(* ================================================================= *)
(*  CMoreraDisk.v  --  unif_limit_holo with DISK-LOCAL holomorphy.     *)
(*                                                                    *)
(*  CMorera.unif_limit_holo (Weierstrass: a locally uniform limit of   *)
(*  holomorphic functions is holomorphic) demands                      *)
(*                                                                    *)
(*      forall n z, exists d, is_Cderiv (fn n) z d                     *)
(*                                                                    *)
(*  i.e. every approximant ENTIRE.  That is unusable for zeta: the     *)
(*  partial sums Cpsum (htermC .) n each carry GC's 1/(1-s), so they   *)
(*  have a pole at s = 1.  No affine precomposition removes it, and    *)
(*  the radial clamp that repairs continuity is Lipschitz, not         *)
(*  holomorphic.                                                       *)
(*                                                                    *)
(*  But the hypothesis is stronger than the proof uses.  At            *)
(*  CMorera.v:292-293 the only appeal to it reads                      *)
(*                                                                    *)
(*      apply (tri_int_conv_all (disk Rr) HU HO (fn n) (Hfnc n) ...).  *)
(*      intros w _. apply Hfnh.                                        *)
(*                                                                    *)
(*  and the discarded `_` is precisely the hypothesis `disk Rr w`.     *)
(*  So holomorphy is only ever needed INSIDE the disk.  Below is that  *)
(*  proof with the hypothesis weakened and that one line changed to    *)
(*  keep the hypothesis instead of dropping it.  Nothing else differs, *)
(*  and CMorera.v is left untouched.                                   *)
(*                                                                    *)
(*  (Hfnc : forall n, CcontC (fn n) must stay GLOBAL -- it is a proof  *)
(*  argument to tri_int, not a side condition.  The clamp supplies it  *)
(*  harmlessly, since holomorphy is then only demanded where the clamp *)
(*  is the identity.  This is the repo's own idiom: see CMorera.v's    *)
(*  header on MPrim_deriv versus CPrimConv.PrimC_deriv.)               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CSeries CImproperIntegral
        CIntegral2 CPathIntegral CSegInt CSegIntCont CTriangle CGoursatML
        CGoursatLin CPrimitive CPrimConv CPrimitiveDisk CDerivConst
        CDerivHoloDisk UniformIntegralSwap CMorera.
Open Scope R_scope.

Theorem unif_limit_holo_disk : forall (fn : nat -> C -> C) (g : C -> C) (Rr : R),
  1 < Rr ->
  (forall n, CcontC (fn n)) ->
  (forall n z, Cmod z < Rr -> exists d, is_Cderiv (fn n) z d) ->
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
                        Ha Hb Hc).
      (* THE ONE CHANGE: keep the disk hypothesis instead of dropping it *)
      intros w Hw. apply Hfnh. exact Hw. }
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

Print Assumptions unif_limit_holo_disk.

(* ================================================================= *)
(*  END CMoreraDisk.v                                                 *)
(* ================================================================= *)
