(* ================================================================= *)
(*  CZeroFactorDisk.v  —  factoring one zero out of a disk-holomorphic  *)
(*  function:  F w = 0  ==>  F z = (z - w) . H z  with H holomorphic.   *)
(*                                                                    *)
(*    zero_factor_disk :  F pointwise-continuous and holomorphic on     *)
(*      Cmod z < R2, with 1 < R2, F w = C0 and Cmod w < (R2 - 1) / 2    *)
(*        ==> exists H,  (forall z, F z = Cmul (Cminus z w) (H z))      *)
(*                    /\ H holomorphic on ALL of Cmod z < R2            *)
(*                    /\ H pointwise-continuous everywhere.            *)
(*                                                                    *)
(*  This is the step that turns "rho is a zero of xi" into the Jensen   *)
(*  shape  xi = prodfac l . G  that jensen_count_D consumes.           *)
(*                                                                    *)
(*  THE RADIUS BOOKKEEPING IS THE POINT.  The cofactor is Riemann's     *)
(*  removable quotient  H = rphi F w dw  (CRemovableExt), which is    *)
(*  ALREADY known holomorphic on the punctured disk (rphi_holo_off_dom) *)
(*  -- only the single point w is open.  So the analytic work is        *)
(*  confined to w, and the conclusion keeps the FULL disk Cmod z < R2   *)
(*  rather than shrinking it.  That matters: peeling n zeros must not   *)
(*  shrink the domain n times over, or the count n(r) could never be    *)
(*  taken to infinity.  The price is instead a condition on WHERE the   *)
(*  zero sits, Cmod w < (R2 - 1)/2 -- harmless, since one is free to    *)
(*  run the argument on a disk R2 >> 2 Rr + 1 around the Jensen circle. *)
(*                                                                    *)
(*  HOLOMORPHY AT w, the removable singularity.  H is continuous        *)
(*  everywhere (rphi_cc_dom / rphi_ptcont_dom) and bounded near w       *)
(*  (rphi_bd), so CGoursatExcept.PrimE_deriv -- Goursat with ONE        *)
(*  exceptional vertex -- gives a primitive P = seg_int H C0 on the     *)
(*  convex disk with P' = H there.  P is then a disk-holomorphic        *)
(*  function whose pointwise continuity is seg_int_cmod_cont, so        *)
(*  CDerivHoloDisk.deriv_holo_radius says its derivative H is           *)
(*  holomorphic -- at w included.  Axiom-clean.                        *)
(*                                                                    *)
(*  Holomorphy is taken in the EXISTENTIAL form (exists d, is_Cderiv    *)
(*  F z d) rather than as a named derivative function Fp: the           *)
(*  derivative is needed at the single point w, where destruct supplies *)
(*  it.  That matters downstream -- iterating the peel (CZeroListFactor)*)
(*  produces cofactors known only existentially, and manufacturing a    *)
(*  derivative FUNCTION from a pointwise existential would need a       *)
(*  choice axiom this development does not use.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral PerronRemovable CRemovableExt CRemovableExtDom
        CGoursatExcept CPrimitiveDisk CSegIntCont CDerivHoloDisk.
Open Scope R_scope.

Theorem zero_factor_disk : forall (F : C -> C) (R2 : R) (w : C),
  1 < R2 ->
  Cmod w < (R2 - 1) / 2 ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps) ->
  (forall z, Cmod z < R2 -> exists d, is_Cderiv F z d) ->
  F w = C0 ->
  exists H : C -> C,
    (forall z, F z = Cmul (Cminus z w) (H z)) /\
    (forall z, Cmod z < R2 -> exists d, is_Cderiv H z d) /\
    (forall z eps, 0 < eps -> exists del, 0 < del /\
       forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (H z') (H z)) < eps).
Proof.
  intros F R2 w HR2 Hw HFptc HFhol HFw.
  assert (HR2pos : 0 < R2) by lra.
  assert (HwR2 : Cmod w < R2) by lra.
  destruct (HFhol w HwR2) as [dw Hdw].
  set (H := rphi F w dw).
  exists H.
  (* --- the continuity of H, both flavours (Riemann's quotient) ----- *)
  assert (HHptc : forall z eps, 0 < eps -> exists del, 0 < del /\
             forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (H z') (H z)) < eps)
    by (intros z eps He; exact (rphi_ptcont_dom F w dw Hdw HFptc z eps He)).
  assert (HHcc : CcontC H) by exact (rphi_cc_dom F w dw Hdw HFptc).
  (* --- H is holomorphic on the PUNCTURED disk, for free ------------ *)
  assert (HFholo : forall z, Cmod z < R2 -> z <> w -> exists d, is_Cderiv F z d)
    by (intros z Hz _; apply HFhol; exact Hz).
  assert (HHoff : forall z, Cmod z < R2 -> z <> w -> exists d, is_Cderiv H z d)
    by (intros z Hz Hzw; exact (rphi_holo_off_dom F w dw R2 HFholo z Hz Hzw)).
  (* --- the primitive of H on the convex disk, exceptional point w --- *)
  assert (HdiskW : disk R2 w) by (unfold disk; exact HwR2).
  assert (HdiskC0 : disk R2 C0)
    by (unfold disk; rewrite (proj2 (Cmod0 C0) eq_refl); exact HR2pos).
  set (P := PrimE H HHcc C0).
  assert (HPd : forall z, disk R2 z -> is_Cderiv P z (H z)).
  { apply (PrimE_deriv (disk R2) (disk_convex R2) (disk_open R2) H HHcc w HdiskW).
    - intros z Hz Hzw. exact (HHoff z Hz Hzw).
    - exact (rphi_bd F w dw Hdw).
    - intros z _ eps Heps. exact (HHptc z eps Heps).
    - exact HdiskC0. }
  (* --- P is pointwise continuous: it is a segment integral ---------- *)
  assert (HPptc : forall z eps, 0 < eps -> exists del, 0 < del /\
             forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (P z') (P z)) < eps)
    by (intros z eps He; exact (seg_int_cmod_cont H HHcc C0 HHptc z eps He)).
  (* --- so H = P' is holomorphic on Cmod z < (R2-1)/2, w included ---- *)
  assert (HPd' : forall z, Cmod z < 2 * ((R2 - 1) / 2) + 1 -> is_Cderiv P z (H z)).
  { intros z Hz. apply HPd. unfold disk. lra. }
  assert (HHin : forall z, Cmod z < (R2 - 1) / 2 -> exists d, is_Cderiv H z d)
    by (apply (deriv_holo_radius P H ((R2 - 1) / 2) ltac:(lra) HPptc HPd')).
  split; [ | split ].
  - (* the factorisation identity, pure algebra *)
    intro z. destruct (Ceq_dec z w) as [E | N].
    + subst z. rewrite HFw. replace (Cminus w w) with C0 by ring. ring.
    + unfold H. rewrite (rphi_off F w dw z N), HFw.
      assert (Hne : Cminus z w <> C0) by (apply minus_ne; exact N).
      field. exact Hne.
  - (* holomorphic on the WHOLE disk: off w for free, at w by the above *)
    intros z Hz. destruct (Ceq_dec z w) as [E | N].
    + subst z. apply HHin. exact Hw.
    + exact (HHoff z Hz N).
  - exact HHptc.
Qed.

Print Assumptions zero_factor_disk.
