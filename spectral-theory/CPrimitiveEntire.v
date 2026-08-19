(* ================================================================= *)
(*  CPrimitiveEntire.v  —  Hadamard keystone, brick 3 enabler:          *)
(*  an entire function has an entire primitive.                         *)
(*                                                                    *)
(*    primitive_entire : CcontC g -> (forall z, holomorphic g z) ->     *)
(*                       exists G, forall z, is_Cderiv G z (g z).       *)
(*                                                                    *)
(*  The disk primitive (brick A, CPrimitiveDisk.primitive_on_disk) is   *)
(*  a single fixed function PrimE g C0 = seg_int g C0 that is           *)
(*  holomorphic on EVERY disk when g is entire; so it is a primitive on *)
(*  all of C.  This upgrade is needed for brick 3: the holomorphic mean *)
(*  value property (CCauchyFormula.M_const / meanval0) requires the     *)
(*  function to be ENTIRE, and the complex logarithm G = Log F (brick B,*)
(*  CLogFExp.logF_exp) is entire exactly when g = F'/F is entire        *)
(*  (F entire and zero-free).                                          *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CSegInt CGoursatExcept
        CHoloCalculus CPrimConv CPrimitiveDisk.
Open Scope R_scope.

Theorem primitive_entire : forall (g : C -> C), CcontC g ->
  (forall z, exists d, is_Cderiv g z d) ->
  exists G : C -> C, forall z, is_Cderiv G z (g z).
Proof.
  intros g Hg Hghol. exists (PrimE g Hg C0). intros z.
  set (Rr := Cmod z + 1).
  assert (HR : 0 < Rr) by (unfold Rr; pose proof (Cmod_nonneg z); lra).
  assert (HzD : disk Rr z) by (unfold disk, Rr; lra).
  assert (HCm0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
  assert (HC0D : disk Rr C0)
    by (unfold disk, Rr; rewrite HCm0; pose proof (Cmod_nonneg z); lra).
  apply (PrimE_deriv (disk Rr) (disk_convex Rr) (disk_open Rr) g Hg C0 HC0D).
  - intros z' _ _. apply Hghol.
  - destruct (Hghol C0) as [d0 Hd0].
    destruct (Cderiv_cont_w g C0 d0 Hd0 1 Rlt_0_1) as [eta [Heta Hb0]].
    exists (Cmod (g C0) + 1), eta. split; [ exact Heta | ]. intros w Hw.
    apply Rle_trans with (Cmod (g C0) + Cmod (Cminus (g w) (g C0))).
    + pose proof (Cmod_triangle (g C0) (Cminus (g w) (g C0))) as HT.
      replace (Cadd (g C0) (Cminus (g w) (g C0))) with (g w) in HT by ring. exact HT.
    + specialize (Hb0 w Hw). lra.
  - intros z' _ eps Heps. destruct (Hghol z') as [d' Hd'].
    exact (Cderiv_cont_w g z' d' Hd' eps Heps).
  - exact HC0D.
  - exact HzD.
Qed.

Print Assumptions primitive_entire.
