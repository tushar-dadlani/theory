(* ================================================================= *)
(*  CSegFTCDisk.v  —  disk-cofactor bridge, Stage 1:                     *)
(*  the segment fundamental theorem of calculus, DOMAIN-LOCAL.          *)
(*                                                                    *)
(*    seg_FTC_disk : Convex U -> U a -> U b ->                          *)
(*      (forall z, U z -> is_Cderiv H z (f z)) ->                       *)
(*      seg_int f Hf a b = H b - H a.                                   *)
(*                                                                    *)
(*  Exactly CGoursatFTC.seg_FTC, but the primitive H need only be       *)
(*  holomorphic ON U (not on all of C): the segment seg a b s lies in   *)
(*  U for s in [0,1] by convexity, and pathint_FTC only ever needs the  *)
(*  derivative ON the path.  This is the glue that lets the mean-value  *)
(*  chain (Stage 2) be re-derived disk-locally.  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CIntegral2 CPathIntegral
        CPathFTC CSegInt CGoursatFTC CPrimConv.
Open Scope R_scope.

Lemma seg_FTC_disk : forall (U : C -> Prop), Convex U ->
  forall (H f : C -> C) (Hf : CcontC f) a b,
  U a -> U b -> (forall z, U z -> is_Cderiv H z (f z)) ->
  seg_int f Hf a b = Cminus (H b) (H a).
Proof.
  intros U HU H f Hf a b Ha Hb HH; unfold seg_int.
  transitivity (Cminus (H (seg a b 1)) (H (seg a b 0))).
  - exact (pathint_FTC H f (seg a b) (seg' a b) (seg_ig_cont f Hf a b) 0 1 ltac:(lra)
            (fun s Hs => HH (seg a b s) (HU a b Ha Hb s Hs))
            (fun s _ => dseg_Re a b s)
            (fun s _ => dseg_Im a b s)).
  - rewrite seg_1, seg_0; reflexivity.
Qed.

Print Assumptions seg_FTC_disk.
