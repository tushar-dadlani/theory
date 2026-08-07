(* ================================================================= *)
(*  CTriangle.v  —  Milestone C, brick C2a-2: the triangle boundary     *)
(*  integral and Goursat's bisection identity.                         *)
(*                                                                    *)
(*  tri_int f v0 v1 v2 = ∮ over ∂(triangle) = seg(v0,v1)+seg(v1,v2)+     *)
(*  seg(v2,v0).  Bisecting at the edge midpoints m01,m12,m20 gives four  *)
(*  medial sub-triangles whose boundary integrals sum to tri_int(T):     *)
(*  the outer edges split by seg_concat, the three inner (medial) edges   *)
(*  are each traversed twice in opposite directions and cancel by        *)
(*  seg_reverse.  This is the algebraic heart of Goursat's theorem.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral CSegCoV CSegInt.
Open Scope R_scope.

Definition tri_int (f : C -> C) (Hf : CcontC f) (v0 v1 v2 : C) : C :=
  Cadd (seg_int f Hf v0 v1) (Cadd (seg_int f Hf v1 v2) (seg_int f Hf v2 v0)).

(* ---- Goursat's bisection identity ---- *)
Theorem tri_bisect : forall f (Hf : CcontC f) v0 v1 v2,
  tri_int f Hf v0 v1 v2
  = Cadd (tri_int f Hf v0 (mid v0 v1) (mid v2 v0))
    (Cadd (tri_int f Hf (mid v0 v1) v1 (mid v1 v2))
    (Cadd (tri_int f Hf (mid v2 v0) (mid v1 v2) v2)
          (tri_int f Hf (mid v0 v1) (mid v1 v2) (mid v2 v0)))).
Proof.
  intros f Hf v0 v1 v2; unfold tri_int.
  (* split the three outer edges at their midpoints *)
  rewrite (seg_concat f Hf v0 v1), (seg_concat f Hf v1 v2), (seg_concat f Hf v2 v0).
  (* flip the three medial edges of the central sub-triangle to cancel *)
  rewrite (seg_reverse f Hf (mid v0 v1) (mid v2 v0)),
          (seg_reverse f Hf (mid v1 v2) (mid v0 v1)),
          (seg_reverse f Hf (mid v2 v0) (mid v1 v2)).
  ring.
Qed.

Print Assumptions tri_bisect.

(* ================================================================= *)
(*  END CTriangle.v  —  Goursat bisection identity (C2a-2).             *)
(* ================================================================= *)
