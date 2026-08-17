(* ================================================================= *)
(*  CauchyRectangle.v  —  Cauchy's theorem for a rectangle.             *)
(*                                                                    *)
(*  Explicit formula, Stage B brick 1 (the load-bearing assembly tool). *)
(*                                                                    *)
(*  The boundary integral of an ENTIRE function around the closed        *)
(*  quadrilateral  P0 -> P1 -> P2 -> P3 -> P0  vanishes:                  *)
(*                                                                    *)
(*    rect_cauchy :  seg_int h P0 P1 + seg_int h P1 P2                    *)
(*                 + seg_int h P2 P3 + seg_int h P3 P0  =  0.             *)
(*                                                                    *)
(*  Proof: split the quadrilateral into the two Goursat triangles         *)
(*  (P0,P1,P2) and (P0,P2,P3); each boundary integral is 0 (CGoursat.     *)
(*  goursat), and the shared diagonal P0-P2 is traversed in opposite      *)
(*  directions, so it cancels (CSegInt.seg_reverse).                      *)
(*                                                                    *)
(*  Role in Stage B: this is the deformation/residue-collection engine.   *)
(*  Subtracting the principal parts  r_k/(s - a_k)  of the explicit-       *)
(*  formula kernel  Phi(s) x^s/s  at the poles inside a contour leaves an  *)
(*  entire remainder whose rectangle integral is 0 here; hence the        *)
(*  contour integral equals the sum of the residues (the Stage-A bricks   *)
(*  rect_residue_pole1 / _pole01 / _poleC supply those residue values).   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals.
Require Import ComplexField Cmodulus CTriangle CSegInt CGoursat Holomorphic.
Open Scope R_scope.

Theorem rect_cauchy : forall (h : C -> C) (Hcont : CcontC h),
  (forall z : C, exists d : C, is_Cderiv h z d) ->
  forall P0 P1 P2 P3 : C,
  Cadd (seg_int h Hcont P0 P1)
    (Cadd (seg_int h Hcont P1 P2)
      (Cadd (seg_int h Hcont P2 P3) (seg_int h Hcont P3 P0))) = C0.
Proof.
  intros h Hcont Hhol P0 P1 P2 P3.
  pose proof (goursat h Hcont Hhol P0 P1 P2) as G1.
  pose proof (goursat h Hcont Hhol P0 P2 P3) as G2.
  unfold tri_int in G1, G2.
  rewrite (seg_reverse h Hcont P0 P2) in G1.
  set (A := seg_int h Hcont P0 P1) in *.
  set (B := seg_int h Hcont P1 P2) in *.
  set (Cc := seg_int h Hcont P2 P3) in *.
  set (D := seg_int h Hcont P3 P0) in *.
  set (E := seg_int h Hcont P0 P2) in *.
  assert (Hcomb : Cadd A (Cadd B (Cadd Cc D))
                = Cadd (Cadd A (Cadd B (Copp E))) (Cadd E (Cadd Cc D))) by ring.
  rewrite Hcomb, G1, G2. ring.
Qed.

Print Assumptions rect_cauchy.
