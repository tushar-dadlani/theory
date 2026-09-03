(* ================================================================= *)
(*  CLoopCofactor.v  --  the cofactor contributes nothing.            *)
(*                                                                    *)
(*  The second half of the argument principle: once F = prodfac l . G  *)
(*  has had its zeros peeled off, the remaining G'/G is holomorphic on *)
(*  the region and its loop integral round the rectangle vanishes.     *)
(*                                                                    *)
(*  ExplicitFormulaRegionResidue.rect_cauchy_region already does the   *)
(*  work -- four seg_ints round a quadrilateral in a convex open U,    *)
(*  summing to 0, with h holomorphic only on U (two triangles, the     *)
(*  diagonal cancelling, via CPrimConv.tri_int_conv_all).  Only the    *)
(*  four CORNERS need lie in U; convexity supplies the edges and the   *)
(*  interior.  All that is missing is the seg_int -> pathint bridge.   *)
(*                                                                    *)
(*  THE INTERFACE POINT.  rect_cauchy_region demands h be GLOBALLY     *)
(*  CcontC, which G'/G is not -- G may vanish arbitrarily close to U   *)
(*  from outside.  Rather than clamp here, h is taken as a PARAMETER   *)
(*  with an agreement hypothesis on U, exactly as CTruncCauchy.        *)
(*  trunc_cauchy takes its removable quotient phi.  The caller builds  *)
(*  the clamp; the recipe is NewmanCutoff.cutprod_ptcont, used three   *)
(*  times already (gtrunc, Kcut, and gcut before them).                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CIntegral2 CSegInt CPathIntegral CPrimConv
        ExplicitFormulaResidueThm ExplicitFormulaRegionResidue.
Open Scope R_scope.

(* ---- the quadrilateral loop, in pathint form ---- *)

Theorem rect_loop_region : forall (U : C -> Prop), Convex U -> Open U ->
  forall (h : C -> C) (Hcont : CcontC h),
  (forall z, U z -> exists d, is_Cderiv h z d) ->
  forall P0 P1 P2 P3, U P0 -> U P1 -> U P2 -> U P3 ->
  forall (Hf1 : Ccont (fun u => Cmul (h (seg P0 P1 u)) (seg' P0 P1 u)))
         (Hf2 : Ccont (fun u => Cmul (h (seg P1 P2 u)) (seg' P1 P2 u)))
         (Hf3 : Ccont (fun u => Cmul (h (seg P2 P3 u)) (seg' P2 P3 u)))
         (Hf4 : Ccont (fun u => Cmul (h (seg P3 P0 u)) (seg' P3 P0 u))),
  Cadd (pathint (seg P0 P1) (seg' P0 P1) h Hf1 0 1)
  (Cadd (pathint (seg P1 P2) (seg' P1 P2) h Hf2 0 1)
  (Cadd (pathint (seg P2 P3) (seg' P2 P3) h Hf3 0 1)
        (pathint (seg P3 P0) (seg' P3 P0) h Hf4 0 1)))
  = C0.
Proof.
  intros U HU HO h Hcont Hhol P0 P1 P2 P3 H0 H1 H2 H3 Hf1 Hf2 Hf3 Hf4.
  rewrite <- (seg_int_is_pathint h Hcont P0 P1 Hf1).
  rewrite <- (seg_int_is_pathint h Hcont P1 P2 Hf2).
  rewrite <- (seg_int_is_pathint h Hcont P2 P3 Hf3).
  rewrite <- (seg_int_is_pathint h Hcont P3 P0 Hf4).
  exact (rect_cauchy_region U HU HO h Hcont Hhol P0 P1 P2 P3 H0 H1 H2 H3).
Qed.

(* ---- the axis-aligned instance, with the corners named ---- *)

Theorem rect_loop_axis : forall (U : C -> Prop), Convex U -> Open U ->
  forall (h : C -> C) (Hcont : CcontC h),
  (forall z, U z -> exists d, is_Cderiv h z d) ->
  forall (x0 x1 y0 y1 : R),
  U (mkC x1 y0) -> U (mkC x1 y1) -> U (mkC x0 y1) -> U (mkC x0 y0) ->
  forall (Hf1 : Ccont (fun u => Cmul (h (seg (mkC x1 y0) (mkC x1 y1) u))
                                     (seg' (mkC x1 y0) (mkC x1 y1) u)))
         (Hf2 : Ccont (fun u => Cmul (h (seg (mkC x1 y1) (mkC x0 y1) u))
                                     (seg' (mkC x1 y1) (mkC x0 y1) u)))
         (Hf3 : Ccont (fun u => Cmul (h (seg (mkC x0 y1) (mkC x0 y0) u))
                                     (seg' (mkC x0 y1) (mkC x0 y0) u)))
         (Hf4 : Ccont (fun u => Cmul (h (seg (mkC x0 y0) (mkC x1 y0) u))
                                     (seg' (mkC x0 y0) (mkC x1 y0) u))),
  Cadd (pathint (seg (mkC x1 y0) (mkC x1 y1)) (seg' (mkC x1 y0) (mkC x1 y1)) h Hf1 0 1)
  (Cadd (pathint (seg (mkC x1 y1) (mkC x0 y1)) (seg' (mkC x1 y1) (mkC x0 y1)) h Hf2 0 1)
  (Cadd (pathint (seg (mkC x0 y1) (mkC x0 y0)) (seg' (mkC x0 y1) (mkC x0 y0)) h Hf3 0 1)
        (pathint (seg (mkC x0 y0) (mkC x1 y0)) (seg' (mkC x0 y0) (mkC x1 y0)) h Hf4 0 1)))
  = C0.
Proof.
  intros U HU HO h Hcont Hhol x0 x1 y0 y1 H0 H1 H2 H3.
  apply (rect_loop_region U HU HO h Hcont Hhol); assumption.
Qed.

(* ---- the cofactor's log-derivative IS holomorphic on U ---- *)

Theorem cofactor_logderiv_holo :
  forall (U : C -> Prop) (G Gd : C -> C),
  (forall z, U z -> is_Cderiv G z (Gd z)) ->
  (forall z, U z -> exists d, is_Cderiv Gd z d) ->
  (forall z, U z -> G z <> C0) ->
  forall z, U z -> exists d, is_Cderiv (fun u => Cmul (Gd u) (Cinv (G u))) z d.
Proof.
  intros U G Gd HGd HGdd HGne z HUz.
  destruct (HGdd z HUz) as [d2 Hd2].
  eexists; apply Cderiv_div;
    [ exact Hd2 | apply HGd; exact HUz | apply HGne; exact HUz ].
Qed.

Print Assumptions rect_loop_region.
Print Assumptions cofactor_logderiv_holo.

(* ================================================================= *)
(*  END CLoopCofactor.v -- the zero-free cofactor's log-derivative     *)
(*  integrates to 0 round the rectangle.                               *)
(* ================================================================= *)
