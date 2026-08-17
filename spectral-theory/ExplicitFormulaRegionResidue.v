(* ================================================================= *)
(*  ExplicitFormulaRegionResidue.v  —  Explicit formula, Stage C brick 1: *)
(*  the RESIDUE THEOREM for a function holomorphic only on a REGION.      *)
(*                                                                    *)
(*  Stage B's residue theorem required the holomorphic part to be ENTIRE.  *)
(*  The actual explicit-formula kernel is meromorphic:  Phi = -zeta'/zeta  *)
(*  has infinitely many zero-poles, so subtracting the finitely many       *)
(*  poles inside a contour leaves a remainder holomorphic only on a         *)
(*  NEIGHBOURHOOD of the contour (the exterior zero-poles are still there). *)
(*  Stage C needs the residue theorem at that generality.                  *)
(*                                                                    *)
(*    rect_cauchy_region : the boundary integral of h around a rectangle    *)
(*      whose corners lie in a convex open U vanishes, provided h is        *)
(*      holomorphic on U (NOT entire).  Two region-Goursat triangles        *)
(*      (CPrimConv.tri_int_conv_all) with the diagonal cancelling.          *)
(*                                                                    *)
(*    residue_theorem_1pole_region : for h holomorphic on a convex open U   *)
(*      containing the a-centred rectangle, the contour integral of         *)
(*      h(s) + y^s/(s-a) is  2*pi*i * y^a  -- the region-holomorphic part    *)
(*      contributes nothing, the simple pole contributes its residue.       *)
(*                                                                    *)
(*  This is the honest region-restricted residue theorem the meromorphic    *)
(*  Phi requires.  (h must still be globally CONTINUOUS -- for the real Phi  *)
(*  that is arranged by CLAMPING off the region, as in GammaCLogTerm's      *)
(*  ghat.)  What remains of Stage C is the ZETA-SPECIFIC analytic input:    *)
(*  (i) the clamp of Phi and its holomorphy on the strip minus zeros, and   *)
(*  (ii) the zeta'/zeta growth bounds that vanish the far contour edges     *)
(*  (Hadamard product / zero-density) -- the deepest, RH-adjacent part.     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CIntegral2 CPathIntegral CSegInt
        CTriangle CGoursat CGoursatLin CLeibniz CPrimConv PerronKernel PerronPower
        Holomorphic CTruncCauchy ExplicitFormulaPole01 ExplicitFormulaPoleZero
        ExplicitFormulaResidueThm.
Open Scope R_scope.

Theorem rect_cauchy_region : forall (U : C -> Prop), Convex U -> Open U ->
  forall (h : C -> C) (Hcont : CcontC h),
  (forall z, U z -> exists d, is_Cderiv h z d) ->
  forall P0 P1 P2 P3, U P0 -> U P1 -> U P2 -> U P3 ->
  Cadd (seg_int h Hcont P0 P1)
    (Cadd (seg_int h Hcont P1 P2)
      (Cadd (seg_int h Hcont P2 P3) (seg_int h Hcont P3 P0))) = C0.
Proof.
  intros U HU HO h Hcont Hhol P0 P1 P2 P3 H0 H1 H2 H3.
  pose proof (tri_int_conv_all U HU HO h Hcont P0 P1 P2 H0 H1 H2 Hhol) as G1.
  pose proof (tri_int_conv_all U HU HO h Hcont P0 P2 P3 H0 H2 H3 Hhol) as G2.
  unfold tri_int in G1, G2.
  rewrite (seg_reverse h Hcont P0 P2) in G1.
  set (A := seg_int h Hcont P0 P1) in *. set (B := seg_int h Hcont P1 P2) in *.
  set (Cc := seg_int h Hcont P2 P3) in *. set (D := seg_int h Hcont P3 P0) in *.
  set (E := seg_int h Hcont P0 P2) in *.
  assert (Hcomb : Cadd A (Cadd B (Cadd Cc D))
                = Cadd (Cadd A (Cadd B (Copp E))) (Cadd E (Cadd Cc D))) by ring.
  rewrite Hcomb, G1, G2. ring.
Qed.

(* THE RESIDUE THEOREM, region form.  h need only be holomorphic on a convex
   open U containing the a-centred rectangle (not entire): the contour integral
   of  h(s) + y^s/(s-a)  ccw around that rectangle is still  2*pi*i * y^a. *)
Theorem residue_theorem_1pole_region :
  forall (U : C -> Prop) (HU : Convex U) (HO : Open U)
         (h : C -> C) (Hcont : CcontC h)
         (Hhol : forall z, U z -> exists d, is_Cderiv h z d)
         (y : R) (a : C) (c Uu T : R),
  0 < y -> 0 < c -> 0 < Uu -> 0 < T ->
  U (Cadd a (mkC c (- T))) -> U (Cadd a (mkC c T)) ->
  U (Cadd a (mkC (- Uu) T)) -> U (Cadd a (mkC (- Uu) (- T))) ->
  forall
    (Hs1 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) u)) (seg' (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) u)))
    (Hs2 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) u)) (seg' (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) u)))
    (Hs3 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) u)) (seg' (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) u)))
    (Hs4 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) u)) (seg' (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) u))),
  Cadd (pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) (seg' (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) (fun s => Cadd (h s) (KpoleC y a s)) Hs1 0 1)
  (Cadd (pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) (seg' (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) (fun s => Cadd (h s) (KpoleC y a s)) Hs2 0 1)
  (Cadd (pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) (seg' (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) (fun s => Cadd (h s) (KpoleC y a s)) Hs3 0 1)
        (pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) (seg' (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) (fun s => Cadd (h s) (KpoleC y a s)) Hs4 0 1)))
  = Cmul (mkC 0 (2 * PI)) (Cpw y a).
Proof.
  intros U HU HO h Hcont Hhol y a c Uu T Hy Hc HUu HT HUa1 HUa2 HUa3 HUa4 Hs1 Hs2 Hs3 Hs4.
  assert (Dne : forall (P0 Q0 : C) u, (forall v, seg P0 Q0 v <> C0) ->
             Cminus (seg (Cadd a P0) (Cadd a Q0) u) a <> C0)
    by (intros P0 Q0 u Hpq; rewrite seg_add_sub; apply Hpq).
  assert (HkC : forall (P0 Q0 : C), (forall v, seg P0 Q0 v <> C0) ->
    Ccont (fun u => Cmul (KpoleC y a (seg (Cadd a P0) (Cadd a Q0) u)) (seg' (Cadd a P0) (Cadd a Q0) u))).
  { intros P0 Q0 Hpq. unfold KpoleC.
    apply (cont_kernel y (Cadd a P0) (Cadd a Q0)
             (fun u => Cminus (seg (Cadd a P0) (Cadd a Q0) u) a)).
    - apply Ccont_sub; [ apply Ccont_seg_id | apply Ccont_const ].
    - intro u. apply Dne; exact Hpq. }
  assert (Hr0 : forall (P0 Q0 : C), (forall v, seg P0 Q0 v <> C0) ->
    Ccont (fun u => Cmul (Cmul (Cpw y (seg P0 Q0 u)) (Cinv (seg P0 Q0 u))) (seg' P0 Q0 u)))
    by (intros P0 Q0 Hpq; apply (cont_kernel y P0 Q0 (seg P0 Q0)); [ apply Ccont_seg_id | exact Hpq ]).
  set (Hk1 := HkC (mkC c (- T)) (mkC c T) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hk2 := HkC (mkC c T) (mkC (- Uu) T) ltac:(intro v; apply seg_ne0_h; lra)).
  set (Hk3 := HkC (mkC (- Uu) T) (mkC (- Uu) (- T)) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hk4 := HkC (mkC (- Uu) (- T)) (mkC c (- T)) ltac:(intro v; apply seg_ne0_h; lra)).
  set (Hg1 := Hr0 (mkC c (- T)) (mkC c T) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hg2 := Hr0 (mkC c T) (mkC (- Uu) T) ltac:(intro v; apply seg_ne0_h; lra)).
  set (Hg3 := Hr0 (mkC (- Uu) T) (mkC (- Uu) (- T)) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hg4 := Hr0 (mkC (- Uu) (- T)) (mkC c (- T)) ltac:(intro v; apply seg_ne0_h; lra)).
  rewrite (pathint_split_hK h y a _ _ Hs1 (seg_ig_cont h Hcont _ _) Hk1).
  rewrite (pathint_split_hK h y a _ _ Hs2 (seg_ig_cont h Hcont _ _) Hk2).
  rewrite (pathint_split_hK h y a _ _ Hs3 (seg_ig_cont h Hcont _ _) Hk3).
  rewrite (pathint_split_hK h y a _ _ Hs4 (seg_ig_cont h Hcont _ _) Hk4).
  pose proof (rect_cauchy_region U HU HO h Hcont Hhol
                (Cadd a (mkC c (- T))) (Cadd a (mkC c T))
                (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))
                HUa1 HUa2 HUa3 HUa4) as HC.
  rewrite !(seg_int_is_pathint h Hcont _ _ (seg_ig_cont h Hcont _ _)) in HC.
  pose proof (rect_residue_poleC y a c Uu T Hy Hc HUu HT Hk1 Hk2 Hk3 Hk4 Hg1 Hg2 Hg3 Hg4) as HP.
  set (h1 := pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) _ h _ 0 1) in *.
  set (h2 := pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) _ h _ 0 1) in *.
  set (h3 := pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) _ h _ 0 1) in *.
  set (h4 := pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) _ h _ 0 1) in *.
  set (k1 := pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) _ (KpoleC y a) Hk1 0 1) in *.
  set (k2 := pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) _ (KpoleC y a) Hk2 0 1) in *.
  set (k3 := pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) _ (KpoleC y a) Hk3 0 1) in *.
  set (k4 := pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) _ (KpoleC y a) Hk4 0 1) in *.
  replace (Cadd (Cadd h1 k1) (Cadd (Cadd h2 k2) (Cadd (Cadd h3 k3) (Cadd h4 k4))))
    with (Cadd (Cadd h1 (Cadd h2 (Cadd h3 h4))) (Cadd k1 (Cadd k2 (Cadd k3 k4)))) by ring.
  rewrite HC, HP. ring.
Qed.

Print Assumptions rect_cauchy_region.
Print Assumptions residue_theorem_1pole_region.
