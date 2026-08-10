(* ================================================================= *)
(*  PerronLt1.v  —  Perron A1d (y<1): the right-rectangle apparatus.      *)
(*                                                                    *)
(*  For 0<y<1 the contour must close to the RIGHT (Re from c to U):       *)
(*  the far edge y^U → 0, and the rectangle encloses NO pole, so           *)
(*    ∮_rightrect y^s/s = 0.                                              *)
(*                                                                    *)
(*  This file starts with the reusable primitive rect_winding_right:       *)
(*    ∮ dz/z over the right rectangle = 0  (the four Im-parts cancel via   *)
(*    atan(x)+atan(1/x)=π/2 applied to T/c and U/T, one on each side).    *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CSegInt CWinding ContinuousCoV RectWinding.
Open Scope R_scope.

Theorem rect_winding_right : forall (c U T : R), 0 < c -> c < U -> 0 < T ->
  forall (Hf1 : Ccont (fun u => Cmul (Cinv (seg (mkC c (- T)) (mkC c T) u))
                                     (seg' (mkC c (- T)) (mkC c T) u)))
         (Hf2 : Ccont (fun u => Cmul (Cinv (seg (mkC c T) (mkC U T) u))
                                     (seg' (mkC c T) (mkC U T) u)))
         (Hf3 : Ccont (fun u => Cmul (Cinv (seg (mkC U T) (mkC U (- T)) u))
                                     (seg' (mkC U T) (mkC U (- T)) u)))
         (Hf4 : Ccont (fun u => Cmul (Cinv (seg (mkC U (- T)) (mkC c (- T)) u))
                                     (seg' (mkC U (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T))
                (seg' (mkC c (- T)) (mkC c T)) Cinv Hf1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC U T))
                 (seg' (mkC c T) (mkC U T)) Cinv Hf2 0 1)
  (Cadd (pathint (seg (mkC U T) (mkC U (- T)))
                 (seg' (mkC U T) (mkC U (- T))) Cinv Hf3 0 1)
        (pathint (seg (mkC U (- T)) (mkC c (- T)))
                 (seg' (mkC U (- T)) (mkC c (- T))) Cinv Hf4 0 1)))
  = C0.
Proof.
  intros c U T Hc HU HT Hf1 Hf2 Hf3 Hf4.
  assert (Hc0 : c <> 0) by lra.
  assert (HU0 : U <> 0) by lra.
  assert (HT0 : T <> 0) by lra.
  assert (HnT0 : - T <> 0) by lra.
  rewrite (vseg_winding c (- T) T Hc0 Hf1).
  rewrite (hseg_winding c U T HT0 Hf2).
  rewrite (vseg_winding U T (- T) HU0 Hf3).
  rewrite (hseg_winding U c (- T) HnT0 Hf4).
  unfold Cadd, C0; apply Ceq; cbn [Re Im].
  - replace ((- T) * (- T)) with (T * T) by ring; ring.
  - pose proof (atan_compl (T / c) (Rdiv_lt_0_compat T c HT Hc)) as H1.
    pose proof (atan_compl (U / T) (Rdiv_lt_0_compat U T ltac:(lra) HT)) as H2.
    replace (/ (T / c)) with (c / T) in H1 by (field; lra).
    replace (/ (U / T)) with (T / U) in H2 by (field; lra).
    replace (- T / c) with (- (T / c)) in * by (field; lra).
    replace (- T / U) with (- (T / U)) in * by (field; lra).
    replace (c / - T) with (- (c / T)) in * by (field; lra).
    replace (U / - T) with (- (U / T)) in * by (field; lra).
    rewrite !atan_opp.
    lra.
Qed.

Print Assumptions rect_winding_right.

(* ================================================================= *)
(*  (checkpoint) right-rectangle winding = 0.  Next: phi_ext quad loop,   *)
(*  the right-rect residue = 0, the y<1 horizontal bound, and perron_lt1. *)
(* ================================================================= *)
