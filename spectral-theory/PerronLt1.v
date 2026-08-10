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
        CPathIntegral CSegInt CWinding ContinuousCoV RectWinding
        CexpFull PerronPower PerronRemovable PerronKernel CTruncCauchy.
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

(* ----------------------------------------------------------------- *)
(*  the removable part telescopes to 0 over ANY closed quadrilateral   *)
(* ----------------------------------------------------------------- *)

Lemma phi_ext_quad : forall y (Hy : 0 < y) P1 P2 P3 P4
  (Hf12 : Ccont (fun u => Cmul (phi_ext y (seg P1 P2 u)) (seg' P1 P2 u)))
  (Hf23 : Ccont (fun u => Cmul (phi_ext y (seg P2 P3 u)) (seg' P2 P3 u)))
  (Hf34 : Ccont (fun u => Cmul (phi_ext y (seg P3 P4 u)) (seg' P3 P4 u)))
  (Hf41 : Ccont (fun u => Cmul (phi_ext y (seg P4 P1 u)) (seg' P4 P1 u))),
  Cadd (pathint (seg P1 P2) (seg' P1 P2) (phi_ext y) Hf12 0 1)
  (Cadd (pathint (seg P2 P3) (seg' P2 P3) (phi_ext y) Hf23 0 1)
  (Cadd (pathint (seg P3 P4) (seg' P3 P4) (phi_ext y) Hf34 0 1)
        (pathint (seg P4 P1) (seg' P4 P1) (phi_ext y) Hf41 0 1))) = C0.
Proof.
  intros y Hy P1 P2 P3 P4 Hf12 Hf23 Hf34 Hf41.
  rewrite (Iedge y Hy P1 P2 Hf12), (Iedge y Hy P2 P3 Hf23),
    (Iedge y Hy P3 P4 Hf34), (Iedge y Hy P4 P1 Hf41); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the right-rectangle residue is 0 (no pole enclosed)               *)
(* ----------------------------------------------------------------- *)

Theorem right_rect_residue : forall (y c U T : R),
  0 < y -> 0 < c -> c < U -> 0 < T ->
  forall (HfF1 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c (- T)) (mkC c T) u))
                          (Cinv (seg (mkC c (- T)) (mkC c T) u))) (seg' (mkC c (- T)) (mkC c T) u)))
         (HfF2 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c T) (mkC U T) u))
                          (Cinv (seg (mkC c T) (mkC U T) u))) (seg' (mkC c T) (mkC U T) u)))
         (HfF3 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC U T) (mkC U (- T)) u))
                          (Cinv (seg (mkC U T) (mkC U (- T)) u))) (seg' (mkC U T) (mkC U (- T)) u)))
         (HfF4 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC U (- T)) (mkC c (- T)) u))
                          (Cinv (seg (mkC U (- T)) (mkC c (- T)) u))) (seg' (mkC U (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T))
                (fun z => Cmul (Cpw y z) (Cinv z)) HfF1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC U T)) (seg' (mkC c T) (mkC U T))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF2 0 1)
  (Cadd (pathint (seg (mkC U T) (mkC U (- T))) (seg' (mkC U T) (mkC U (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF3 0 1)
        (pathint (seg (mkC U (- T)) (mkC c (- T))) (seg' (mkC U (- T)) (mkC c (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF4 0 1)))
  = C0.
Proof.
  intros y c U T Hy Hc HU HT HfF1 HfF2 HfF3 HfF4.
  assert (H01 : forall u, seg (mkC c (- T)) (mkC c T) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H02 : forall u, seg (mkC c T) (mkC U T) u <> C0) by (intro u; apply seg_ne0_h; lra).
  assert (H03 : forall u, seg (mkC U T) (mkC U (- T)) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H04 : forall u, seg (mkC U (- T)) (mkC c (- T)) u <> C0) by (intro u; apply seg_ne0_h; lra).
  assert (Hi1 : Ccont (fun u => Cmul (Cinv (seg (mkC c (- T)) (mkC c T) u)) (seg' (mkC c (- T)) (mkC c T) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H01 ] | apply Ccont_seg'_id ]).
  assert (Hi2 : Ccont (fun u => Cmul (Cinv (seg (mkC c T) (mkC U T) u)) (seg' (mkC c T) (mkC U T) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H02 ] | apply Ccont_seg'_id ]).
  assert (Hi3 : Ccont (fun u => Cmul (Cinv (seg (mkC U T) (mkC U (- T)) u)) (seg' (mkC U T) (mkC U (- T)) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H03 ] | apply Ccont_seg'_id ]).
  assert (Hi4 : Ccont (fun u => Cmul (Cinv (seg (mkC U (- T)) (mkC c (- T)) u)) (seg' (mkC U (- T)) (mkC c (- T)) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H04 ] | apply Ccont_seg'_id ]).
  assert (Hp1 : Ccont (fun u => Cmul (phi_ext y (seg (mkC c (- T)) (mkC c T) u)) (seg' (mkC c (- T)) (mkC c T) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hp2 : Ccont (fun u => Cmul (phi_ext y (seg (mkC c T) (mkC U T) u)) (seg' (mkC c T) (mkC U T) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hp3 : Ccont (fun u => Cmul (phi_ext y (seg (mkC U T) (mkC U (- T)) u)) (seg' (mkC U T) (mkC U (- T)) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hp4 : Ccont (fun u => Cmul (phi_ext y (seg (mkC U (- T)) (mkC c (- T)) u)) (seg' (mkC U (- T)) (mkC c (- T)) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  rewrite (edge_split y (mkC c (- T)) (mkC c T) H01 HfF1 Hp1 Hi1).
  rewrite (edge_split y (mkC c T) (mkC U T) H02 HfF2 Hp2 Hi2).
  rewrite (edge_split y (mkC U T) (mkC U (- T)) H03 HfF3 Hp3 Hi3).
  rewrite (edge_split y (mkC U (- T)) (mkC c (- T)) H04 HfF4 Hp4 Hi4).
  transitivity
    (Cadd (Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T)) (phi_ext y) Hp1 0 1)
           (Cadd (pathint (seg (mkC c T) (mkC U T)) (seg' (mkC c T) (mkC U T)) (phi_ext y) Hp2 0 1)
           (Cadd (pathint (seg (mkC U T) (mkC U (- T))) (seg' (mkC U T) (mkC U (- T))) (phi_ext y) Hp3 0 1)
                 (pathint (seg (mkC U (- T)) (mkC c (- T))) (seg' (mkC U (- T)) (mkC c (- T))) (phi_ext y) Hp4 0 1))))
          (Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T)) Cinv Hi1 0 1)
           (Cadd (pathint (seg (mkC c T) (mkC U T)) (seg' (mkC c T) (mkC U T)) Cinv Hi2 0 1)
           (Cadd (pathint (seg (mkC U T) (mkC U (- T))) (seg' (mkC U T) (mkC U (- T))) Cinv Hi3 0 1)
                 (pathint (seg (mkC U (- T)) (mkC c (- T))) (seg' (mkC U (- T)) (mkC c (- T))) Cinv Hi4 0 1))))).
  - ring.
  - rewrite (phi_ext_quad y Hy (mkC c (- T)) (mkC c T) (mkC U T) (mkC U (- T)) Hp1 Hp2 Hp3 Hp4).
    rewrite (rect_winding_right c U T Hc HU HT Hi1 Hi2 Hi3 Hi4).
    ring.
Qed.

Print Assumptions right_rect_residue.

(* ================================================================= *)
(*  (checkpoint) right-rect residue = 0.  Next: the y<1 horizontal       *)
(*  bound, the far-edge decay, and perron_lt1.                          *)
(* ================================================================= *)
