(* ================================================================= *)
(*  PerronKernel.v  —  Perron milestone A1d (residue step): the Perron   *)
(*  kernel y^s/s integrated around the rectangle equals 2πi.            *)
(*                                                                    *)
(*  On the rectangle edges (which avoid 0) we have the exact splitting   *)
(*    y^s/s  =  (y^s−1)/s  +  1/s  =  phi_ext(s)  +  1/s,                 *)
(*  so the rectangle integral of y^s/s is                                *)
(*    ∮_rect (y^s−1)/s  +  ∮_rect 1/s  =  0  +  2πi  =  2πi,              *)
(*  combining PerronRemovable.phi_ext_rect_loop (A1c) and                *)
(*  RectWinding.rect_winding (A1b).  This is the pole residue that        *)
(*  feeds the truncated Perron bound perron_gt1.  Axiom-clean.           *)
(*                                                                    *)
(*  Also builds the reusable Ccont_Cinv_comp: 1/z is continuous along a   *)
(*  path avoiding 0 (the recurring integrand-continuity the repo takes    *)
(*  as a hypothesis everywhere).                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CGoursatLin
        CPathIntegral CexpFull PerronPower RectWinding PerronRemovable CTruncCauchy.
Open Scope R_scope.

Lemma continuity_pt_ext : forall f g t,
  (forall x, f x = g x) -> continuity_pt f t -> continuity_pt g t.
Proof.
  intros f g t Hfg Hf; replace g with f; [ exact Hf | apply functional_extensionality; exact Hfg ].
Qed.

(* ----------------------------------------------------------------- *)
(*  1/z is continuous along any path that avoids 0                     *)
(* ----------------------------------------------------------------- *)

Lemma Cnorm2_ne0 : forall c, c <> C0 -> Cnorm2 c <> 0.
Proof.
  intros c Hc H; apply Hc; unfold Cnorm2 in H; apply Ceq; cbn;
    pose proof (Rle_0_sqr (Re c)); pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; nra.
Qed.

Lemma Ccont_Cnorm2_comp : forall g, Ccont g ->
  forall x, continuity_pt (fun u => Cnorm2 (g u)) x.
Proof.
  intros g [HgR HgI] x.
  apply (continuity_pt_ext (fun u => Re (g u) * Re (g u) + Im (g u) * Im (g u)));
    [ intro u; reflexivity | ].
  apply continuity_pt_plus; apply continuity_pt_mult; solve [ apply HgR | apply HgI ].
Qed.

Lemma Ccont_Cinv_comp : forall g, Ccont g -> (forall u, g u <> C0) ->
  Ccont (fun u => Cinv (g u)).
Proof.
  intros g Hg Hg0; assert (HgRI := Hg); destruct HgRI as [HgR HgI]; split; intro x.
  - apply (continuity_pt_ext (fun u => Re (g u) / Cnorm2 (g u)));
      [ intro u; unfold Cinv; reflexivity | ].
    apply continuity_pt_div;
      [ apply HgR | apply Ccont_Cnorm2_comp; exact Hg | apply Cnorm2_ne0; apply Hg0 ].
  - apply (continuity_pt_ext (fun u => - Im (g u) / Cnorm2 (g u)));
      [ intro u; unfold Cinv; reflexivity | ].
    apply continuity_pt_div;
      [ apply continuity_pt_opp; apply HgI
      | apply Ccont_Cnorm2_comp; exact Hg | apply Cnorm2_ne0; apply Hg0 ].
Qed.

(* ----------------------------------------------------------------- *)
(*  rectangle edges avoid 0                                            *)
(* ----------------------------------------------------------------- *)

Lemma seg_ne0_v : forall a p q u, a <> 0 -> seg (mkC a p) (mkC a q) u <> C0.
Proof.
  intros a p q u Ha H; rewrite segv in H; apply (f_equal Re) in H; cbn in H; apply Ha; exact H.
Qed.

Lemma seg_ne0_h : forall p q b u, b <> 0 -> seg (mkC p b) (mkC q b) u <> C0.
Proof.
  intros p q b u Hb H; rewrite segh in H; apply (f_equal Im) in H; cbn in H; apply Hb; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  per-edge split:  ∫ y^s/s = ∫ phi_ext + ∫ 1/s                        *)
(* ----------------------------------------------------------------- *)

Lemma edge_split : forall y P Q (H0 : forall u, seg P Q u <> C0)
  (HfF : Ccont (fun u => Cmul (Cmul (Cpw y (seg P Q u)) (Cinv (seg P Q u))) (seg' P Q u)))
  (Hfp : Ccont (fun u => Cmul (phi_ext y (seg P Q u)) (seg' P Q u)))
  (Hfi : Ccont (fun u => Cmul (Cinv (seg P Q u)) (seg' P Q u))),
  pathint (seg P Q) (seg' P Q) (fun z => Cmul (Cpw y z) (Cinv z)) HfF 0 1
  = Cadd (pathint (seg P Q) (seg' P Q) (phi_ext y) Hfp 0 1)
         (pathint (seg P Q) (seg' P Q) Cinv Hfi 0 1).
Proof.
  intros y P Q H0 HfF Hfp Hfi; unfold pathint.
  rewrite (Cintf_ext
             (fun u => Cmul (Cmul (Cpw y (seg P Q u)) (Cinv (seg P Q u))) (seg' P Q u))
             (fun u => Cadd (Cmul (phi_ext y (seg P Q u)) (seg' P Q u))
                            (Cmul (Cinv (seg P Q u)) (seg' P Q u)))
             HfF (Ccont_add _ _ Hfp Hfi) 0 1);
    [ | intro u; rewrite (phi_ext_off0 y (seg P Q u) (H0 u)); unfold qy; ring ].
  rewrite (Cintf_add (fun u => Cmul (phi_ext y (seg P Q u)) (seg' P Q u))
             (fun u => Cmul (Cinv (seg P Q u)) (seg' P Q u))
             Hfp Hfi (Ccont_add _ _ Hfp Hfi) 0 1 Rle_0_1).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE PERRON RESIDUE:  ∮_rect y^s/s = 2πi                             *)
(* ----------------------------------------------------------------- *)

Theorem perron_rect_residue : forall (y c Uu T : R),
  0 < y -> 0 < c -> 0 < Uu -> 0 < T ->
  forall (HfF1 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c (- T)) (mkC c T) u))
                          (Cinv (seg (mkC c (- T)) (mkC c T) u))) (seg' (mkC c (- T)) (mkC c T) u)))
         (HfF2 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c T) (mkC (- Uu) T) u))
                          (Cinv (seg (mkC c T) (mkC (- Uu) T) u))) (seg' (mkC c T) (mkC (- Uu) T) u)))
         (HfF3 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u))
                          (Cinv (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
         (HfF4 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u))
                          (Cinv (seg (mkC (- Uu) (- T)) (mkC c (- T)) u))) (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T))
                (fun z => Cmul (Cpw y z) (Cinv z)) HfF1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC (- Uu) T)) (seg' (mkC c T) (mkC (- Uu) T))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF2 0 1)
  (Cadd (pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF3 0 1)
        (pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) (seg' (mkC (- Uu) (- T)) (mkC c (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF4 0 1)))
  = mkC 0 (2 * PI).
Proof.
  intros y c Uu T Hy Hc HU HT HfF1 HfF2 HfF3 HfF4.
  (* edges avoid 0 *)
  assert (H01 : forall u, seg (mkC c (- T)) (mkC c T) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H02 : forall u, seg (mkC c T) (mkC (- Uu) T) u <> C0) by (intro u; apply seg_ne0_h; lra).
  assert (H03 : forall u, seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H04 : forall u, seg (mkC (- Uu) (- T)) (mkC c (- T)) u <> C0) by (intro u; apply seg_ne0_h; lra).
  (* 1/z integrand continuities *)
  assert (Hi1 : Ccont (fun u => Cmul (Cinv (seg (mkC c (- T)) (mkC c T) u)) (seg' (mkC c (- T)) (mkC c T) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H01 ] | apply Ccont_seg'_id ]).
  assert (Hi2 : Ccont (fun u => Cmul (Cinv (seg (mkC c T) (mkC (- Uu) T) u)) (seg' (mkC c T) (mkC (- Uu) T) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H02 ] | apply Ccont_seg'_id ]).
  assert (Hi3 : Ccont (fun u => Cmul (Cinv (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u)) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H03 ] | apply Ccont_seg'_id ]).
  assert (Hi4 : Ccont (fun u => Cmul (Cinv (seg (mkC (- Uu) (- T)) (mkC c (- T)) u)) (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u)))
    by (apply Ccont_mul; [ apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H04 ] | apply Ccont_seg'_id ]).
  (* phi_ext integrand continuities *)
  assert (Hp1 : Ccont (fun u => Cmul (phi_ext y (seg (mkC c (- T)) (mkC c T) u)) (seg' (mkC c (- T)) (mkC c T) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hp2 : Ccont (fun u => Cmul (phi_ext y (seg (mkC c T) (mkC (- Uu) T) u)) (seg' (mkC c T) (mkC (- Uu) T) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hp3 : Ccont (fun u => Cmul (phi_ext y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u)) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Hp4 : Ccont (fun u => Cmul (phi_ext y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u)) (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u)))
    by (apply Ccont_mul; [ apply (phi_ext_cont y Hy); apply Ccont_seg_id | apply Ccont_seg'_id ]).
  (* split each edge *)
  rewrite (edge_split y (mkC c (- T)) (mkC c T) H01 HfF1 Hp1 Hi1).
  rewrite (edge_split y (mkC c T) (mkC (- Uu) T) H02 HfF2 Hp2 Hi2).
  rewrite (edge_split y (mkC (- Uu) T) (mkC (- Uu) (- T)) H03 HfF3 Hp3 Hi3).
  rewrite (edge_split y (mkC (- Uu) (- T)) (mkC c (- T)) H04 HfF4 Hp4 Hi4).
  (* regroup: (Σ phi) + (Σ 1/z) *)
  transitivity
    (Cadd (Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T)) (phi_ext y) Hp1 0 1)
           (Cadd (pathint (seg (mkC c T) (mkC (- Uu) T)) (seg' (mkC c T) (mkC (- Uu) T)) (phi_ext y) Hp2 0 1)
           (Cadd (pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T))) (phi_ext y) Hp3 0 1)
                 (pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) (seg' (mkC (- Uu) (- T)) (mkC c (- T))) (phi_ext y) Hp4 0 1))))
          (Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T)) Cinv Hi1 0 1)
           (Cadd (pathint (seg (mkC c T) (mkC (- Uu) T)) (seg' (mkC c T) (mkC (- Uu) T)) Cinv Hi2 0 1)
           (Cadd (pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T))) Cinv Hi3 0 1)
                 (pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) (seg' (mkC (- Uu) (- T)) (mkC c (- T))) Cinv Hi4 0 1))))).
  - ring.
  - rewrite (phi_ext_rect_loop y Hy c Uu T Hc HU HT Hp1 Hp2 Hp3 Hp4).
    rewrite (rect_winding c Uu T Hc HU HT Hi1 Hi2 Hi3 Hi4).
    ring.
Qed.

Print Assumptions perron_rect_residue.

(* ================================================================= *)
(*  END PerronKernel.v (residue step) — ∮_rect y^s/s = 2πi, the Perron   *)
(*  pole residue, combining A1b (rect_winding) and A1c (phi_ext loop).    *)
(*  Next: the vertical-line truncation bounds perron_gt1 / perron_lt1.   *)
(* ================================================================= *)
