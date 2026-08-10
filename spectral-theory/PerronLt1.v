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
Require Import ComplexField Cmodulus CDeriv CImproperIntegral CIntegral2
        CPathIntegral CSegInt CWinding ContinuousCoV RectWinding
        CexpFull PerronPower PerronRemovable PerronKernel PerronBound PerronEdge
        PerronVertical PerronGt1 CTruncCauchy.
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

(* ----------------------------------------------------------------- *)
(*  general monotonicity sign of Rpower (valid for any y>0)           *)
(* ----------------------------------------------------------------- *)

Lemma Rpower_diff_sign_gen : forall y p q, 0 < y ->
  0 <= ln y * ((q - p) * (Rpower y q - Rpower y p)).
Proof.
  intros y p q Hy.
  destruct (Rtotal_order q p) as [Hlt | [Heq | Hgt]].
  - destruct (Rtotal_order (ln y) 0) as [HL | [HL | HL]].
    + assert (Rpower y p < Rpower y q) by (unfold Rpower; apply exp_increasing; nra).
      assert ((q - p) * (Rpower y q - Rpower y p) <= 0) by nra; nra.
    + rewrite HL, Rmult_0_l; apply Rle_refl.
    + assert (Rpower y q < Rpower y p) by (unfold Rpower; apply exp_increasing; nra).
      assert (0 <= (q - p) * (Rpower y q - Rpower y p)) by nra; nra.
  - assert (Hz : (q - p) * (Rpower y q - Rpower y p) = 0) by (rewrite Heq; ring);
      rewrite Hz, Rmult_0_r; apply Rle_refl.
  - destruct (Rtotal_order (ln y) 0) as [HL | [HL | HL]].
    + assert (Rpower y q < Rpower y p) by (unfold Rpower; apply exp_increasing; nra).
      assert ((q - p) * (Rpower y q - Rpower y p) <= 0) by nra; nra.
    + rewrite HL, Rmult_0_l; apply Rle_refl.
    + assert (Rpower y p < Rpower y q) by (unfold Rpower; apply exp_increasing; nra).
      assert (0 <= (q - p) * (Rpower y q - Rpower y p)) by nra; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the horizontal-edge bound for any y>0, y≠1 (|ln y| form)          *)
(* ----------------------------------------------------------------- *)

Theorem horiz_edge_bound_gen : forall y p q b
  (Hy : 0 < y) (Hlne : ln y <> 0) (Hb : b <> 0) (Hpq : q <> p)
  (HfF : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC p b) (mkC q b) u))
                    (Cinv (seg (mkC p b) (mkC q b) u))) (seg' (mkC p b) (mkC q b) u))),
  Cmod (pathint (seg (mkC p b) (mkC q b)) (seg' (mkC p b) (mkC q b))
                (fun z => Cmul (Cpw y z) (Cinv z)) HfF 0 1)
  <= 2 * (Rabs (Rpower y q - Rpower y p) / (Rabs b * Rabs (ln y))).
Proof.
  intros y p q b Hy Hlne Hb Hpq HfF.
  assert (Hab : 0 < Rabs b) by (apply Rabs_pos_lt; exact Hb).
  assert (Hlab : 0 < Rabs (ln y)) by (apply Rabs_pos_lt; exact Hlne).
  assert (Hqpab : 0 < Rabs (q - p)) by (apply Rabs_pos_lt; intro Hc; apply Hpq; lra).
  set (k := Rabs (q - p) / Rabs b).
  assert (Hcm : Riemann_integrable
                  (fun u => Cmod (Cmul (Cmul (Cpw y (seg (mkC p b) (mkC q b) u))
                    (Cinv (seg (mkC p b) (mkC q b) u))) (seg' (mkC p b) (mkC q b) u))) 0 1)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply Ccont_Cmod; exact HfF ]).
  assert (Hbd : Riemann_integrable (fun u => k * Rpower y (Ld p q u)) 0 1).
  { apply continuity_implies_RiemannInt; [ lra | intros x _ ].
    apply (continuity_pt_mult (fun _ => k) (fun u => Rpower y (Ld p q u)) x);
      [ apply continuity_pt_const; intros a c; reflexivity
      | apply derivable_continuous_pt; exists (ln y * Rpower y (Ld p q x) * (q - p));
        apply Rpower_Ld_deriv; exact Hy ]. }
  assert (Hpt : forall u, 0 < u < 1 ->
    Cmod (Cmul (Cmul (Cpw y (seg (mkC p b) (mkC q b) u))
          (Cinv (seg (mkC p b) (mkC q b) u))) (seg' (mkC p b) (mkC q b) u))
    <= k * Rpower y (Ld p q u)).
  { intros u _; rewrite segh, segh', !Cmod_mul, (Cpw_mod y (mkC (Ld p q u) b)); cbn [Re].
    rewrite (Cmod_inv (mkC (Ld p q u) b) (mkC_Im_ne0 _ _ Hb)).
    replace (Cmod (mkC (q - p) 0)) with (Rabs (q - p))
      by (change (mkC (q - p) 0) with (RtoC (q - p)); rewrite Cmod_RtoC; reflexivity).
    assert (Hge : Rabs b <= Cmod (mkC (Ld p q u) b))
      by (pose proof (Cmod_Im (mkC (Ld p q u) b)) as H; cbn in H; exact H).
    assert (Hcp : 0 < Cmod (mkC (Ld p q u) b)) by lra.
    assert (Hinv : / Cmod (mkC (Ld p q u) b) <= / Rabs b)
      by (apply Rinv_le_contravar; [ exact Hab | exact Hge ]).
    assert (Hrp : 0 <= Rpower y (Ld p q u)) by (left; apply exp_pos).
    apply Rle_trans with (Rpower y (Ld p q u) * / Rabs b * Rabs (q - p)).
    - apply Rmult_le_compat_r; [ apply Rabs_pos | apply Rmult_le_compat_l; [ exact Hrp | exact Hinv ] ].
    - apply Req_le; unfold k; field; intro Hz; nra. }
  unfold pathint.
  eapply Rle_trans; [ apply (Cintf_mod_le2 _ HfF 0 1 Hcm Rle_0_1) | ].
  apply Rmult_le_compat_l; [ lra | ].
  eapply Rle_trans; [ apply (RiemannInt_P19 Hcm Hbd Rle_0_1 Hpt) | ].
  rewrite (int_kRpower_Ld y p q k Hy Hlne ltac:(lra) Hbd).
  apply Req_le.
  assert (Hqpl : (q - p) * ln y <> 0)
    by (apply Rmult_integral_contrapositive_currified; [ intro Hc; apply Hpq; lra | exact Hlne ]).
  assert (Hsgn : Rabs (q - p) * (Rpower y q - Rpower y p) * Rabs (ln y)
                 = Rabs (Rpower y q - Rpower y p) * ((q - p) * ln y)).
  { pose proof (Rpower_diff_sign_gen y p q Hy) as Hsg.
    assert (Hsg2 : 0 <= (q - p) * ln y * (Rpower y q - Rpower y p)) by nra.
    replace (Rabs (q - p) * (Rpower y q - Rpower y p) * Rabs (ln y))
      with (Rabs (q - p) * Rabs (ln y) * (Rpower y q - Rpower y p)) by ring.
    rewrite <- Rabs_mult.
    unfold Rabs; destruct (Rcase_abs ((q - p) * ln y));
      destruct (Rcase_abs (Rpower y q - Rpower y p)); nra. }
  unfold k.
  apply Rmult_eq_reg_r with (Rabs b * Rabs (ln y)); [ | intro Hz; nra ].
  transitivity (Rabs (Rpower y q - Rpower y p)).
  - replace (Rabs (q - p) / Rabs b * ((Rpower y q - Rpower y p) / ((q - p) * ln y))
             * (Rabs b * Rabs (ln y)))
      with (Rabs (q - p) * (Rpower y q - Rpower y p) * Rabs (ln y) / ((q - p) * ln y))
      by (field; repeat split; intro Hz; nra).
    rewrite Hsgn; field; repeat split; intro Hz; nra.
  - field; repeat split; intro Hz; nra.
Qed.

Print Assumptions horiz_edge_bound_gen.

(* ----------------------------------------------------------------- *)
(*  the far (right) vertical edge  →  O(y^U/U)  (→ 0 for y<1)          *)
(* ----------------------------------------------------------------- *)

Theorem far_edge_bound : forall y U T (Hy : 0 < y) (HU : 0 < U) (HT : 0 < T)
  (HfF : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC U T) (mkC U (- T)) u))
                    (Cinv (seg (mkC U T) (mkC U (- T)) u))) (seg' (mkC U T) (mkC U (- T)) u))),
  Cmod (pathint (seg (mkC U T) (mkC U (- T))) (seg' (mkC U T) (mkC U (- T)))
                (fun z => Cmul (Cpw y z) (Cinv z)) HfF 0 1)
  <= 2 * (2 * T * Rpower y U / U).
Proof.
  intros y U T Hy HU HT HfF.
  assert (Hpt : forall u, 0 <= u <= 1 ->
    Cmod (Cmul (Cmul (Cpw y (seg (mkC U T) (mkC U (- T)) u))
          (Cinv (seg (mkC U T) (mkC U (- T)) u))) (seg' (mkC U T) (mkC U (- T)) u))
    <= 2 * T * Rpower y U / U).
  { intros u _; rewrite segv, segv', !Cmod_mul, (Cpw_mod y (mkC U (Ld T (- T) u))); cbn [Re].
    assert (HUne : mkC U (Ld T (- T) u) <> C0) by (apply mkC_Re_ne0; apply Rgt_not_eq; lra).
    rewrite (Cmod_inv (mkC U (Ld T (- T) u)) HUne).
    replace (Cmod (mkC 0 (- T - T))) with (2 * T)
      by (rewrite Cmod_mkC0; replace (- T - T) with (- (2 * T)) by ring;
          rewrite Rabs_Ropp; symmetry; apply Rabs_pos_eq; lra).
    assert (Hge : U <= Cmod (mkC U (Ld T (- T) u)))
      by (pose proof (Cmod_Re (mkC U (Ld T (- T) u))) as H; cbn in H;
          rewrite Rabs_pos_eq in H by lra; lra).
    assert (Hcp : 0 < Cmod (mkC U (Ld T (- T) u))) by lra.
    assert (Hinv : / Cmod (mkC U (Ld T (- T) u)) <= / U)
      by (apply Rinv_le_contravar; [ exact HU | exact Hge ]).
    assert (Hrp : 0 <= Rpower y U) by (left; apply exp_pos).
    apply Rle_trans with (Rpower y U * / U * (2 * T)).
    - apply Rmult_le_compat_r; [ lra | apply Rmult_le_compat_l; [ exact Hrp | exact Hinv ] ].
    - apply Req_le; field; lra. }
  unfold pathint.
  eapply Rle_trans;
    [ apply (Cintf_ML _ HfF 0 1 (2 * T * Rpower y U / U) Rle_0_1 Hpt) | apply Req_le; ring ].
Qed.

(* the residue-0 version:  |Vperron| = |E|/(2π)  (no pole) *)
Lemma vperron_error_eq0 : forall y c T (Hc : c <> 0) E,
  Cadd (Cmul Ci (Vraw y c T Hc)) E = C0 ->
  Cmod (Vperron y c T Hc) = / (2 * PI) * Cmod E.
Proof.
  intros y c T Hc E Hres.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (HciV : Cmul Ci (Vraw y c T Hc) = Copp E)
    by (transitivity (Cminus (Cadd (Cmul Ci (Vraw y c T Hc)) E) E); [ ring | rewrite Hres; ring ]).
  assert (Halg : Cmul Ci (Vperron y c T Hc) = Cmul (RtoC (/ (2 * PI))) (Copp E)).
  { unfold Vperron.
    replace (Cmul Ci (Cmul (RtoC (/ (2 * PI))) (Vraw y c T Hc)))
      with (Cmul (RtoC (/ (2 * PI))) (Cmul Ci (Vraw y c T Hc))) by ring.
    rewrite HciV; reflexivity. }
  assert (Hm := f_equal Cmod Halg).
  rewrite !Cmod_mul, Cmod_Ci, Cmod_opp, Cmod_RtoC in Hm.
  rewrite (Rabs_pos_eq (/ (2 * PI))) in Hm by (left; apply Rinv_0_lt_compat; lra).
  lra.
Qed.

(* ================================================================= *)
(*  THE TRUNCATED PERRON BOUND (0<y<1).                                 *)
(* ================================================================= *)

Theorem perron_lt1 : forall y c T (Hy0 : 0 < y) (Hy1 : y < 1) (Hcpos : 0 < c)
  (HT : 0 < T) (Hc : c <> 0),
  Cmod (Vperron y c T Hc) <= 2 * Rpower y c / (PI * T * (- ln y)).
Proof.
  intros y c T Hy0 Hy1 Hcpos HT Hc.
  assert (Hlny : ln y < 0) by (pose proof (ln_increasing y 1 Hy0 Hy1); rewrite ln_1 in *; lra).
  assert (Hlne : ln y <> 0) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  apply Rle_epsilon; intros eps Heps.
  set (delta := eps * PI / (2 * T)).
  assert (Hd0 : 0 < delta)
    by (unfold delta; apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; lra | apply Rinv_0_lt_compat; lra ]).
  set (Uu := Rmax (c + 1) (- ln delta / (- ln y))).
  assert (HUuc : c < Uu) by (apply Rlt_le_trans with (c + 1); [ lra | apply Rmax_l ]).
  assert (HUu1 : 1 <= Uu) by (apply Rle_trans with (c + 1); [ lra | apply Rmax_l ]).
  assert (HUu : 0 < Uu) by lra.
  assert (HUuln : Uu * ln y <= ln delta).
  { assert (Hmaxr : - ln delta / (- ln y) <= Uu) by (apply Rmax_r).
    assert (- ln delta <= Uu * (- ln y))
      by (apply Rle_trans with (- ln delta / (- ln y) * (- ln y));
            [ apply Req_le; field; lra | apply Rmult_le_compat_r; [ lra | exact Hmaxr ] ]).
    lra. }
  assert (HRp : Rpower y Uu <= delta)
    by (unfold Rpower; rewrite <- (exp_ln delta Hd0); apply exp_le_compat; exact HUuln).
  (* seg-avoids-0 and edge integrand continuities for the right rectangle *)
  assert (H1 : forall u, seg (mkC c (- T)) (mkC c T) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H2 : forall u, seg (mkC c T) (mkC Uu T) u <> C0) by (intro u; apply seg_ne0_h; lra).
  assert (H3 : forall u, seg (mkC Uu T) (mkC Uu (- T)) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H4 : forall u, seg (mkC Uu (- T)) (mkC c (- T)) u <> C0) by (intro u; apply seg_ne0_h; lra).
  pose (HfF1 := edge_yss_cont y (mkC c (- T)) (mkC c T) H1).
  pose (HfF2 := edge_yss_cont y (mkC c T) (mkC Uu T) H2).
  pose (HfF3 := edge_yss_cont y (mkC Uu T) (mkC Uu (- T)) H3).
  pose (HfF4 := edge_yss_cont y (mkC Uu (- T)) (mkC c (- T)) H4).
  pose proof (right_rect_residue y c Uu T Hy0 Hcpos HUuc HT HfF1 HfF2 HfF3 HfF4) as Hres.
  rewrite (right_edge_Vraw y c T Hc HT HfF1) in Hres.
  rewrite (vperron_error_eq0 y c T Hc _ Hres).
  set (Etop := pathint (seg (mkC c T) (mkC Uu T)) (seg' (mkC c T) (mkC Uu T))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF2 0 1).
  set (Efar := pathint (seg (mkC Uu T) (mkC Uu (- T))) (seg' (mkC Uu T) (mkC Uu (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF3 0 1).
  set (Ebot := pathint (seg (mkC Uu (- T)) (mkC c (- T))) (seg' (mkC Uu (- T)) (mkC c (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF4 0 1).
  assert (Hrpc : 0 < Rpower y c) by (apply exp_pos).
  assert (Hrpu : 0 < Rpower y Uu) by (apply exp_pos).
  assert (Hlt : Rpower y Uu < Rpower y c)
    by (unfold Rpower; apply exp_increasing; nra).
  assert (Htop : Cmod Etop <= 2 * Rpower y c / (T * - ln y)).
  { unfold Etop; eapply Rle_trans;
      [ apply (horiz_edge_bound_gen y c Uu T Hy0 Hlne
                 (Rgt_not_eq T 0 ltac:(lra)) (Rgt_not_eq Uu c ltac:(lra)) HfF2) | ].
    rewrite (Rabs_left (Rpower y Uu - Rpower y c)) by lra.
    rewrite (Rabs_pos_eq T) by lra.
    rewrite (Rabs_left (ln y)) by lra.
    unfold Rdiv; pose proof (Rinv_0_lt_compat (T * - ln y) ltac:(nra)); nra. }
  assert (Hbot : Cmod Ebot <= 2 * Rpower y c / (T * - ln y)).
  { unfold Ebot; eapply Rle_trans;
      [ apply (horiz_edge_bound_gen y Uu c (- T) Hy0 Hlne
                 (Rlt_not_eq (- T) 0 ltac:(lra)) (Rlt_not_eq c Uu ltac:(lra)) HfF4) | ].
    rewrite (Rabs_pos_eq (Rpower y c - Rpower y Uu)) by lra.
    replace (Rabs (- T)) with T by (rewrite Rabs_Ropp, Rabs_pos_eq; lra).
    rewrite (Rabs_left (ln y)) by lra.
    unfold Rdiv; pose proof (Rinv_0_lt_compat (T * - ln y) ltac:(nra)); nra. }
  assert (Hfar : Cmod Efar <= 4 * T * Rpower y Uu / Uu).
  { unfold Efar; eapply Rle_trans;
      [ apply (far_edge_bound y Uu T Hy0 HUu HT HfF3) | apply Req_le; field; lra ]. }
  assert (HEtri : Cmod (Cadd Etop (Cadd Efar Ebot)) <= Cmod Etop + Cmod Efar + Cmod Ebot).
  { eapply Rle_trans; [ apply Cmod_triangle | ].
    pose proof (Cmod_triangle Efar Ebot); lra. }
  apply Rle_trans with (/ (2 * PI) * (Cmod Etop + Cmod Efar + Cmod Ebot)).
  { apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; lra | exact HEtri ]. }
  apply Rle_trans with (/ (2 * PI) * (4 * Rpower y c / (T * - ln y) + 4 * T * Rpower y Uu / Uu)).
  { apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; lra | lra ]. }
  assert (Hfin : / (2 * PI) * (4 * Rpower y c / (T * - ln y) + 4 * T * Rpower y Uu / Uu)
                 = 2 * Rpower y c / (PI * T * - ln y) + 2 * T * Rpower y Uu / (PI * Uu))
    by (field; repeat split; lra).
  rewrite Hfin.
  apply Rplus_le_compat_l.
  apply Rmult_le_reg_r with (PI * Uu); [ nra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra.
  assert (Hde : 2 * T * delta = eps * PI) by (unfold delta; field; lra).
  assert (Hstep1 : 2 * T * Rpower y Uu <= 2 * T * delta) by nra.
  assert (Hstep2 : eps * PI <= eps * (PI * Uu)) by (apply Rmult_le_compat_l; [ lra | nra ]).
  lra.
Qed.

Print Assumptions perron_lt1.

(* ================================================================= *)
(*  END PerronLt1.v — perron_lt1 (0<y<1) complete, mirroring perron_gt1  *)
(*  on the right (pole-free) rectangle.  Axiom-clean.                    *)
(* ================================================================= *)
