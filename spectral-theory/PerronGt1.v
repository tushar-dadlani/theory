(* ================================================================= *)
(*  PerronGt1.v  —  Perron A1d: the truncated Perron bound perron_gt1.    *)
(*                                                                    *)
(*  For y>1, c>0, T>0:                                                   *)
(*    | (1/2π)∫_{−T}^{T} y^{c+it}/(c+it) dt − 1 |  ≤  2·y^c/(π·T·ln y).    *)
(*                                                                    *)
(*  From perron_rect_residue (∮_rect y^s/s = 2πi) + right_edge_Vraw       *)
(*  (right edge = i·Vraw): i·Vraw + (top+left+bottom) = 2πi, so           *)
(*  |Vperron − 1| = |top+left+bottom|/(2π).  The horizontal edges are      *)
(*  ≤ 2(y^c−y^{−U})/(T ln y) (horiz_edge_bound); the left edge → 0; and    *)
(*  U→∞ gives the bound.  Axiom-clean.                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv CImproperIntegral CIntegral2
        CPathIntegral CexpFull PerronPower RectWinding PerronKernel PerronVertical
        PerronEdge PerronRemovable CTruncCauchy.
Open Scope R_scope.

Lemma mkC_Re_ne0 : forall a b, a <> 0 -> mkC a b <> C0.
Proof. intros a b Ha H; apply Ha; apply (f_equal Re) in H; cbn in H; exact H. Qed.

Lemma Cmod_mkC0 : forall z, Cmod (mkC 0 z) = Rabs z.
Proof.
  intro z; unfold Cmod, Cnorm2; cbn;
    replace (0 * 0 + z * z) with (Rsqr z) by (unfold Rsqr; ring); apply sqrt_Rsqr_abs.
Qed.

(* the y^s/s integrand along an edge that avoids 0 is continuous *)
Lemma edge_yss_cont : forall y P Q, (forall u, seg P Q u <> C0) ->
  Ccont (fun u => Cmul (Cmul (Cpw y (seg P Q u)) (Cinv (seg P Q u))) (seg' P Q u)).
Proof.
  intros y P Q H0; apply Ccont_mul; [ apply Ccont_mul | apply Ccont_seg'_id ].
  - apply (CcontC_Cpw y (seg P Q) (Ccont_seg_id P Q)).
  - apply Ccont_Cinv_comp; [ apply Ccont_seg_id | exact H0 ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the left (far) vertical edge  →  O(y^{−U}/U)                        *)
(* ----------------------------------------------------------------- *)

Theorem left_edge_bound : forall y U T (Hy1 : 1 < y) (HU : 0 < U) (HT : 0 < T)
  (HfF : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- U) T) (mkC (- U) (- T)) u))
                    (Cinv (seg (mkC (- U) T) (mkC (- U) (- T)) u))) (seg' (mkC (- U) T) (mkC (- U) (- T)) u))),
  Cmod (pathint (seg (mkC (- U) T) (mkC (- U) (- T))) (seg' (mkC (- U) T) (mkC (- U) (- T)))
                (fun z => Cmul (Cpw y z) (Cinv z)) HfF 0 1)
  <= 2 * (2 * T * Rpower y (- U) / U).
Proof.
  intros y U T Hy1 HU HT HfF.
  assert (Hy : 0 < y) by lra.
  assert (Hpt : forall u, 0 <= u <= 1 ->
    Cmod (Cmul (Cmul (Cpw y (seg (mkC (- U) T) (mkC (- U) (- T)) u))
          (Cinv (seg (mkC (- U) T) (mkC (- U) (- T)) u))) (seg' (mkC (- U) T) (mkC (- U) (- T)) u))
    <= 2 * T * Rpower y (- U) / U).
  { intros u _; rewrite segv, segv', !Cmod_mul, (Cpw_mod y (mkC (- U) (Ld T (- T) u))); cbn [Re].
    assert (HUne : mkC (- U) (Ld T (- T) u) <> C0)
      by (apply mkC_Re_ne0; apply Rlt_not_eq; lra).
    rewrite (Cmod_inv (mkC (- U) (Ld T (- T) u)) HUne).
    replace (Cmod (mkC 0 (- T - T))) with (2 * T)
      by (rewrite Cmod_mkC0; replace (- T - T) with (- (2 * T)) by ring;
          rewrite Rabs_Ropp; symmetry; apply Rabs_pos_eq; lra).
    assert (Hge : U <= Cmod (mkC (- U) (Ld T (- T) u))).
    { pose proof (Cmod_Re (mkC (- U) (Ld T (- T) u))) as H; cbn in H;
        rewrite Rabs_left in H by lra; lra. }
    assert (Hcp : 0 < Cmod (mkC (- U) (Ld T (- T) u))) by lra.
    assert (Hinv : / Cmod (mkC (- U) (Ld T (- T) u)) <= / U)
      by (apply Rinv_le_contravar; [ exact HU | exact Hge ]).
    assert (Hrp : 0 <= Rpower y (- U)) by (left; apply exp_pos).
    apply Rle_trans with (Rpower y (- U) * / U * (2 * T)).
    - apply Rmult_le_compat_r; [ lra | apply Rmult_le_compat_l; [ exact Hrp | exact Hinv ] ].
    - apply Req_le; field; lra. }
  unfold pathint.
  eapply Rle_trans;
    [ apply (Cintf_ML _ HfF 0 1 (2 * T * Rpower y (- U) / U) Rle_0_1 Hpt) | apply Req_le; ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the residue algebra and the U→∞ limit                              *)
(* ----------------------------------------------------------------- *)

Lemma Cmod_Ci : Cmod Ci = 1.
Proof.
  unfold Cmod, Cnorm2, Ci; cbn; replace (0 * 0 + 1 * 1) with 1 by ring; apply sqrt_1.
Qed.

Lemma Rle_epsilon : forall a b, (forall eps, 0 < eps -> a <= b + eps) -> a <= b.
Proof.
  intros a b H; destruct (Rle_or_lt a b) as [Hle | Hlt]; [ exact Hle | ].
  exfalso; pose proof (H ((a - b) / 2) ltac:(lra)); lra.
Qed.

(* from the residue relation, the Perron error equals |E|/(2π) *)
Lemma vperron_error_eq : forall y c T (Hc : c <> 0) E,
  Cadd (Cmul Ci (Vraw y c T Hc)) E = mkC 0 (2 * PI) ->
  Cmod (Cminus (Vperron y c T Hc) C1) = / (2 * PI) * Cmod E.
Proof.
  intros y c T Hc E Hres.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (HciV : Cmul Ci (Vraw y c T Hc) = Cminus (mkC 0 (2 * PI)) E)
    by (rewrite <- Hres; ring).
  assert (Halg : Cmul Ci (Cminus (Vperron y c T Hc) C1) = Copp (Cmul (RtoC (/ (2 * PI))) E)).
  { unfold Vperron.
    replace (Cmul Ci (Cminus (Cmul (RtoC (/ (2 * PI))) (Vraw y c T Hc)) C1))
      with (Cminus (Cmul (RtoC (/ (2 * PI))) (Cmul Ci (Vraw y c T Hc))) Ci) by ring.
    rewrite HciV; unfold Ci, RtoC, Cmul, Cminus, Cadd, Copp; apply Ceq; cbn; field; lra. }
  assert (Hm := f_equal Cmod Halg).
  rewrite Cmod_mul, Cmod_Ci, Cmod_opp, Cmod_mul, Cmod_RtoC in Hm.
  rewrite (Rabs_pos_eq (/ (2 * PI))) in Hm by (left; apply Rinv_0_lt_compat; lra).
  lra.
Qed.

(* ================================================================= *)
(*  THE TRUNCATED PERRON BOUND (y>1).                                   *)
(* ================================================================= *)

Theorem perron_gt1 : forall y c T (Hy1 : 1 < y) (Hcpos : 0 < c) (HT : 0 < T) (Hc : c <> 0),
  Cmod (Cminus (Vperron y c T Hc) C1) <= 2 * Rpower y c / (PI * T * ln y).
Proof.
  intros y c T Hy1 Hcpos HT Hc.
  assert (Hy : 0 < y) by lra.
  assert (Hlny : 0 < ln y) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  apply Rle_epsilon; intros eps Heps.
  set (delta := eps * PI / (2 * T)).
  assert (Hd0 : 0 < delta)
    by (unfold delta; apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; lra | apply Rinv_0_lt_compat; lra ]).
  set (Uu := Rmax 1 (- ln delta / ln y)).
  assert (HUu1 : 1 <= Uu) by (apply Rmax_l).
  assert (HUu : 0 < Uu) by lra.
  assert (Hstep : - ln delta <= Uu * ln y).
  { apply Rle_trans with (- ln delta / ln y * ln y);
      [ apply Req_le; field; lra | apply Rmult_le_compat_r; [ lra | apply Rmax_r ] ]. }
  assert (HRp : Rpower y (- Uu) <= delta).
  { unfold Rpower; rewrite <- (exp_ln delta Hd0); apply exp_le_compat; lra. }
  (* seg-avoids-0 and edge integrand continuities *)
  assert (H1 : forall u, seg (mkC c (- T)) (mkC c T) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H2 : forall u, seg (mkC c T) (mkC (- Uu) T) u <> C0) by (intro u; apply seg_ne0_h; lra).
  assert (H3 : forall u, seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u <> C0) by (intro u; apply seg_ne0_v; lra).
  assert (H4 : forall u, seg (mkC (- Uu) (- T)) (mkC c (- T)) u <> C0) by (intro u; apply seg_ne0_h; lra).
  pose (HfF1 := edge_yss_cont y (mkC c (- T)) (mkC c T) H1).
  pose (HfF2 := edge_yss_cont y (mkC c T) (mkC (- Uu) T) H2).
  pose (HfF3 := edge_yss_cont y (mkC (- Uu) T) (mkC (- Uu) (- T)) H3).
  pose (HfF4 := edge_yss_cont y (mkC (- Uu) (- T)) (mkC c (- T)) H4).
  pose proof (perron_rect_residue y c Uu T Hy Hcpos HUu HT HfF1 HfF2 HfF3 HfF4) as Hres.
  rewrite (right_edge_Vraw y c T Hc HT HfF1) in Hres.
  rewrite (vperron_error_eq y c T Hc _ Hres).
  (* bound |E| = |top + left + bottom| *)
  set (Etop := pathint (seg (mkC c T) (mkC (- Uu) T)) (seg' (mkC c T) (mkC (- Uu) T))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF2 0 1).
  set (Eleft := pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF3 0 1).
  set (Ebot := pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) (seg' (mkC (- Uu) (- T)) (mkC c (- T)))
                 (fun z => Cmul (Cpw y z) (Cinv z)) HfF4 0 1).
  assert (Htop : Cmod Etop <= 2 * Rpower y c / (T * ln y)).
  { unfold Etop; eapply Rle_trans;
      [ apply (horiz_edge_bound y c (- Uu) T Hy1
                 (Rgt_not_eq T 0 ltac:(lra)) (Rlt_not_eq (- Uu) c ltac:(lra)) HfF2) | ].
    assert (Hlt : Rpower y (- Uu) < Rpower y c)
      by (unfold Rpower; apply exp_increasing, Rmult_lt_compat_r; lra).
    assert (Hpu : 0 < Rpower y (- Uu)) by (unfold Rpower; apply exp_pos).
    rewrite (Rabs_left (Rpower y (- Uu) - Rpower y c)) by lra.
    rewrite (Rabs_pos_eq T) by lra.
    unfold Rdiv; pose proof (Rinv_0_lt_compat (T * ln y) ltac:(nra)); nra. }
  assert (Hbot : Cmod Ebot <= 2 * Rpower y c / (T * ln y)).
  { unfold Ebot; eapply Rle_trans;
      [ apply (horiz_edge_bound y (- Uu) c (- T) Hy1
                 (Rlt_not_eq (- T) 0 ltac:(lra)) (Rgt_not_eq c (- Uu) ltac:(lra)) HfF4) | ].
    assert (Hlt : Rpower y (- Uu) < Rpower y c)
      by (unfold Rpower; apply exp_increasing, Rmult_lt_compat_r; lra).
    assert (Hpu : 0 < Rpower y (- Uu)) by (unfold Rpower; apply exp_pos).
    rewrite (Rabs_pos_eq (Rpower y c - Rpower y (- Uu))) by lra.
    replace (Rabs (- T)) with T by (rewrite Rabs_Ropp, Rabs_pos_eq; lra).
    unfold Rdiv; pose proof (Rinv_0_lt_compat (T * ln y) ltac:(nra)); nra. }
  assert (Hleft : Cmod Eleft <= 4 * T * Rpower y (- Uu) / Uu).
  { unfold Eleft; eapply Rle_trans;
      [ apply (left_edge_bound y Uu T Hy1 HUu HT HfF3) | apply Req_le; field; lra ]. }
  assert (HEtri : Cmod (Cadd Etop (Cadd Eleft Ebot)) <= Cmod Etop + Cmod Eleft + Cmod Ebot).
  { eapply Rle_trans; [ apply Cmod_triangle | ].
    pose proof (Cmod_triangle Eleft Ebot); lra. }
  (* combine numerically *)
  assert (Hrpc : 0 < Rpower y c) by (apply exp_pos).
  assert (Hrpu : 0 < Rpower y (- Uu)) by (apply exp_pos).
  apply Rle_trans with (/ (2 * PI) * (Cmod Etop + Cmod Eleft + Cmod Ebot)).
  { apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; lra | exact HEtri ]. }
  apply Rle_trans with (/ (2 * PI) * (4 * Rpower y c / (T * ln y) + 4 * T * Rpower y (- Uu) / Uu)).
  { apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; lra | lra ]. }
  (* = 2 Rpower c/(π T ln y) + 2 T Rpower(-Uu)/(π Uu) ≤ RHS + eps *)
  assert (Hfin : / (2 * PI) * (4 * Rpower y c / (T * ln y) + 4 * T * Rpower y (- Uu) / Uu)
                 = 2 * Rpower y c / (PI * T * ln y) + 2 * T * Rpower y (- Uu) / (PI * Uu))
    by (field; repeat split; lra).
  rewrite Hfin.
  apply Rplus_le_compat_l.
  (* 2 T Rpower(-Uu)/(π Uu) ≤ eps *)
  assert (Hpu : 0 < Rpower y (- Uu)) by (unfold Rpower; apply exp_pos).
  apply Rmult_le_reg_r with (PI * Uu); [ nra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra.
  assert (Hde : 2 * T * delta = eps * PI) by (unfold delta; field; lra).
  assert (Hstep1 : 2 * T * Rpower y (- Uu) <= 2 * T * delta) by nra.
  assert (Hstep2 : eps * PI <= eps * (PI * Uu))
    by (apply Rmult_le_compat_l; [ lra | nra ]).
  lra.
Qed.

Print Assumptions perron_gt1.

(* ================================================================= *)
(*  END PerronGt1.v — the truncated Perron bound perron_gt1.             *)
(* ================================================================= *)
