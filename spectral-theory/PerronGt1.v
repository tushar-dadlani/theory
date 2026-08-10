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
        PerronEdge CTruncCauchy.
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

Print Assumptions left_edge_bound.

(* ================================================================= *)
(*  (checkpoint) horizontal + left edge bounds in place; perron_gt1 next.*)
(* ================================================================= *)
