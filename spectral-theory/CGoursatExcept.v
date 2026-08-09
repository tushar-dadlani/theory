(* ================================================================= *)
(*  CGoursatExcept.v  —  Milestone C, brick C4-3: Goursat with one      *)
(*  exceptional point (removable singularity).                          *)
(*                                                                    *)
(*  h continuous everywhere but holomorphic only on U∖{p} still has       *)
(*  vanishing triangle integrals.  Foundation: a general segment split    *)
(*  seg_split_param (Chasles at an arbitrary parameter δ), generalising   *)
(*  CSegInt.seg_concat (δ=½).                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Classical.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegCoV CSegInt
        CPathIntegral CPathFTC CTriangle Holomorphic CHoloCalculus CGoursatML
        CGoursatGeom CGoursatLin CGoursat CGoursatConv CPrimitive CPrimConv.
Open Scope R_scope.

Section SplitParam.
Variables (f : C -> C) (Hf : CcontC f) (a c : C).
Let F := fun u => Cmul (f (seg a c u)) (seg' a c u).

Lemma seg_sp1 : forall delta v, seg a c (delta * v + 0) = seg a (seg a c delta) v.
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.
Lemma seg_sp2 : forall delta v, seg a c ((1 - delta) * v + delta) = seg (seg a c delta) c v.
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.
Lemma scal_sp1 : forall delta, Cmul (RtoC delta) (Cminus c a) = Cminus (seg a c delta) a.
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.
Lemma scal_sp2 : forall delta, Cmul (RtoC (1 - delta)) (Cminus c a) = Cminus c (seg a c delta).
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

Lemma HGsp1 : forall delta,
  Ccont (fun v => Cmul (RtoC delta) (F ((fun w => delta * w + 0) v))).
Proof.
  intro delta; apply Ccont_scal; unfold F, seg'.
  apply Ccont_mul; [ apply Hf, Ccont_seg_comp | apply Ccont_const ].
  intro x; apply derivable_continuous_pt; exists delta; apply dlin.
Qed.
Lemma HGsp2 : forall delta,
  Ccont (fun v => Cmul (RtoC (1 - delta)) (F ((fun w => (1 - delta) * w + delta) v))).
Proof.
  intro delta; apply Ccont_scal; unfold F, seg'.
  apply Ccont_mul; [ apply Hf, Ccont_seg_comp | apply Ccont_const ].
  intro x; apply derivable_continuous_pt; exists (1 - delta); apply dlin.
Qed.

Theorem seg_split_param : forall delta, 0 <= delta <= 1 ->
  seg_int f Hf a c
  = Cadd (seg_int f Hf a (seg a c delta)) (seg_int f Hf (seg a c delta) c).
Proof.
  intros delta [Hd0 Hd1].
  assert (Hcov1 : Cintf (fun v => Cmul (RtoC delta) (F ((fun w => delta * w + 0) v)))
                    (HGsp1 delta) 0 1
                  = Cintf F (seg_ig_cont f Hf a c) 0 delta).
  { transitivity (Cintf F (seg_ig_cont f Hf a c)
                    ((fun w => delta * w + 0) 0) ((fun w => delta * w + 0) 1)).
    - apply (Cintf_cov F (fun w => delta * w + 0) (fun _ => delta) 0 1
              (seg_ig_cont f Hf a c) (HGsp1 delta) ltac:(lra)
              (fun t _ => dlin delta 0 t)
              (fun t _ => continuity_pt_const (fun _ => delta) t (fun _ _ => eq_refl))
              ltac:(intros t Ht; cbv beta; nra)).
    - f_equal; cbv beta; ring. }
  assert (Hcov2 : Cintf (fun v => Cmul (RtoC (1 - delta)) (F ((fun w => (1 - delta) * w + delta) v)))
                    (HGsp2 delta) 0 1
                  = Cintf F (seg_ig_cont f Hf a c) delta 1).
  { transitivity (Cintf F (seg_ig_cont f Hf a c)
                    ((fun w => (1 - delta) * w + delta) 0) ((fun w => (1 - delta) * w + delta) 1)).
    - apply (Cintf_cov F (fun w => (1 - delta) * w + delta) (fun _ => 1 - delta) 0 1
              (seg_ig_cont f Hf a c) (HGsp2 delta) ltac:(lra)
              (fun t _ => dlin (1 - delta) delta t)
              (fun t _ => continuity_pt_const (fun _ => 1 - delta) t (fun _ _ => eq_refl))
              ltac:(intros t Ht; cbv beta; nra)).
    - f_equal; cbv beta; ring. }
  unfold seg_int; fold F.
  rewrite (Cintf_additive F (seg_ig_cont f Hf a c) 0 delta 1).
  rewrite <- Hcov1, <- Hcov2; f_equal.
  - apply Cintf_ext; intro v; cbv beta; unfold F, seg'; rewrite seg_sp1.
    transitivity (Cmul (f (seg a (seg a c delta) v)) (Cmul (RtoC delta) (Cminus c a)));
      [ ring | rewrite scal_sp1; reflexivity ].
  - apply Cintf_ext; intro v; cbv beta; unfold F, seg'; rewrite seg_sp2.
    transitivity (Cmul (f (seg (seg a c delta) c v)) (Cmul (RtoC (1 - delta)) (Cminus c a)));
      [ ring | rewrite scal_sp2; reflexivity ].
Qed.

End SplitParam.

(* ---- cut the corner at p: p_a = seg p a δ, p_b = seg p b δ ---- *)
Lemma tri_corner_split : forall f (Hf : CcontC f) p a b delta, 0 <= delta <= 1 ->
  tri_int f Hf p a b
  = Cadd (tri_int f Hf p (seg p a delta) (seg p b delta))
    (Cadd (tri_int f Hf (seg p a delta) a b)
          (tri_int f Hf (seg p a delta) b (seg p b delta))).
Proof.
  intros f Hf p a b delta H; unfold tri_int.
  rewrite (seg_split_param f Hf p a delta H).
  rewrite (seg_reverse f Hf p b), (seg_split_param f Hf p b delta H).
  rewrite (seg_reverse f Hf p (seg p b delta)).
  rewrite (seg_reverse f Hf (seg p a delta) b).
  rewrite (seg_reverse f Hf (seg p a delta) (seg p b delta)).
  rewrite (seg_reverse f Hf (seg p b delta) b).
  ring.
Qed.

(* ---- signed areas of the shrunk pieces (affine in δ) ---- *)
Lemma sarea_seg1 : forall p a b delta,
  sarea (seg p a delta) a b = (1 - delta) * sarea p a b.
Proof. intros; unfold sarea, cross, seg, Cadd, Cmul, RtoC, Cminus; cbn; ring. Qed.
Lemma sarea_bd : forall p a b delta,
  sarea (seg p a delta) b (seg p b delta) = delta * (1 - delta) * sarea p a b.
Proof. intros; unfold sarea, cross, seg, Cadd, Cmul, RtoC, Cminus; cbn; ring. Qed.
Lemma sarea_pd : forall p a b delta,
  sarea (seg p a delta) p (seg p b delta) = - (delta * delta) * sarea p a b.
Proof. intros; unfold sarea, cross, seg, Cadd, Cmul, RtoC, Cminus; cbn; ring. Qed.

(* ---- p lies outside the two p-avoiding shrunk triangles ---- *)
Lemma p_notin_1 : forall p a b delta, sarea p a b <> 0 -> 0 < delta < 1 ->
  ~ InTri (seg p a delta) a b p.
Proof.
  intros p a b delta Hs [Hd0 Hd1] [al [be [ga [Hal [Hbe [Hga [Hsum Hp]]]]]]].
  assert (Hbary : sarea p a b = al * sarea (seg p a delta) a b)
    by (rewrite <- (sarea_bary_a al be ga (seg p a delta) a b Hsum), <- Hp; reflexivity).
  rewrite (sarea_seg1 p a b delta) in Hbary.
  assert (H0 : (al * (1 - delta) - 1) * sarea p a b = 0).
  { replace ((al * (1 - delta) - 1) * sarea p a b)
       with (al * ((1 - delta) * sarea p a b) - sarea p a b) by ring.
    rewrite <- Hbary; ring. }
  apply Rmult_integral in H0; destruct H0 as [H0 | H0]; [ | contradiction ].
  assert (al <= 1) by lra; nra.
Qed.

Lemma p_notin_2 : forall p a b delta, sarea p a b <> 0 -> 0 < delta < 1 ->
  ~ InTri (seg p a delta) b (seg p b delta) p.
Proof.
  intros p a b delta Hs [Hd0 Hd1] [al [be [ga [Hal [Hbe [Hga [Hsum Hp]]]]]]].
  assert (Hbary : sarea (seg p a delta) p (seg p b delta)
                  = be * sarea (seg p a delta) b (seg p b delta))
    by (rewrite <- (sarea_bary_b al be ga (seg p a delta) b (seg p b delta) Hsum), <- Hp; reflexivity).
  rewrite (sarea_pd p a b delta), (sarea_bd p a b delta) in Hbary.
  assert (H0 : (be * (delta * (1 - delta)) + delta * delta) * sarea p a b = 0).
  { replace ((be * (delta * (1 - delta)) + delta * delta) * sarea p a b)
       with (be * (delta * (1 - delta) * sarea p a b) - (- (delta * delta) * sarea p a b)) by ring.
    rewrite <- Hbary; ring. }
  apply Rmult_integral in H0; destruct H0 as [H0 | H0]; [ | contradiction ].
  assert (0 < delta * delta) by nra.
  assert (0 <= be * (delta * (1 - delta))) by (apply Rmult_le_pos; [ exact Hbe | nra ]).
  lra.
Qed.

(* ---- the corner triangle shrinks: perimeter and edge bounds ---- *)
Lemma perim_corner : forall p a b delta, 0 <= delta ->
  perim p (seg p a delta) (seg p b delta)
  = delta * (Cmod (Cminus a p) + Cmod (Cminus b a) + Cmod (Cminus b p)).
Proof.
  intros p a b delta Hd; unfold perim.
  replace (Cminus (seg p a delta) p) with (Cmul (RtoC delta) (Cminus a p))
    by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
  replace (Cminus (seg p b delta) (seg p a delta)) with (Cmul (RtoC delta) (Cminus b a))
    by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
  replace (Cminus p (seg p b delta)) with (Cmul (RtoC delta) (Cminus p b))
    by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
  rewrite !Cmod_mul, !Cmod_RtoC, (Rabs_pos_eq delta) by exact Hd.
  rewrite (Cmod_Cminus_sym p b); ring.
Qed.

(* each corner-edge point stays within delta·D1 of p *)
Lemma corner_edge : forall p a b delta s, 0 <= delta -> 0 <= s <= 1 ->
  Cmod (Cminus (seg p (seg p a delta) s) p)
    <= delta * (Cmod (Cminus a p) + Cmod (Cminus b a) + Cmod (Cminus b p))
  /\ Cmod (Cminus (seg (seg p a delta) (seg p b delta) s) p)
    <= delta * (Cmod (Cminus a p) + Cmod (Cminus b a) + Cmod (Cminus b p))
  /\ Cmod (Cminus (seg (seg p b delta) p s) p)
    <= delta * (Cmod (Cminus a p) + Cmod (Cminus b a) + Cmod (Cminus b p)).
Proof.
  intros p a b delta s Hd [Hs0 Hs1].
  pose proof (Cmod_nonneg (Cminus a p)); pose proof (Cmod_nonneg (Cminus b a));
    pose proof (Cmod_nonneg (Cminus b p)).
  assert (Hsd : 0 <= s * delta) by nra.
  assert (Hsd' : 0 <= (1 - s) * delta) by nra.
  repeat split.
  - replace (Cminus (seg p (seg p a delta) s) p)
       with (Cmul (RtoC (s * delta)) (Cminus a p))
       by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
    rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq (s * delta) Hsd); nra.
  - replace (Cminus (seg (seg p a delta) (seg p b delta) s) p)
       with (Cadd (Cmul (RtoC delta) (Cminus a p)) (Cmul (RtoC (s * delta)) (Cminus b a)))
       by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite !Cmod_mul, !Cmod_RtoC, (Rabs_pos_eq delta Hd), (Rabs_pos_eq (s * delta) Hsd); nra.
  - replace (Cminus (seg (seg p b delta) p s) p)
       with (Cmul (RtoC ((1 - s) * delta)) (Cminus b p))
       by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
    rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq ((1 - s) * delta) Hsd'); nra.
Qed.

Theorem tri_except_vertex : forall (U : C -> Prop), Convex U ->
  forall h (Hcont : CcontC h) p a b,
  U p -> U a -> U b -> sarea p a b <> 0 ->
  (forall z, U z -> z <> p -> exists d, is_Cderiv h z d) ->
  (exists M eta, 0 < eta /\ forall w, Cmod (Cminus w p) < eta -> Cmod (h w) <= M) ->
  tri_int h Hcont p a b = C0.
Proof.
  intros U HU h Hcont p a b HUp HUa HUb Hs Hhol [M [eta [Heta HM]]].
  set (D1 := Cmod (Cminus a p) + Cmod (Cminus b a) + Cmod (Cminus b p)).
  assert (HD1 : 0 <= D1) by (unfold D1; pose proof (Cmod_nonneg (Cminus a p));
    pose proof (Cmod_nonneg (Cminus b a)); pose proof (Cmod_nonneg (Cminus b p)); lra).
  assert (HM0 : 0 <= M).
  { eapply Rle_trans; [ apply Cmod_nonneg | apply HM ].
    replace (Cminus p p) with C0 by ring; rewrite (proj2 (Cmod0 C0) eq_refl); exact Heta. }
  apply Cmod0.
  apply (le_all_eps (Cmod (tri_int h Hcont p a b)) (2 * M * (D1 + 1)));
    [ apply Cmod_nonneg
    | apply Rmult_le_pos; [ apply Rmult_le_pos; lra | lra ]
    | ].
  intros e He.
  set (delta := Rmin (Rmin e (eta / (D1 + 1))) (/ 2)).
  assert (Hde : delta <= e) by (unfold delta; eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
  assert (Hdeta : delta <= eta / (D1 + 1))
    by (unfold delta; eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
  assert (Hd0 : 0 < delta) by (unfold delta; apply Rmin_pos;
    [ apply Rmin_pos; [ exact He | apply Rdiv_lt_0_compat; lra ] | lra ]).
  assert (Hd1 : delta < 1) by (unfold delta; eapply Rle_lt_trans; [ apply Rmin_r | lra ]).
  assert (HdD : delta * D1 < eta).
  { apply Rle_lt_trans with (eta / (D1 + 1) * D1);
      [ apply Rmult_le_compat_r; lra | ].
    apply Rmult_lt_reg_r with (D1 + 1); [ lra | ].
    replace (eta / (D1 + 1) * D1 * (D1 + 1)) with (eta * D1) by (field; lra); nra. }
  (* the two p-avoiding pieces vanish; only the shrinking corner remains *)
  rewrite (tri_corner_split h Hcont p a b delta ltac:(lra)).
  assert (Hpiece : forall v0 v1 v2 : C, sarea v0 v1 v2 <> 0 -> U v0 -> U v1 -> U v2 ->
    ~ InTri v0 v1 v2 p -> tri_int h Hcont v0 v1 v2 = C0).
  { intros v0 v1 v2 Hnd HUv0 HUv1 HUv2 Hnp.
    apply (tri_int_conv h Hcont v0 v1 v2 Hnd); intros z Hz; apply Hhol.
    - exact (convex_hull_subset U HU v0 v1 v2 HUv0 HUv1 HUv2 z Hz).
    - intro Heq; subst z; exact (Hnp Hz). }
  assert (HUpa : U (seg p a delta)) by (apply HU; [ exact HUp | exact HUa | lra ]).
  assert (HUpb : U (seg p b delta)) by (apply HU; [ exact HUp | exact HUb | lra ]).
  rewrite (Hpiece (seg p a delta) a b
            ltac:(rewrite sarea_seg1; apply Rmult_integral_contrapositive_currified; [ lra | exact Hs ])
            HUpa HUa HUb (p_notin_1 p a b delta Hs ltac:(lra))).
  rewrite (Hpiece (seg p a delta) b (seg p b delta)
            ltac:(rewrite sarea_bd; apply Rmult_integral_contrapositive_currified;
                  [ nra | exact Hs ])
            HUpa HUb HUpb (p_notin_2 p a b delta Hs ltac:(lra))).
  replace (Cadd (tri_int h Hcont p (seg p a delta) (seg p b delta)) (Cadd C0 C0))
     with (tri_int h Hcont p (seg p a delta) (seg p b delta)) by ring.
  (* ML on the corner: ≤ 2 M perim = 2 M δ D1 ≤ 2 M (D1+1) e *)
  eapply Rle_trans.
  { apply (tri_int_ML h Hcont p (seg p a delta) (seg p b delta) M).
    - intros s Hs'; apply HM; eapply Rle_lt_trans;
        [ apply (proj1 (corner_edge p a b delta s ltac:(lra) Hs')) | exact HdD ].
    - intros s Hs'; apply HM; eapply Rle_lt_trans;
        [ apply (proj1 (proj2 (corner_edge p a b delta s ltac:(lra) Hs'))) | exact HdD ].
    - intros s Hs'; apply HM; eapply Rle_lt_trans;
        [ apply (proj2 (proj2 (corner_edge p a b delta s ltac:(lra) Hs'))) | exact HdD ]. }
  rewrite (perim_corner p a b delta ltac:(lra)); fold D1.
  replace (2 * M * (D1 + 1) * e) with (2 * M * ((D1 + 1) * e)) by ring.
  apply Rmult_le_compat_l; [ lra | ].
  apply Rle_trans with (delta * (D1 + 1)); [ apply Rmult_le_compat_l; lra | ].
  rewrite (Rmult_comm delta (D1 + 1)); apply Rmult_le_compat_l; lra.
Qed.

(* ================================================================= *)
(*  Degenerate (collinear) triangles vanish for merely-continuous h.     *)
(* ================================================================= *)

(* a collinear b lies on the line a—c: b = seg a c t for some real t *)
Lemma extract_t : forall a b c, a <> c -> sarea a b c = 0 -> exists t, b = seg a c t.
Proof.
  intros a b c Hac Hs; unfold sarea, cross, Cminus in Hs; cbn in Hs.
  destruct (Req_dec (Re c - Re a) 0) as [Hr | Hr].
  - assert (Him : Im c - Im a <> 0) by (intro Hi; apply Hac; apply Ceq; lra).
    assert (Hreb : Re b = Re a).
    { assert (H : (Re b - Re a) * (Im c - Im a) = 0) by nra.
      apply Rmult_integral in H; destruct H; [ lra | contradiction ]. }
    exists ((Im b - Im a) / (Im c - Im a)).
    apply Ceq; unfold seg, Cadd, Cmul, RtoC, Cminus; cbn; [ rewrite Hr; lra | field; exact Him ].
  - exists ((Re b - Re a) / (Re c - Re a)).
    apply Ceq; unfold seg, Cadd, Cmul, RtoC, Cminus; cbn; [ field; exact Hr | ].
    apply (Rmult_eq_reg_r (Re c - Re a)); [ field_simplify; try exact Hr; nra | exact Hr ].
Qed.

(* general collinear Chasles: seg_int a c = seg_int a b + seg_int b c *)
Lemma seg_chasles_collinear : forall f (Hf : CcontC f) a b c,
  a <> c -> sarea a b c = 0 ->
  seg_int f Hf a c = Cadd (seg_int f Hf a b) (seg_int f Hf b c).
Proof.
  intros f Hf a b c Hac Hs; destruct (extract_t a b c Hac Hs) as [t Ht].
  destruct (Rlt_le_dec t 0) as [Ht0 | Ht0].
  - (* t < 0 : a is between b and c *)
    set (s := - t / (1 - t)).
    assert (Hs01 : 0 <= s <= 1) by (unfold s; split;
      [ apply Rle_mult_inv_pos; lra | apply Rmult_le_reg_r with (1 - t); [ lra | ];
        replace (- t / (1 - t) * (1 - t)) with (- t) by (field; lra); lra ]).
    assert (Hba : seg b c s = a)
      by (rewrite Ht; unfold s, seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; field; lra).
    pose proof (seg_split_param f Hf b c s Hs01) as HH; rewrite Hba in HH.
    rewrite (seg_reverse f Hf a b) in HH; ring [HH].
  - destruct (Rle_lt_dec t 1) as [Ht1 | Ht1].
    + (* 0 <= t <= 1 : b between a and c *)
      rewrite Ht; apply (seg_split_param f Hf a c t); lra.
    + (* t > 1 : c is between a and b *)
      set (s := / t).
      assert (Hs01 : 0 <= s <= 1) by (unfold s; split;
        [ left; apply Rinv_0_lt_compat; lra
        | rewrite <- Rinv_1; apply Rinv_le_contravar; lra ]).
      assert (Hca : seg a b s = c)
        by (rewrite Ht; unfold s, seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; field; lra).
      pose proof (seg_split_param f Hf a b s Hs01) as HH; rewrite Hca in HH.
      rewrite (seg_reverse f Hf b c) in HH; ring [HH].
Qed.

Lemma tri_int_collinear : forall f (Hf : CcontC f) a b c,
  sarea a b c = 0 -> tri_int f Hf a b c = C0.
Proof.
  intros f Hf a b c Hs; destruct (classic (a = c)) as [-> | Hac].
  - apply tri_int_deg20.
  - unfold tri_int; rewrite (seg_reverse f Hf a c).
    pose proof (seg_chasles_collinear f Hf a b c Hac Hs) as HC; ring [HC].
Qed.

(* ---- Goursat with one exceptional point (anywhere) ---- *)
Theorem tri_int_except : forall (U : C -> Prop), Convex U ->
  forall h (Hcont : CcontC h) p v0 v1 v2,
  U p -> U v0 -> U v1 -> U v2 ->
  (forall z, U z -> z <> p -> exists d, is_Cderiv h z d) ->
  (exists M eta, 0 < eta /\ forall w, Cmod (Cminus w p) < eta -> Cmod (h w) <= M) ->
  tri_int h Hcont v0 v1 v2 = C0.
Proof.
  intros U HU h Hcont p v0 v1 v2 HUp HU0 HU1 HU2 Hhol Hbd.
  rewrite (tri_split_vertex h Hcont p v0 v1 v2).
  assert (Hsub : forall a b, U a -> U b -> tri_int h Hcont p a b = C0).
  { intros a b HUa HUb; destruct (Req_dec (sarea p a b) 0) as [Hd | Hnd].
    - apply tri_int_collinear; exact Hd.
    - apply (tri_except_vertex U HU h Hcont p a b HUp HUa HUb Hnd Hhol Hbd). }
  rewrite (Hsub v0 v1 HU0 HU1), (Hsub v1 v2 HU1 HU2), (Hsub v2 v0 HU2 HU0); ring.
Qed.

(* ================================================================= *)
(*  The exceptional-point primitive and loop-zero (mirrors ConvexPrim). *)
(* ================================================================= *)
Section ExceptPrim.
Variable U : C -> Prop.
Hypothesis HU : Convex U.
Hypothesis HO : Open U.
Variable F : C -> C.
Variable HF : CcontC F.
Variable p : C.
Hypothesis HUp : U p.
Hypothesis HFhol : forall z, U z -> z <> p -> exists d, is_Cderiv F z d.
Hypothesis HFbd : exists M eta, 0 < eta /\ forall w, Cmod (Cminus w p) < eta -> Cmod (F w) <= M.
Hypothesis HFcont : forall z, U z -> forall eps, 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps.
Variable z0 : C.
Hypothesis HUz0 : U z0.

Definition PrimE (z : C) : C := seg_int F HF z0 z.

Lemma PrimE_diff : forall z k, U z -> U (Cadd z k) ->
  seg_int F HF z (Cadd z k) = Cminus (PrimE (Cadd z k)) (PrimE z).
Proof.
  intros z k HUz HUzk; unfold PrimE.
  pose proof (tri_int_except U HU F HF p z0 z (Cadd z k) HUp HUz0 HUz HUzk HFhol HFbd) as HG.
  unfold tri_int in HG; rewrite (seg_reverse F HF z0 (Cadd z k)) in HG.
  assert (HR := f_equal Re HG); assert (HI := f_equal Im HG).
  apply Ceq; unfold Cadd, Copp, Cminus, C0 in *; cbn in *; lra.
Qed.

Theorem PrimE_deriv : forall z, U z -> is_Cderiv PrimE z (F z).
Proof.
  intros z HUz eps Heps.
  destruct (HFcont z HUz (eps / 2) ltac:(lra)) as [del1 [Hdel1 Hc]].
  destruct (HO z HUz) as [r [Hr Hball]].
  exists (Rmin del1 r); split; [ apply Rmin_pos; lra | ]; intros k Hk.
  assert (HUzk : U (Cadd z k)).
  { apply Hball; replace (Cminus (Cadd z k) z) with k by ring;
      eapply Rlt_le_trans; [ exact Hk | apply Rmin_r ]. }
  rewrite <- (PrimE_diff z k HUz HUzk).
  assert (HFk : Cmul (F z) k = seg_int (fun _ => F z) (CcontC_const (F z)) z (Cadd z k))
    by (rewrite seg_int_const; replace (Cminus (Cadd z k) z) with k by ring; reflexivity).
  rewrite HFk.
  rewrite <- (seg_int_sub F (fun _ => F z) HF (CcontC_const (F z))
              (CcontC_add F (fun _ => Copp (F z)) HF (CcontC_const (Copp (F z))))
              z (Cadd z k)).
  eapply Rle_trans.
  { apply (seg_int_ML (fun w => Cminus (F w) (F z)) _ z (Cadd z k) (eps / 2)).
    intros s Hs.
    assert (Hws : Cmod (Cminus (seg z (Cadd z k) s) z) <= Cmod k).
    { replace (Cminus (seg z (Cadd z k) s) z) with (Cmul (RtoC s) k)
        by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
      rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq s) by lra.
      apply Rle_trans with (1 * Cmod k);
        [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ] | lra ]. }
    apply Rlt_le, Hc; eapply Rle_lt_trans;
      [ exact Hws | eapply Rlt_le_trans; [ exact Hk | apply Rmin_l ] ]. }
  replace (Cminus (Cadd z k) z) with k by ring.
  apply Req_le; lra.
Qed.

Theorem pathint_loop_except : forall (gam gam' : R -> C)
  (Hf : Ccont (fun u => Cmul (F (gam u)) (gam' u))) a b,
  a <= b -> gam a = gam b ->
  (forall s, a <= s <= b -> U (gam s)) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Re (gam r)) s (Re (gam' s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Im (gam r)) s (Im (gam' s))) ->
  pathint gam gam' F Hf a b = C0.
Proof.
  intros gam gam' Hf a b Hab Hloop HUgam HgR HgI.
  apply (pathint_primitive_loop PrimE F gam gam' Hf a b Hab Hloop);
    [ intros s Hs; apply PrimE_deriv; apply HUgam; exact Hs | exact HgR | exact HgI ].
Qed.

End ExceptPrim.

Print Assumptions tri_int_except.
Print Assumptions pathint_loop_except.

(* ================================================================= *)
(*  END CGoursatExcept.v  —  Goursat + primitive with one bad point.    *)
(* ================================================================= *)
