(* ================================================================= *)
(*  CPrimConv.v  —  Milestone C, brick C4-2: primitive on a convex     *)
(*  region ⇒ loop integrals vanish.                                    *)
(*                                                                    *)
(*  For F holomorphic on an open convex U, the base-point segment       *)
(*  integral Prim z := seg_int F z0 z is a primitive on U (via region   *)
(*  Goursat on the triangle z0,z,z+k), so pathint F = 0 over any closed  *)
(*  C¹ loop in U.  The one wrinkle is the collinear triangle (z0,z,z+k), *)
(*  handled by splitting through an off-line vertex w ∈ U.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Classical.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CPathIntegral
        CPathFTC CTriangle Holomorphic CHoloCalculus CGoursatFTC CGoursatML
        CGoursatLin CPrimitive CGoursatConv.
Open Scope R_scope.

(* ---- convex sets contain the convex hull of their points ---- *)
Definition Convex (U : C -> Prop) : Prop :=
  forall a b, U a -> U b -> forall s, 0 <= s <= 1 -> U (seg a b s).

Lemma convex_hull_subset : forall U, Convex U ->
  forall v0 v1 v2, U v0 -> U v1 -> U v2 ->
  forall z, InTri v0 v1 v2 z -> U z.
Proof.
  intros U HU v0 v1 v2 H0 H1 H2 z [a [b [c [Ha [Hb [Hc [Hsum ->]]]]]]].
  destruct (Req_dec a 1) as [Ha1 | Ha1].
  - assert (Hb0 : b = 0) by lra; assert (Hc0 : c = 0) by lra; subst a b c.
    replace (combo 1 0 0 v0 v1 v2) with v0;
      [ exact H0 | unfold combo, Cmul, RtoC, Cadd; apply Ceq; cbn; ring ].
  - assert (Hlt : 0 < 1 - a) by lra.
    set (w := seg v1 v2 (c / (1 - a))).
    assert (HUw : U w)
      by (apply HU; [ exact H1 | exact H2 | split;
            [ unfold Rdiv; apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ] | ] ];
          apply Rmult_le_reg_r with (1 - a); [ lra | ];
          replace (c / (1 - a) * (1 - a)) with c by (field; lra); lra).
    replace (combo a b c v0 v1 v2) with (seg v0 w (1 - a)).
    + apply HU; [ exact H0 | exact HUw | split; lra ].
    + assert (Hbeq : b = 1 - a - c) by lra; subst b;
        unfold w, seg, combo, Cmul, RtoC, Cadd, Cminus; apply Ceq; cbn; field; lra.
Qed.

(* ---- degenerate / coincident-vertex triangle integrals ---- *)
Lemma seg_int_self : forall f (Hf : CcontC f) a, seg_int f Hf a a = C0.
Proof.
  intros f Hf a; unfold seg_int.
  transitivity (Cintf (fun _ => C0) (Ccont_const C0) 0 1).
  - apply Cintf_ext; intro u; unfold seg'; replace (Cminus a a) with C0 by ring; ring.
  - apply Cintf_const01.
Qed.

Lemma tri_int_deg01 : forall f (Hf : CcontC f) a c, tri_int f Hf a a c = C0.
Proof.
  intros f Hf a c; unfold tri_int; rewrite (seg_int_self f Hf a).
  rewrite (seg_reverse f Hf c a); ring.
Qed.
Lemma tri_int_deg12 : forall f (Hf : CcontC f) a b, tri_int f Hf a b b = C0.
Proof.
  intros f Hf a b; unfold tri_int; rewrite (seg_int_self f Hf b).
  rewrite (seg_reverse f Hf b a); ring.
Qed.
Lemma tri_int_deg20 : forall f (Hf : CcontC f) a b, tri_int f Hf a b a = C0.
Proof.
  intros f Hf a b; unfold tri_int; rewrite (seg_int_self f Hf a).
  rewrite (seg_reverse f Hf b a); ring.
Qed.

(* ---- split a triangle through an arbitrary vertex w (edges cancel) ---- *)
Lemma tri_split_vertex : forall f (Hf : CcontC f) w a b c,
  tri_int f Hf a b c
  = Cadd (tri_int f Hf w a b) (Cadd (tri_int f Hf w b c) (tri_int f Hf w c a)).
Proof.
  intros f Hf w a b c; unfold tri_int.
  rewrite (seg_reverse f Hf a w), (seg_reverse f Hf b w), (seg_reverse f Hf c w); ring.
Qed.

(* ---- signed-area algebra for the degenerate (collinear) split ---- *)
Definition dotp (a b : C) : R := Re a * Re b + Im a * Im b.

Lemma lagrange : forall a b, (cross a b) ^ 2 + (dotp a b) ^ 2 = Cnorm2 a * Cnorm2 b.
Proof. intros; unfold cross, dotp, Cnorm2; ring. Qed.

Lemma Cnorm2_pos : forall a, a <> C0 -> 0 < Cnorm2 a.
Proof.
  intros a Ha; assert (0 <= Cnorm2 a) by (unfold Cnorm2; nra).
  destruct (Req_dec (Cnorm2 a) 0) as [E | ]; [ | lra ].
  exfalso; apply Ha; unfold Cnorm2 in E; apply Ceq; cbn; nra.
Qed.

Lemma Cmod_pos_ne0 : forall c, c <> C0 -> 0 < Cmod c.
Proof. intros c H; unfold Cmod; apply sqrt_lt_R0; apply Cnorm2_pos; exact H. Qed.

Lemma dotp_ne0 : forall a b, cross a b = 0 -> a <> C0 -> b <> C0 -> dotp a b <> 0.
Proof.
  intros a b Hc Ha Hb Hd; pose proof (lagrange a b) as HL;
    pose proof (Cnorm2_pos a Ha); pose proof (Cnorm2_pos b Hb); rewrite Hc, Hd in HL; nra.
Qed.

Lemma Cmod_Ci : Cmod Ci = 1.
Proof. unfold Cmod; replace (Cnorm2 Ci) with 1 by (unfold Cnorm2, Ci; cbn; ring); apply sqrt_1. Qed.

Lemma Cminus_eq0 : forall a b, Cminus a b = C0 -> a = b.
Proof. intros a b H; apply Ceq; [ assert (Hr := f_equal Re H) | assert (Hi := f_equal Im H) ];
         unfold Cminus, C0 in *; cbn in *; lra. Qed.

Lemma Cminus_ne0 : forall a b, a <> b -> Cminus a b <> C0.
Proof. intros a b H Hc; apply H; apply Cminus_eq0; exact Hc. Qed.

Definition Open (U : C -> Prop) : Prop :=
  forall z, U z -> exists r, 0 < r /\ forall w, Cmod (Cminus w z) < r -> U w.

(* the off-line apex w = v0 + lam·i·(v2−v0), and its three sub-triangle areas *)
Section WSplit.
Variables (v0 v1 v2 : C) (lam : R).
Let d := Cminus v2 v0.
Let w := Cadd v0 (Cmul (RtoC lam) (Cmul Ci d)).

Lemma sarea_w01 : sarea w v0 v1 = lam * dotp (Cminus v2 v0) (Cminus v1 v0).
Proof. unfold sarea, cross, dotp, w, d, Cadd, Cmul, RtoC, Ci, Cminus; cbn; ring. Qed.
Lemma sarea_w20 : sarea w v2 v0 = - (lam * Cnorm2 (Cminus v2 v0)).
Proof. unfold sarea, cross, w, d, Cnorm2, Cadd, Cmul, RtoC, Ci, Cminus; cbn; ring. Qed.
Lemma sarea_w12 : sarea v0 v1 v2 = 0 ->
  sarea w v1 v2 = lam * dotp (Cminus v2 v1) (Cminus v2 v0).
Proof.
  intro H; unfold sarea, cross in H |- *; unfold dotp, w, d, Cadd, Cmul, RtoC, Ci, Cminus in *;
    cbn in *; nra.
Qed.
End WSplit.

(* ---- region Goursat for ALL triangles in an open convex U ---- *)
Lemma tri_int_conv_all : forall (U : C -> Prop), Convex U -> Open U ->
  forall h (Hcont : CcontC h) v0 v1 v2, U v0 -> U v1 -> U v2 ->
  (forall z, U z -> exists d, is_Cderiv h z d) ->
  tri_int h Hcont v0 v1 v2 = C0.
Proof.
  intros U HU HO h Hcont v0 v1 v2 HU0 HU1 HU2 Hhol.
  destruct (Req_dec (sarea v0 v1 v2) 0) as [Hdeg | Hnondeg].
  2:{ apply (tri_int_conv h Hcont v0 v1 v2 Hnondeg).
      intros z Hz; apply Hhol; exact (convex_hull_subset U HU v0 v1 v2 HU0 HU1 HU2 z Hz). }
  destruct (classic (v0 = v1)) as [E|N01]; [ subst; apply tri_int_deg01 | ].
  destruct (classic (v1 = v2)) as [E|N12]; [ subst; apply tri_int_deg12 | ].
  destruct (classic (v0 = v2)) as [E|N02]; [ subst; apply tri_int_deg20 | ].
  (* all distinct + collinear: split through an off-line apex w ∈ U *)
  assert (Hd : Cminus v2 v0 <> C0) by (apply Cminus_ne0; auto).
  assert (Hdm : 0 < Cmod (Cminus v2 v0)) by (apply Cmod_pos_ne0; exact Hd).
  destruct (HO v0 HU0) as [r [Hr Hball]].
  set (lam := r / 2 / Cmod (Cminus v2 v0)).
  assert (Hlam : 0 < lam) by (unfold lam; apply Rdiv_lt_0_compat; [ lra | exact Hdm ]).
  set (w := Cadd v0 (Cmul (RtoC lam) (Cmul Ci (Cminus v2 v0)))).
  assert (HUw : U w).
  { apply Hball; unfold w.
    replace (Cminus (Cadd v0 (Cmul (RtoC lam) (Cmul Ci (Cminus v2 v0)))) v0)
       with (Cmul (RtoC lam) (Cmul Ci (Cminus v2 v0))) by ring.
    rewrite Cmod_mul, Cmod_RtoC, Cmod_mul, Cmod_Ci, (Rabs_pos_eq lam) by lra.
    unfold lam; field_simplify; [ lra | apply Rgt_not_eq; exact Hdm ]. }
  assert (Hsub : forall a b, U a -> U b -> forall z, InTri w a b z -> exists dd, is_Cderiv h z dd)
    by (intros a b Ha Hb z Hz; apply Hhol;
        exact (convex_hull_subset U HU w a b HUw Ha Hb z Hz)).
  rewrite (tri_split_vertex h Hcont w v0 v1 v2).
  rewrite (tri_int_conv h Hcont w v0 v1
            ltac:(unfold w; rewrite (sarea_w01 v0 v1 v2 lam); apply Rmult_integral_contrapositive_currified;
                  [ lra | apply dotp_ne0;
                    [ replace (cross (Cminus v2 v0) (Cminus v1 v0)) with (- sarea v0 v1 v2)
                        by (unfold sarea, cross, Cminus; cbn; ring); rewrite Hdeg; ring
                    | exact Hd | apply Cminus_ne0; auto ] ])
            (Hsub v0 v1 HU0 HU1)).
  rewrite (tri_int_conv h Hcont w v1 v2
            ltac:(unfold w; rewrite (sarea_w12 v0 v1 v2 lam Hdeg);
                  apply Rmult_integral_contrapositive_currified;
                  [ lra | apply dotp_ne0;
                    [ replace (cross (Cminus v2 v1) (Cminus v2 v0)) with (- sarea v0 v1 v2)
                        by (unfold sarea, cross, Cminus; cbn; ring); rewrite Hdeg; ring
                    | apply Cminus_ne0; auto | apply Cminus_ne0; auto ] ])
            (Hsub v1 v2 HU1 HU2)).
  rewrite (tri_int_conv h Hcont w v2 v0
            ltac:(unfold w; rewrite (sarea_w20 v0 v2 lam);
                  apply Ropp_neq_0_compat; apply Rmult_integral_contrapositive_currified;
                  [ lra | apply Rgt_not_eq; apply Cnorm2_pos; exact Hd ])
            (Hsub v2 v0 HU2 HU0)).
  ring.
Qed.

(* ================================================================= *)
(*  The convex-region primitive and loop-zero.                          *)
(* ================================================================= *)
Section ConvexPrim.
Variable U : C -> Prop.
Hypothesis HU : Convex U.
Hypothesis HO : Open U.
Variable F : C -> C.
Variable HF : CcontC F.
Hypothesis HFhol : forall z, U z -> exists d, is_Cderiv F z d.
Variable z0 : C.
Hypothesis HUz0 : U z0.

Definition PrimC (z : C) : C := seg_int F HF z0 z.

Lemma Fcont_pt_conv : forall z, U z -> forall eps, 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps.
Proof.
  intros z HUz eps Heps; destruct (HFhol z HUz) as [d Hd].
  destruct (is_Cderiv_cont F z d Hd eps Heps) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ]; intros w Hw.
  replace (Cminus (F w) (F z)) with (Cminus (F (Cadd z (Cminus w z))) (F z))
    by (replace (Cadd z (Cminus w z)) with w by ring; reflexivity).
  apply Hc; exact Hw.
Qed.

Lemma PrimC_diff : forall z k, U z -> U (Cadd z k) ->
  seg_int F HF z (Cadd z k) = Cminus (PrimC (Cadd z k)) (PrimC z).
Proof.
  intros z k HUz HUzk; unfold PrimC.
  pose proof (tri_int_conv_all U HU HO F HF z0 z (Cadd z k) HUz0 HUz HUzk HFhol) as HG.
  unfold tri_int in HG; rewrite (seg_reverse F HF z0 (Cadd z k)) in HG.
  assert (HR := f_equal Re HG); assert (HI := f_equal Im HG).
  apply Ceq; unfold Cadd, Copp, Cminus, C0 in *; cbn in *; lra.
Qed.

Theorem PrimC_deriv : forall z, U z -> is_Cderiv PrimC z (F z).
Proof.
  intros z HUz eps Heps.
  destruct (Fcont_pt_conv z HUz (eps / 2) ltac:(lra)) as [del1 [Hdel1 Hc]].
  destruct (HO z HUz) as [r [Hr Hball]].
  exists (Rmin del1 r); split; [ apply Rmin_pos; lra | ]; intros k Hk.
  assert (HUzk : U (Cadd z k)).
  { apply Hball; replace (Cminus (Cadd z k) z) with k by ring;
      eapply Rlt_le_trans; [ exact Hk | apply Rmin_r ]. }
  rewrite <- (PrimC_diff z k HUz HUzk).
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

Theorem pathint_loop_conv : forall (gam gam' : R -> C)
  (Hf : Ccont (fun u => Cmul (F (gam u)) (gam' u))) a b,
  a <= b -> gam a = gam b ->
  (forall s, a <= s <= b -> U (gam s)) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Re (gam r)) s (Re (gam' s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Im (gam r)) s (Im (gam' s))) ->
  pathint gam gam' F Hf a b = C0.
Proof.
  intros gam gam' Hf a b Hab Hloop HUgam HgR HgI.
  apply (pathint_primitive_loop PrimC F gam gam' Hf a b Hab Hloop);
    [ intros s Hs; apply PrimC_deriv; apply HUgam; exact Hs | exact HgR | exact HgI ].
Qed.

End ConvexPrim.

Print Assumptions PrimC_deriv.
Print Assumptions pathint_loop_conv.

(* ================================================================= *)
(*  END CPrimConv.v  —  primitive on a convex region ⇒ loop zero.       *)
(* ================================================================= *)
