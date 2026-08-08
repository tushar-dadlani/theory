(* ================================================================= *)
(*  CGoursatConv.v  —  Milestone C, brick C4-1: region Goursat.         *)
(*                                                                    *)
(*  Goursat's theorem for h globally continuous but holomorphic only on  *)
(*  the CLOSED triangle (v0,v1,v2).  The nested-triangle argument of      *)
(*  CGoursat is reused; the ONE new obligation is that the nested limit   *)
(*  zc lies in the closed triangle.  We characterise the closed triangle  *)
(*  by signed-area (barycentric) SIGN conditions — each a CLOSED          *)
(*  condition (continuous ≥ 0), so preserved under the limit V0(seqT n)   *)
(*  → zc with NO compactness/choice.  (Non-degenerate triangle.)          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CSegInt CPathIntegral CTriangle
        Holomorphic CGoursatML CGoursatGeom CGoursatLin CGoursatAffine
        CGeomCauchy CGoursat.
Open Scope R_scope.

(* ---- tiny field helpers ---- *)
Lemma RtoC_neq0 : forall r, r <> 0 -> RtoC r <> C0.
Proof. intros r Hr Hc; apply Hr; change 0 with (Re C0); rewrite <- Hc; reflexivity. Qed.

Lemma Cmul_cancel_l : forall a b c, a <> C0 -> Cmul a b = Cmul a c -> b = c.
Proof.
  intros a b c Ha H.
  transitivity (Cmul (Cinv a) (Cmul a b)).
  - transitivity (Cmul (Cmul (Cinv a) a) b); [ rewrite (Cinv_l a Ha); ring | ring ].
  - rewrite H; transitivity (Cmul (Cmul (Cinv a) a) c); [ ring | rewrite (Cinv_l a Ha); ring ].
Qed.

Lemma div_sign : forall x s, s <> 0 -> 0 <= x * s -> 0 <= x / s.
Proof.
  intros x s Hs H; apply Rmult_le_reg_r with (s * s); [ nra | ].
  rewrite Rmult_0_l; replace (x / s * (s * s)) with (x * s) by (field; exact Hs); exact H.
Qed.

(* ---- signed area (2D cross product), convex combinations ---- *)
Definition cross (a b : C) : R := Re a * Im b - Im a * Re b.
Definition sarea (p q r : C) : R := cross (Cminus q p) (Cminus r p).
Definition combo (a b c : R) (v0 v1 v2 : C) : C :=
  Cadd (Cmul (RtoC a) v0) (Cadd (Cmul (RtoC b) v1) (Cmul (RtoC c) v2)).
Definition InTri (v0 v1 v2 z : C) : Prop :=
  exists a b c, 0 <= a /\ 0 <= b /\ 0 <= c /\ a + b + c = 1 /\ z = combo a b c v0 v1 v2.

Lemma combo_scal : forall k a b c v0 v1 v2,
  Cmul (RtoC k) (combo a b c v0 v1 v2) = combo (k * a) (k * b) (k * c) v0 v1 v2.
Proof. intros; unfold combo, Cmul, RtoC, Cadd; apply Ceq; cbn; ring. Qed.

(* barycentric numerators of a convex combo (affine ⇒ uses a+b+c=1) *)
Lemma sarea_bary_a : forall a b c v0 v1 v2, a + b + c = 1 ->
  sarea (combo a b c v0 v1 v2) v1 v2 = a * sarea v0 v1 v2.
Proof.
  intros a b c v0 v1 v2 H; unfold sarea, cross, combo, Cadd, Cmul, RtoC, Cminus; cbn.
  replace c with (1 - a - b) by lra; ring.
Qed.
Lemma sarea_bary_b : forall a b c v0 v1 v2, a + b + c = 1 ->
  sarea v0 (combo a b c v0 v1 v2) v2 = b * sarea v0 v1 v2.
Proof.
  intros a b c v0 v1 v2 H; unfold sarea, cross, combo, Cadd, Cmul, RtoC, Cminus; cbn.
  replace c with (1 - a - b) by lra; ring.
Qed.
Lemma sarea_bary_c : forall a b c v0 v1 v2, a + b + c = 1 ->
  sarea v0 v1 (combo a b c v0 v1 v2) = c * sarea v0 v1 v2.
Proof.
  intros a b c v0 v1 v2 H; unfold sarea, cross, combo, Cadd, Cmul, RtoC, Cminus; cbn.
  replace c with (1 - a - b) by lra; ring.
Qed.

Lemma sarea_sum : forall v0 v1 v2 z,
  sarea z v1 v2 + sarea v0 z v2 + sarea v0 v1 z = sarea v0 v1 v2.
Proof. intros; unfold sarea, cross, Cminus; cbn; ring. Qed.
Lemma sarea_recon : forall v0 v1 v2 z,
  Cmul (RtoC (sarea v0 v1 v2)) z
  = combo (sarea z v1 v2) (sarea v0 z v2) (sarea v0 v1 z) v0 v1 v2.
Proof. intros; unfold sarea, cross, combo, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

(* ---- sign characterization of the closed (non-degenerate) triangle ---- *)
Lemma InTri_sign_fwd : forall v0 v1 v2 z, InTri v0 v1 v2 z ->
  0 <= sarea z v1 v2 * sarea v0 v1 v2
  /\ 0 <= sarea v0 z v2 * sarea v0 v1 v2
  /\ 0 <= sarea v0 v1 z * sarea v0 v1 v2.
Proof.
  intros v0 v1 v2 z [a [b [c [Ha [Hb [Hc [Hsum ->]]]]]]].
  rewrite (sarea_bary_a a b c v0 v1 v2 Hsum), (sarea_bary_b a b c v0 v1 v2 Hsum),
          (sarea_bary_c a b c v0 v1 v2 Hsum).
  repeat split; nra.
Qed.

Lemma InTri_sign_bwd : forall v0 v1 v2 z, sarea v0 v1 v2 <> 0 ->
  0 <= sarea z v1 v2 * sarea v0 v1 v2 ->
  0 <= sarea v0 z v2 * sarea v0 v1 v2 ->
  0 <= sarea v0 v1 z * sarea v0 v1 v2 ->
  InTri v0 v1 v2 z.
Proof.
  intros v0 v1 v2 z Hs H1 H2 H3.
  exists (sarea z v1 v2 / sarea v0 v1 v2), (sarea v0 z v2 / sarea v0 v1 v2),
         (sarea v0 v1 z / sarea v0 v1 v2).
  repeat split; try (apply div_sign; assumption).
  - replace (sarea z v1 v2 / sarea v0 v1 v2 + sarea v0 z v2 / sarea v0 v1 v2
             + sarea v0 v1 z / sarea v0 v1 v2)
       with ((sarea z v1 v2 + sarea v0 z v2 + sarea v0 v1 z) / sarea v0 v1 v2)
       by (field; exact Hs).
    rewrite (sarea_sum v0 v1 v2 z); field; exact Hs.
  - apply (Cmul_cancel_l (RtoC (sarea v0 v1 v2))); [ apply RtoC_neq0; exact Hs | ].
    rewrite combo_scal.
    replace (sarea v0 v1 v2 * (sarea z v1 v2 / sarea v0 v1 v2)) with (sarea z v1 v2)
      by (field; exact Hs).
    replace (sarea v0 v1 v2 * (sarea v0 z v2 / sarea v0 v1 v2)) with (sarea v0 z v2)
      by (field; exact Hs).
    replace (sarea v0 v1 v2 * (sarea v0 v1 z / sarea v0 v1 v2)) with (sarea v0 v1 z)
      by (field; exact Hs).
    exact (sarea_recon v0 v1 v2 z).
Qed.

(* ---- convex-combination closure (vertices, midpoints) ---- *)
Lemma vertex0_in_tri : forall v0 v1 v2, InTri v0 v1 v2 v0.
Proof. intros; exists 1, 0, 0; repeat split; try lra; unfold combo; apply Ceq; cbn; ring. Qed.
Lemma vertex1_in_tri : forall v0 v1 v2, InTri v0 v1 v2 v1.
Proof. intros; exists 0, 1, 0; repeat split; try lra; unfold combo; apply Ceq; cbn; ring. Qed.
Lemma vertex2_in_tri : forall v0 v1 v2, InTri v0 v1 v2 v2.
Proof. intros; exists 0, 0, 1; repeat split; try lra; unfold combo; apply Ceq; cbn; ring. Qed.

Lemma midpoint_in_tri : forall v0 v1 v2 a b,
  InTri v0 v1 v2 a -> InTri v0 v1 v2 b -> InTri v0 v1 v2 (mid a b).
Proof.
  intros v0 v1 v2 a b [pa [qa [ra [Ha1 [Ha2 [Ha3 [Hasum ->]]]]]]]
                     [pb [qb [rb [Hb1 [Hb2 [Hb3 [Hbsum ->]]]]]]].
  exists ((pa + pb) / 2), ((qa + qb) / 2), ((ra + rb) / 2); repeat split; try lra.
  unfold mid, combo, Cmul, RtoC, Cadd; apply Ceq; cbn; field.
Qed.

(* ---- Lipschitz bound making the sign conditions limit-stable ---- *)
Lemma sarea_lip : forall v1 v2 a b,
  Rabs (sarea a v1 v2 - sarea b v1 v2)
  <= (Rabs (Im v1 - Im v2) + Rabs (Re v2 - Re v1)) * Cmod (Cminus a b).
Proof.
  intros v1 v2 a b.
  replace (sarea a v1 v2 - sarea b v1 v2)
     with ((Re a - Re b) * (Im v1 - Im v2) + (Im a - Im b) * (Re v2 - Re v1))
     by (unfold sarea, cross, Cminus; cbn; ring).
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite Rmult_plus_distr_r; apply Rplus_le_compat.
  - rewrite Rabs_mult, Rmult_comm; apply Rmult_le_compat_l; [ apply Rabs_pos | ].
    replace (Re a - Re b) with (Re (Cminus a b)) by (unfold Cminus; cbn; ring); apply Cmod_Re_le.
  - rewrite Rabs_mult, Rmult_comm; apply Rmult_le_compat_l; [ apply Rabs_pos | ].
    replace (Im a - Im b) with (Im (Cminus a b)) by (unfold Cminus; cbn; ring); apply Cmod_Im_le.
Qed.

Lemma bilin_lip : forall p q a b,
  Rabs (p * (Re a - Re b) + q * (Im a - Im b)) <= (Rabs p + Rabs q) * Cmod (Cminus a b).
Proof.
  intros p q a b; eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite Rmult_plus_distr_r; apply Rplus_le_compat.
  - rewrite Rabs_mult; apply Rmult_le_compat_l; [ apply Rabs_pos | ].
    replace (Re a - Re b) with (Re (Cminus a b)) by (unfold Cminus; cbn; ring); apply Cmod_Re_le.
  - rewrite Rabs_mult; apply Rmult_le_compat_l; [ apply Rabs_pos | ].
    replace (Im a - Im b) with (Im (Cminus a b)) by (unfold Cminus; cbn; ring); apply Cmod_Im_le.
Qed.

Lemma sarea_arg2_lip : forall v0 v2 a b,
  Rabs (sarea v0 a v2 - sarea v0 b v2)
  <= (Rabs (Im v2 - Im v0) + Rabs (Re v2 - Re v0)) * Cmod (Cminus a b).
Proof.
  intros v0 v2 a b.
  replace (sarea v0 a v2 - sarea v0 b v2)
     with ((Im v2 - Im v0) * (Re a - Re b) + (- (Re v2 - Re v0)) * (Im a - Im b))
     by (unfold sarea, cross, Cminus; cbn; ring).
  eapply Rle_trans; [ apply bilin_lip | ].
  rewrite Rabs_Ropp; apply Rle_refl.
Qed.

Lemma sarea_arg3_lip : forall v0 v1 a b,
  Rabs (sarea v0 v1 a - sarea v0 v1 b)
  <= (Rabs (Im v1 - Im v0) + Rabs (Re v1 - Re v0)) * Cmod (Cminus a b).
Proof.
  intros v0 v1 a b.
  replace (sarea v0 v1 a - sarea v0 v1 b)
     with ((- (Im v1 - Im v0)) * (Re a - Re b) + (Re v1 - Re v0) * (Im a - Im b))
     by (unfold sarea, cross, Cminus; cbn; ring).
  eapply Rle_trans; [ apply bilin_lip | ].
  rewrite Rabs_Ropp; apply Rle_refl.
Qed.

(* limit of a nonneg sequence with a geometric error bound is nonneg *)
Lemma nonneg_limit_geom : forall (u : nat -> R) (L M : R), 0 <= M ->
  (forall n, Rabs (u n - L) <= M * (/ 2) ^ n) -> (forall n, 0 <= u n) -> 0 <= L.
Proof.
  intros u L M HM Hb Hpos; apply Rnot_lt_le; intro Hneg.
  destruct (pow_lt_1_zero (/ 2) ltac:(rewrite Rabs_pos_eq; lra)
             ((- L) / (M + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  pose proof (Hb N) as HbN; pose proof (Hpos N) as HpN.
  pose proof (HN N (le_n N)) as HNN; rewrite Rabs_pos_eq in HNN by (apply pow_le; lra).
  assert (Hlt : M * (/ 2) ^ N < - L).
  { apply Rle_lt_trans with (M * ((- L) / (M + 1)));
      [ apply Rmult_le_compat_l; [ exact HM | left; exact HNN ] | ].
    apply Rmult_lt_reg_r with (M + 1); [ lra | ].
    replace (M * ((- L) / (M + 1)) * (M + 1)) with (M * (- L)) by (field; lra); nra. }
  assert (Rabs (u N - L) < - L) by lra.
  apply Rabs_def2 in H; lra.
Qed.

(* ================================================================= *)
(*  Region Goursat: reuse CGoursat's nested argument, invoking          *)
(*  holomorphy at the limit zc via zc ∈ InTri.                          *)
(* ================================================================= *)
Section RegionGoursat.
Variable h : C -> C.
Variable Hcont : CcontC h.
Variables v0 v1 v2 : C.
Hypothesis Hnd : sarea v0 v1 v2 <> 0.
Hypothesis Hhol_r : forall z, InTri v0 v1 v2 z -> exists d, is_Cderiv h z d.

Local Notation sq := (seqT h Hcont).
Local Notation TT := (TI h Hcont).
Let t0 : Tri := (v0, v1, v2).

Definition TriHull (t : Tri) : Prop :=
  InTri v0 v1 v2 (V0 t) /\ InTri v0 v1 v2 (V1 t) /\ InTri v0 v1 v2 (V2 t).

Lemma TriHull_nextT : forall t, TriHull t -> TriHull (nextT h Hcont t).
Proof.
  intros t [I0 [I1 I2]].
  assert (M01 : InTri v0 v1 v2 (mid (V0 t) (V1 t))) by (apply midpoint_in_tri; assumption).
  assert (M12 : InTri v0 v1 v2 (mid (V1 t) (V2 t))) by (apply midpoint_in_tri; assumption).
  assert (M20 : InTri v0 v1 v2 (mid (V2 t) (V0 t))) by (apply midpoint_in_tri; assumption).
  unfold nextT; repeat (destruct (Rle_dec _ _));
    unfold TriHull, sub0, sub1, sub2, sub3; cbn [V0 V1 V2 fst snd];
    repeat split; assumption.
Qed.

Lemma TriHull_all : forall n, TriHull (sq t0 n).
Proof.
  induction n.
  - unfold t0; cbn [seqT Nat.iter V0 V1 V2 fst snd]; unfold TriHull; cbn [V0 V1 V2 fst snd];
      repeat split; [ apply vertex0_in_tri | apply vertex1_in_tri | apply vertex2_in_tri ].
  - rewrite (seqT_S h Hcont t0 n); apply TriHull_nextT; exact IHn.
Qed.

Theorem tri_int_conv : tri_int h Hcont v0 v1 v2 = C0.
Proof.
  change (tri_int h Hcont v0 v1 v2) with (TT t0).
  set (D0 := diam3 t0).
  assert (HD0 : 0 <= D0) by apply diam3_nonneg.
  destruct (geom_cauchy_cv (fun n => Re (V0 (sq t0 n))) (D0 / 2) ltac:(lra)
    ltac:(intro n; apply Rle_trans with (Cmod (Cminus (V0 (sq t0 (S n))) (V0 (sq t0 n))));
      [ replace (Re (V0 (sq t0 (S n))) - Re (V0 (sq t0 n)))
          with (Re (Cminus (V0 (sq t0 (S n))) (V0 (sq t0 n)))) by (unfold Cminus; cbn; ring);
        apply Cmod_Re_le | apply v0_incr ])) as [lR [_ HlRb]].
  destruct (geom_cauchy_cv (fun n => Im (V0 (sq t0 n))) (D0 / 2) ltac:(lra)
    ltac:(intro n; apply Rle_trans with (Cmod (Cminus (V0 (sq t0 (S n))) (V0 (sq t0 n))));
      [ replace (Im (V0 (sq t0 (S n))) - Im (V0 (sq t0 n)))
          with (Im (Cminus (V0 (sq t0 (S n))) (V0 (sq t0 n)))) by (unfold Cminus; cbn; ring);
        apply Cmod_Im_le | apply v0_incr ])) as [lI [_ HlIb]].
  set (zc := mkC lR lI).
  assert (Hv0 : forall n, Cmod (Cminus (V0 (sq t0 n)) zc) <= 2 * D0 * (/ 2) ^ n).
  { intro n; eapply Rle_trans; [ apply Cmod_le_sum | ].
    replace (Re (Cminus (V0 (sq t0 n)) zc)) with (Re (V0 (sq t0 n)) - lR)
      by (unfold zc, Cminus; cbn; ring).
    replace (Im (Cminus (V0 (sq t0 n)) zc)) with (Im (V0 (sq t0 n)) - lI)
      by (unfold zc, Cminus; cbn; ring).
    pose proof (HlRb n); pose proof (HlIb n); lra. }
  (* zc lies in the closed triangle: each sign condition is a limit of nonneg ones *)
  assert (Hzc : InTri v0 v1 v2 zc).
  { apply InTri_sign_bwd; [ exact Hnd | | | ].
    - apply (nonneg_limit_geom (fun n => sarea (V0 (sq t0 n)) v1 v2 * sarea v0 v1 v2)
              _ ((Rabs (Im v1 - Im v2) + Rabs (Re v2 - Re v1)) * 2 * D0 * Rabs (sarea v0 v1 v2))).
      + repeat apply Rmult_le_pos; try apply Rabs_pos; try lra;
          apply Rplus_le_le_0_compat; apply Rabs_pos.
      + intro n; replace (sarea (V0 (sq t0 n)) v1 v2 * sarea v0 v1 v2 - sarea zc v1 v2 * sarea v0 v1 v2)
          with ((sarea (V0 (sq t0 n)) v1 v2 - sarea zc v1 v2) * sarea v0 v1 v2) by ring.
        rewrite Rabs_mult.
        eapply Rle_trans;
          [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply sarea_lip ] | ].
        replace ((Rabs (Im v1 - Im v2) + Rabs (Re v2 - Re v1)) * 2 * D0 * Rabs (sarea v0 v1 v2) * (/ 2) ^ n)
          with ((Rabs (Im v1 - Im v2) + Rabs (Re v2 - Re v1)) * (2 * D0 * (/ 2) ^ n) * Rabs (sarea v0 v1 v2))
          by ring.
        apply Rmult_le_compat_r; [ apply Rabs_pos | ].
        apply Rmult_le_compat_l; [ apply Rplus_le_le_0_compat; apply Rabs_pos | apply Hv0 ].
      + intro n; apply (proj1 (InTri_sign_fwd v0 v1 v2 _ (proj1 (TriHull_all n)))).
    - apply (nonneg_limit_geom (fun n => sarea v0 (V0 (sq t0 n)) v2 * sarea v0 v1 v2)
              _ ((Rabs (Im v2 - Im v0) + Rabs (Re v2 - Re v0)) * 2 * D0 * Rabs (sarea v0 v1 v2))).
      + repeat apply Rmult_le_pos; try apply Rabs_pos; try lra;
          apply Rplus_le_le_0_compat; apply Rabs_pos.
      + intro n; replace (sarea v0 (V0 (sq t0 n)) v2 * sarea v0 v1 v2 - sarea v0 zc v2 * sarea v0 v1 v2)
          with ((sarea v0 (V0 (sq t0 n)) v2 - sarea v0 zc v2) * sarea v0 v1 v2) by ring.
        rewrite Rabs_mult.
        eapply Rle_trans;
          [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply sarea_arg2_lip ] | ].
        replace ((Rabs (Im v2 - Im v0) + Rabs (Re v2 - Re v0)) * 2 * D0 * Rabs (sarea v0 v1 v2) * (/ 2) ^ n)
          with ((Rabs (Im v2 - Im v0) + Rabs (Re v2 - Re v0)) * (2 * D0 * (/ 2) ^ n) * Rabs (sarea v0 v1 v2))
          by ring.
        apply Rmult_le_compat_r; [ apply Rabs_pos | ].
        apply Rmult_le_compat_l; [ apply Rplus_le_le_0_compat; apply Rabs_pos | apply Hv0 ].
      + intro n; apply (proj1 (proj2 (InTri_sign_fwd v0 v1 v2 _ (proj1 (TriHull_all n))))).
    - apply (nonneg_limit_geom (fun n => sarea v0 v1 (V0 (sq t0 n)) * sarea v0 v1 v2)
              _ ((Rabs (Im v1 - Im v0) + Rabs (Re v1 - Re v0)) * 2 * D0 * Rabs (sarea v0 v1 v2))).
      + repeat apply Rmult_le_pos; try apply Rabs_pos; try lra;
          apply Rplus_le_le_0_compat; apply Rabs_pos.
      + intro n; replace (sarea v0 v1 (V0 (sq t0 n)) * sarea v0 v1 v2 - sarea v0 v1 zc * sarea v0 v1 v2)
          with ((sarea v0 v1 (V0 (sq t0 n)) - sarea v0 v1 zc) * sarea v0 v1 v2) by ring.
        rewrite Rabs_mult.
        eapply Rle_trans;
          [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply sarea_arg3_lip ] | ].
        replace ((Rabs (Im v1 - Im v0) + Rabs (Re v1 - Re v0)) * 2 * D0 * Rabs (sarea v0 v1 v2) * (/ 2) ^ n)
          with ((Rabs (Im v1 - Im v0) + Rabs (Re v1 - Re v0)) * (2 * D0 * (/ 2) ^ n) * Rabs (sarea v0 v1 v2))
          by ring.
        apply Rmult_le_compat_r; [ apply Rabs_pos | ].
        apply Rmult_le_compat_l; [ apply Rplus_le_le_0_compat; apply Rabs_pos | apply Hv0 ].
      + intro n; apply (proj2 (proj2 (InTri_sign_fwd v0 v1 v2 _ (proj1 (TriHull_all n))))).
  }
  (* --- from here the argument is CGoursat.TI_zero verbatim (region h at zc) --- *)
  assert (Hvert : forall (w : Tri) n, w = sq t0 n ->
    Cmod (Cminus (V1 w) zc) <= 3 * D0 * (/ 2) ^ n /\
    Cmod (Cminus (V2 w) zc) <= 3 * D0 * (/ 2) ^ n /\
    Cmod (Cminus (V0 w) zc) <= 3 * D0 * (/ 2) ^ n).
  { intros w n ->.
    assert (Hd : diam (V0 (sq t0 n)) (V1 (sq t0 n)) (V2 (sq t0 n)) <= D0 * (/ 2) ^ n)
      by apply diamn.
    assert (Hv0n := Hv0 n).
    assert (He1 : Cmod (Cminus (V1 (sq t0 n)) (V0 (sq t0 n))) <= D0 * (/ 2) ^ n)
      by (eapply Rle_trans;
          [ apply (diam_e1 (V0 (sq t0 n)) (V1 (sq t0 n)) (V2 (sq t0 n))) | exact Hd ]).
    assert (He2 : Cmod (Cminus (V2 (sq t0 n)) (V0 (sq t0 n))) <= D0 * (/ 2) ^ n)
      by (rewrite Cmod_Cminus_sym; eapply Rle_trans;
          [ apply (diam_e3 (V0 (sq t0 n)) (V1 (sq t0 n)) (V2 (sq t0 n))) | exact Hd ]).
    assert (HP : 0 <= D0 * (/ 2) ^ n)
      by (apply Rmult_le_pos; [ exact HD0 | apply pow_le; lra ]).
    repeat split.
    - apply Rle_trans with (Cmod (Cminus (V1 (sq t0 n)) (V0 (sq t0 n)))
                            + Cmod (Cminus (V0 (sq t0 n)) zc)).
      + replace (Cminus (V1 (sq t0 n)) zc)
          with (Cadd (Cminus (V1 (sq t0 n)) (V0 (sq t0 n))) (Cminus (V0 (sq t0 n)) zc)) by ring;
          apply Cmod_triangle.
      + apply Rle_trans with (D0 * (/ 2) ^ n + 2 * D0 * (/ 2) ^ n);
          [ apply Rplus_le_compat; [ exact He1 | exact Hv0n ] | apply Req_le; ring ].
    - apply Rle_trans with (Cmod (Cminus (V2 (sq t0 n)) (V0 (sq t0 n)))
                            + Cmod (Cminus (V0 (sq t0 n)) zc)).
      + replace (Cminus (V2 (sq t0 n)) zc)
          with (Cadd (Cminus (V2 (sq t0 n)) (V0 (sq t0 n))) (Cminus (V0 (sq t0 n)) zc)) by ring;
          apply Cmod_triangle.
      + apply Rle_trans with (D0 * (/ 2) ^ n + 2 * D0 * (/ 2) ^ n);
          [ apply Rplus_le_compat; [ exact He2 | exact Hv0n ] | apply Req_le; ring ].
    - apply Rle_trans with (2 * D0 * (/ 2) ^ n); [ exact Hv0n | ].
      apply Rle_trans with (D0 * (/ 2) ^ n + 2 * D0 * (/ 2) ^ n); [ | apply Req_le; ring ].
      apply Rle_trans with (0 + 2 * D0 * (/ 2) ^ n);
        [ apply Req_le; ring | apply Rplus_le_compat; [ exact HP | apply Rle_refl ] ]. }
  destruct (Hhol_r zc Hzc) as [dstar Hdstar].
  set (A := Aff (h zc) dstar zc).
  set (rem := fun z => Cadd (h z) (Copp (A z))).
  assert (HAcont : CcontC A) by apply Ccont_Aff.
  assert (Hremcont : CcontC rem) by (apply CcontC_add; [ exact Hcont | apply CcontC_opp; exact HAcont ]).
  assert (Hsplit : forall z, h z = Cadd (A z) (rem z)) by (intro z; unfold rem; ring).
  assert (HTIrem : forall n, TT (sq t0 n)
    = tri_int rem Hremcont (V0 (sq t0 n)) (V1 (sq t0 n)) (V2 (sq t0 n))).
  { intro n; unfold TT, TI.
    rewrite (tri_int_ext h (fun z => Cadd (A z) (rem z)) Hcont
              (CcontC_add A rem HAcont Hremcont) _ _ _ Hsplit).
    rewrite (tri_int_add A rem HAcont Hremcont (CcontC_add A rem HAcont Hremcont)).
    assert (HA0 : tri_int A HAcont (V0 (sq t0 n)) (V1 (sq t0 n)) (V2 (sq t0 n)) = C0).
    { unfold A;
      rewrite (tri_int_ext (Aff (h zc) dstar zc) (Aff (h zc) dstar zc) HAcont
                (Ccont_Aff (h zc) dstar zc) _ _ _ (fun _ => eq_refl));
      apply affine_tri_zero. }
    rewrite HA0; ring. }
  assert (Hrembnd : forall e, 0 < e -> exists del, 0 < del /\
    forall z, Cmod (Cminus z zc) < del -> Cmod (rem z) <= e * Cmod (Cminus z zc)).
  { intros e He; destruct (Hdstar e He) as [del [Hdel Hb]].
    exists del; split; [ exact Hdel | ]; intros z Hz.
    replace (rem z) with (Cminus (Cminus (h (Cadd zc (Cminus z zc))) (h zc))
                                  (Cmul dstar (Cminus z zc))).
    - apply Hb; exact Hz.
    - unfold rem, A, Aff; replace (Cadd zc (Cminus z zc)) with z by ring; ring. }
  assert (Hall : forall e, 0 < e -> Cmod (TT t0) <= 18 * (D0 * D0) * e).
  { intros e He; destruct (Hrembnd e He) as [del [Hdel Hrb]].
    destruct (pow_lt_1_zero (/ 2) ltac:(rewrite Rabs_pos_eq; lra)
               (del / (3 * D0 + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    pose proof (HN N (le_n N)) as HNn; rewrite Rabs_pos_eq in HNn by (apply pow_le; lra).
    set (rho := 3 * D0 * (/ 2) ^ N).
    assert (Hpowpos : 0 <= (/ 2) ^ N) by (apply pow_le; lra).
    assert (Hrho : rho < del).
    { unfold rho; apply Rle_lt_trans with ((3 * D0) * (del / (3 * D0 + 1)));
        [ apply Rmult_le_compat_l; lra | ].
      apply Rlt_le_trans with ((3 * D0 + 1) * (del / (3 * D0 + 1)));
        [ apply Rmult_lt_compat_r; [ apply Rdiv_lt_0_compat; lra | lra ]
        | apply Req_le; field; lra ]. }
    destruct (Hvert (sq t0 N) N eq_refl) as [Hb1 [Hb2 Hb0]].
    assert (Hedge : forall x y, Cmod (Cminus x zc) <= rho -> Cmod (Cminus y zc) <= rho ->
      forall s, 0 <= s <= 1 -> Cmod (rem (seg x y s)) <= e * rho).
    { intros x y Hx Hy s Hs.
      assert (Hzc' : Cmod (Cminus (seg x y s) zc) <= rho)
        by (eapply Rle_trans; [ apply seg_convex_bound; exact Hs | apply Rmax_lub; assumption ]).
      eapply Rle_trans; [ apply Hrb; lra | ].
      apply Rmult_le_compat_l; lra. }
    assert (HTIn : Cmod (TT (sq t0 N)) <= 2 * (e * rho) * perim (V0 (sq t0 N)) (V1 (sq t0 N)) (V2 (sq t0 N))).
    { rewrite HTIrem; apply tri_int_ML.
      - intros s Hs; apply Hedge; assumption.
      - intros s Hs; apply Hedge; assumption.
      - intros s Hs; apply Hedge; assumption. }
    assert (Hperim : perim (V0 (sq t0 N)) (V1 (sq t0 N)) (V2 (sq t0 N)) <= rho).
    { eapply Rle_trans; [ apply perim_le_3diam | ].
      unfold rho; replace (3 * D0 * (/ 2) ^ N) with (3 * (D0 * (/ 2) ^ N)) by ring.
      apply Rmult_le_compat_l; [ lra | apply diamn ]. }
    pose proof (tin h Hcont t0 N) as Hlow.
    assert (Hrho0 : 0 <= rho) by (unfold rho; apply Rmult_le_pos; [ lra | exact Hpowpos ]).
    assert (Herho : 0 <= e * rho) by (apply Rmult_le_pos; lra).
    assert (HTIn2 : Cmod (TT (sq t0 N)) <= 2 * (e * rho) * rho)
      by (eapply Rle_trans; [ exact HTIn | apply Rmult_le_compat_l; [ lra | exact Hperim ] ]).
    assert (Hpow4 : (/ 2) ^ N * (/ 2) ^ N = (/ 4) ^ N)
      by (rewrite <- Rpow_mult_distr; f_equal; lra).
    assert (Hcm : Cmod (TT t0) * (/ 4) ^ N <= 18 * (D0 * D0) * e * (/ 4) ^ N).
    { eapply Rle_trans; [ exact Hlow | ].
      eapply Rle_trans; [ exact HTIn2 | ].
      unfold rho; rewrite <- Hpow4; nra. }
    assert (Hp4pos : 0 < (/ 4) ^ N) by (apply pow_lt; lra).
    apply Rmult_le_reg_r with ((/ 4) ^ N); [ exact Hp4pos | exact Hcm ]. }
  assert (HTImod : Cmod (TT t0) = 0).
  { apply (le_all_eps (Cmod (TT t0)) (18 * (D0 * D0)));
      [ apply Cmod_nonneg | apply Rmult_le_pos; [ lra | apply Rmult_le_pos; exact HD0 ] | exact Hall ]. }
  apply Cmod0; exact HTImod.
Qed.

End RegionGoursat.

Print Assumptions tri_int_conv.

(* ================================================================= *)
(*  END CGoursatConv.v  —  region Goursat (non-degenerate triangle).    *)
(* ================================================================= *)
