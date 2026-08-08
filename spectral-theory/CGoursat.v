(* ================================================================= *)
(*  CGoursat.v  —  Milestone C, brick C2a-4b: Goursat's theorem.        *)
(*  The boundary integral of a holomorphic function over any triangle    *)
(*  vanishes.  Assembles the bisection (tri_bisect), the affine-vanishing *)
(*  (affine_tri_zero), the ML estimate (tri_int_ML), the shrinking        *)
(*  geometry (CGoursatGeom) and the completeness limit (CGeomCauchy).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CIntegral2 CPathIntegral CSegInt
        CTriangle CGoursatFTC CGoursatLin CGoursatML CGoursatAffine CGoursatGeom
        CGeomCauchy.
Open Scope R_scope.

Section Goursat.
Variable h : C -> C.
Variable Hcont : CcontC h.

(* triangle triples *)
Definition Tri := (C * C * C)%type.
Definition V0 (t : Tri) : C := fst (fst t).
Definition V1 (t : Tri) : C := snd (fst t).
Definition V2 (t : Tri) : C := snd t.
Definition TI (t : Tri) : C := tri_int h Hcont (V0 t) (V1 t) (V2 t).
Definition diam3 (t : Tri) : R := diam (V0 t) (V1 t) (V2 t).

Definition sub0 (t : Tri) : Tri := (V0 t, mid (V0 t) (V1 t), mid (V2 t) (V0 t)).
Definition sub1 (t : Tri) : Tri := (mid (V0 t) (V1 t), V1 t, mid (V1 t) (V2 t)).
Definition sub2 (t : Tri) : Tri := (mid (V2 t) (V0 t), mid (V1 t) (V2 t), V2 t).
Definition sub3 (t : Tri) : Tri := (mid (V0 t) (V1 t), mid (V1 t) (V2 t), mid (V2 t) (V0 t)).

Lemma TI_bisect : forall t,
  TI t = Cadd (TI (sub0 t)) (Cadd (TI (sub1 t)) (Cadd (TI (sub2 t)) (TI (sub3 t)))).
Proof.
  intro t; unfold TI, sub0, sub1, sub2, sub3, V0, V1, V2; cbn [fst snd].
  apply tri_bisect.
Qed.

(* the sub-triangle of largest |TI| *)
Definition nextT (t : Tri) : Tri :=
  let a0 := Cmod (TI (sub0 t)) in let a1 := Cmod (TI (sub1 t)) in
  let a2 := Cmod (TI (sub2 t)) in let a3 := Cmod (TI (sub3 t)) in
  if Rle_dec a1 a0 then
    if Rle_dec a2 a0 then (if Rle_dec a3 a0 then sub0 t else sub3 t)
    else (if Rle_dec a3 a2 then sub2 t else sub3 t)
  else
    if Rle_dec a2 a1 then (if Rle_dec a3 a1 then sub1 t else sub3 t)
    else (if Rle_dec a3 a2 then sub2 t else sub3 t).

(* nextT dominates all four sub-integrals *)
Lemma nextT_ge : forall t,
  Cmod (TI (sub0 t)) <= Cmod (TI (nextT t)) /\
  Cmod (TI (sub1 t)) <= Cmod (TI (nextT t)) /\
  Cmod (TI (sub2 t)) <= Cmod (TI (nextT t)) /\
  Cmod (TI (sub3 t)) <= Cmod (TI (nextT t)).
Proof.
  intro t; unfold nextT;
    repeat (destruct (Rle_dec _ _)); repeat split; lra.
Qed.

Lemma TI_next : forall t, Cmod (TI t) <= 4 * Cmod (TI (nextT t)).
Proof.
  intro t; rewrite TI_bisect.
  destruct (nextT_ge t) as [G0 [G1 [G2 G3]]].
  eapply Rle_trans; [ apply Cmod_triangle | ].
  eapply Rle_trans; [ apply Rplus_le_compat_l; apply Cmod_triangle | ].
  eapply Rle_trans; [ apply Rplus_le_compat_l; apply Rplus_le_compat_l; apply Cmod_triangle | ].
  lra.
Qed.

Lemma diam_next : forall t, diam3 (nextT t) <= / 2 * diam3 t.
Proof.
  intro t; unfold nextT, diam3, sub0, sub1, sub2, sub3, V0, V1, V2; cbn [fst snd];
    repeat (destruct (Rle_dec _ _));
    solve [ apply diam_sub0 | apply diam_sub1 | apply diam_sub2 | apply diam_sub3 ].
Qed.

Lemma V0_sub0 : forall t, V0 (sub0 t) = V0 t.
Proof. reflexivity. Qed.
Lemma V0_sub1 : forall t, V0 (sub1 t) = mid (V0 t) (V1 t).
Proof. reflexivity. Qed.
Lemma V0_sub2 : forall t, V0 (sub2 t) = mid (V2 t) (V0 t).
Proof. reflexivity. Qed.
Lemma V0_sub3 : forall t, V0 (sub3 t) = mid (V0 t) (V1 t).
Proof. reflexivity. Qed.

Lemma diam3_nonneg : forall t, 0 <= diam3 t.
Proof.
  intro t; unfold diam3, diam;
    eapply Rle_trans; [ apply Cmod_nonneg | apply Rmax_l ].
Qed.

Lemma v0_next : forall t, Cmod (Cminus (V0 (nextT t)) (V0 t)) <= / 2 * diam3 t.
Proof.
  intro t.
  assert (Hz : Cmod (Cminus (V0 t) (V0 t)) <= / 2 * diam3 t).
  { replace (Cminus (V0 t) (V0 t)) with C0 by ring.
    replace (Cmod C0) with 0 by (symmetry; apply Cmod0; reflexivity).
    pose proof (diam3_nonneg t); lra. }
  unfold nextT; repeat (destruct (Rle_dec _ _));
    (rewrite ?V0_sub0, ?V0_sub1, ?V0_sub2, ?V0_sub3);
    solve [ exact Hz | apply vmove_m01 | apply vmove_m20 ].
Qed.

(* ---- the nested sequence and its bounds ---- *)
Definition seqT (t0 : Tri) (n : nat) : Tri := Nat.iter n nextT t0.

Lemma seqT_S : forall t0 n, seqT t0 (S n) = nextT (seqT t0 n).
Proof. reflexivity. Qed.

Lemma diamn : forall t0 n, diam3 (seqT t0 n) <= diam3 t0 * (/ 2) ^ n.
Proof.
  intros t0 n; induction n.
  - unfold seqT; simpl; lra.
  - rewrite seqT_S; eapply Rle_trans; [ apply diam_next | ].
    apply Rle_trans with (/ 2 * (diam3 t0 * (/ 2) ^ n));
      [ apply Rmult_le_compat_l; [ lra | exact IHn ] | ].
    assert (Hs : (/ 2) ^ (S n) = / 2 * (/ 2) ^ n) by (cbn [pow]; ring).
    rewrite Hs; apply Req_le; ring.
Qed.

Lemma tin : forall t0 n, Cmod (TI t0) * (/ 4) ^ n <= Cmod (TI (seqT t0 n)).
Proof.
  intros t0 n; induction n.
  - unfold seqT; simpl; lra.
  - rewrite seqT_S; pose proof (TI_next (seqT t0 n)) as HT.
    assert (Hs : (/ 4) ^ (S n) = / 4 * (/ 4) ^ n) by (cbn [pow]; ring).
    rewrite Hs; apply Rle_trans with (Cmod (TI (seqT t0 n)) / 4).
    + apply Rle_trans with (Cmod (TI t0) * (/ 4) ^ n / 4);
        [ apply Req_le; field | apply Rmult_le_compat_r; [ lra | exact IHn ] ].
    + lra.
Qed.

Lemma v0_incr : forall t0 n,
  Cmod (Cminus (V0 (seqT t0 (S n))) (V0 (seqT t0 n))) <= (diam3 t0 / 2) * (/ 2) ^ n.
Proof.
  intros t0 n; rewrite seqT_S; eapply Rle_trans; [ apply v0_next | ].
  apply Rle_trans with (/ 2 * (diam3 t0 * (/ 2) ^ n));
    [ apply Rmult_le_compat_l; [ lra | apply diamn ] | apply Req_le; field ].
Qed.

(* ---- general helpers used by the assembly ---- *)
Lemma seg_convex_bound : forall a b zc s, 0 <= s <= 1 ->
  Cmod (Cminus (seg a b s) zc)
  <= Rmax (Cmod (Cminus a zc)) (Cmod (Cminus b zc)).
Proof.
  intros a b zc s [Hs0 Hs1].
  assert (Heq : Cminus (seg a b s) zc =
    Cadd (Cmul (RtoC (1 - s)) (Cminus a zc)) (Cmul (RtoC s) (Cminus b zc)))
    by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
  rewrite Heq; eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC.
  rewrite (Rabs_pos_eq (1 - s)) by lra; rewrite (Rabs_pos_eq s) by lra.
  apply Rle_trans with ((1 - s) * Rmax (Cmod (Cminus a zc)) (Cmod (Cminus b zc))
    + s * Rmax (Cmod (Cminus a zc)) (Cmod (Cminus b zc))).
  - apply Rplus_le_compat.
    + apply Rmult_le_compat_l; [ lra | apply Rmax_l ].
    + apply Rmult_le_compat_l; [ lra | apply Rmax_r ].
  - apply Req_le; ring.
Qed.

Lemma CcontC_opp : forall f, CcontC f -> CcontC (fun z => Copp (f z)).
Proof. intros f Hf gam Hgam; apply Ccont_opp, Hf; exact Hgam. Qed.

Lemma seg_int_ext : forall f g Hf Hg a b,
  (forall z, f z = g z) -> seg_int f Hf a b = seg_int g Hg a b.
Proof.
  intros f g Hf Hg a b Heq; unfold seg_int; apply Cintf_ext; intro u;
    rewrite Heq; reflexivity.
Qed.

Lemma tri_int_ext : forall f g Hf Hg v0 v1 v2,
  (forall z, f z = g z) -> tri_int f Hf v0 v1 v2 = tri_int g Hg v0 v1 v2.
Proof.
  intros f g Hf Hg v0 v1 v2 Heq; unfold tri_int;
    rewrite (seg_int_ext f g Hf Hg v0 v1 Heq), (seg_int_ext f g Hf Hg v1 v2 Heq),
            (seg_int_ext f g Hf Hg v2 v0 Heq); reflexivity.
Qed.

Print Assumptions v0_incr.

End Goursat.

(* ================================================================= *)
(*  END CGoursat.v (chunk 2) — sequence bounds + assembly helpers.      *)
(* ================================================================= *)
