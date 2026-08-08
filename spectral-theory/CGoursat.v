(* ================================================================= *)
(*  CGoursat.v  —  Milestone C, brick C2a-4b: Goursat's theorem.        *)
(*  The boundary integral of a holomorphic function over any triangle    *)
(*  vanishes.  Assembles the bisection (tri_bisect), the affine-vanishing *)
(*  (affine_tri_zero), the ML estimate (tri_int_ML), the shrinking        *)
(*  geometry (CGoursatGeom) and the completeness limit (CGeomCauchy).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CSegInt CTriangle
        CGoursatFTC CGoursatLin CGoursatML CGoursatAffine CGoursatGeom CGeomCauchy.
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

Print Assumptions v0_next.

End Goursat.

(* ================================================================= *)
(*  END CGoursat.v (chunk 1) — nextT sequence step + properties.        *)
(* ================================================================= *)
