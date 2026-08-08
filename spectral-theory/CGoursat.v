(* ================================================================= *)
(*  CGoursat.v  —  Milestone C, brick C2a-4b: Goursat's theorem.        *)
(*  The boundary integral of a holomorphic function over any triangle    *)
(*  vanishes.  Assembles the bisection (tri_bisect), the affine-vanishing *)
(*  (affine_tri_zero), the ML estimate (tri_int_ML), the shrinking        *)
(*  geometry (CGoursatGeom) and the completeness limit (CGeomCauchy).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries Holomorphic CIntegral2 CPathIntegral
        CSegInt CTriangle CGoursatFTC CGoursatLin CGoursatML CGoursatAffine
        CGoursatGeom CGeomCauchy.
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

Lemma perim_le_3diam : forall a b c, perim a b c <= 3 * diam a b c.
Proof.
  intros a b c; unfold perim;
    pose proof (diam_e1 a b c); pose proof (diam_e2 a b c); pose proof (diam_e3 a b c); lra.
Qed.

Lemma le_all_eps : forall x K, 0 <= x -> 0 <= K ->
  (forall e, 0 < e -> x <= K * e) -> x = 0.
Proof.
  intros x K Hx HK Hall; apply Rle_antisym; [ | exact Hx ].
  apply Rnot_lt_le; intro Hpos.
  pose proof (Hall (x / (2 * (K + 1))) ltac:(apply Rdiv_lt_0_compat; lra)) as H.
  assert (Hlt : K * (x / (2 * (K + 1))) < x).
  { apply Rmult_lt_reg_r with (2 * (K + 1)); [ lra | ].
    replace (K * (x / (2 * (K + 1))) * (2 * (K + 1))) with (K * x) by (field; lra); nra. }
  lra.
Qed.

Hypothesis Hhol : forall z, exists d, is_Cderiv h z d.

Theorem TI_zero : forall t0, TI t0 = C0.
Proof.
  intro t0; set (D0 := diam3 t0).
  assert (HD0 : 0 <= D0) by apply diam3_nonneg.
  (* completeness: the tracked corner converges to zc *)
  destruct (geom_cauchy_cv (fun n => Re (V0 (seqT t0 n))) (D0 / 2) ltac:(lra)
    ltac:(intro n; apply Rle_trans with (Cmod (Cminus (V0 (seqT t0 (S n))) (V0 (seqT t0 n))));
      [ replace (Re (V0 (seqT t0 (S n))) - Re (V0 (seqT t0 n)))
          with (Re (Cminus (V0 (seqT t0 (S n))) (V0 (seqT t0 n)))) by (unfold Cminus; cbn; ring);
        apply Cmod_Re_le | apply v0_incr ])) as [lR [_ HlRb]].
  destruct (geom_cauchy_cv (fun n => Im (V0 (seqT t0 n))) (D0 / 2) ltac:(lra)
    ltac:(intro n; apply Rle_trans with (Cmod (Cminus (V0 (seqT t0 (S n))) (V0 (seqT t0 n))));
      [ replace (Im (V0 (seqT t0 (S n))) - Im (V0 (seqT t0 n)))
          with (Im (Cminus (V0 (seqT t0 (S n))) (V0 (seqT t0 n)))) by (unfold Cminus; cbn; ring);
        apply Cmod_Im_le | apply v0_incr ])) as [lI [_ HlIb]].
  set (zc := mkC lR lI).
  assert (Hv0 : forall n, Cmod (Cminus (V0 (seqT t0 n)) zc) <= 2 * D0 * (/ 2) ^ n).
  { intro n; eapply Rle_trans; [ apply Cmod_le_sum | ].
    replace (Re (Cminus (V0 (seqT t0 n)) zc)) with (Re (V0 (seqT t0 n)) - lR)
      by (unfold zc, Cminus; cbn; ring).
    replace (Im (Cminus (V0 (seqT t0 n)) zc)) with (Im (V0 (seqT t0 n)) - lI)
      by (unfold zc, Cminus; cbn; ring).
    pose proof (HlRb n); pose proof (HlIb n); lra. }
  (* the other two vertices: within 3 D0 (/2)^n of zc *)
  assert (Hvert : forall (w : Tri) n, w = seqT t0 n ->
    Cmod (Cminus (V1 w) zc) <= 3 * D0 * (/ 2) ^ n /\
    Cmod (Cminus (V2 w) zc) <= 3 * D0 * (/ 2) ^ n /\
    Cmod (Cminus (V0 w) zc) <= 3 * D0 * (/ 2) ^ n).
  { intros w n ->.
    assert (Hd : diam (V0 (seqT t0 n)) (V1 (seqT t0 n)) (V2 (seqT t0 n)) <= D0 * (/ 2) ^ n)
      by apply diamn.
    assert (Hv0n := Hv0 n).
    assert (He1 : Cmod (Cminus (V1 (seqT t0 n)) (V0 (seqT t0 n))) <= D0 * (/ 2) ^ n)
      by (eapply Rle_trans;
          [ apply (diam_e1 (V0 (seqT t0 n)) (V1 (seqT t0 n)) (V2 (seqT t0 n))) | exact Hd ]).
    assert (He2 : Cmod (Cminus (V2 (seqT t0 n)) (V0 (seqT t0 n))) <= D0 * (/ 2) ^ n)
      by (rewrite Cmod_Cminus_sym; eapply Rle_trans;
          [ apply (diam_e3 (V0 (seqT t0 n)) (V1 (seqT t0 n)) (V2 (seqT t0 n))) | exact Hd ]).
    assert (HP : 0 <= D0 * (/ 2) ^ n)
      by (apply Rmult_le_pos; [ exact HD0 | apply pow_le; lra ]).
    repeat split.
    - apply Rle_trans with (Cmod (Cminus (V1 (seqT t0 n)) (V0 (seqT t0 n)))
                            + Cmod (Cminus (V0 (seqT t0 n)) zc)).
      + replace (Cminus (V1 (seqT t0 n)) zc)
          with (Cadd (Cminus (V1 (seqT t0 n)) (V0 (seqT t0 n))) (Cminus (V0 (seqT t0 n)) zc)) by ring;
          apply Cmod_triangle.
      + apply Rle_trans with (D0 * (/ 2) ^ n + 2 * D0 * (/ 2) ^ n);
          [ apply Rplus_le_compat; [ exact He1 | exact Hv0n ] | apply Req_le; ring ].
    - apply Rle_trans with (Cmod (Cminus (V2 (seqT t0 n)) (V0 (seqT t0 n)))
                            + Cmod (Cminus (V0 (seqT t0 n)) zc)).
      + replace (Cminus (V2 (seqT t0 n)) zc)
          with (Cadd (Cminus (V2 (seqT t0 n)) (V0 (seqT t0 n))) (Cminus (V0 (seqT t0 n)) zc)) by ring;
          apply Cmod_triangle.
      + apply Rle_trans with (D0 * (/ 2) ^ n + 2 * D0 * (/ 2) ^ n);
          [ apply Rplus_le_compat; [ exact He2 | exact Hv0n ] | apply Req_le; ring ].
    - apply Rle_trans with (2 * D0 * (/ 2) ^ n); [ exact Hv0n | ].
      apply Rle_trans with (D0 * (/ 2) ^ n + 2 * D0 * (/ 2) ^ n); [ | apply Req_le; ring ].
      apply Rle_trans with (0 + 2 * D0 * (/ 2) ^ n);
        [ apply Req_le; ring | apply Rplus_le_compat; [ exact HP | apply Rle_refl ] ]. }
  (* the affine part at zc, its primitive, and the remainder *)
  destruct (Hhol zc) as [dstar Hdstar].
  set (A := Aff (h zc) dstar zc).
  set (rem := fun z => Cadd (h z) (Copp (A z))).
  assert (HAcont : CcontC A) by apply Ccont_Aff.
  assert (Hremcont : CcontC rem) by (apply CcontC_add; [ exact Hcont | apply CcontC_opp; exact HAcont ]).
  assert (Hsplit : forall z, h z = Cadd (A z) (rem z)) by (intro z; unfold rem; ring).
  (* TI(seqT n) = tri_int rem over the same vertices *)
  assert (HTIrem : forall n, TI (seqT t0 n)
    = tri_int rem Hremcont (V0 (seqT t0 n)) (V1 (seqT t0 n)) (V2 (seqT t0 n))).
  { intro n; unfold TI.
    rewrite (tri_int_ext h (fun z => Cadd (A z) (rem z)) Hcont
              (CcontC_add A rem HAcont Hremcont) _ _ _ Hsplit).
    rewrite (tri_int_add A rem HAcont Hremcont (CcontC_add A rem HAcont Hremcont)).
    assert (HA0 : tri_int A HAcont (V0 (seqT t0 n)) (V1 (seqT t0 n)) (V2 (seqT t0 n)) = C0).
    { unfold A;
      rewrite (tri_int_ext (Aff (h zc) dstar zc) (Aff (h zc) dstar zc) HAcont
                (Ccont_Aff (h zc) dstar zc) _ _ _ (fun _ => eq_refl));
      apply affine_tri_zero. }
    rewrite HA0; ring. }
  (* the remainder is small near zc *)
  assert (Hrembnd : forall e, 0 < e -> exists del, 0 < del /\
    forall z, Cmod (Cminus z zc) < del -> Cmod (rem z) <= e * Cmod (Cminus z zc)).
  { intros e He; destruct (Hdstar e He) as [del [Hdel Hb]].
    exists del; split; [ exact Hdel | ]; intros z Hz.
    replace (rem z) with (Cminus (Cminus (h (Cadd zc (Cminus z zc))) (h zc))
                                  (Cmul dstar (Cminus z zc))).
    - apply Hb; exact Hz.
    - unfold rem, A, Aff; replace (Cadd zc (Cminus z zc)) with z by ring; ring. }
  (* the final all-epsilon bound *)
  assert (Hall : forall e, 0 < e -> Cmod (TI t0) <= 18 * (D0 * D0) * e).
  { intros e He; destruct (Hrembnd e He) as [del [Hdel Hrb]].
    (* pick n with 3 D0 (/2)^n < del *)
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
    (* boundary points of seqT N are within rho of zc *)
    destruct (Hvert (seqT t0 N) N eq_refl) as [Hb1 [Hb2 Hb0]].
    assert (Hedge : forall x y, Cmod (Cminus x zc) <= rho -> Cmod (Cminus y zc) <= rho ->
      forall s, 0 <= s <= 1 -> Cmod (rem (seg x y s)) <= e * rho).
    { intros x y Hx Hy s Hs.
      assert (Hzc : Cmod (Cminus (seg x y s) zc) <= rho)
        by (eapply Rle_trans; [ apply seg_convex_bound; exact Hs | apply Rmax_lub; assumption ]).
      eapply Rle_trans; [ apply Hrb; lra | ].
      apply Rmult_le_compat_l; lra. }
    (* ML on tri_int rem *)
    assert (HTIn : Cmod (TI (seqT t0 N)) <= 2 * (e * rho) * perim (V0 (seqT t0 N)) (V1 (seqT t0 N)) (V2 (seqT t0 N))).
    { rewrite HTIrem; apply tri_int_ML.
      - intros s Hs; apply Hedge; assumption.
      - intros s Hs; apply Hedge; assumption.
      - intros s Hs; apply Hedge; assumption. }
    assert (Hperim : perim (V0 (seqT t0 N)) (V1 (seqT t0 N)) (V2 (seqT t0 N)) <= rho).
    { eapply Rle_trans; [ apply perim_le_3diam | ].
      unfold rho; replace (3 * D0 * (/ 2) ^ N) with (3 * (D0 * (/ 2) ^ N)) by ring.
      apply Rmult_le_compat_l; [ lra | apply diamn ]. }
    (* combine with the lower bound tin *)
    pose proof (tin t0 N) as Hlow.
    assert (Hrho0 : 0 <= rho) by (unfold rho; apply Rmult_le_pos; [ lra | exact Hpowpos ]).
    assert (Herho : 0 <= e * rho) by (apply Rmult_le_pos; lra).
    assert (HTIn2 : Cmod (TI (seqT t0 N)) <= 2 * (e * rho) * rho)
      by (eapply Rle_trans; [ exact HTIn | apply Rmult_le_compat_l; [ lra | exact Hperim ] ]).
    (* Cmod(TI t0) (/4)^N <= 2 e rho^2 = 2 e (3 D0 (/2)^N)^2 = 18 e D0^2 (/4)^N *)
    assert (Hpow4 : (/ 2) ^ N * (/ 2) ^ N = (/ 4) ^ N)
      by (rewrite <- Rpow_mult_distr; f_equal; lra).
    assert (Hcm : Cmod (TI t0) * (/ 4) ^ N <= 18 * (D0 * D0) * e * (/ 4) ^ N).
    { eapply Rle_trans; [ exact Hlow | ].
      eapply Rle_trans; [ exact HTIn2 | ].
      unfold rho; rewrite <- Hpow4; nra. }
    assert (Hp4pos : 0 < (/ 4) ^ N) by (apply pow_lt; lra).
    apply Rmult_le_reg_r with ((/ 4) ^ N); [ exact Hp4pos | exact Hcm ]. }
  (* conclude *)
  assert (HTImod : Cmod (TI t0) = 0).
  { apply (le_all_eps (Cmod (TI t0)) (18 * (D0 * D0)));
      [ apply Cmod_nonneg | apply Rmult_le_pos; [ lra | apply Rmult_le_pos; exact HD0 ] | exact Hall ]. }
  apply Cmod0; exact HTImod.
Qed.

Theorem goursat : forall v0 v1 v2, tri_int h Hcont v0 v1 v2 = C0.
Proof. intros v0 v1 v2; exact (TI_zero (v0, v1, v2)). Qed.

Print Assumptions goursat.

End Goursat.

(* ================================================================= *)
(*  END CGoursat.v — Goursat's theorem (C2a-4b complete).              *)
(* ================================================================= *)
