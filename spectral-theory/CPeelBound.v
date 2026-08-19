(* ================================================================= *)
(*  CPeelBound.v  —  every peel list is SHORT.                         *)
(*                                                                    *)
(*    peel_decay : F = prodfac l . G with every zero in l of modulus   *)
(*      <= Rr/4, G regular on the disk, |F| <= M on the circle |z|=Rr  *)
(*        ==>  Cmod (F C0) <= 2 * M / 3 ^ (length l).                  *)
(*                                                                    *)
(*    peel_length_bound : if moreover F C0 <> C0, the length of ANY    *)
(*      such l is bounded by one N depending only on F, Rr, M.         *)
(*                                                                    *)
(*    peel_count_explicit : INR (length l) <= ln (2 M / |F(0)|) / ln 3.*)
(*                                                                    *)
(*  THE MECHANISM, in one line: each peeled factor (z - rho) is at      *)
(*  most Rr/4 at the centre but at least 3Rr/4 on the circle, so every  *)
(*  factor costs the cofactor a clean 1/3.  Precisely --                *)
(*                                                                    *)
(*    on |z| = Rr :  |prodfac l| >= (3Rr/4)^n,  so |G| <= M/(3Rr/4)^n  *)
(*    at the centre: |G(0)| <= 2 M /(3Rr/4)^n     (CCentreBound)       *)
(*    at the centre: |prodfac l C0| = prod |rho_i| <= (Rr/4)^n         *)
(*    multiply     : |F(0)| <= 2 M (Rr/4)^n /(3Rr/4)^n = 2 M / 3^n.    *)
(*                                                                    *)
(*  WHY THIS MATTERS.  |F(0)| is a fixed positive number, so n cannot   *)
(*  grow: the zero list is bounded outright.  No isolation, no          *)
(*  accumulation point, no compactness, no Bolzano-Weierstrass and no   *)
(*  identity theorem enter anywhere.  peel_count_explicit is already    *)
(*  the counting bound n(r) = O(ln M) -- fed XiGrowthBound.XiC_growth   *)
(*  it gives n(r) = O(r ln r) for xi without Jensen's formula at all.   *)
(*                                                                    *)
(*  The 1/3 needs the zeros inside Rr/4 rather than Jensen's Rr/2: with *)
(*  |rho| <= a.Rr the ratio is a/(1-a), which is < 1 exactly when       *)
(*  a < 1/2, so a = 1/4 is a convenient strict choice.  Axiom-clean.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CPathIntegral
        CWindingOffCenter JensenMultiZero CZeroListFactor CCentreBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the peeled product: big on the circle, small at the centre     *)
(* ----------------------------------------------------------------- *)
Lemma prodfac_circle_lb : forall (l : list C) (Rr t : R), 0 < Rr ->
  (forall w, In w l -> Cmod w <= Rr / 4) ->
  (3 * Rr / 4) ^ (length l) <= Cmod (prodfac l (arc Rr t)).
Proof.
  induction l as [| w l' IH]; intros Rr t HR Hsm.
  - cbn [prodfac length pow]. rewrite Cmod_C1. lra.
  - cbn [prodfac length pow]. rewrite Cmod_mul.
    apply Rmult_le_compat.
    + lra.
    + apply pow_le; lra.
    + pose proof (Cmod_rev_triangle (arc Rr t) w) as HT.
      rewrite (Cmod_arc Rr t ltac:(lra)) in HT.
      pose proof (Hsm w (or_introl eq_refl)). lra.
    + apply IH; [ exact HR | intros r Hr; apply Hsm; right; exact Hr ].
Qed.

Lemma prodfac_centre_ub : forall (l : list C) (Rr : R), 0 <= Rr ->
  (forall w, In w l -> Cmod w <= Rr / 4) ->
  Cmod (prodfac l C0) <= (Rr / 4) ^ (length l).
Proof.
  induction l as [| w l' IH]; intros Rr HR Hsm.
  - cbn [prodfac length pow]. rewrite Cmod_C1. lra.
  - cbn [prodfac length pow]. rewrite Cmod_mul.
    assert (HC : Cmod (Cminus C0 w) = Cmod w)
      by (replace (Cminus C0 w) with (Copp w) by ring; apply Cmod_opp).
    rewrite HC. apply Rmult_le_compat.
    + apply Cmod_nonneg.
    + apply Cmod_nonneg.
    + apply Hsm; left; reflexivity.
    + apply IH; [ exact HR | intros r Hr; apply Hsm; right; exact Hr ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  each peeled factor costs the cofactor a clean 1/3              *)
(* ----------------------------------------------------------------- *)
Theorem peel_decay : forall (F G : C -> C) (Rr M : R) (l : list C),
  0 < Rr ->
  (forall z, F z = Cmul (prodfac l z) (G z)) ->
  ptcont G ->
  disk_holo G (Rr + 1) ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  (forall w, In w l -> Cmod w <= Rr / 4) ->
  Cmod (F C0) <= 2 * M / 3 ^ (length l).
Proof.
  intros F G Rr M l HR Hid Hptc Hhol HM Hsm.
  set (n := length l).
  set (A := (Rr / 4) ^ n). set (P := (3 * Rr / 4) ^ n).
  assert (HA : 0 < A) by (unfold A; apply pow_lt; lra).
  assert (HP : 0 < P) by (unfold P; apply pow_lt; lra).
  assert (H3n : 0 < 3 ^ n) by (apply pow_lt; lra).
  assert (HPA : P = 3 ^ n * A)
    by (unfold P, A; replace (3 * Rr / 4) with (3 * (Rr / 4)) by field;
        apply Rpow_mult_distr).
  (* the cofactor is small on the circle *)
  assert (HGcirc : forall u, Cmod (G (arc Rr u)) <= M / P).
  { intro u.
    assert (Hlb : P <= Cmod (prodfac l (arc Rr u)))
      by (unfold P, n; apply prodfac_circle_lb; assumption).
    assert (Hsplit : Cmod (F (arc Rr u))
                     = Cmod (prodfac l (arc Rr u)) * Cmod (G (arc Rr u)))
      by (rewrite (Hid (arc Rr u)); apply Cmod_mul).
    pose proof (HM u) as HMu. rewrite Hsplit in HMu.
    apply (Rmult_le_reg_l P); [ exact HP | ].
    replace (P * (M / P)) with M by (field; lra).
    apply Rle_trans with (Cmod (prodfac l (arc Rr u)) * Cmod (G (arc Rr u)));
      [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | exact Hlb ] | exact HMu ]. }
  (* hence small at the centre *)
  pose proof (centre_bound G Rr (M / P) HR Hptc Hhol HGcirc) as HG0.
  assert (Hub : Cmod (prodfac l C0) <= A)
    by (unfold A, n; apply prodfac_centre_ub; [ lra | assumption ]).
  assert (HF0 : Cmod (F C0) = Cmod (prodfac l C0) * Cmod (G C0))
    by (rewrite (Hid C0); apply Cmod_mul).
  rewrite HF0.
  apply Rle_trans with (A * (2 * (M / P))).
  - apply Rmult_le_compat;
      [ apply Cmod_nonneg | apply Cmod_nonneg | exact Hub | exact HG0 ].
  - assert (HAne : A <> 0) by lra.
    assert (H3ne : 3 ^ n <> 0) by lra.
    rewrite HPA. apply Req_le. field. split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  so the list length is bounded outright                        *)
(* ----------------------------------------------------------------- *)
Theorem peel_length_bound : forall (F : C -> C) (Rr M : R),
  0 < Rr ->
  F C0 <> C0 ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  exists N : nat, forall (G : C -> C) (l : list C),
    (forall z, F z = Cmul (prodfac l z) (G z)) ->
    ptcont G ->
    disk_holo G (Rr + 1) ->
    (forall w, In w l -> Cmod w <= Rr / 4) ->
    (length l <= N)%nat.
Proof.
  intros F Rr M HR HF0 HM.
  set (c := Cmod (F C0)).
  assert (Hc : 0 < c).
  { unfold c. destruct (Cmod_nonneg (F C0)) as [Hlt | Heq]; [ exact Hlt | ].
    exfalso. apply HF0. apply (proj1 (Cmod0 (F C0))). symmetry. exact Heq. }
  assert (HMnn : 0 <= M)
    by (pose proof (Cmod_nonneg (F (arc Rr 0))); pose proof (HM 0); lra).
  assert (Habs3 : Rabs 3 > 1) by (rewrite Rabs_pos_eq; lra).
  destruct (Pow_x_infinity 3 Habs3 (2 * (2 * M + 1) / c)) as [N HN].
  exists N. intros G l Hid Hptc Hhol Hsm.
  destruct (Nat.lt_ge_cases (length l) (S N)) as [Hlt | Hge]; [ lia | exfalso ].
  assert (Hge' : (length l >= N)%nat) by lia.
  pose proof (HN (length l) Hge') as H3.
  rewrite Rabs_pos_eq in H3 by (apply pow_le; lra).
  assert (H3n : 0 < 3 ^ (length l)) by (apply pow_lt; lra).
  pose proof (peel_decay F G Rr M l HR Hid Hptc Hhol HM Hsm) as Hdec.
  fold c in Hdec.
  assert (H1 : c * 3 ^ (length l) <= 2 * M).
  { replace (2 * M) with (2 * M / 3 ^ (length l) * 3 ^ (length l)) by (field; lra).
    apply Rmult_le_compat_r; [ lra | exact Hdec ]. }
  assert (H2 : 2 * (2 * M + 1) <= c * 3 ^ (length l)).
  { replace (2 * (2 * M + 1)) with (c * (2 * (2 * M + 1) / c)) by (field; lra).
    apply Rmult_le_compat_l; [ lra | apply Rge_le; exact H3 ]. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the same inequality, read as a COUNTING bound                  *)
(* ----------------------------------------------------------------- *)
Lemma ln_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left; apply ln_increasing; assumption.
  - rewrite Heq; apply Rle_refl.
Qed.

Theorem peel_count_explicit : forall (F G : C -> C) (Rr M : R) (l : list C),
  0 < Rr ->
  F C0 <> C0 ->
  (forall z, F z = Cmul (prodfac l z) (G z)) ->
  ptcont G ->
  disk_holo G (Rr + 1) ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  (forall w, In w l -> Cmod w <= Rr / 4) ->
  INR (length l) <= ln (2 * M / Cmod (F C0)) / ln 3.
Proof.
  intros F G Rr M l HR HF0 Hid Hptc Hhol HM Hsm.
  set (c := Cmod (F C0)). set (n := length l).
  assert (Hc : 0 < c).
  { unfold c. destruct (Cmod_nonneg (F C0)) as [Hlt | Heq]; [ exact Hlt | ].
    exfalso. apply HF0. apply (proj1 (Cmod0 (F C0))). symmetry. exact Heq. }
  assert (H3n : 0 < 3 ^ n) by (apply pow_lt; lra).
  assert (Hln3 : 0 < ln 3)
    by (rewrite <- ln_1; apply ln_increasing; lra).
  pose proof (peel_decay F G Rr M l HR Hid Hptc Hhol HM Hsm) as Hdec.
  fold c n in Hdec.
  (* 3^n <= 2 M / c *)
  assert (Hpow : 3 ^ n <= 2 * M / c).
  { apply (Rmult_le_reg_l c); [ exact Hc | ].
    replace (c * (2 * M / c)) with (2 * M) by (field; lra).
    replace (2 * M) with (2 * M / 3 ^ n * 3 ^ n) by (field; lra).
    apply Rmult_le_compat_r; [ lra | exact Hdec ]. }
  assert (Hlnp : ln (3 ^ n) <= ln (2 * M / c)) by (apply ln_mono; assumption).
  rewrite (ln_pow 3 ltac:(lra) n) in Hlnp.
  apply (Rmult_le_reg_r (ln 3)); [ exact Hln3 | ].
  replace (ln (2 * M / c) / ln 3 * ln 3) with (ln (2 * M / c)) by (field; lra).
  exact Hlnp.
Qed.

Print Assumptions peel_length_bound.
Print Assumptions peel_count_explicit.
