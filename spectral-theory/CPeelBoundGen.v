(* ================================================================= *)
(*  CPeelBoundGen.v  --  CPeelBound with the 1/4 made a PARAMETER.     *)
(*                                                                    *)
(*  CPeelBound fixes the peel radius at Rr/4 and gets the clean 1/3    *)
(*  per factor.  Its own header explains why 1/4 is arbitrary:         *)
(*                                                                    *)
(*      with |rho| <= a.Rr the ratio is a/(1-a), which is < 1 exactly  *)
(*      when a < 1/2, so a = 1/4 is a convenient strict choice.        *)
(*                                                                    *)
(*  For counting zeta zeros in a disk centred at 1.1 + i t the choice  *)
(*  is NOT free.  The count disk must reach sigma = 1/2, so its radius *)
(*  is at least a - 1/2; the bound circle must then have radius        *)
(*  > (a - 1/2)/alpha, and its left edge sits at a - (a-1/2)/alpha.    *)
(*  At alpha = 1/4 and a = 1.1 that is 2 - 3a = -1.3, which is OUTSIDE *)
(*  the half-plane Re s > -1 where the trapezoid Euler-Maclaurin       *)
(*  representation of zeta converges.  At alpha = 9/20 it is -0.23.    *)
(*  So generalising 1/4 is mandatory, not cosmetic.                    *)
(*                                                                    *)
(*  Everything below is CPeelBound with                                *)
(*      Rr/4  -->  alpha * Rr,   3*Rr/4 --> (1-alpha) * Rr,            *)
(*      3     -->  q := (1-alpha)/alpha,   ln 3 --> ln q.              *)
(*  CCentreBound.centre_bound is alpha-independent and reused as is.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CPathIntegral
        CWindingOffCenter JensenMultiZero CZeroListFactor CCentreBound.
Open Scope R_scope.

Section PeelGen.

Variable alpha : R.
Hypothesis Halpha : 0 < alpha < / 2.

(* the per-factor gain *)
Definition qpeel : R := (1 - alpha) / alpha.

Lemma alpha_pos : 0 < alpha.
Proof. destruct Halpha; lra. Qed.

Lemma one_minus_alpha_pos : 0 < 1 - alpha.
Proof. destruct Halpha; lra. Qed.

Lemma qpeel_gt1 : 1 < qpeel.
Proof.
  destruct Halpha as [H1 H2]. unfold qpeel.
  apply (Rmult_lt_reg_r alpha); [ exact H1 | ].
  replace ((1 - alpha) / alpha * alpha) with (1 - alpha) by (field; lra).
  lra.
Qed.

Lemma qpeel_pos : 0 < qpeel.
Proof. pose proof qpeel_gt1; lra. Qed.

Lemma ln_qpeel_pos : 0 < ln qpeel.
Proof. rewrite <- ln_1. apply ln_increasing; [ lra | apply qpeel_gt1 ]. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the peeled product: big on the circle, small at the centre     *)
(* ----------------------------------------------------------------- *)
Lemma prodfac_circle_lb_gen : forall (l : list C) (Rr t : R), 0 < Rr ->
  (forall w, In w l -> Cmod w <= alpha * Rr) ->
  ((1 - alpha) * Rr) ^ (length l) <= Cmod (prodfac l (arc Rr t)).
Proof.
  pose proof alpha_pos as Hap. pose proof one_minus_alpha_pos as Hmp.
  induction l as [| w l' IH]; intros Rr t HR Hsm.
  - cbn [prodfac length pow]. rewrite Cmod_C1. lra.
  - cbn [prodfac length pow]. rewrite Cmod_mul.
    apply Rmult_le_compat.
    + nra.
    + apply pow_le; nra.
    + pose proof (Cmod_rev_triangle (arc Rr t) w) as HT.
      rewrite (Cmod_arc Rr t ltac:(lra)) in HT.
      pose proof (Hsm w (or_introl eq_refl)). nra.
    + apply IH; [ exact HR | intros r Hr; apply Hsm; right; exact Hr ].
Qed.

Lemma prodfac_centre_ub_gen : forall (l : list C) (Rr : R), 0 <= Rr ->
  (forall w, In w l -> Cmod w <= alpha * Rr) ->
  Cmod (prodfac l C0) <= (alpha * Rr) ^ (length l).
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
(*  B.  each peeled factor costs the cofactor a clean 1/qpeel          *)
(* ----------------------------------------------------------------- *)
Theorem peel_decay_gen : forall (F G : C -> C) (Rr M : R) (l : list C),
  0 < Rr ->
  (forall z, F z = Cmul (prodfac l z) (G z)) ->
  ptcont G ->
  disk_holo G (Rr + 1) ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  (forall w, In w l -> Cmod w <= alpha * Rr) ->
  Cmod (F C0) <= 2 * M / qpeel ^ (length l).
Proof.
  intros F G Rr M l HR Hid Hptc Hhol HM Hsm.
  pose proof alpha_pos as Hap. pose proof one_minus_alpha_pos as Hmp.
  pose proof qpeel_pos as Hqp.
  set (n := length l).
  set (A := (alpha * Rr) ^ n). set (P := ((1 - alpha) * Rr) ^ n).
  assert (HA : 0 < A) by (unfold A; apply pow_lt; nra).
  assert (HP : 0 < P) by (unfold P; apply pow_lt; nra).
  assert (Hqn : 0 < qpeel ^ n) by (apply pow_lt; exact Hqp).
  assert (HPA : P = qpeel ^ n * A).
  { unfold P, A. rewrite <- Rpow_mult_distr. f_equal.
    unfold qpeel. field. lra. }
  (* the cofactor is small on the circle *)
  assert (HGcirc : forall u, Cmod (G (arc Rr u)) <= M / P).
  { intro u.
    assert (Hlb : P <= Cmod (prodfac l (arc Rr u)))
      by (unfold P, n; apply prodfac_circle_lb_gen; assumption).
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
    by (unfold A, n; apply prodfac_centre_ub_gen; [ lra | assumption ]).
  assert (HF0 : Cmod (F C0) = Cmod (prodfac l C0) * Cmod (G C0))
    by (rewrite (Hid C0); apply Cmod_mul).
  rewrite HF0.
  apply Rle_trans with (A * (2 * (M / P))).
  - apply Rmult_le_compat;
      [ apply Cmod_nonneg | apply Cmod_nonneg | exact Hub | exact HG0 ].
  - assert (HAne : A <> 0) by lra.
    assert (Hqne : qpeel ^ n <> 0) by lra.
    rewrite HPA. apply Req_le. field. split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  so the list length is bounded outright                        *)
(* ----------------------------------------------------------------- *)
Theorem peel_length_bound_gen : forall (F : C -> C) (Rr M : R),
  0 < Rr ->
  F C0 <> C0 ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  exists N : nat, forall (G : C -> C) (l : list C),
    (forall z, F z = Cmul (prodfac l z) (G z)) ->
    ptcont G ->
    disk_holo G (Rr + 1) ->
    (forall w, In w l -> Cmod w <= alpha * Rr) ->
    (length l <= N)%nat.
Proof.
  intros F Rr M HR HF0 HM.
  pose proof qpeel_gt1 as Hq1. pose proof qpeel_pos as Hqp.
  set (c := Cmod (F C0)).
  assert (Hc : 0 < c).
  { unfold c. destruct (Cmod_nonneg (F C0)) as [Hlt | Heq]; [ exact Hlt | ].
    exfalso. apply HF0. apply (proj1 (Cmod0 (F C0))). symmetry. exact Heq. }
  assert (HMnn : 0 <= M)
    by (pose proof (Cmod_nonneg (F (arc Rr 0))); pose proof (HM 0); lra).
  assert (Habsq : Rabs qpeel > 1) by (rewrite Rabs_pos_eq; lra).
  destruct (Pow_x_infinity qpeel Habsq (2 * (2 * M + 1) / c)) as [N HN].
  exists N. intros G l Hid Hptc Hhol Hsm.
  destruct (Nat.lt_ge_cases (length l) (S N)) as [Hlt | Hge]; [ lia | exfalso ].
  assert (Hge' : (length l >= N)%nat) by lia.
  pose proof (HN (length l) Hge') as Hqn.
  rewrite Rabs_pos_eq in Hqn by (apply pow_le; lra).
  assert (Hqnp : 0 < qpeel ^ (length l)) by (apply pow_lt; lra).
  pose proof (peel_decay_gen F G Rr M l HR Hid Hptc Hhol HM Hsm) as Hdec.
  fold c in Hdec.
  assert (H1 : c * qpeel ^ (length l) <= 2 * M).
  { replace (2 * M) with (2 * M / qpeel ^ (length l) * qpeel ^ (length l))
      by (field; lra).
    apply Rmult_le_compat_r; [ lra | exact Hdec ]. }
  assert (H2 : 2 * (2 * M + 1) <= c * qpeel ^ (length l)).
  { replace (2 * (2 * M + 1)) with (c * (2 * (2 * M + 1) / c)) by (field; lra).
    apply Rmult_le_compat_l; [ lra | apply Rge_le; exact Hqn ]. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the same inequality, read as a COUNTING bound                  *)
(* ----------------------------------------------------------------- *)
Lemma ln_mono_gen : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left; apply ln_increasing; assumption.
  - rewrite Heq; apply Rle_refl.
Qed.

Theorem peel_count_explicit_gen : forall (F G : C -> C) (Rr M : R) (l : list C),
  0 < Rr ->
  F C0 <> C0 ->
  (forall z, F z = Cmul (prodfac l z) (G z)) ->
  ptcont G ->
  disk_holo G (Rr + 1) ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  (forall w, In w l -> Cmod w <= alpha * Rr) ->
  INR (length l) <= ln (2 * M / Cmod (F C0)) / ln qpeel.
Proof.
  intros F G Rr M l HR HF0 Hid Hptc Hhol HM Hsm.
  pose proof qpeel_gt1 as Hq1. pose proof ln_qpeel_pos as Hlnq.
  set (c := Cmod (F C0)). set (n := length l).
  assert (Hc : 0 < c).
  { unfold c. destruct (Cmod_nonneg (F C0)) as [Hlt | Heq]; [ exact Hlt | ].
    exfalso. apply HF0. apply (proj1 (Cmod0 (F C0))). symmetry. exact Heq. }
  assert (Hqn : 0 < qpeel ^ n) by (apply pow_lt; lra).
  pose proof (peel_decay_gen F G Rr M l HR Hid Hptc Hhol HM Hsm) as Hdec.
  fold c n in Hdec.
  assert (Hpow : qpeel ^ n <= 2 * M / c).
  { apply (Rmult_le_reg_l c); [ exact Hc | ].
    replace (c * (2 * M / c)) with (2 * M) by (field; lra).
    replace (2 * M) with (2 * M / qpeel ^ n * qpeel ^ n) by (field; lra).
    apply Rmult_le_compat_r; [ lra | exact Hdec ]. }
  assert (Hlnp : ln (qpeel ^ n) <= ln (2 * M / c))
    by (apply ln_mono_gen; assumption).
  rewrite (ln_pow qpeel ltac:(lra) n) in Hlnp.
  apply (Rmult_le_reg_r (ln qpeel)); [ exact Hlnq | ].
  replace (ln (2 * M / c) / ln qpeel * ln qpeel) with (ln (2 * M / c))
    by (field; lra).
  exact Hlnp.
Qed.

End PeelGen.

Print Assumptions peel_count_explicit_gen.

(* ================================================================= *)
(*  END CPeelBoundGen.v                                               *)
(* ================================================================= *)
