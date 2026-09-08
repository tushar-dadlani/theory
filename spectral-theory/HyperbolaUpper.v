(* ================================================================= *)
(*  HyperbolaUpper.v  --  L(1,chi) <> 0 for a real character.         *)
(*                                                                    *)
(*  Assume L(1,chi) = 0.  Then sum_{n<=N*N} f(n)/sqrt n is BOUNDED,   *)
(*  while HyperbolaLower.B_diverges says it is at least ln (N+1).     *)
(*                                                                    *)
(*  Setting L1 = 0 at the start (rather than proving the full          *)
(*  asymptotic 2 sqrt x L + O(1)) removes the main term from every     *)
(*  estimate: what is left is three error terms, each O(1).            *)
(*                                                                    *)
(*  The two estimates that carry the argument:                         *)
(*                                                                    *)
(*    d <= N region:  |ach d (RS bh (X/d)) - 2N w1s d - Csq ach d|     *)
(*                      <= bh d * 4/sqrt N                             *)
(*      -- the floor error sqrt(X/d) - N/sqrt d is at most 1/sqrt(X/d),*)
(*      and X/d >= N there, so summing against RS bh N ~ 2 sqrt N      *)
(*      gives 8 + O(1) rather than the O(sqrt x) of the unsplit sum.   *)
(*                                                                    *)
(*    far region:  pieces 2 and 3 FUSE, because RS bh N occurs in both:*)
(*        P2 - P3 = sum_{e<=N} bh e (RS ach (X/e) - RS ach N)          *)
(*      and both inner sums are within 2p/sqrt(N+1) of the same limit  *)
(*      Lchih, since X/e >= N.  That difference-of-tails is the whole  *)
(*      reason the hyperbola works; neither piece is bounded alone.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory List.
Require Import CRealChar CRealCharPos SqrtSumAsym RAbelSum CharTailBound
        HyperbolaSplit HyperbolaLower HyperbolaDouble HyperbolaBridges.
Open Scope R_scope.

Lemma bh_nonneg : forall e, 0 <= bh e.
Proof.
  intro e. destruct e as [| e].
  - unfold bh. rewrite INR_0, sqrt_0, Rinv_0. apply Rle_refl.
  - apply Rlt_le, Rinv_0_lt_compat, sqrtn_pos; lia.
Qed.

Lemma abs_split3 : forall x a b : R, Rabs x <= Rabs (x - a - b) + Rabs a + Rabs b.
Proof.
  intros x a b.
  replace (Rabs x) with (Rabs ((x - a - b) + a + b)) by (f_equal; ring).
  eapply Rle_trans; [ apply Rabs_triang | ].
  apply Rplus_le_compat_r. apply Rabs_triang.
Qed.

Lemma Hdiv_ge : forall N e, (1 <= e <= N)%nat -> (N <= N * N / e)%nat.
Proof. intros N e He. apply le_div_iff; [ lia | nia ]. Qed.

Lemma sqrt_INR_mono : forall a b, (a <= b)%nat -> sqrt (INR a) <= sqrt (INR b).
Proof. intros a b H. apply sqrt_le_1_alt, le_INR; lia. Qed.

(* the floor error in sqrt (X/d) *)
Lemma sqrt_floor_le : forall N d, (1 <= N)%nat -> (1 <= d <= N)%nat ->
  Rabs (sqrt (INR (N * N / d)) - INR N / sqrt (INR d))
  <= / sqrt (INR (N * N / d)).
Proof.
  intros N d HN Hd.
  assert (Hu : (N <= N * N / d)%nat) by (apply Hdiv_ge; lia).
  set (u := (N * N / d)%nat).
  set (sd := sqrt (INR d)). set (su := sqrt (INR u)). set (sv := INR N / sd).
  assert (Hsd : 0 < sd) by (apply sqrtn_pos; lia).
  assert (Hsu : 0 < su) by (apply sqrtn_pos; lia).
  assert (Hsd0 : sd <> 0) by (apply Rgt_not_eq; exact Hsd).
  assert (Hsq : sd * sd = INR d) by (unfold sd; apply sqrt_sqrt; apply pos_INR).
  assert (Hsuq : su * su = INR u) by (unfold su; apply sqrt_sqrt; apply pos_INR).
  assert (HN1 : 1 <= INR N) by (apply INR_ge1; lia).
  assert (Hd1 : 1 <= INR d) by (apply INR_ge1; lia).
  assert (Hsv : 0 < sv).
  { unfold sv, Rdiv. apply Rmult_lt_0_compat;
      [ lra | apply Rinv_0_lt_compat; exact Hsd ]. }
  assert (Hsvsq : sv * sv * (sd * sd) = INR N * INR N).
  { unfold sv, Rdiv.
    replace (INR N * / sd * (INR N * / sd) * (sd * sd))
      with (INR N * INR N * (/ sd * sd) * (/ sd * sd)) by ring.
    rewrite Rinv_l by exact Hsd0. ring. }
  rewrite Hsq in Hsvsq.
  assert (Hmod : (N * N = d * u + (N * N) mod d)%nat)
    by (unfold u; apply Nat.div_mod_eq).
  assert (Hmlt : ((N * N) mod d < d)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (HR : INR N * INR N = INR d * INR u + INR ((N * N) mod d)).
  { rewrite <- mult_INR, <- mult_INR, <- plus_INR. f_equal. exact Hmod. }
  assert (Hm0 : 0 <= INR ((N * N) mod d)) by apply pos_INR.
  assert (Hmd : INR ((N * N) mod d) < INR d) by (apply lt_INR; lia).
  assert (Heq : (sv * sv - INR u) * INR d = INR ((N * N) mod d)) by nra.
  assert (Hgap : 0 <= sv * sv - INR u <= 1) by nra.
  assert (Hle : su <= sv) by nra.
  rewrite Rabs_left1 by lra.
  apply (Rmult_le_reg_r su); [ exact Hsu | ].
  rewrite Rinv_l by (apply Rgt_not_eq; exact Hsu).
  nra.
Qed.

Section Upper.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ZmodOrder.ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.
Hypothesis Hreal : forall n,
  ComplexField.Cconj (DirichletModP.dchar p g A n) = DirichletModP.dchar p g A n.

Notation LH := (Lchih p g A Hp Hg Hord HA Hreal).
Notation L1 := (Lchi1 p g A Hp Hg Hord HA Hreal).
Notation ac := (ach p g A).
Notation ws := (w1s p g A).

Lemma ach_abs : forall d, (1 <= d)%nat -> Rabs (ac d) <= bh d.
Proof.
  intros d Hd. unfold ach, bh, Rdiv.
  assert (Hs : 0 < sqrt (INR d)) by (apply sqrtn_pos; lia).
  assert (Hi : 0 < / sqrt (INR d)) by (apply Rinv_0_lt_compat; exact Hs).
  rewrite Rabs_mult, (Rabs_right (/ sqrt (INR d))) by (apply Rle_ge; lra).
  assert (H1 : Rabs (IZR (chz p g A d)) <= 1).
  { rewrite <- abs_IZR. replace 1 with (IZR 1) by reflexivity. apply IZR_le.
    destruct (chz_values p g A d) as [E | [E | E]]; rewrite E; cbn; lia. }
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the d <= N region                                                 *)
(* ----------------------------------------------------------------- *)

Lemma P1_pointwise : forall N d, (1 <= N)%nat -> (1 <= d <= N)%nat ->
  Rabs (ac d * RS bh (N * N / d)%nat - 2 * INR N * ws d - Csq * ac d)
  <= bh d * (4 / sqrt (INR N)).
Proof.
  intros N d HN Hd.
  assert (Hu : (N <= N * N / d)%nat) by (apply Hdiv_ge; lia).
  set (u := (N * N / d)%nat).
  assert (Hu1 : (1 <= u)%nat) by lia.
  set (sd := sqrt (INR d)). set (su := sqrt (INR u)).
  assert (Hsd : 0 < sd) by (apply sqrtn_pos; lia).
  assert (Hsu : 0 < su) by (apply sqrtn_pos; lia).
  assert (HsN : 0 < sqrt (INR N)) by (apply sqrtn_pos; lia).
  assert (Hsd0 : sd <> 0) by (apply Rgt_not_eq; exact Hsd).
  assert (Hsq : sd * sd = INR d) by (unfold sd; apply sqrt_sqrt; apply pos_INR).
  (* the algebraic decomposition *)
  assert (Hid : 2 * INR N * ws d = 2 * ac d * (INR N / sd)).
  { unfold w1s, ach, Rdiv. fold sd. rewrite <- Hsq, Rinv_mult. ring. }
  assert (Hdec : ac d * RS bh u - 2 * INR N * ws d - Csq * ac d
                 = ac d * (RS bh u - 2 * su - Csq)
                   + 2 * ac d * (su - INR N / sd)).
  { rewrite Hid. ring. }
  rewrite Hdec.
  (* bound each half *)
  assert (Hab : Rabs (ac d) <= bh d) by (apply ach_abs; lia).
  assert (Hbh0 : 0 <= bh d) by apply bh_nonneg.
  assert (Hr1 : Rabs (RS bh u - 2 * su - Csq) <= 2 / su).
  { unfold su. apply bh_asym; lia. }
  assert (Hr2 : Rabs (su - INR N / sd) <= / su).
  { unfold su, sd, u. apply sqrt_floor_le; [ lia | lia ]. }
  assert (Hsu0 : 0 < / su) by (apply Rinv_0_lt_compat; exact Hsu).
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult, (Rabs_right 2) by lra.
  assert (Hstep : Rabs (ac d) * Rabs (RS bh u - 2 * su - Csq)
                  + 2 * Rabs (ac d) * Rabs (su - INR N / sd)
                  <= bh d * (2 / su) + 2 * (bh d * / su)).
  { assert (0 <= Rabs (ac d)) by apply Rabs_pos.
    assert (0 <= Rabs (RS bh u - 2 * su - Csq)) by apply Rabs_pos.
    assert (0 <= Rabs (su - INR N / sd)) by apply Rabs_pos.
    assert (0 <= 2 / su) by (unfold Rdiv; lra).
    nra. }
  eapply Rle_trans; [ exact Hstep | ].
  (* bh d * (4 / su) <= bh d * (4 / sqrt (INR N)) *)
  assert (Hmon : / su <= / sqrt (INR N)).
  { apply Rinv_le_contravar; [ exact HsN | ].
    unfold su. apply sqrt_INR_mono. lia. }
  unfold Rdiv. nra.
Qed.

Lemma P1_err : forall N, (1 <= N)%nat ->
  Rabs (RS (fun d => ac d * RS bh (N * N / d)%nat) N
        - 2 * INR N * RS ws N - Csq * RS ac N)
  <= (4 / sqrt (INR N)) * RS bh N.
Proof.
  intros N HN.
  assert (Hrw : RS (fun d => ac d * RS bh (N * N / d)%nat) N
                - 2 * INR N * RS ws N - Csq * RS ac N
                = RS (fun d => ac d * RS bh (N * N / d)%nat
                               - 2 * INR N * ws d - Csq * ac d) N).
  { rewrite <- (RS_scal (2 * INR N) ws N), <- (RS_scal Csq ac N).
    rewrite <- RS_minus, <- RS_minus. apply RS_ext. intros d Hd. ring. }
  rewrite Hrw.
  eapply Rle_trans.
  - apply (RS_abs_le _ (fun d => bh d * (4 / sqrt (INR N))) N).
    intros d Hd. apply P1_pointwise; [ exact HN | exact Hd ].
  - rewrite (RS_ext (fun d => bh d * (4 / sqrt (INR N)))
                    (fun d => (4 / sqrt (INR N)) * bh d) N) by (intros; ring).
    rewrite RS_scal. apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  the far region: pieces 2 and 3 fuse                               *)
(* ----------------------------------------------------------------- *)

Lemma P23_bound : forall N, (1 <= N)%nat ->
  Rabs (RS (fun e => bh e * RS ac (N * N / e)%nat) N - RS ac N * RS bh N)
  <= (4 * INR p / sqrt (INR (S N))) * RS bh N.
Proof.
  intros N HN.
  assert (Hp0 : 0 <= INR p) by apply pos_INR.
  assert (HsN : 0 < sqrt (INR (S N))) by (apply sqrtn_pos; lia).
  assert (Hrw : RS (fun e => bh e * RS ac (N * N / e)%nat) N - RS ac N * RS bh N
                = RS (fun e => bh e * (RS ac (N * N / e)%nat - RS ac N)) N).
  { rewrite <- (RS_scal (RS ac N) bh N), <- RS_minus.
    apply RS_ext. intros e He. ring. }
  rewrite Hrw.
  eapply Rle_trans.
  - apply (RS_abs_le _ (fun e => bh e * (4 * INR p / sqrt (INR (S N)))) N).
    intros e He.
    assert (Hue : (N <= N * N / e)%nat) by (apply Hdiv_ge; lia).
    assert (H1 : Rabs (RS ac (N * N / e)%nat - LH)
                 <= 2 * INR p / sqrt (INR (S N))).
    { eapply Rle_trans; [ apply ach_tail; lia | ].
      unfold Rdiv. apply Rmult_le_compat_l; [ lra | ].
      apply Rinv_le_contravar; [ exact HsN | apply sqrt_INR_mono; lia ]. }
    assert (H2 : Rabs (RS ac N - LH) <= 2 * INR p / sqrt (INR (S N)))
      by (apply ach_tail; lia).
    rewrite Rabs_mult, (Rabs_right (bh e)) by (apply Rle_ge, bh_nonneg).
    apply Rmult_le_compat_l; [ apply bh_nonneg | ].
    replace (RS ac (N * N / e)%nat - RS ac N)
      with ((RS ac (N * N / e)%nat - LH) + - (RS ac N - LH)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_Ropp.
    unfold Rdiv in *. lra.
  - rewrite (RS_ext (fun e => bh e * (4 * INR p / sqrt (INR (S N))))
                    (fun e => (4 * INR p / sqrt (INR (S N))) * bh e) N)
      by (intros; ring).
    rewrite RS_scal. apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  assembly                                                          *)
(* ----------------------------------------------------------------- *)

Definition Kup : R :=
  (8 + 4 * (Rabs Csq + 2)) + 4 * INR p + Rabs Csq * (Rabs LH + 2 * INR p)
  + (8 * INR p + 4 * INR p * (Rabs Csq + 2)).

Theorem hyper_upper : L1 = 0 ->
  forall N, (1 <= N)%nat -> RS (Bt p g A) (N * N) <= Kup.
Proof.
  intros Hz N HN.
  assert (Hp0 : 0 <= INR p) by apply pos_INR.
  assert (HsN1 : 1 <= sqrt (INR N)) by (apply sqrt_INR_ge1; lia).
  assert (HsSN1 : 1 <= sqrt (INR (S N))) by (apply sqrt_INR_ge1; lia).
  assert (HsNle : sqrt (INR N) <= sqrt (INR (S N))) by (apply sqrt_INR_mono; lia).
  assert (Hbb : RS bh N <= 2 * sqrt (INR N) + Rabs Csq + 2)
    by (apply bh_bounded; lia).
  assert (Hbb0 : 0 <= RS bh N).
  { rewrite <- (RS_zero N). apply RS_le. intros n Hn. apply bh_nonneg. }
  (* decomposition *)
  rewrite (Bt_double p g A (N * N)), (hyper_split ac bh N).
  pose proof (P1_err N HN) as E1.
  pose proof (P23_bound N HN) as E2.
  (* the main term vanishes *)
  assert (Hw : Rabs (2 * INR N * RS ws N) <= 4 * INR p).
  { assert (Hwt : Rabs (RS ws N - L1) <= 2 * INR p / INR (S N))
      by (apply w1s_tail; lia).
    rewrite Hz, Rminus_0_r in Hwt.
    assert (HN1 : 1 <= INR N) by (apply INR_ge1; lia).
    assert (HSN : INR (S N) = INR N + 1) by (rewrite S_INR; ring).
    assert (Hpos : 0 < INR (S N)) by lra.
    rewrite Rabs_mult, (Rabs_right (2 * INR N)) by (apply Rle_ge; lra).
    assert (Hstep : 2 * INR N * Rabs (RS ws N) <= 2 * INR N * (2 * INR p / INR (S N)))
      by nra.
    assert (Hfin : 2 * INR N * (2 * INR p / INR (S N)) <= 4 * INR p).
    { unfold Rdiv. apply (Rmult_le_reg_r (INR (S N))); [ exact Hpos | ].
      replace (2 * INR N * (2 * INR p * / INR (S N)) * INR (S N))
        with (4 * INR N * INR p * (/ INR (S N) * INR (S N))) by ring.
      rewrite Rinv_l by (apply Rgt_not_eq; exact Hpos). nra. }
    lra. }
  assert (Hac : Rabs (Csq * RS ac N) <= Rabs Csq * (Rabs LH + 2 * INR p)).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; [ apply Rabs_pos | ].
    apply ach_bounded; lia. }
  (* piece 1 *)
  assert (HP1 : Rabs (RS (fun d => ac d * RS bh (N * N / d)%nat) N)
                <= (8 + 4 * (Rabs Csq + 2)) + 4 * INR p
                   + Rabs Csq * (Rabs LH + 2 * INR p)).
  { assert (Hsplit : Rabs (RS (fun d => ac d * RS bh (N * N / d)%nat) N)
      <= Rabs (RS (fun d => ac d * RS bh (N * N / d)%nat) N
               - 2 * INR N * RS ws N - Csq * RS ac N)
         + Rabs (2 * INR N * RS ws N) + Rabs (Csq * RS ac N)).
    { apply abs_split3. }
    assert (Herr : (4 / sqrt (INR N)) * RS bh N <= 8 + 4 * (Rabs Csq + 2)).
    { assert (Hinv : 0 < / sqrt (INR N)) by (apply Rinv_0_lt_compat; lra).
      assert (Hi1 : / sqrt (INR N) <= 1)
        by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
      assert (Hkey : / sqrt (INR N) * (2 * sqrt (INR N)) = 2).
      { replace (/ sqrt (INR N) * (2 * sqrt (INR N)))
          with (2 * (/ sqrt (INR N) * sqrt (INR N))) by ring.
        rewrite Rinv_l by lra. ring. }
      assert (Hc0 : 0 <= Rabs Csq) by apply Rabs_pos.
      unfold Rdiv. nra. }
    lra. }
  (* piece 2+3 *)
  assert (HP23 : Rabs (RS (fun e => bh e * RS ac (N * N / e)%nat) N
                       - RS ac N * RS bh N)
                 <= 8 * INR p + 4 * INR p * (Rabs Csq + 2)).
  { eapply Rle_trans; [ exact E2 | ].
    assert (Hinv : 0 < / sqrt (INR (S N))) by (apply Rinv_0_lt_compat; lra).
    assert (Hi1 : / sqrt (INR (S N)) <= 1)
      by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
    assert (Hkey : / sqrt (INR (S N)) * (2 * sqrt (INR N)) <= 2).
    { assert (H2 : 2 * sqrt (INR N) <= 2 * sqrt (INR (S N))) by lra.
      assert (H3 : / sqrt (INR (S N)) * (2 * sqrt (INR (S N))) = 2).
      { replace (/ sqrt (INR (S N)) * (2 * sqrt (INR (S N))))
          with (2 * (/ sqrt (INR (S N)) * sqrt (INR (S N)))) by ring.
        rewrite Rinv_l by lra. ring. }
      nra. }
    assert (Hc0 : 0 <= Rabs Csq) by apply Rabs_pos.
    unfold Rdiv.
    assert (Hs1 : 4 * INR p * / sqrt (INR (S N)) * RS bh N
                  <= 4 * INR p * / sqrt (INR (S N))
                     * (2 * sqrt (INR N) + Rabs Csq + 2)).
    { apply Rmult_le_compat_l; [ apply Rmult_le_pos; lra | exact Hbb ]. }
    assert (Hs2 : 4 * INR p * / sqrt (INR (S N))
                  * (2 * sqrt (INR N) + Rabs Csq + 2)
                  = 4 * INR p * (/ sqrt (INR (S N)) * (2 * sqrt (INR N)))
                    + 4 * INR p * (/ sqrt (INR (S N)) * (Rabs Csq + 2))) by ring.
    assert (Hs3 : 4 * INR p * (/ sqrt (INR (S N)) * (2 * sqrt (INR N)))
                  <= 4 * INR p * 2)
      by (apply Rmult_le_compat_l; [ lra | exact Hkey ]).
    assert (Hs4 : 4 * INR p * (/ sqrt (INR (S N)) * (Rabs Csq + 2))
                  <= 4 * INR p * (Rabs Csq + 2))
      by (apply Rmult_le_compat_l; [ lra | nra ]).
    lra. }
  unfold Kup.
  pose proof (Rle_abs (RS (fun d => ac d * RS bh (N * N / d)%nat) N)) as A1.
  pose proof (Rle_abs (RS (fun e => bh e * RS ac (N * N / e)%nat) N
                       - RS ac N * RS bh N)) as A2.
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the contradiction                                                 *)
(* ----------------------------------------------------------------- *)

Theorem Lchi1_ne0 : L1 <> 0.
Proof.
  intro Hz.
  assert (Hr : 0 < exp Kup) by apply exp_pos.
  destruct (archimed (exp Kup)) as [Ha _].
  assert (Hz0 : (0 < up (exp Kup))%Z).
  { apply lt_IZR. change (IZR 0) with 0. lra. }
  set (N := Z.to_nat (up (exp Kup))).
  assert (HN1 : (1 <= N)%nat) by (unfold N; lia).
  assert (HNR : INR N = IZR (up (exp Kup)))
    by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
  assert (Hbig : exp Kup < INR (S N)).
  { rewrite S_INR, HNR. lra. }
  assert (Hlow : ln (INR (S N)) <= RS (Bt p g A) (N * N))
    by (apply (B_diverges p g A Hp Hg Hord Hreal); exact HN1).
  assert (Hup : RS (Bt p g A) (N * N) <= Kup) by (apply hyper_upper; assumption).
  assert (Hln : Kup < ln (INR (S N))).
  { replace Kup with (ln (exp Kup)) by apply ln_exp.
    apply ln_increasing; [ exact Hr | exact Hbig ]. }
  lra.
Qed.

End Upper.

Print Assumptions Lchi1_ne0.

(* ================================================================= *)
(*  END HyperbolaUpper.v                                              *)
(* ================================================================= *)
