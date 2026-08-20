(* ================================================================= *)
(*  XiBubBound.v  —  bounding -LBexp, the whole minimum-modulus loss.  *)
(*                                                                    *)
(*    Bxi_le_Bub    : Bxi s <= Bub s := Lxi (8s+8) / ln 3   (0 <= s)   *)
(*    K_le_log      : 2^K < 80 r  ==>  INR K <= 4 ln r                 *)
(*    negLBexp_bound: -LBexp rr del K <= Cu . r . (ln r)^2             *)
(*                                                                    *)
(*  Bxi was only ever bounded at DYADIC points (XiHgrow.xi_Hgrow),     *)
(*  and Bxi's monotonicity is not available -- it would need Tgb       *)
(*  monotone, which nothing proves.  Bub sidesteps both: XiHgrow's     *)
(*  ln4XiM_bound holds for EVERY real u >= 9, and its right-hand side  *)
(*  is literally Lxi (u-1), so Bub is just Lxi rescaled, inheriting    *)
(*  the monotonicity already proved for Lxi.                           *)
(*                                                                    *)
(*  K_le_log is where the dyadic cut pays for itself a second time:    *)
(*  2^K < 80 r turns into INR K . ln 2 < ln (80 r), and ln 2 > 1/2     *)
(*  (Stdlib ln_lt_2) gives INR K <= 4 ln r.  Without a logarithmic     *)
(*  bound on K the Aser K = K(K+1)/2 term would be O(r^3) and the      *)
(*  whole estimate would fail -- this is the one place where a crude   *)
(*  bound on K is fatal rather than merely lossy.                      *)
(*                                                                    *)
(*  THE NESTED LOGARITHM is the only delicate part.  Piece A carries   *)
(*  ln (Bxi (80 r) + 1), and bounding it needs Bxi (80 r) + 1 <= C r^2 *)
(*  so the outer log collapses to 2 ln r + ln C <= 3 ln r.  Getting    *)
(*  there via ln r <= r (rather than any sharper estimate) is what     *)
(*  keeps it elementary: Bub is O(r ln r), hence O(r^2), and that is   *)
(*  all the outer logarithm needs.                                     *)
(*                                                                    *)
(*  Everything lands on a single scalar multiple of r (ln r)^2, which  *)
(*  is exactly what RSubQuad.SubQuad_rln2 consumes.  Axiom-clean.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDyadicSum CDyadicSum2 XiGrowthBound
        RLogPower RSubQuad XiZeroCount XiZeroDensity XiHgrow XiLnBound
        XiLxiMajor XiProdLower.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  Bxi, bounded at every real argument                            *)
(* ----------------------------------------------------------------- *)
Definition Bub (s : R) : R := Lxi (8 * s + 8) / ln 3.

Lemma ln3_pos' : 0 < ln 3.
Proof. pose proof ln3_ge1. lra. Qed.

Lemma Bxi_le_Bub : forall s, 0 <= s -> Bxi s <= Bub s.
Proof.
  intros s Hs. pose proof ln3_pos' as H3.
  unfold Bxi, Bub, Rdiv.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact H3 | ].
  assert (Heq : 4 * XiM (8 * (s + 1))
                = 2 + 4 * (8 * s + 9) ^ 2 * Tgb (8 * s + 9)).
  { rewrite (XiM_eq (8 * (s + 1))).
    replace (8 * (s + 1) + 1) with (8 * s + 9) by ring. reflexivity. }
  rewrite Heq.
  assert (HL : Lxi (8 * s + 8)
               = ln M0 + 2 * ln (8 * s + 9)
                 + (8 * s + 9) / 2 * ln ((8 * s + 9) / PI)).
  { unfold Lxi. replace (8 * s + 8 + 1) with (8 * s + 9) by ring. reflexivity. }
  rewrite HL. apply ln4XiM_bound. lra.
Qed.

Lemma Bxi_nonneg : forall s, 0 <= Bxi s.
Proof.
  intro s. pose proof ln3_pos' as H3.
  pose proof (XiM_pos (8 * (s + 1))) as HX.
  unfold Bxi. apply Rle_mult_inv_pos; [ | exact H3 ].
  rewrite <- ln_1. apply ln_mono_le; [ lra | ].
  unfold XiM in *. pose proof (Tgb_pos (8 * (s + 1) + 1)) as HT.
  pose proof (Rle_0_sqr (8 * (s + 1) + 1)) as Hsq. unfold Rsqr in Hsq.
  assert (0 <= (8 * (s + 1) + 1) ^ 2 * Tgb (8 * (s + 1) + 1))
    by (apply Rmult_le_pos; nra).
  lra.
Qed.

Lemma Bub_mono : forall a b, 0 <= a -> a <= b -> Bub a <= Bub b.
Proof.
  intros a b Ha Hab. pose proof ln3_pos' as H3.
  unfold Bub, Rdiv.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact H3 | ].
  apply Lxi_mono; lra.
Qed.

(* the size of Bub, in the crude form the outer logarithm needs *)
Lemma Bub_le : forall r, 648 <= r ->
  Bub (80 * r) <= ln M0 + 8 * ln r + 2592 * (r * ln r).
Proof.
  intros r Hr. pose proof ln3_ge1 as H3.
  pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
  assert (HLnn : 0 <= Lxi (8 * (80 * r) + 8)) by (apply Lxi_nonneg; lra).
  assert (Hstep : Bub (80 * r) <= Lxi (8 * (80 * r) + 8)).
  { unfold Bub, Rdiv.
    rewrite <- (Rmult_1_r (Lxi (8 * (80 * r) + 8))) at 2.
    apply Rmult_le_compat_l; [ exact HLnn | ].
    rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  apply Rle_trans with (1 := Hstep).
  assert (Hle : 8 * (80 * r) + 8 <= 648 * r) by lra.
  assert (Hln : ln (8 * (80 * r) + 8) <= 2 * ln r).
  { apply Rle_trans with (ln (648 * r));
      [ apply ln_mono_le; lra | apply ln_scal_le; lra ]. }
  assert (Hln0 : 0 <= ln (8 * (80 * r) + 8))
    by (rewrite <- ln_1; apply ln_mono_le; lra).
  pose proof (Lxi_le (8 * (80 * r) + 8) ltac:(lra)) as HL.
  assert (Hpr : (8 * (80 * r) + 8) * ln (8 * (80 * r) + 8) <= 648 * r * (2 * ln r))
    by (apply Rmult_le_compat; lra).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the truncation index is logarithmic                            *)
(* ----------------------------------------------------------------- *)
Lemma K_le_log : forall (K : nat) (r : R), 80 <= r -> 2 ^ K < 80 * r ->
  INR K <= 4 * ln r.
Proof.
  intros K r Hr HK. pose proof ln_lt_2 as H2.
  pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
  assert (Hpos : (0:R) < 2 ^ K) by (apply pow_lt; lra).
  assert (Hln : INR K * ln 2 <= ln (80 * r)).
  { rewrite <- (ln_pow 2 ltac:(lra) K). apply ln_mono_le; lra. }
  assert (H80 : ln (80 * r) <= 2 * ln r) by (apply ln_scal_le; lra).
  assert (HK2 : INR K * ln 2 <= 2 * ln r) by lra.
  apply (Rmult_le_reg_r (ln 2)); [ lra | ].
  apply Rle_trans with (2 * ln r); [ exact HK2 | nra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the nested logarithm collapses                                 *)
(* ----------------------------------------------------------------- *)
Definition Cb : R := Rabs (ln M0) + 2601.
Definition Rbase : R := 2700 + Rabs (ln M0).

Lemma Cb_le_Rbase : Cb <= Rbase.
Proof. unfold Cb, Rbase. lra. Qed.

Lemma lnBxi_le : forall r, Rbase <= r -> ln (Bxi (80 * r) + 1) <= 3 * ln r.
Proof.
  intros r Hr.
  assert (Hr648 : 648 <= r) by (unfold Rbase in Hr; pose proof (Rabs_pos (ln M0)); lra).
  pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
  pose proof (Bxi_nonneg (80 * r)) as HB0.
  pose proof (Bub_le r Hr648) as HBub.
  pose proof (Bxi_le_Bub (80 * r) ltac:(lra)) as HBB.
  pose proof (ln_le_lin r ltac:(lra)) as Hlin.
  pose proof (Rle_abs (ln M0)) as HM.
  (* Bxi (80 r) + 1 <= Cb r^2 *)
  pose proof (Rabs_pos (ln M0)) as HMa.
  assert (Hrr : r <= r ^ 2) by nra.
  assert (Hrl : r * ln r <= r ^ 2) by nra.
  assert (Hln8 : 8 * ln r <= 8 * r ^ 2) by nra.
  assert (H2592 : 2592 * (r * ln r) <= 2592 * r ^ 2) by nra.
  assert (Hone : 1 <= r ^ 2) by nra.
  assert (HMr : Rabs (ln M0) <= Rabs (ln M0) * r ^ 2) by nra.
  assert (Hsq : Bxi (80 * r) + 1 <= Cb * r ^ 2)
    by (unfold Cb; lra).
  (* hence its logarithm is at most 3 ln r *)
  assert (HCb : 0 < Cb) by (unfold Cb; pose proof (Rabs_pos (ln M0)); lra).
  apply Rle_trans with (ln (Cb * r ^ 2)); [ apply ln_mono_le; lra | ].
  rewrite ln_mult by nra.
  rewrite (ln_pow r ltac:(lra) 2).
  assert (HlnCb : ln Cb <= ln r).
  { apply ln_mono_le; [ exact HCb | ].
    pose proof Cb_le_Rbase. lra. }
  simpl. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the whole minimum-modulus loss                                 *)
(* ----------------------------------------------------------------- *)
Definition Cu : R := 5 * Rabs (ln M0) + 13000 + 60 * agrow.

Theorem negLBexp_bound : forall (r rr del : R) (K : nat),
  Rbase <= r ->
  2 * r <= rr -> rr <= 4 * r ->
  0 < del -> del <= r ->
  r / (Bxi (80 * r) + 1) <= del ->
  10 * rr <= 2 ^ K -> 2 ^ K < 20 * rr ->
  - LBexp rr del K <= Cu * (r * (ln r) ^ 2).
Proof.
  intros r rr del K Hr Hlo Hhi Hd0 Hdr Hdb HK1 HK2.
  assert (Hr648 : 648 <= r)
    by (unfold Rbase in Hr; pose proof (Rabs_pos (ln M0)); lra).
  pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
  pose proof agrow_nonneg as Hag.
  pose proof (Rabs_pos (ln M0)) as HM0a.
  pose proof (Rle_abs (ln M0)) as HM0.
  assert (H2Klo : 20 * r <= 2 ^ K) by lra.
  assert (H2Khi : 2 ^ K < 80 * r) by lra.
  assert (H2Kpos : (0:R) < 2 ^ K) by lra.
  pose proof (K_le_log K r ltac:(lra) H2Khi) as HKlog.
  pose proof (pos_INR K) as HK0.
  (* --- the two logarithms in piece A --- *)
  assert (HlnK : ln (2 ^ K) <= 2 * ln r).
  { apply Rle_trans with (ln (80 * r));
      [ apply ln_mono_le; lra | apply ln_scal_le; lra ]. }
  assert (HB0 : 0 <= Bxi (80 * r)) by apply Bxi_nonneg.
  assert (Hdel_lo : ln r - ln (Bxi (80 * r) + 1) <= ln del).
  { assert (Heq : ln (r / (Bxi (80 * r) + 1)) = ln r - ln (Bxi (80 * r) + 1)).
    { unfold Rdiv. rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
      rewrite ln_Rinv by lra. ring. }
    rewrite <- Heq.
    apply ln_mono_le; [ apply Rdiv_lt_0_compat; lra | exact Hdb ]. }
  pose proof (lnBxi_le r Hr) as HlnB.
  assert (Hbr : ln (2 ^ K) - ln del <= 5 * ln r) by lra.
  assert (Hbr0 : 0 <= ln (2 ^ K) - ln del).
  { assert (ln del <= ln (2 ^ K)) by (apply ln_mono_le; lra). lra. }
  (* --- piece A --- *)
  assert (HBxiK : Bxi (2 ^ K) <= ln M0 + 8 * ln r + 2592 * (r * ln r)).
  { apply Rle_trans with (Bub (80 * r));
      [ apply Rle_trans with (Bub (2 ^ K));
          [ apply Bxi_le_Bub; lra | apply Bub_mono; lra ]
      | apply Bub_le; lra ]. }
  assert (HBxiK0 : 0 <= Bxi (2 ^ K)) by apply Bxi_nonneg.
  assert (HA : - (Bxi (2 ^ K) * ln (del / 2 ^ K))
               <= (ln M0 + 8 * ln r + 2592 * (r * ln r)) * (5 * ln r)).
  { assert (Hsplit : ln (del / 2 ^ K) = ln del - ln (2 ^ K)).
    { unfold Rdiv. rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
      rewrite ln_Rinv by lra. ring. }
    rewrite Hsplit.
    replace (- (Bxi (2 ^ K) * (ln del - ln (2 ^ K))))
      with (Bxi (2 ^ K) * (ln (2 ^ K) - ln del)) by ring.
    apply Rmult_le_compat; assumption. }
  (* --- piece B --- *)
  assert (HAser : Aser K <= 10 * (ln r) ^ 2).
  { rewrite (Aser_closed K). nra. }
  assert (HB : rr * (agrow * Aser K) <= 40 * agrow * (r * (ln r) ^ 2)).
  { assert (H1 : agrow * Aser K <= agrow * (10 * (ln r) ^ 2))
      by (apply Rmult_le_compat_l; lra).
    assert (H2 : 0 <= agrow * Aser K).
    { apply Rmult_le_pos; [ exact Hag | ].
      rewrite (Aser_closed K). nra. }
    nra. }
  (* --- piece C --- *)
  assert (HC : 2 * rr ^ 2 * (agrow * (2 * (INR K + 2) / 2 ^ K))
               <= 20 * agrow * (r * (ln r) ^ 2)).
  { assert (Hq : 2 * (INR K + 2) / 2 ^ K <= 12 * ln r / (20 * r)).
    { unfold Rdiv. apply Rmult_le_compat; [ lra | | lra | ].
      - left; apply Rinv_0_lt_compat; lra.
      - apply Rinv_le_contravar; lra. }
    assert (Hq0 : 0 <= 2 * (INR K + 2) / 2 ^ K)
      by (apply Rle_mult_inv_pos; lra).
    assert (H1 : agrow * (2 * (INR K + 2) / 2 ^ K)
                 <= agrow * (12 * ln r / (20 * r)))
      by (apply Rmult_le_compat_l; lra).
    assert (H2 : 0 <= agrow * (2 * (INR K + 2) / 2 ^ K))
      by (apply Rmult_le_pos; lra).
    assert (Hrr2 : rr ^ 2 <= 16 * r ^ 2) by nra.
    assert (Hchain : 2 * rr ^ 2 * (agrow * (2 * (INR K + 2) / 2 ^ K))
                     <= 2 * (16 * r ^ 2) * (agrow * (12 * ln r / (20 * r))))
      by nra.
    apply Rle_trans with (1 := Hchain).
    replace (2 * (16 * r ^ 2) * (agrow * (12 * ln r / (20 * r))))
      with (agrow * (96 / 5) * (r * ln r)) by (field; lra).
    assert (Hln2 : ln r <= (ln r) ^ 2) by nra.
    assert (Hrl : r * ln r <= r * (ln r) ^ 2) by nra.
    assert (Hnn : 0 <= r * (ln r) ^ 2) by nra.
    assert (Hs : agrow * (96 / 5) * (r * ln r)
                 <= agrow * (96 / 5) * (r * (ln r) ^ 2))
      by (apply Rmult_le_compat_l; lra).
    nra. }
  (* --- assemble --- *)
  assert (Hfold1 : ln r <= r * (ln r) ^ 2) by nra.
  assert (Hfold2 : (ln r) ^ 2 <= r * (ln r) ^ 2) by nra.
  assert (HAexp : (ln M0 + 8 * ln r + 2592 * (r * ln r)) * (5 * ln r)
                  <= (5 * Rabs (ln M0) + 13000) * (r * (ln r) ^ 2)).
  { assert (E : (ln M0 + 8 * ln r + 2592 * (r * ln r)) * (5 * ln r)
                = 5 * ln M0 * ln r + 40 * (ln r) ^ 2
                  + 12960 * (r * (ln r) ^ 2)) by ring.
    rewrite E.
    assert (T0 : 5 * ln M0 * ln r <= 5 * Rabs (ln M0) * ln r) by nra.
    assert (T1 : 5 * Rabs (ln M0) * ln r
                 <= 5 * Rabs (ln M0) * (r * (ln r) ^ 2)) by nra.
    assert (T2 : 40 * (ln r) ^ 2 <= 40 * (r * (ln r) ^ 2)) by nra.
    lra. }
  unfold LBexp, Cu. lra.
Qed.

Print Assumptions Bxi_le_Bub.
Print Assumptions K_le_log.
Print Assumptions negLBexp_bound.
