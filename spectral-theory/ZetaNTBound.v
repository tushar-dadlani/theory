(* ================================================================= *)
(*  ZetaNTBound.v  --  N(T) << T ln T, by covering with windows.       *)
(*                                                                    *)
(*  ZetaWindowCount.zeta_window_count bounds the zeros in one window   *)
(*  of height 11/10 about tj.  Covering [3, T] by k such windows gives *)
(*  the Riemann-von Mangoldt ORDER.  The constant is bad and is not    *)
(*  the point; the point is that the bound is uniform in the height,   *)
(*  which nothing in the repo was before.                             *)
(*                                                                    *)
(*  Wbnd tj is not obviously monotone in tj (it is a difference of two *)
(*  increasing quantities), so the induction is run against WM, a      *)
(*  manifestly monotone majorant obtained by bounding each of the      *)
(*  three summands separately.                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CSeries CDeriv Holomorphic
        CZeta ZetaFn CPeelBoundGen ZetaWindowCount.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  1.  a monotone majorant for the per-window bound                   *)
(* ----------------------------------------------------------------- *)

Definition WM (T : R) : R :=
  (ln (2 * Mcirc T) - ln 3 + (ln 1000 + ln (343 * (ln (2 * T) + 10))) / 4)
  / ln (11 / 9).

Lemma lnq_pos : 0 < ln (11 / 9).
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma Mcirc_mono : forall a b, 0 <= a -> a <= b -> Mcirc a <= Mcirc b.
Proof.
  intros a b Ha Hab. unfold Mcirc.
  apply Rplus_le_compat_l.
  assert (H1 : (a + 59 / 20) * (a + 79 / 20)
               <= (b + 59 / 20) * (b + 79 / 20)) by nra.
  apply Rmult_le_compat; nra.
Qed.

Lemma ln2T_nonneg : forall T, 3 <= T -> 0 <= ln (2 * T).
Proof. intros T HT. rewrite <- ln_1. apply ln_mono_gen; lra. Qed.

Lemma Wbnd_le_WM : forall tj T, 3 <= tj -> tj <= T -> Wbnd tj <= WM T.
Proof.
  intros tj T H3 HT.
  pose proof lnq_pos as Hq.
  pose proof (ln2T_nonneg tj ltac:(lra)) as Hl1.
  pose proof (ln2T_nonneg T ltac:(lra)) as Hl2.
  assert (HM1 : 0 < Mcirc tj) by (unfold Mcirc; nra).
  assert (HM2 : Mcirc tj <= Mcirc T) by (apply Mcirc_mono; lra).
  assert (Ha : ln (2 * Mcirc tj) <= ln (2 * Mcirc T))
    by (apply ln_mono_gen; lra).
  assert (Hb : ln 3 <= ln tj) by (apply ln_mono_gen; lra).
  assert (Hc : ln (343 * (ln (2 * tj) + 10)) <= ln (343 * (ln (2 * T) + 10))).
  { apply ln_mono_gen; [ lra | ].
    assert (ln (2 * tj) <= ln (2 * T)) by (apply ln_mono_gen; lra). lra. }
  unfold Wbnd, WM, Lcen.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hq | lra ].
Qed.

Lemma WM_mono : forall T1 T2, 3 <= T1 -> T1 <= T2 -> WM T1 <= WM T2.
Proof.
  intros T1 T2 H3 H12.
  pose proof lnq_pos as Hq.
  assert (HM1 : 0 < Mcirc T1) by (unfold Mcirc; nra).
  assert (HM2 : Mcirc T1 <= Mcirc T2) by (apply Mcirc_mono; lra).
  assert (Ha : ln (2 * Mcirc T1) <= ln (2 * Mcirc T2))
    by (apply ln_mono_gen; lra).
  pose proof (ln2T_nonneg T1 ltac:(lra)) as Hl1.
  assert (Hc : ln (343 * (ln (2 * T1) + 10)) <= ln (343 * (ln (2 * T2) + 10))).
  { apply ln_mono_gen; [ lra | ].
    assert (ln (2 * T1) <= ln (2 * T2)) by (apply ln_mono_gen; lra). lra. }
  unfold WM.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hq | lra ].
Qed.

Lemma WM_nonneg : forall T, 3 <= T -> 0 <= WM T.
Proof.
  intros T HT. pose proof lnq_pos as Hq.
  pose proof (ln2T_nonneg T HT) as Hl.
  assert (HM : 3 <= 2 * Mcirc T) by (unfold Mcirc; nra).
  assert (Ha : ln 3 <= ln (2 * Mcirc T)) by (apply ln_mono_gen; lra).
  assert (Hb : 0 <= ln 1000) by (rewrite <- ln_1; apply ln_mono_gen; lra).
  assert (Hc : 0 <= ln (343 * (ln (2 * T) + 10)))
    by (rewrite <- ln_1; apply ln_mono_gen; lra).
  unfold WM. apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; exact Hq ].
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  the covering induction                                        *)
(* ----------------------------------------------------------------- *)

Definition below (T' : R) (z : C) : bool :=
  if Rle_dec (Im z) T' then true else false.

Theorem zeta_N_bound_k : forall (k : nat) (T : R) (L : list C),
  3 <= T -> T <= 3 + 11 / 10 * INR k -> NoDup L ->
  (forall z, In z L ->
     zF z = C0 /\ 0 < Re z /\ Re z < 1 /\ 3 <= Im z <= T) ->
  INR (length L) <= INR (S k) * (2 * WM T).
Proof.
  induction k as [| k IH]; intros T L HT3 HTk Hnd Hz.
  - (* k = 0 : T = 3, a single window at tj = 3 covers everything *)
    rewrite INR_0 in HTk.
    assert (HTeq : T = 3) by lra.
    assert (Hcov : INR (length L) <= 2 * Wbnd 3).
    { apply (zeta_window_count 3 L ltac:(lra) Hnd).
      intros z Hin. destruct (Hz z Hin) as [Ha [Hb [Hc Hd]]].
      repeat split; try assumption.
      rewrite Rabs_pos_eq; lra. }
    pose proof (Wbnd_le_WM 3 T ltac:(lra) ltac:(lra)) as HW.
    pose proof (WM_nonneg T HT3) as HW0.
    replace (INR 1) with 1 by (simpl; ring). lra.
  - (* k+1 windows *)
    destruct (Rle_dec T (3 + 11 / 10 * INR k)) as [Hsmall | Hbig].
    + (* the previous bound already suffices *)
      pose proof (IH T L HT3 Hsmall Hnd Hz) as HIH.
      pose proof (WM_nonneg T HT3) as HW0.
      assert (Hle : INR (S k) <= INR (S (S k))) by (apply le_INR; lia).
      nra.
    + apply Rnot_le_lt in Hbig.
      destruct (Rle_dec (71 / 20) T) as [Hbig2 | Hsm2].
      * (* split off the top window, centred at T - 11/20 >= 3 *)
        set (T' := 3 + 11 / 10 * INR k).
        assert (HT'3 : 3 <= T') by (unfold T'; pose proof (pos_INR k); lra).
        assert (HT'T : T' <= T) by (unfold T'; lra).
        assert (Hgap : T - T' <= 11 / 10).
        { unfold T'. rewrite S_INR in HTk. lra. }
        set (Lr := filter (below T') L).
        set (Lt := filter (fun z => negb (below T' z)) L).
        assert (Hsplit : (length Lr + length Lt)%nat = length L)
          by (unfold Lr, Lt; apply filter_split_length).
        (* the lower part, by induction *)
        assert (HLr : INR (length Lr) <= INR (S k) * (2 * WM T')).
        { apply (IH T' Lr HT'3 ltac:(unfold T'; lra));
            [ unfold Lr; apply NoDup_filter; exact Hnd | ].
          intros z Hin. unfold Lr in Hin. apply filter_In in Hin.
          destruct Hin as [HinL Hf].
          destruct (Hz z HinL) as [Ha [Hb [Hc Hd]]].
          unfold below in Hf. destruct (Rle_dec (Im z) T') as [He | He];
            [ | discriminate ].
          repeat split; try assumption; lra. }
        (* the top window *)
        assert (HLt : INR (length Lt) <= 2 * Wbnd (T - 11 / 20)).
        { apply (zeta_window_count (T - 11 / 20) Lt ltac:(lra));
            [ unfold Lt; apply NoDup_filter; exact Hnd | ].
          intros z Hin. unfold Lt in Hin. apply filter_In in Hin.
          destruct Hin as [HinL Hf].
          destruct (Hz z HinL) as [Ha [Hb [Hc Hd]]].
          unfold below in Hf. destruct (Rle_dec (Im z) T') as [He | He];
            [ discriminate | ].
          apply Rnot_le_lt in He.
          repeat split; try assumption.
          apply Rabs_le. lra. }
        pose proof (Wbnd_le_WM (T - 11 / 20) T ltac:(lra) ltac:(lra)) as HW1.
        pose proof (WM_mono T' T HT'3 HT'T) as HW2.
        pose proof (WM_nonneg T HT3) as HW0.
        pose proof (pos_INR k) as Hk0.
        assert (Hchain : INR (length L) <= INR (S k) * (2 * WM T) + 2 * WM T).
        { rewrite <- Hsplit, plus_INR. nra. }
        rewrite S_INR. nra.
      * (* T < 71/20 : one window at tj = 3 still covers [3, T] *)
        apply Rnot_le_lt in Hsm2.
        assert (Hcov : INR (length L) <= 2 * Wbnd 3).
        { apply (zeta_window_count 3 L ltac:(lra) Hnd).
          intros z Hin. destruct (Hz z Hin) as [Ha [Hb [Hc Hd]]].
          repeat split; try assumption.
          rewrite Rabs_pos_eq; lra. }
        pose proof (Wbnd_le_WM 3 T ltac:(lra) ltac:(lra)) as HW.
        pose proof (WM_nonneg T HT3) as HW0.
        assert (H1 : 1 <= INR (S (S k)))
          by (rewrite <- INR_1; apply le_INR; lia).
        nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  3.  the count, with the number of windows made explicit            *)
(* ----------------------------------------------------------------- *)

Theorem zeta_N_bound : forall (k : nat) (T : R) (L : list C),
  3 <= T -> T <= 3 + 11 / 10 * INR k -> NoDup L ->
  (forall z, In z L ->
     zF z = C0 /\ 0 < Re z /\ Re z < 1 /\ 3 <= Im z <= T) ->
  INR (length L) <= 2 * INR (S k) * WM T.
Proof.
  intros k T L H1 H2 H3 H4.
  pose proof (zeta_N_bound_k k T L H1 H2 H3 H4). lra.
Qed.

Print Assumptions zeta_N_bound.

(* ================================================================= *)
(*  END ZetaNTBound.v                                                 *)
(* ================================================================= *)
