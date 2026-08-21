(* ================================================================= *)
(*  ZetaDerivBoundExt.v  --  the zeta' bound, extended BELOW Re s = 1. *)
(*                                                                    *)
(*    zeta_deriv_log_bound_ext : 0 <= d <= 1/4, 1 - d <= Re s <= 2,    *)
(*      2 <= |Im s|, 1 <= B, (|Im s| + 3)^d <= B  ==>                  *)
(*        Cmod (zDF s) <= B (ln|Im s| + 4)^2 + 3 B + 16 B^2/(d e)      *)
(*                                                                    *)
(*  The second of the two mechanical restatements, and the last piece  *)
(*  of analysis Tier B link [4] was waiting on.  Same two changes as   *)
(*  ZetaLogBoundExt, plus one more that is specific to the derivative: *)
(*                                                                    *)
(*   * head: every term picks up a factor x^d <= B, exactly as before. *)
(*   * tail, plain part: RPowerTail.ptail_delta replaces tail_tele.    *)
(*   * tail, LOG-WEIGHTED part: RPowerLogTail.logptail_ub replaces     *)
(*     ZetaDerivBound.logtail_tele.  This is the extra one -- the      *)
(*     derivative series carries a factor ln(n+2) per term, and the    *)
(*     uterm telescoping that handled it exists only at exponent 2.    *)
(*                                                                    *)
(*  logptail_ub costs the constant 1/(d e), which at d = 1/ln|t| is    *)
(*  (ln|t|)/e -- one extra log.  That is why the bound carries a       *)
(*  B^2/(d e) term where ZetaLogBoundExt needed none: it is the price  *)
(*  of spending the log on the exponent.  It is affordable because the *)
(*  term it multiplies decays like N^{-(1-2d)} ~ 1/|t| at N ~ |t|,     *)
(*  against |s| ~ |t|, leaving O(ln|t|) overall -- still below the     *)
(*  O(ln^2|t|) head.  Axiom-clean.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CexpFull CSeries HarmonicSum
        Holomorphic CDeriv CZetaTerm CZeta ZetaFn CZetaDeriv2 CZetaDeriv3
        ZetaDeriv ZetaStripBound ZetaLogBound ZetaDerivBound
        RPowerTail RPowerLogTail.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the two atoms, with the x^d factor                             *)
(* ----------------------------------------------------------------- *)
Lemma dsk_bound_ext : forall s d B x, 0 <= d -> 1 - d <= Re s -> 1 <= x ->
  Rpower x d <= B -> Cmod (dsk s x) <= B * (ln x / x).
Proof.
  intros s d B x Hd Hs Hx HB. unfold dsk.
  rewrite !Cmod_mul, Cpw_mod.
  assert (E1 : Cmod (Copp C1) = 1) by (rewrite Cmod_opp''; apply Cmod_one).
  assert (Hln : 0 <= ln x) by (apply ln_nonneg; lra).
  rewrite E1, Cmod_RtoC, (Rabs_right (ln x) ltac:(lra)).
  assert (E3 : Re (Copp s) = - Re s) by (unfold Copp; cbn [Re]; ring).
  rewrite E3.
  assert (H1 : Rpower x (- Re s) <= Rpower x (-1 + d))
    by (apply Rpower_exp_le; lra).
  assert (H2 : Rpower x (-1 + d) = / x * Rpower x d)
    by (rewrite Rpower_plus, (Rpower_m1 x ltac:(lra)); reflexivity).
  assert (H3 : 0 < / x) by (apply Rinv_0_lt_compat; lra).
  assert (H4 : / x * Rpower x d <= B * / x)
    by (rewrite Rmult_comm; apply Rmult_le_compat_r; lra).
  assert (H5 : Rpower x (- Re s) <= B * / x) by lra.
  assert (E : B * (ln x / x) = ln x * (B * / x)) by (unfold Rdiv; ring).
  rewrite E.
  assert (Hfin : ln x * Rpower x (- Re s) <= ln x * (B * / x))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Lemma dsGC_bound_ext : forall s d B x, 0 <= d -> 1 - d <= Re s ->
  2 <= Rabs (Im s) -> 1 <= x -> Rpower x d <= B ->
  Cmod (dsGC s x) <= B * (ln x / Rabs (Im s) + / (Rabs (Im s) * Rabs (Im s))).
Proof.
  intros s d B x Hd Hs Ht Hx HB.
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hlow : Rabs (Im s) <= Cmod (Cminus C1 s)).
  { eapply Rle_trans; [ | apply (Im_le_Cmod (Cminus C1 s)) ].
    assert (E : Im (Cminus C1 s) = - Im s) by (unfold Cminus, C1; cbn [Re Im]; ring).
    rewrite E, Rabs_Ropp. apply Rle_refl. }
  assert (HRe : Re (Cminus C1 s) = 1 - Re s) by (unfold Cminus, C1; cbn [Re Im]; ring).
  assert (Hp : Rpower x (1 - Re s) <= B)
    by (eapply Rle_trans; [ apply (Rpower_exp_le x (1 - Re s) d); lra | exact HB ]).
  assert (Hp0 : 0 < Rpower x (1 - Re s)) by (unfold Rpower; apply exp_pos).
  assert (Hi : / Cmod (Cminus C1 s) <= / Rabs (Im s))
    by (apply Rinv_le_contravar; lra).
  assert (Hi0 : 0 < / Cmod (Cminus C1 s)) by (apply Rinv_0_lt_compat; lra).
  assert (Hln : 0 <= ln x) by (apply ln_nonneg; lra).
  assert (HT0 : 0 < Rabs (Im s)) by lra.
  unfold dsGC.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  assert (Esplit : B * (ln x / Rabs (Im s) + / (Rabs (Im s) * Rabs (Im s)))
                 = B * (ln x / Rabs (Im s)) + B * / (Rabs (Im s) * Rabs (Im s)))
    by ring.
  rewrite Esplit.
  apply Rplus_le_compat.
  - rewrite !Cmod_mul, Cpw_mod, (Cmod_Cinv _ Hne), HRe, Cmod_RtoC,
      (Rabs_left1 (- ln x) ltac:(lra)), Ropp_involutive.
    assert (Hstep : Rpower x (1 - Re s) * / Cmod (Cminus C1 s) <= B * / Rabs (Im s))
      by (apply Rmult_le_compat; lra).
    assert (E : B * (ln x / Rabs (Im s)) = ln x * (B * / Rabs (Im s)))
      by (unfold Rdiv; ring).
    rewrite E.
    assert (Hfin : ln x * (Rpower x (1 - Re s) * / Cmod (Cminus C1 s))
                <= ln x * (B * / Rabs (Im s)))
      by (apply Rmult_le_compat_l; lra).
    lra.
  - rewrite !Cmod_mul, Cpw_mod, (Cmod_Cinv _ Hne), HRe.
    assert (Hsq : / Cmod (Cminus C1 s) * / Cmod (Cminus C1 s)
               <= / Rabs (Im s) * / Rabs (Im s))
      by (apply Rmult_le_compat; lra).
    assert (Hinv : B * / (Rabs (Im s) * Rabs (Im s))
                 = B * (/ Rabs (Im s) * / Rabs (Im s))) by (field; lra).
    rewrite Hinv.
    assert (Hstep : Rpower x (1 - Re s) * (/ Cmod (Cminus C1 s) * / Cmod (Cminus C1 s))
                 <= B * (/ Rabs (Im s) * / Rabs (Im s)))
      by (apply Rmult_le_compat; try lra; nra).
    exact Hstep.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the HEAD per-term bound                                        *)
(* ----------------------------------------------------------------- *)
Lemma dhead_term_ext : forall s d B n, 0 <= d -> 1 - d <= Re s ->
  2 <= Rabs (Im s) -> Rpower (INR (S (S n))) d <= B ->
  Cmod (dgtermC s n)
  <= B * (ln (INR (S n)) / INR (S n)
          + 2 * (ln (INR (S (S n))) / Rabs (Im s)
                 + / (Rabs (Im s) * Rabs (Im s)))).
Proof.
  intros s d B n Hd Hs Ht HB.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hy : 1 <= INR (S (S n))) by (rewrite !S_INR; pose proof (pos_INR n); lra).
  assert (Hxy : INR (S n) <= INR (S (S n))) by (apply le_INR; lia).
  assert (HBx : Rpower (INR (S n)) d <= B)
    by (eapply Rle_trans; [ apply Rpower_base_le; [ lra | exact Hxy | exact Hd ] | exact HB ]).
  assert (HB1 : 1 <= B).
  { eapply Rle_trans; [ | exact HB ].
    assert (E : (1:R) = Rpower (INR (S (S n))) 0) by (rewrite Rpower_0'; reflexivity).
    rewrite E at 1. apply Rpower_exp_le; lra. }
  assert (HT0 : 0 < Rabs (Im s)) by lra.
  assert (Hmono : ln (INR (S n)) <= ln (INR (S (S n))))
    by (apply ln_le'; [ lra | exact Hxy ]).
  unfold dgtermC.
  eapply Rle_trans; [ apply Cmod_sub_le | ].
  pose proof (dsk_bound_ext s d B _ Hd Hs Hx HBx) as H1.
  assert (H2 : Cmod (Cminus (dsGC s (INR (S (S n)))) (dsGC s (INR (S n))))
            <= B * (2 * (ln (INR (S (S n))) / Rabs (Im s)
                         + / (Rabs (Im s) * Rabs (Im s))))).
  { eapply Rle_trans; [ apply Cmod_sub_le | ].
    pose proof (dsGC_bound_ext s d B _ Hd Hs Ht Hy HB) as A.
    pose proof (dsGC_bound_ext s d B _ Hd Hs Ht Hx HBx) as C.
    assert (Hd2 : ln (INR (S n)) / Rabs (Im s) <= ln (INR (S (S n))) / Rabs (Im s))
      by (apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | exact Hmono ]).
    nra. }
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the TAIL per-term bound, at exponent -(2-d)                    *)
(* ----------------------------------------------------------------- *)
Lemma dtail_term_ext : forall s d n, 0 <= d -> d <= / 4 -> 1 - d <= Re s ->
  Cminus C1 s <> C0 ->
  Cmod (dgtermC s n)
  <= 2 * Rpower (INR (S n)) (- (2 - d))
     + 2 * Cmod s * (ln (INR (S (S n))) * Rpower (INR (S n)) (- (2 - d))).
Proof.
  intros s d n Hd Hd4 Hs Hne.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hy : 1 <= INR (S (S n))) by (rewrite !S_INR; pose proof (pos_INR n); lra).
  pose proof (Cmod_dgtermC_bound s n ltac:(lra) Hne) as HB.
  unfold dbound1 in HB.
  assert (Hp : Rpower (INR (S n)) (- Re s - 1) <= Rpower (INR (S n)) (- (2 - d)))
    by (apply Rpower_exp_le; lra).
  assert (Hln0 : 0 <= ln (INR (S (S n)))) by (apply ln_nonneg; lra).
  pose proof (Cmod_nonneg s) as Hs0.
  assert (Hpos : 0 <= 1 + ln (INR (S (S n))) * Cmod s) by nra.
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the head sum                                                   *)
(* ----------------------------------------------------------------- *)
Lemma dterm_sum_bound : forall T m, 2 <= T ->
  sum_f_R0 (fun n => ln (INR (S n)) / INR (S n)
                     + 2 * (ln (INR (S (S n))) / T + / (T * T))) m
  <= ln (INR (S m)) * (ln (INR (S m)) + 1)
     + 2 / T * (INR (S m) * ln (INR (S (S m))))
     + 2 / (T * T) * INR (S m).
Proof.
  intros T m HT. rewrite !sum_plus.
  assert (Hmono : forall n, (n <= m)%nat -> ln (INR (S n)) <= ln (INR (S m)))
    by (intros n Hn; apply ln_le'; [ rewrite S_INR; pose proof (pos_INR n); lra
                                   | apply le_INR; lia ]).
  assert (Hmono2 : forall n, (n <= m)%nat -> ln (INR (S (S n))) <= ln (INR (S (S m))))
    by (intros n Hn; apply ln_le'; [ rewrite !S_INR; pose proof (pos_INR n); lra
                                   | apply le_INR; lia ]).
  assert (P1 : sum_f_R0 (fun n => ln (INR (S n)) / INR (S n)) m
            <= ln (INR (S m)) * (ln (INR (S m)) + 1)).
  { assert (HL : 0 <= ln (INR (S m)))
      by (apply ln_nonneg; rewrite S_INR; pose proof (pos_INR m); lra).
    eapply Rle_trans.
    - apply sum_Rle. intros n Hn.
      assert (Hp : 0 < INR (S n)) by (apply lt_0_INR; lia).
      assert (Hd : ln (INR (S n)) / INR (S n) <= / INR (S n) * ln (INR (S m))).
      { unfold Rdiv. rewrite Rmult_comm.
        apply Rmult_le_compat_l;
          [ left; apply Rinv_0_lt_compat; exact Hp | apply Hmono; exact Hn ]. }
      exact Hd.
    - rewrite <- (scal_sum (fun n => / INR (S n)) m (ln (INR (S m)))).
      pose proof (harm_sum_le m). nra. }
  assert (P2 : sum_f_R0 (fun n => 2 * (ln (INR (S (S n))) / T)) m
            <= 2 / T * (INR (S m) * ln (INR (S (S m))))).
  { eapply Rle_trans.
    - apply sum_Rle. intros n Hn.
      assert (Hi : 0 < / T) by (apply Rinv_0_lt_compat; lra).
      pose proof (Hmono2 n Hn).
      assert (Hd : 2 * (ln (INR (S (S n))) / T) <= 2 / T * ln (INR (S (S m))))
        by (unfold Rdiv; nra).
      exact Hd.
    - rewrite sum_cte. nra. }
  assert (P3 : sum_f_R0 (fun _ : nat => 2 * / (T * T)) m
             = 2 / (T * T) * INR (S m)) by (rewrite sum_cte; unfold Rdiv; ring).
  assert (Hsplit : sum_f_R0 (fun n => 2 * (ln (INR (S (S n))) / T + / (T * T))) m
                 = sum_f_R0 (fun n => 2 * (ln (INR (S (S n))) / T)) m
                   + sum_f_R0 (fun _ : nat => 2 * / (T * T)) m)
    by (rewrite <- sum_plus; apply sum_eq; intros i _; ring).
  rewrite Hsplit, P3. lra.
Qed.

Lemma dhead_sum_ext : forall s d B m, 0 <= d -> 1 - d <= Re s -> 2 <= Rabs (Im s) ->
  Rpower (INR (S (S m))) d <= B ->
  sum_f_R0 (fun n => Cmod (dgtermC s n)) m
  <= B * (ln (INR (S m)) * (ln (INR (S m)) + 1)
          + 2 / Rabs (Im s) * (INR (S m) * ln (INR (S (S m))))
          + 2 / (Rabs (Im s) * Rabs (Im s)) * INR (S m)).
Proof.
  intros s d B m Hd Hs Ht HB.
  assert (HB0 : 0 <= B)
    by (eapply Rle_trans; [ | exact HB ]; left; unfold Rpower; apply exp_pos).
  eapply Rle_trans.
  - apply sum_Rle. intros n Hn.
    apply (dhead_term_ext s d B n Hd Hs Ht).
    eapply Rle_trans; [ | exact HB ].
    apply Rpower_base_le; [ rewrite !S_INR; pose proof (pos_INR n); lra
                          | apply le_INR; lia | exact Hd ].
  - assert (E : sum_f_R0 (fun n => B * (ln (INR (S n)) / INR (S n)
                    + 2 * (ln (INR (S (S n))) / Rabs (Im s)
                           + / (Rabs (Im s) * Rabs (Im s))))) m
              = B * sum_f_R0 (fun n => ln (INR (S n)) / INR (S n)
                    + 2 * (ln (INR (S (S n))) / Rabs (Im s)
                           + / (Rabs (Im s) * Rabs (Im s)))) m).
    { rewrite (scal_sum (fun n => ln (INR (S n)) / INR (S n)
                 + 2 * (ln (INR (S (S n))) / Rabs (Im s)
                        + / (Rabs (Im s) * Rabs (Im s)))) m B).
      apply sum_eq; intros i _; ring. }
    rewrite E.
    apply Rmult_le_compat_l; [ exact HB0 | apply dterm_sum_bound; lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the partial sums, split at N ~ |Im s|                          *)
(* ----------------------------------------------------------------- *)
Lemma dpsum_bound_ext : forall s d B N M,
  0 <= d -> d <= / 4 -> 0 < d -> 1 - d <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  Cminus C1 s <> C0 -> (1 <= N)%nat -> 1 <= B ->
  Rabs (Im s) <= INR N -> INR N <= Rabs (Im s) + 1 ->
  Rpower (Rabs (Im s) + 3) d <= B ->
  sum_f_R0 (fun n => Cmod (dgtermC s n)) M
  <= B * (ln (Rabs (Im s)) + 4) ^ 2 + 2 * B + 16 * B * B / (d * exp 1).
Proof.
  intros s d B N M Hd Hd4 Hd0 Hs1 Hs2 Ht Hne HN HB1 Nlo Nhi HB.
  set (T := Rabs (Im s)) in *. set (L := ln T).
  assert (HT0 : 0 < T) by lra.
  assert (HL0 : 0 <= L) by (unfold L; apply ln_nonneg; lra).
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (HNpos : 0 < INR N) by lra.
  assert (Hbase : forall x, 1 <= x -> x <= T + 3 -> Rpower x d <= B)
    by (intros x Hx1 Hx3;
        eapply Rle_trans; [ apply Rpower_base_le; [ lra | exact Hx3 | exact Hd ] | exact HB ]).
  (* head *)
  assert (Hhead : forall m, INR (S m) <= INR N ->
            sum_f_R0 (fun n => Cmod (dgtermC s n)) m <= B * (L + 4) ^ 2).
  { intros m Hm.
    assert (HSm0 : 0 < INR (S m)) by (apply lt_0_INR; lia).
    assert (HSm : INR (S m) <= T + 1) by lra.
    assert (HSSm : INR (S (S m)) <= T + 2) by (rewrite (S_INR (S m)); lra).
    assert (HBm : Rpower (INR (S (S m))) d <= B)
      by (apply Hbase; [ rewrite !S_INR; pose proof (pos_INR m); lra | lra ]).
    pose proof (dhead_sum_ext s d B m Hd Hs1 Ht HBm) as HS. fold T in HS.
    assert (Hl1 : ln (INR (S m)) <= L + 2).
    { eapply Rle_trans; [ apply ln_le'; [ lra | exact HSm ] | ].
      apply (ln_shift_gen 1 T); lra. }
    assert (Hl2 : ln (INR (S (S m))) <= L + 2).
    { eapply Rle_trans;
        [ apply ln_le'; [ rewrite (S_INR (S m)); lra | exact HSSm ] | ].
      apply (ln_shift_gen 2 T); lra. }
    assert (Hl1p : 0 <= ln (INR (S m)))
      by (apply ln_nonneg; rewrite S_INR; pose proof (pos_INR m); lra).
    assert (Hl2p : 0 <= ln (INR (S (S m))))
      by (apply ln_nonneg; rewrite !S_INR; pose proof (pos_INR m); lra).
    assert (A1 : ln (INR (S m)) * (ln (INR (S m)) + 1) <= (L + 2) * (L + 3)) by nra.
    assert (A2 : 2 / T * (INR (S m) * ln (INR (S (S m)))) <= 3 * (L + 2)).
    { assert (Hp : INR (S m) * ln (INR (S (S m))) <= (T + 1) * (L + 2)) by nra.
      assert (Hr : 2 / T * (T + 1) <= 3).
      { assert (E : 2 / T * (T + 1) = 2 + 2 / T) by (field; lra).
        assert (E2 : 2 / T = 2 * / T) by (unfold Rdiv; ring).
        assert (Hi : / T <= / 2) by (apply Rinv_le_contravar; lra). lra. }
      assert (Hs : 2 / T * (INR (S m) * ln (INR (S (S m)))) <= 2 / T * ((T + 1) * (L + 2)))
        by (apply Rmult_le_compat_l; [ apply Rle_mult_inv_pos; lra | exact Hp ]).
      nra. }
    assert (A3 : 2 / (T * T) * INR (S m) <= 2).
    { assert (E : 2 / (T * T) * INR (S m) <= 2 / (T * T) * (T + 1))
        by (apply Rmult_le_compat_l; [ apply Rle_mult_inv_pos; nra | lra ]).
      assert (E2 : 2 / (T * T) * (T + 1) = 2 / T + 2 / (T * T)) by (field; lra).
      assert (E3 : 2 / (T * T) <= 2 / T)
        by (unfold Rdiv; apply Rmult_le_compat_l; [ lra | apply Rinv_le_contravar; nra ]).
      assert (E4 : 2 / T = 2 * / T) by (unfold Rdiv; ring).
      assert (Hi : / T <= / 2) by (apply Rinv_le_contravar; lra). lra. }
    assert (Hin : ln (INR (S m)) * (ln (INR (S m)) + 1)
                  + 2 / T * (INR (S m) * ln (INR (S (S m))))
                  + 2 / (T * T) * INR (S m) <= (L + 4) ^ 2) by nra.
    assert (Hmul : B * (ln (INR (S m)) * (ln (INR (S m)) + 1)
                        + 2 / T * (INR (S m) * ln (INR (S (S m))))
                        + 2 / (T * T) * INR (S m)) <= B * (L + 4) ^ 2)
      by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hsmod : Cmod s <= 2 + T).
  { pose proof (Cmod_le_sum s) as H.
    rewrite (Rabs_right (Re s) ltac:(lra)) in H. unfold T. lra. }
  assert (Hs0 : 0 <= Cmod s) by apply Cmod_nonneg.
  destruct (Nat.le_gt_cases N M) as [Hge | Hlt].
  - destruct N as [| Nm1]; [ exfalso; lia | ].
    assert (Hlt' : (Nm1 < M)%nat) by lia.
    rewrite (tech2 (fun n => Cmod (dgtermC s n)) Nm1 M Hlt').
    assert (Hh : sum_f_R0 (fun n => Cmod (dgtermC s n)) Nm1 <= B * (L + 4) ^ 2)
      by (apply Hhead; lra).
    set (K := (M - S Nm1)%nat).
    assert (Htail : sum_f_R0 (fun i => Cmod (dgtermC s (S Nm1 + i))) K
                 <= 2 * (2 * Rpower (INR (S Nm1)) (- (1 - d)))
                    + 2 * Cmod s * (4 / (d * exp 1)
                                    * Rpower (INR (S Nm1)) (- (1 - 2 * d)))).
    { eapply Rle_trans.
      - apply sum_Rle. intros i _. apply (dtail_term_ext s d); assumption.
      - rewrite sum_plus.
        assert (E1 : sum_f_R0 (fun i => 2 * Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K
                   = 2 * sum_f_R0 (fun i =>
                       Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K).
        { rewrite (scal_sum (fun i => Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K 2).
          apply sum_eq; intros i _; ring. }
        assert (E2 : sum_f_R0 (fun i => 2 * Cmod s
                       * (ln (INR (S (S (S Nm1 + i))))
                          * Rpower (INR (S (S Nm1 + i))) (- (2 - d)))) K
                   = 2 * Cmod s * sum_f_R0 (fun i =>
                       ln (INR (S (S (S Nm1 + i))))
                       * Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K).
        { rewrite (scal_sum (fun i => ln (INR (S (S (S Nm1 + i))))
                     * Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K (2 * Cmod s)).
          apply sum_eq; intros i _; ring. }
        rewrite E1, E2.
        pose proof (ptail_delta d (S Nm1) K Hd ltac:(lra) ltac:(lia)) as T1.
        pose proof (logptail_ub d (S Nm1) K Hd0 Hd4 ltac:(lia)) as T2.
        assert (S1 : 2 * sum_f_R0 (fun i =>
                       Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K
                  <= 2 * (2 * Rpower (INR (S Nm1)) (- (1 - d)))) by lra.
        assert (S2 : 2 * Cmod s * sum_f_R0 (fun i =>
                       ln (INR (S (S (S Nm1 + i))))
                       * Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K
                  <= 2 * Cmod s * (4 / (d * exp 1)
                                   * Rpower (INR (S Nm1)) (- (1 - 2 * d))))
          by (apply Rmult_le_compat_l; [ lra | exact T2 ]).
        lra. }
    (* size the two tails *)
    assert (Hr1 : Rpower (INR (S Nm1)) (- (1 - d)) <= B * / T).
    { assert (E : Rpower (INR (S Nm1)) (- (1 - d))
                = / INR (S Nm1) * Rpower (INR (S Nm1)) d).
      { replace (- (1 - d)) with (-1 + d) by ring.
        rewrite Rpower_plus, (Rpower_m1 (INR (S Nm1)) ltac:(lra)). reflexivity. }
      rewrite E.
      assert (H1 : Rpower (INR (S Nm1)) d <= B) by (apply Hbase; lra).
      assert (H2 : / INR (S Nm1) <= / T) by (apply Rinv_le_contravar; lra).
      assert (H3 : 0 < / INR (S Nm1)) by (apply Rinv_0_lt_compat; lra).
      assert (H4 : 0 < Rpower (INR (S Nm1)) d) by (unfold Rpower; apply exp_pos).
      assert (H5 : / INR (S Nm1) * Rpower (INR (S Nm1)) d <= / T * B)
        by (apply Rmult_le_compat; lra).
      lra. }
    assert (Hr2 : Rpower (INR (S Nm1)) (- (1 - 2 * d)) <= B * B * / T).
    { assert (E : Rpower (INR (S Nm1)) (- (1 - 2 * d))
                = / INR (S Nm1) * (Rpower (INR (S Nm1)) d * Rpower (INR (S Nm1)) d)).
      { replace (- (1 - 2 * d)) with (-1 + (d + d)) by ring.
        rewrite Rpower_plus, Rpower_plus, (Rpower_m1 (INR (S Nm1)) ltac:(lra)).
        reflexivity. }
      rewrite E.
      assert (H1 : Rpower (INR (S Nm1)) d <= B) by (apply Hbase; lra).
      assert (H4 : 0 < Rpower (INR (S Nm1)) d) by (unfold Rpower; apply exp_pos).
      assert (H2 : / INR (S Nm1) <= / T) by (apply Rinv_le_contravar; lra).
      assert (H3 : 0 < / INR (S Nm1)) by (apply Rinv_0_lt_compat; lra).
      assert (Hsq : Rpower (INR (S Nm1)) d * Rpower (INR (S Nm1)) d <= B * B)
        by (apply Rmult_le_compat; lra).
      assert (H5 : / INR (S Nm1) * (Rpower (INR (S Nm1)) d * Rpower (INR (S Nm1)) d)
                <= / T * (B * B)) by (apply Rmult_le_compat; nra).
      lra. }
    assert (Hnum1 : 2 * (2 * Rpower (INR (S Nm1)) (- (1 - d))) <= 2 * B).
    { assert (Hi : / T <= / 2) by (apply Rinv_le_contravar; lra).
      assert (Hr0 : 0 <= Rpower (INR (S Nm1)) (- (1 - d)))
        by (left; unfold Rpower; apply exp_pos).
      nra. }
    assert (Hnum2 : 2 * Cmod s * (4 / (d * exp 1)
                      * Rpower (INR (S Nm1)) (- (1 - 2 * d)))
                 <= 16 * B * B / (d * exp 1)).
    { assert (Hde : 0 < d * exp 1) by nra.
      assert (Hc0 : 0 < 4 / (d * exp 1))
        by (unfold Rdiv; apply Rmult_lt_0_compat;
            [ lra | apply Rinv_0_lt_compat; exact Hde ]).
      assert (Hr0 : 0 <= Rpower (INR (S Nm1)) (- (1 - 2 * d)))
        by (left; unfold Rpower; apply exp_pos).
      assert (D1 : 2 * Cmod s * (4 / (d * exp 1)
                     * Rpower (INR (S Nm1)) (- (1 - 2 * d)))
                <= 2 * (2 + T) * (4 / (d * exp 1) * (B * B * / T))).
      { apply Rmult_le_compat; try lra.
        - nra.
        - apply Rmult_le_compat_l; lra. }
      assert (D2 : 2 * (2 + T) * (4 / (d * exp 1) * (B * B * / T))
                 = (8 + 16 / T) * (B * B / (d * exp 1))) by (field; nra).
      assert (D3 : 16 / T <= 8)
        by (assert (E : 16 / T = 16 * / T) by (unfold Rdiv; ring);
            assert (Hi : / T <= / 2) by (apply Rinv_le_contravar; lra); lra).
      assert (Hq0 : 0 <= B * B / (d * exp 1))
        by (unfold Rdiv; apply Rmult_le_pos; [ nra | left; apply Rinv_0_lt_compat; exact Hde ]).
      assert (D4 : (8 + 16 / T) * (B * B / (d * exp 1))
                <= 16 * (B * B / (d * exp 1))) by nra.
      assert (D5 : 16 * (B * B / (d * exp 1)) = 16 * B * B / (d * exp 1))
        by (unfold Rdiv; ring).
      lra. }
    lra.
  - assert (Hde : 0 < d * exp 1) by nra.
    assert (Hq0 : 0 <= 16 * B * B / (d * exp 1))
      by (unfold Rdiv; apply Rmult_le_pos;
          [ nra | left; apply Rinv_0_lt_compat; exact Hde ]).
    apply Rle_trans with (B * (L + 4) ^ 2); [ apply Hhead; apply le_INR; lia | lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  THE EXTENDED DERIVATIVE BOUND                                  *)
(* ----------------------------------------------------------------- *)
Theorem zeta_deriv_log_bound_ext : forall s d B,
  0 < d -> d <= / 4 -> 1 - d <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  1 <= B -> Rpower (Rabs (Im s) + 3) d <= B ->
  Cmod (zDF s)
  <= B * (ln (Rabs (Im s)) + 4) ^ 2 + 3 * B + 16 * B * B / (d * exp 1).
Proof.
  intros s d B Hd0 Hd4 Hs1 Hs2 Ht HB1 HB.
  assert (H0 : 0 < Re s) by lra.
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hne1 : Cminus s C1 <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hlow : Rabs (Im s) <= Cmod (Cminus s C1)).
  { eapply Rle_trans; [ | apply (Im_le_Cmod (Cminus s C1)) ].
    assert (E : Im (Cminus s C1) = Im s) by (unfold Cminus, C1; cbn [Re Im]; ring).
    rewrite E. apply Rle_refl. }
  set (z := up (Rabs (Im s))).
  destruct (archimed (Rabs (Im s))) as [Hup1 Hup2]. fold z in Hup1, Hup2.
  assert (Hz0 : (0 <= z)%Z) by (apply le_IZR; simpl; lra).
  set (N := Z.to_nat z).
  assert (HNz : INR N = IZR z)
    by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by exact Hz0; reflexivity).
  assert (HN1 : (1 <= N)%nat) by (apply INR_le; rewrite HNz, INR_1; lra).
  assert (Nlo : Rabs (Im s) <= INR N) by (rewrite HNz; lra).
  assert (Nhi : INR N <= Rabs (Im s) + 1) by (rewrite HNz; lra).
  assert (HZ : Cmod (proj1_sig (dgtermC_cv s H0 Hne))
            <= B * (ln (Rabs (Im s)) + 4) ^ 2 + 2 * B + 16 * B * B / (d * exp 1)).
  { pose proof (proj2_sig (dgtermC_cv s H0 Hne)) as HC.
    eapply Rle_cv_lim.
    - intro M. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
      exact (dpsum_bound_ext s d B N M ltac:(lra) Hd4 Hd0 Hs1 Hs2 Ht Hne
               HN1 HB1 Nlo Nhi HB).
    - apply CUn_cv_Cmod. exact HC.
    - apply Un_cv_const. }
  assert (Hhead : Cmod (Dhead s) <= / 4).
  { unfold Dhead.
    assert (Hsq : Cmul (Cminus s C1) (Cminus s C1) <> C0)
      by (apply Cmul_ne0; exact Hne1).
    rewrite Cmod_mul, Cmod_one, Cmod_opp'', (Cmod_Cinv _ Hsq), Cmod_mul.
    assert (Hb : 2 * 2 <= Cmod (Cminus s C1) * Cmod (Cminus s C1))
      by (apply Rmult_le_compat; lra).
    assert (Hi : / (Cmod (Cminus s C1) * Cmod (Cminus s C1)) <= / (2 * 2))
      by (apply Rinv_le_contravar; lra).
    lra. }
  rewrite (zDF_eq s H0 Hne).
  eapply Rle_trans; [ apply Cmod_triangle | ].
  lra.
Qed.

(* the intended instantiation: d = 1/ln|t|, B = e^2 *)
Corollary zeta_deriv_log_bound_below : forall s,
  3 <= Rabs (Im s) -> 4 <= ln (Rabs (Im s)) ->
  1 - / ln (Rabs (Im s)) <= Re s -> Re s <= 2 ->
  Cmod (zDF s)
  <= exp 2 * (ln (Rabs (Im s)) + 4) ^ 2 + 3 * exp 2
     + 16 * exp 2 * exp 2 * ln (Rabs (Im s)) / exp 1.
Proof.
  intros s H3 Hln Hs1 Hs2.
  assert (HT0 : 0 < Rabs (Im s)) by lra.
  assert (HlnT : 0 < ln (Rabs (Im s))) by lra.
  assert (Hd0 : 0 < / ln (Rabs (Im s))) by (apply Rinv_0_lt_compat; exact HlnT).
  assert (Hd4 : / ln (Rabs (Im s)) <= / 4) by (apply Rinv_le_contravar; lra).
  assert (HB1 : 1 <= exp 2) by (pose proof (exp_ineq1_le 2); lra).
  assert (HB : Rpower (Rabs (Im s) + 3) (/ ln (Rabs (Im s))) <= exp 2).
  { unfold Rpower. apply exp_le.
    assert (Hle : ln (Rabs (Im s) + 3) <= 2 * ln (Rabs (Im s))).
    { assert (Hsq : Rabs (Im s) + 3 <= Rabs (Im s) * Rabs (Im s)) by nra.
      eapply Rle_trans; [ apply ln_le'; [ lra | exact Hsq ] | ].
      rewrite ln_mult by lra. lra. }
    apply (Rmult_le_reg_r (ln (Rabs (Im s)))); [ exact HlnT | ].
    assert (E : / ln (Rabs (Im s)) * ln (Rabs (Im s) + 3) * ln (Rabs (Im s))
              = ln (Rabs (Im s) + 3)) by (field; lra).
    rewrite E. lra. }
  pose proof (zeta_deriv_log_bound_ext s (/ ln (Rabs (Im s))) (exp 2)
                Hd0 Hd4 Hs1 Hs2 ltac:(lra) HB1 HB) as H.
  assert (E : 16 * exp 2 * exp 2 / (/ ln (Rabs (Im s)) * exp 1)
            = 16 * exp 2 * exp 2 * ln (Rabs (Im s)) / exp 1)
    by (field; split; [ pose proof (exp_pos 1); lra | lra ]).
  rewrite E in H. exact H.
Qed.

Print Assumptions dhead_term_ext.
Print Assumptions dpsum_bound_ext.
Print Assumptions zeta_deriv_log_bound_ext.
Print Assumptions zeta_deriv_log_bound_below.
