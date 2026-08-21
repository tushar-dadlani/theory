(* ================================================================= *)
(*  ZetaDerivBound.v  --  |zeta'| = O(ln^2 t) in the strip.            *)
(*                                                                    *)
(*  Tier B link [3].  Same split as ZetaLogBound: zeta' is ALREADY     *)
(*  identified as a series in this repo --                             *)
(*                                                                    *)
(*    ZetaDeriv.zDF s = Dhead s + Sum_n dgtermC s n,                   *)
(*    Dhead s = -1/(s-1)^2,   ZetaDeriv.zF_deriv ties it to is_Cderiv, *)
(*                                                                    *)
(*  with dgtermC (CZetaDeriv2) the explicit s-derivative of the Euler- *)
(*  Maclaurin term and Cmod_dgtermC_bound (CZetaDeriv3) its tail       *)
(*  estimate.  So no term-by-term differentiation has to be justified  *)
(*  here; only the two sums have to be estimated.                      *)
(*                                                                    *)
(*  The one genuinely new analytic ingredient is the tail of           *)
(*  Sum ln(n+2)/(n+1)^2.  A crude majorant does NOT work: the head     *)
(*  wants the cut N small and the tail wants it large, and with        *)
(*  ln(n+2) <= 2 sqrt(n+2) the two demands are incompatible (they      *)
(*  balance at N ~ t^{4/3}, leaving a polynomial bound).  What is      *)
(*  needed is the sharp Sum_{n>=N} ln(n+2)/(n+1)^2 = O(ln N / N), and  *)
(*  that telescopes exactly, against                                   *)
(*                                                                    *)
(*      uterm n = (ln (n+2) + 3) / n,                                  *)
(*                                                                    *)
(*  because n*(ln(n+3) - ln(n+2)) <= n/(n+2) <= 1 absorbs the drift.   *)
(*  With that, N ~ |t| serves both ends.  Axiom-clean.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CexpFull CSeries HarmonicSum
        Holomorphic CDeriv CZetaTerm CZeta ZetaFn CZetaDeriv2 CZetaDeriv3 ZetaDeriv
        ZetaStripBound ZetaLogBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  ln u <= u - 1                                                  *)
(* ----------------------------------------------------------------- *)
Lemma ln_le_lin : forall u, 0 < u -> ln u <= u - 1.
Proof.
  intros u Hu.
  pose proof (exp_ineq1_le (u - 1)) as H.
  replace (1 + (u - 1)) with u in H by ring.
  rewrite <- (ln_exp (u - 1)). apply ln_le'; lra.
Qed.

Lemma ln_div' : forall a b, 0 < a -> 0 < b -> ln (a / b) = ln a - ln b.
Proof.
  intros a b Ha Hb. unfold Rdiv.
  rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
  rewrite ln_Rinv by lra. ring.
Qed.

Lemma ln_step_le : forall n, (1 <= n)%nat ->
  ln (INR (S (S (S n)))) - ln (INR (S (S n))) <= / INR (S (S n)).
Proof.
  intros n Hn.
  assert (H2 : 0 < INR (S (S n))) by (apply lt_0_INR; lia).
  assert (E : INR (S (S (S n))) = INR (S (S n)) + 1) by (rewrite S_INR; ring).
  assert (Hd : ln (INR (S (S (S n)))) - ln (INR (S (S n)))
             = ln (INR (S (S (S n))) / INR (S (S n)))).
  { rewrite ln_div'.
    - reflexivity.
    - rewrite E; lra.
    - lra. }
  rewrite Hd.
  eapply Rle_trans; [ apply ln_le_lin; rewrite E; apply Rdiv_lt_0_compat; lra | ].
  rewrite E. assert (Hq : (INR (S (S n)) + 1) / INR (S (S n)) - 1 = / INR (S (S n)))
    by (field; lra).
  rewrite Hq. apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the sharp log tail, by telescoping                             *)
(* ----------------------------------------------------------------- *)
Definition uterm (n : nat) : R := (ln (INR (S (S n))) + 3) / INR n.

Lemma uterm_nonneg : forall n, (1 <= n)%nat -> 0 <= uterm n.
Proof.
  intros n Hn. unfold uterm.
  assert (H0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (HL : 0 <= ln (INR (S (S n))))
    by (apply ln_nonneg; rewrite !S_INR; pose proof (pos_INR n); lra).
  apply Rle_mult_inv_pos; lra.
Qed.

Lemma uterm_step : forall n, (1 <= n)%nat ->
  ln (INR (S (S n))) / (INR (S n) * INR (S n)) <= uterm n - uterm (S n).
Proof.
  intros n Hn.
  assert (Hx : 1 <= INR n) by (replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia).
  assert (Ex : INR (S n) = INR n + 1) by (rewrite S_INR; ring).
  assert (E2 : INR (S (S n)) = INR n + 2) by (rewrite !S_INR; ring).
  set (L := ln (INR (S (S n)))).
  set (L' := ln (INR (S (S (S n))))).
  assert (HL : 0 <= L) by (unfold L; apply ln_nonneg; lra).
  assert (Hstep0 : L' - L <= / INR (S (S n)))
    by (unfold L, L'; apply ln_step_le; exact Hn).
  assert (Hstep : L' - L <= / (INR n + 2)) by (rewrite <- E2; exact Hstep0).
  assert (Hdrift : INR n * (L' - L) <= 1).
  { assert (H1 : INR n * (L' - L) <= INR n * / (INR n + 2))
      by (apply Rmult_le_compat_l; lra).
    assert (H2 : INR n * / (INR n + 2) <= 1).
    { apply (Rmult_le_reg_r (INR n + 2)); [ lra | ].
      rewrite Rmult_assoc, Rinv_l by lra. lra. }
    lra. }
  unfold uterm. fold L. fold L'. rewrite Ex.
  assert (Ediff : (L + 3) / INR n - (L' + 3) / (INR n + 1)
                = (L + 3 - INR n * (L' - L)) / (INR n * (INR n + 1)))
    by (field; lra).
  rewrite Ediff.
  assert (Hnum : L + 2 <= L + 3 - INR n * (L' - L)) by lra.
  assert (Hden : 0 < INR n * (INR n + 1)) by nra.
  assert (Hstep2 : (L + 2) / (INR n * (INR n + 1))
                <= (L + 3 - INR n * (L' - L)) / (INR n * (INR n + 1)))
    by (apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hden | exact Hnum ]).
  assert (Hfinal : L / ((INR n + 1) * (INR n + 1)) <= (L + 2) / (INR n * (INR n + 1))).
  { apply (Rmult_le_reg_r ((INR n + 1) * (INR n + 1) * (INR n * (INR n + 1))));
      [ nra | ].
    field_simplify; nra. }
  lra.
Qed.

Lemma logtail_tele : forall N K, (1 <= N)%nat ->
  sum_f_R0 (fun i => ln (INR (S (S (N + i))))
                   / (INR (S (N + i)) * INR (S (N + i)))) K
  <= uterm N.
Proof.
  intros N K HN.
  assert (Htel : forall K', sum_f_R0 (fun i => uterm (N + i) - uterm (S (N + i))) K'
                          = uterm N - uterm (S (N + K'))).
  { induction K' as [| K' IHK].
    - cbn [sum_f_R0]. rewrite Nat.add_0_r. reflexivity.
    - rewrite tech5, IHK.
      assert (E : (S (N + K') = N + S K')%nat) by lia. rewrite E. ring. }
  eapply Rle_trans.
  - apply sum_Rle. intros i _. apply uterm_step. lia.
  - rewrite Htel. pose proof (uterm_nonneg (S (N + K)) ltac:(lia)). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the HEAD per-term bound for the derivative series              *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_opp'' : forall a, Cmod (Copp a) = Cmod a.
Proof. intro a; unfold Cmod, Cnorm2, Copp; cbn [Re Im]; f_equal; ring. Qed.

Lemma dsk_bound : forall s x, 1 <= Re s -> 1 <= x ->
  Cmod (dsk s x) <= ln x / x.
Proof.
  intros s x Hs Hx. unfold dsk.
  rewrite !Cmod_mul, Cpw_mod.
  assert (E1 : Cmod (Copp C1) = 1) by (rewrite Cmod_opp''; apply Cmod_one).
  assert (E2 : Cmod (RtoC (ln x)) = Rabs (ln x)) by apply Cmod_RtoC.
  rewrite E1, E2, (Rabs_right (ln x) ltac:(pose proof (ln_nonneg x Hx); lra)).
  assert (E3 : Re (Copp s) = - Re s) by (unfold Copp; cbn [Re]; ring).
  rewrite E3.
  assert (H4 : Rpower x (- Re s) <= / x)
    by (rewrite <- (Rpower_m1 x ltac:(lra)); apply Rpower_exp_le; lra).
  assert (H5 : 0 <= ln x) by (apply ln_nonneg; lra).
  unfold Rdiv. nra.
Qed.

Lemma dsGC_bound : forall s x, 1 <= Re s -> 2 <= Rabs (Im s) -> 1 <= x ->
  Cmod (dsGC s x) <= ln x / Rabs (Im s) + / (Rabs (Im s) * Rabs (Im s)).
Proof.
  intros s x Hs Ht Hx.
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hlow : Rabs (Im s) <= Cmod (Cminus C1 s)).
  { eapply Rle_trans; [ | apply (Im_le_Cmod (Cminus C1 s)) ].
    assert (E : Im (Cminus C1 s) = - Im s) by (unfold Cminus, C1; cbn [Re Im]; ring).
    rewrite E, Rabs_Ropp. apply Rle_refl. }
  assert (HRe : Re (Cminus C1 s) = 1 - Re s) by (unfold Cminus, C1; cbn [Re Im]; ring).
  assert (Hp : Rpower x (1 - Re s) <= 1).
  { eapply Rle_trans; [ apply (Rpower_exp_le x (1 - Re s) 0); lra | ].
    rewrite Rpower_0'. lra. }
  assert (Hp0 : 0 < Rpower x (1 - Re s)) by (unfold Rpower; apply exp_pos).
  assert (Hi : / Cmod (Cminus C1 s) <= / Rabs (Im s))
    by (apply Rinv_le_contravar; lra).
  assert (Hi0 : 0 < / Cmod (Cminus C1 s)) by (apply Rinv_0_lt_compat; lra).
  assert (Hln : 0 <= ln x) by (apply ln_nonneg; lra).
  unfold dsGC.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  apply Rplus_le_compat.
  - rewrite !Cmod_mul, Cpw_mod, (Cmod_Cinv _ Hne), HRe, Cmod_RtoC,
      (Rabs_left1 (- ln x) ltac:(lra)), Ropp_involutive.
    assert (Hstep : Rpower x (1 - Re s) * / Cmod (Cminus C1 s) <= 1 * / Rabs (Im s))
      by (apply Rmult_le_compat; lra).
    unfold Rdiv. nra.
  - rewrite !Cmod_mul, Cpw_mod, (Cmod_Cinv _ Hne), HRe.
    assert (Hsq : / Cmod (Cminus C1 s) * / Cmod (Cminus C1 s)
               <= / Rabs (Im s) * / Rabs (Im s))
      by (apply Rmult_le_compat; lra).
    assert (Hinv : / (Rabs (Im s) * Rabs (Im s)) = / Rabs (Im s) * / Rabs (Im s))
      by (field; lra).
    rewrite Hinv. nra.
Qed.

Lemma dhead_term : forall s n, 1 <= Re s -> 2 <= Rabs (Im s) ->
  Cmod (dgtermC s n)
  <= ln (INR (S n)) / INR (S n)
     + 2 * (ln (INR (S (S n))) / Rabs (Im s) + / (Rabs (Im s) * Rabs (Im s))).
Proof.
  intros s n Hs Ht.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hy : 1 <= INR (S (S n))) by (rewrite !S_INR; pose proof (pos_INR n); lra).
  assert (Hmono : ln (INR (S n)) <= ln (INR (S (S n))))
    by (apply ln_le'; [ lra | apply le_INR; lia ]).
  unfold dgtermC.
  eapply Rle_trans; [ apply Cmod_sub_le | ].
  pose proof (dsk_bound s _ Hs Hx) as H1.
  assert (H2 : Cmod (Cminus (dsGC s (INR (S (S n)))) (dsGC s (INR (S n))))
            <= 2 * (ln (INR (S (S n))) / Rabs (Im s)
                    + / (Rabs (Im s) * Rabs (Im s)))).
  { eapply Rle_trans; [ apply Cmod_sub_le | ].
    pose proof (dsGC_bound s _ Hs Ht Hy) as A.
    pose proof (dsGC_bound s _ Hs Ht Hx) as B.
    assert (Hd : ln (INR (S n)) / Rabs (Im s) <= ln (INR (S (S n))) / Rabs (Im s))
      by (apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | exact Hmono ]).
    lra. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the partial sums of the derivative series                      *)
(* ----------------------------------------------------------------- *)
Lemma dhead_sum : forall s m, 1 <= Re s -> 2 <= Rabs (Im s) ->
  sum_f_R0 (fun n => Cmod (dgtermC s n)) m
  <= ln (INR (S m)) * (ln (INR (S m)) + 1)
     + 2 / Rabs (Im s) * (INR (S m) * ln (INR (S (S m))))
     + 2 / (Rabs (Im s) * Rabs (Im s)) * INR (S m).
Proof.
  intros s m Hs Ht.
  assert (HT : 0 < Rabs (Im s)) by lra.
  eapply Rle_trans.
  - apply sum_Rle. intros n _. apply dhead_term; assumption.
  - rewrite !sum_plus.
    assert (Hmono : forall n, (n <= m)%nat -> ln (INR (S n)) <= ln (INR (S m))).
    { intros n Hn. apply ln_le'; [ | apply le_INR; lia ].
      rewrite S_INR; pose proof (pos_INR n); lra. }
    assert (Hmono2 : forall n, (n <= m)%nat ->
              ln (INR (S (S n))) <= ln (INR (S (S m)))).
    { intros n Hn. apply ln_le'; [ | apply le_INR; lia ].
      rewrite !S_INR; pose proof (pos_INR n); lra. }
    (* piece 1 : sum ln(S n)/(S n) *)
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
    (* piece 2 : sum 2 ln(S(S n))/T *)
    assert (P2 : sum_f_R0 (fun n => 2 * (ln (INR (S (S n))) / Rabs (Im s))) m
              <= 2 / Rabs (Im s) * (INR (S m) * ln (INR (S (S m))))).
    { eapply Rle_trans.
      - apply sum_Rle. intros n Hn.
        assert (Hd : 2 * (ln (INR (S (S n))) / Rabs (Im s))
                  <= 2 / Rabs (Im s) * ln (INR (S (S m)))).
        { assert (Hi : 0 < / Rabs (Im s)) by (apply Rinv_0_lt_compat; lra).
          pose proof (Hmono2 n Hn). unfold Rdiv. nra. }
        exact Hd.
      - rewrite sum_cte. nra. }
    (* piece 3 : the constant 2/T^2 *)
    assert (P3 : sum_f_R0 (fun _ : nat => 2 * / (Rabs (Im s) * Rabs (Im s))) m
              = 2 / (Rabs (Im s) * Rabs (Im s)) * INR (S m))
      by (rewrite sum_cte; unfold Rdiv; ring).
    assert (Hsplit : sum_f_R0 (fun n => 2 * (ln (INR (S (S n))) / Rabs (Im s)
                       + / (Rabs (Im s) * Rabs (Im s)))) m
                   = sum_f_R0 (fun n => 2 * (ln (INR (S (S n))) / Rabs (Im s))) m
                     + sum_f_R0 (fun _ : nat => 2 * / (Rabs (Im s) * Rabs (Im s))) m).
    { rewrite <- sum_plus. apply sum_eq. intros i _. ring. }
    rewrite Hsplit, P3. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE DERIVATIVE BOUND                                           *)
(* ----------------------------------------------------------------- *)
Lemma ln_shift_gen : forall k t, 0 <= k -> k <= 3 -> 2 <= t -> ln (t + k) <= ln t + 2.
Proof.
  intros k t Hk0 Hk3 Ht.
  assert (H : t + k <= 5 / 2 * t) by lra.
  eapply Rle_trans; [ apply ln_le'; [ lra | exact H ] | ].
  rewrite ln_mult by lra.
  assert (Hl : ln (5 / 2) <= 2).
  { pose proof (exp_ineq1_le 1) as H1.
    assert (He : 2 <= exp 1) by lra.
    assert (Hsq : 4 <= exp 1 * exp 1)
      by (replace 4 with (2 * 2) by ring; apply Rmult_le_compat; lra).
    assert (H2 : 5 / 2 <= exp 1 * exp 1) by lra.
    rewrite <- exp_plus in H2.
    replace (1 + 1) with 2 in H2 by ring.
    eapply Rle_trans; [ apply ln_le'; [ lra | exact H2 ] | ].
    rewrite ln_exp. lra. }
  lra.
Qed.

Lemma dpsum_bound_N : forall s N M, 1 <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  Cminus C1 s <> C0 -> (1 <= N)%nat ->
  Rabs (Im s) <= INR N -> INR N <= Rabs (Im s) + 1 ->
  sum_f_R0 (fun n => Cmod (dgtermC s n)) M
  <= (ln (Rabs (Im s))) ^ 2 + 12 * ln (Rabs (Im s)) + 35.
Proof.
  intros s N M Hs1 Hs2 Ht Hne HN Nlo Nhi.
  set (T := Rabs (Im s)) in *. set (L := ln T).
  assert (HT0 : 0 < T) by lra.
  assert (HL0 : 0 <= L) by (unfold L; apply ln_nonneg; lra).
  assert (HTinv : / T <= / 2) by (apply Rinv_le_contravar; lra).
  assert (HTi0 : 0 < / T) by (apply Rinv_0_lt_compat; lra).
  (* the head estimate at any cut m with INR (S m) <= INR N *)
  assert (Hhead : forall m, INR (S m) <= INR N ->
            sum_f_R0 (fun n => Cmod (dgtermC s n)) m <= L ^ 2 + 8 * L + 14).
  { intros m Hm.
    pose proof (dhead_sum s m Hs1 Ht) as HS. fold T in HS.
    assert (HSm0 : 0 < INR (S m)) by (apply lt_0_INR; lia).
    assert (HSm : INR (S m) <= T + 1) by lra.
    assert (HSSm : INR (S (S m)) <= T + 2) by (rewrite (S_INR (S m)); lra).
    assert (Hl1 : ln (INR (S m)) <= L + 2).
    { eapply Rle_trans; [ apply ln_le'; [ lra | exact HSm ] | ].
      apply (ln_shift_gen 1 T); lra. }
    assert (Hl2 : ln (INR (S (S m))) <= L + 2).
    { eapply Rle_trans; [ apply ln_le'; [ rewrite (S_INR (S m)); lra | exact HSSm ] | ].
      apply (ln_shift_gen 2 T); lra. }
    assert (Hl1p : 0 <= ln (INR (S m))) by (apply ln_nonneg; rewrite S_INR;
      pose proof (pos_INR m); lra).
    assert (Hl2p : 0 <= ln (INR (S (S m)))) by (apply ln_nonneg; rewrite !S_INR;
      pose proof (pos_INR m); lra).
    assert (A1 : ln (INR (S m)) * (ln (INR (S m)) + 1) <= (L + 2) * (L + 3)) by nra.
    assert (A2 : 2 / T * (INR (S m) * ln (INR (S (S m)))) <= 3 * (L + 2)).
    { assert (Hp : INR (S m) * ln (INR (S (S m))) <= (T + 1) * (L + 2)) by nra.
      assert (Hq : 2 / T * ((T + 1) * (L + 2)) <= 3 * (L + 2)).
      { assert (Hr : 2 / T * (T + 1) <= 3).
        { assert (E : 2 / T * (T + 1) = 2 + 2 / T) by (field; lra).
          assert (E2 : 2 / T = 2 * / T) by (unfold Rdiv; ring). lra. }
        nra. }
      assert (Hs : 2 / T * (INR (S m) * ln (INR (S (S m)))) <= 2 / T * ((T + 1) * (L + 2)))
        by (apply Rmult_le_compat_l; [ unfold Rdiv; nra | exact Hp ]).
      lra. }
    assert (A3 : 2 / (T * T) * INR (S m) <= 2).
    { assert (E : 2 / (T * T) * INR (S m) <= 2 / (T * T) * (T + 1))
        by (apply Rmult_le_compat_l; [ unfold Rdiv; apply Rle_mult_inv_pos; nra | lra ]).
      assert (E2 : 2 / (T * T) * (T + 1) = 2 / T + 2 / (T * T)) by (field; lra).
      assert (E3 : 2 / (T * T) <= 2 / T)
        by (unfold Rdiv; apply Rmult_le_compat_l; [ lra | apply Rinv_le_contravar; nra ]).
      assert (E4 : 2 / T = 2 * / T) by (unfold Rdiv; ring). lra. }
    nra. }
  assert (Hsmod : Cmod s <= 2 + T).
  { pose proof (Cmod_le_sum s) as H.
    rewrite (Rabs_right (Re s) ltac:(lra)) in H. unfold T. lra. }
  assert (Hs0 : 0 <= Cmod s) by apply Cmod_nonneg.
  destruct (Nat.le_gt_cases N M) as [Hge | Hlt].
  - destruct N as [| Nm1]; [ exfalso; lia | ].
    assert (Hlt' : (Nm1 < M)%nat) by lia.
    rewrite (tech2 (fun n => Cmod (dgtermC s n)) Nm1 M Hlt').
    assert (Hh : sum_f_R0 (fun n => Cmod (dgtermC s n)) Nm1 <= L ^ 2 + 8 * L + 14)
      by (apply Hhead; lra).
    (* the tail *)
    assert (Htail : sum_f_R0 (fun i => Cmod (dgtermC s (S Nm1 + i))) (M - S Nm1)
                 <= 2 * / INR (S Nm1) + 2 * Cmod s * uterm (S Nm1)).
    { set (K := (M - S Nm1)%nat).
      eapply Rle_trans.
      - apply sum_Rle. intros i _.
        assert (Hxi : 1 <= INR (S (S Nm1 + i)))
          by (rewrite S_INR; pose proof (pos_INR (S Nm1 + i)); lra).
        pose proof (Cmod_dgtermC_bound s (S Nm1 + i) ltac:(lra) Hne) as HB.
        unfold dbound1 in HB.
        assert (Hp : Rpower (INR (S (S Nm1 + i))) (- Re s - 1)
                  <= / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))).
        { rewrite <- (Rpower_m2 (INR (S (S Nm1 + i))) ltac:(lra)).
          apply Rpower_exp_le; lra. }
        assert (Hln0 : 0 <= ln (INR (S (S (S Nm1 + i)))))
          by (apply ln_nonneg; rewrite !S_INR; pose proof (pos_INR (S Nm1 + i)); lra).
        assert (Hgoal : Cmod (dgtermC s (S Nm1 + i))
                     <= 2 * / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))
                        + 2 * Cmod s * (ln (INR (S (S (S Nm1 + i))))
                            / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i))))).
        { assert (Hpos : 0 <= 1 + ln (INR (S (S (S Nm1 + i)))) * Cmod s) by nra.
          unfold Rdiv. nra. }
        exact Hgoal.
      - rewrite sum_plus.
        assert (E1 : sum_f_R0 (fun i => 2 * / (INR (S (S Nm1 + i))
                       * INR (S (S Nm1 + i)))) K
                   = 2 * sum_f_R0 (fun i => / (INR (S (S Nm1 + i))
                       * INR (S (S Nm1 + i)))) K).
        { rewrite (scal_sum (fun i => / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))) K 2).
          apply sum_eq; intros i _; ring. }
        assert (E2 : sum_f_R0 (fun i => 2 * Cmod s * (ln (INR (S (S (S Nm1 + i))))
                       / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i))))) K
                   = 2 * Cmod s * sum_f_R0 (fun i => ln (INR (S (S (S Nm1 + i))))
                       / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))) K).
        { rewrite (scal_sum (fun i => ln (INR (S (S (S Nm1 + i))))
                     / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))) K (2 * Cmod s)).
          apply sum_eq; intros i _; ring. }
        rewrite E1, E2.
        pose proof (tail_tele (S Nm1) K ltac:(lia)) as T1.
        pose proof (logtail_tele (S Nm1) K ltac:(lia)) as T2.
        assert (S1 : 2 * sum_f_R0 (fun i => / (INR (S (S Nm1 + i))
                       * INR (S (S Nm1 + i)))) K <= 2 * / INR (S Nm1)) by lra.
        assert (S2 : 2 * Cmod s * sum_f_R0 (fun i => ln (INR (S (S (S Nm1 + i))))
                       / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))) K
                  <= 2 * Cmod s * uterm (S Nm1))
          by (apply Rmult_le_compat_l; [ lra | exact T2 ]).
        lra. }
    (* size of the tail *)
    assert (Hut : uterm (S Nm1) <= (L + 5) / T).
    { unfold uterm.
      assert (HSS : INR (S (S (S Nm1))) <= T + 3).
      { assert (E : INR (S (S (S Nm1))) = INR (S Nm1) + 2)
          by (rewrite (S_INR (S (S Nm1))), (S_INR (S Nm1)); ring).
        lra. }
      assert (Hl3 : ln (INR (S (S (S Nm1)))) <= L + 2).
      { eapply Rle_trans; [ apply ln_le'; [ rewrite !S_INR;
          pose proof (pos_INR Nm1); lra | exact HSS ] | ].
        apply (ln_shift_gen 3 T); lra. }
      assert (Hd : / INR (S Nm1) <= / T) by (apply Rinv_le_contravar; lra).
      assert (Hn0 : 0 < / INR (S Nm1)) by (apply Rinv_0_lt_compat; lra).
      assert (Hnum : 0 <= ln (INR (S (S (S Nm1)))) + 3)
        by (pose proof (ln_nonneg (INR (S (S (S Nm1))))
              ltac:(replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia)); lra).
      unfold Rdiv. nra. }
    assert (Hnum2 : 2 * / INR (S Nm1) + 2 * Cmod s * uterm (S Nm1) <= 4 * L + 21).
    { assert (D1 : 2 * / INR (S Nm1) <= 1).
      { assert (Hd : / INR (S Nm1) <= / T) by (apply Rinv_le_contravar; lra). lra. }
      assert (Hu0 : 0 <= uterm (S Nm1)) by (apply uterm_nonneg; lia).
      assert (D2 : 2 * Cmod s * uterm (S Nm1) <= 2 * (2 + T) * ((L + 5) / T))
        by (apply Rmult_le_compat; lra).
      assert (D3 : 2 * (2 + T) * ((L + 5) / T) = (4 / T + 2) * (L + 5))
        by (field; lra).
      assert (D4 : 4 / T <= 2)
        by (assert (E : 4 / T = 4 * / T) by (unfold Rdiv; ring); lra).
      nra. }
    lra.
  - apply Rle_trans with (L ^ 2 + 8 * L + 14); [ | lra ].
    apply Hhead. apply le_INR. lia.
Qed.

Theorem zeta_deriv_log_bound : forall s, 1 <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  Cmod (zDF s) <= 10 * (ln (Rabs (Im s)) + 3) ^ 2.
Proof.
  intros s Hs1 Hs2 Ht.
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
  set (L := ln (Rabs (Im s))).
  assert (HL0 : 0 <= L) by (unfold L; apply ln_nonneg; lra).
  (* the cut point *)
  set (z := up (Rabs (Im s))).
  destruct (archimed (Rabs (Im s))) as [Hup1 Hup2]. fold z in Hup1, Hup2.
  assert (Hz0 : (0 <= z)%Z) by (apply le_IZR; simpl; lra).
  set (N := Z.to_nat z).
  assert (HNz : INR N = IZR z)
    by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by exact Hz0; reflexivity).
  assert (HN1 : (1 <= N)%nat) by (apply INR_le; rewrite HNz, INR_1; lra).
  assert (Nlo : Rabs (Im s) <= INR N) by (rewrite HNz; lra).
  assert (Nhi : INR N <= Rabs (Im s) + 1) by (rewrite HNz; lra).
  (* the derivative series *)
  assert (HZ : Cmod (proj1_sig (dgtermC_cv s H0 Hne)) <= L ^ 2 + 12 * L + 35).
  { pose proof (proj2_sig (dgtermC_cv s H0 Hne)) as HC.
    eapply Rle_cv_lim.
    - intro M. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
      exact (dpsum_bound_N s N M Hs1 Hs2 Ht Hne HN1 Nlo Nhi).
    - apply CUn_cv_Cmod. exact HC.
    - apply Un_cv_const. }
  (* the pole term *)
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
  nra.
Qed.

(* the same bound on the ACTUAL derivative, via ZetaDeriv.zF_deriv *)
Corollary zeta_deriv_bound_is_deriv : forall s, 1 <= Re s -> Re s <= 2 ->
  2 <= Rabs (Im s) ->
  is_Cderiv zF s (zDF s) /\ Cmod (zDF s) <= 10 * (ln (Rabs (Im s)) + 3) ^ 2.
Proof.
  intros s Hs1 Hs2 Ht. split; [ | apply zeta_deriv_log_bound; assumption ].
  apply zF_deriv. unfold inDom. split; [ lra | ].
  intro Hc. apply (f_equal Im) in Hc.
  unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
  assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra.
Qed.

Print Assumptions logtail_tele.
Print Assumptions dhead_term.
Print Assumptions zeta_deriv_log_bound.
Print Assumptions zeta_deriv_bound_is_deriv.
