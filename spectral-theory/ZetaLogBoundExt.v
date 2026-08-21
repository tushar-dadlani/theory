(* ================================================================= *)
(*  ZetaLogBoundExt.v  --  the zeta bound, extended BELOW Re s = 1.    *)
(*                                                                    *)
(*    zeta_log_bound_ext : 0 <= d <= 1/2,  1 - d <= Re s <= 2,         *)
(*      2 <= |Im s|,  1 <= B,  (|Im s| + 3)^d <= B   ==>               *)
(*        Cmod (zF s)  <=  B * (ln |Im s| + 15)                        *)
(*                                                                    *)
(*  Link [1], restated on a strip that DIPS BELOW the line.  This is   *)
(*  what Tier B link [4] needs: the mean value segment for a zero runs *)
(*  from beta < 1 up to a > 1, so a bound stated on Re s >= 1 (as      *)
(*  ZetaLogBound.zeta_log_bound is) never reaches the zero.            *)
(*                                                                    *)
(*  The intended instantiation is d = 1/ln|t|, for which               *)
(*  B = (|t|+3)^{1/ln|t|} = exp(ln(|t|+3)/ln|t|) is bounded by e^2 for *)
(*  every |t| >= 2 and tends to e.  Carrying B as a parameter rather   *)
(*  than fixing d keeps the arithmetic out of the analysis: the caller *)
(*  discharges (|t|+3)^d <= e^2 from ln(|t|+3) <= 2 ln|t|, i.e. from   *)
(*  |t| + 3 <= |t|^2.                                                 *)
(*                                                                    *)
(*  Two changes against the Re s >= 1 proof, and only two:             *)
(*                                                                    *)
(*   * head: x^{-Re s} <= x^{-1+d} = (1/x) x^d and x^{1-Re s} <= x^d,  *)
(*     so every head term picks up one factor x^d <= B.  Bounded       *)
(*     because the head only runs to x ~ |t| + 3.                      *)
(*   * tail: the exponent is now -(2-d) rather than -2, so the         *)
(*     1/(n(n+1)) telescoping is unavailable and RPowerTail.ptail_delta *)
(*     replaces ZetaLogBound.tail_tele.  The resulting N^{-(1-d)}      *)
(*     is (1/N) N^d <= B/N, so the tail is still O(1) at N ~ |t|.      *)
(*                                                                    *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CexpFull CSeries HarmonicSum
        CZetaTerm CZeta ZetaFn ZetaStripBound ZetaLogBound
        RPowerTail RPowerLogTail.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the HEAD per-term bound, with the x^d factor                   *)
(* ----------------------------------------------------------------- *)
Lemma head_term_ext : forall s d B n,
  0 <= d -> 1 - d <= Re s -> 2 <= Rabs (Im s) ->
  Rpower (INR (S (S n))) d <= B ->
  Cmod (gtermC s n) <= B * (/ INR (S n) + 2 / Rabs (Im s)).
Proof.
  intros s d B n Hd Hs Ht HB.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hy : 1 <= INR (S (S n))) by (rewrite !S_INR; pose proof (pos_INR n); lra).
  assert (Hxy : INR (S n) <= INR (S (S n))) by (apply le_INR; lia).
  assert (HBx : Rpower (INR (S n)) d <= B).
  { eapply Rle_trans; [ apply Rpower_base_le; [ lra | exact Hxy | exact Hd ] | exact HB ]. }
  assert (HB1 : 1 <= B).
  { eapply Rle_trans; [ | exact HB ].
    assert (E : (1:R) = Rpower (INR (S (S n))) 0) by (rewrite Rpower_0'; reflexivity).
    rewrite E at 1. apply Rpower_exp_le; lra. }
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hlow : Rabs (Im s) <= Cmod (Cminus C1 s)).
  { eapply Rle_trans; [ | apply (Im_le_Cmod (Cminus C1 s)) ].
    assert (E : Im (Cminus C1 s) = - Im s) by (unfold Cminus, C1; cbn [Re Im]; ring).
    rewrite E, Rabs_Ropp. apply Rle_refl. }
  assert (HRe : Re (Cminus C1 s) = 1 - Re s) by (unfold Cminus, C1; cbn [Re Im]; ring).
  (* the g piece *)
  assert (Hg : Cmod (gC s (INR (S n))) <= B * / INR (S n)).
  { unfold gC. rewrite Cpw_mod.
    assert (E : Re (Copp s) = - Re s) by (unfold Copp; cbn [Re]; ring).
    rewrite E.
    assert (H1 : Rpower (INR (S n)) (- Re s) <= Rpower (INR (S n)) (-1 + d))
      by (apply Rpower_exp_le; lra).
    assert (H2 : Rpower (INR (S n)) (-1 + d)
               = / INR (S n) * Rpower (INR (S n)) d)
      by (rewrite Rpower_plus, (Rpower_m1 (INR (S n)) ltac:(lra)); reflexivity).
    assert (H3 : 0 < / INR (S n)) by (apply Rinv_0_lt_compat; lra).
    assert (H4 : / INR (S n) * Rpower (INR (S n)) d <= B * / INR (S n)).
    { rewrite Rmult_comm. apply Rmult_le_compat_r; lra. }
    lra. }
  (* the two G pieces *)
  assert (HG : forall x, 1 <= x -> Rpower x d <= B ->
                 Cmod (GC s x) <= B * / Rabs (Im s)).
  { intros x Hx1 HBx1. unfold GC. rewrite Cmod_mul, (Cmod_Cinv _ Hne), Cpw_mod, HRe.
    assert (H1 : Rpower x (1 - Re s) <= B)
      by (eapply Rle_trans; [ apply (Rpower_exp_le x (1 - Re s) d); lra | exact HBx1 ]).
    assert (H2 : 0 < Rpower x (1 - Re s)) by (unfold Rpower; apply exp_pos).
    assert (H3 : 0 < Rabs (Im s)) by lra.
    assert (H4 : / Cmod (Cminus C1 s) <= / Rabs (Im s))
      by (apply Rinv_le_contravar; lra).
    assert (H5 : 0 < / Cmod (Cminus C1 s)) by (apply Rinv_0_lt_compat; lra).
    assert (Hstep : Rpower x (1 - Re s) * / Cmod (Cminus C1 s)
                 <= B * / Rabs (Im s))
      by (apply Rmult_le_compat; lra).
    lra. }
  unfold gtermC.
  eapply Rle_trans; [ apply Cmod_sub_le | ].
  assert (Hsub : Cmod (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n))))
              <= B * / Rabs (Im s) + B * / Rabs (Im s)).
  { eapply Rle_trans; [ apply Cmod_sub_le | ].
    pose proof (HG _ Hy HB); pose proof (HG _ Hx HBx); lra. }
  assert (Hd2 : B * (/ INR (S n) + 2 / Rabs (Im s))
              = B * / INR (S n) + (B * / Rabs (Im s) + B * / Rabs (Im s)))
    by (unfold Rdiv; ring).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the TAIL per-term bound, at exponent -(2-d)                    *)
(* ----------------------------------------------------------------- *)
Lemma tail_term_ext : forall s d n, 0 <= d -> d <= / 2 -> 1 - d <= Re s ->
  Cminus C1 s <> C0 ->
  Cmod (gtermC s n) <= 2 * Cmod s * Rpower (INR (S n)) (- (2 - d)).
Proof.
  intros s d n Hd Hd2 Hs Hne.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  pose proof (Cmod_gtermC_bound s n ltac:(lra) Hne) as HB.
  assert (Hp : Rpower (INR (S n)) (- Re s - 1) <= Rpower (INR (S n)) (- (2 - d)))
    by (apply Rpower_exp_le; lra).
  pose proof (Cmod_nonneg s) as Hs0.
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the head sum                                                   *)
(* ----------------------------------------------------------------- *)
Lemma head_sum_ext : forall s d B m,
  0 <= d -> 1 - d <= Re s -> 2 <= Rabs (Im s) ->
  Rpower (INR (S (S m))) d <= B ->
  sum_f_R0 (fun n => Cmod (gtermC s n)) m
  <= B * (ln (INR (S m)) + 1 + 2 / Rabs (Im s) * INR (S m)).
Proof.
  intros s d B m Hd Hs Ht HB.
  eapply Rle_trans.
  - apply sum_Rle. intros n Hn.
    apply (head_term_ext s d B n Hd Hs Ht).
    eapply Rle_trans; [ | exact HB ].
    apply Rpower_base_le; [ | apply le_INR; lia | exact Hd ].
    rewrite !S_INR; pose proof (pos_INR n); lra.
  - assert (E : sum_f_R0 (fun n => B * (/ INR (S n) + 2 / Rabs (Im s))) m
              = B * sum_f_R0 (fun n => / INR (S n) + 2 / Rabs (Im s)) m).
    { rewrite (scal_sum (fun n => / INR (S n) + 2 / Rabs (Im s)) m B).
      apply sum_eq; intros i _; ring. }
    rewrite E, sum_plus, sum_cte.
    assert (HB1 : 0 <= B).
    { eapply Rle_trans; [ | exact HB ]. left; unfold Rpower; apply exp_pos. }
    pose proof (harm_sum_le m). nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the partial sums, split at N ~ |Im s|                          *)
(* ----------------------------------------------------------------- *)
Lemma psum_bound_ext : forall s d B N M,
  0 <= d -> d <= / 2 -> 1 - d <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  Cminus C1 s <> C0 -> (1 <= N)%nat -> 1 <= B ->
  Rabs (Im s) <= INR N -> INR N <= Rabs (Im s) + 1 ->
  Rpower (Rabs (Im s) + 3) d <= B ->
  sum_f_R0 (fun n => Cmod (gtermC s n)) M <= B * (ln (Rabs (Im s)) + 13).
Proof.
  intros s d B N M Hd Hd2 Hs1 Hs2 Ht Hne HN HB1 Nlo Nhi HB.
  set (T := Rabs (Im s)) in *.
  assert (HT0 : 0 < T) by lra.
  assert (HNpos : 0 < INR N) by lra.
  (* every base occurring in the head is at most T + 3 *)
  assert (Hbase : forall x, 1 <= x -> x <= T + 3 -> Rpower x d <= B).
  { intros x Hx1 Hx3.
    eapply Rle_trans; [ apply Rpower_base_le; [ lra | exact Hx3 | exact Hd ] | exact HB ]. }
  assert (Hhead : forall m, INR (S m) <= INR N ->
            sum_f_R0 (fun n => Cmod (gtermC s n)) m <= B * (ln T + 5)).
  { intros m Hm.
    assert (HSm0 : 0 < INR (S m)) by (apply lt_0_INR; lia).
    assert (HSm : INR (S m) <= T + 1) by lra.
    assert (HSSm : INR (S (S m)) <= T + 2) by (rewrite (S_INR (S m)); lra).
    assert (HBm : Rpower (INR (S (S m))) d <= B)
      by (apply Hbase; [ rewrite !S_INR; pose proof (pos_INR m); lra | lra ]).
    pose proof (head_sum_ext s d B m Hd Hs1 Ht HBm) as HS. fold T in HS.
    assert (Hl1 : ln (INR (S m)) <= ln T + 1).
    { eapply Rle_trans; [ apply ln_le'; [ lra | exact HSm ] | ].
      apply ln_shift; lra. }
    assert (Hlin : 2 / T * INR (S m) <= 3).
    { assert (H1 : 2 / T * INR (S m) <= 2 / T * (T + 1))
        by (apply Rmult_le_compat_l; [ apply Rle_mult_inv_pos; lra | lra ]).
      assert (H2 : 2 / T * (T + 1) = 2 + 2 / T) by (field; lra).
      assert (H3 : 2 / T <= 1)
        by (assert (E : 2 / T = 2 * / T) by (unfold Rdiv; ring);
            assert (Hi : / T <= / 2) by (apply Rinv_le_contravar; lra); lra).
      lra. }
    assert (Hin : ln (INR (S m)) + 1 + 2 / T * INR (S m) <= ln T + 5) by lra.
    assert (Hmul : B * (ln (INR (S m)) + 1 + 2 / T * INR (S m)) <= B * (ln T + 5))
      by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hsmod : Cmod s <= 2 + T).
  { pose proof (Cmod_le_sum s) as H.
    rewrite (Rabs_right (Re s) ltac:(lra)) in H. unfold T. lra. }
  assert (Hs0 : 0 <= Cmod s) by apply Cmod_nonneg.
  destruct (Nat.le_gt_cases N M) as [Hge | Hlt].
  - destruct N as [| Nm1]; [ exfalso; lia | ].
    assert (Hlt' : (Nm1 < M)%nat) by lia.
    rewrite (tech2 (fun n => Cmod (gtermC s n)) Nm1 M Hlt').
    assert (Hh : sum_f_R0 (fun n => Cmod (gtermC s n)) Nm1 <= B * (ln T + 5))
      by (apply Hhead; lra).
    assert (Htail : sum_f_R0 (fun i => Cmod (gtermC s (S Nm1 + i))) (M - S Nm1)
                 <= 2 * Cmod s * (2 * Rpower (INR (S Nm1)) (- (1 - d)))).
    { set (K := (M - S Nm1)%nat).
      eapply Rle_trans.
      - apply sum_Rle. intros i _. apply (tail_term_ext s d); assumption.
      - assert (E : sum_f_R0 (fun i => 2 * Cmod s
                      * Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K
                  = 2 * Cmod s * sum_f_R0 (fun i =>
                      Rpower (INR (S (S Nm1 + i))) (- (2 - d))) K).
        { rewrite (scal_sum (fun i => Rpower (INR (S (S Nm1 + i))) (- (2 - d)))
                     K (2 * Cmod s)).
          apply sum_eq; intros i _; ring. }
        rewrite E.
        pose proof (ptail_delta d (S Nm1) K Hd Hd2 ltac:(lia)) as HP.
        apply Rmult_le_compat_l; [ lra | exact HP ]. }
    (* size of the tail *)
    assert (Hrp : Rpower (INR (S Nm1)) (- (1 - d)) <= B * / T).
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
    assert (Hnum : 2 * Cmod s * (2 * Rpower (INR (S Nm1)) (- (1 - d))) <= 8 * B).
    { assert (Hr0 : 0 <= Rpower (INR (S Nm1)) (- (1 - d)))
        by (left; unfold Rpower; apply exp_pos).
      assert (D1 : 2 * Cmod s * (2 * Rpower (INR (S Nm1)) (- (1 - d)))
                <= 2 * (2 + T) * (2 * (B * / T)))
        by (apply Rmult_le_compat; lra).
      assert (D2 : 2 * (2 + T) * (2 * (B * / T)) = (4 + 8 / T) * B) by (field; lra).
      assert (D3 : 8 / T <= 4)
        by (assert (E : 8 / T = 8 * / T) by (unfold Rdiv; ring);
            assert (Hi : / T <= / 2) by (apply Rinv_le_contravar; lra); lra).
      nra. }
    lra.
  - apply Rle_trans with (B * (ln T + 5)); [ apply Hhead; apply le_INR; lia | nra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE EXTENDED BOUND                                             *)
(* ----------------------------------------------------------------- *)
Theorem zeta_log_bound_ext : forall s d B,
  0 <= d -> d <= / 2 -> 1 - d <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  1 <= B -> Rpower (Rabs (Im s) + 3) d <= B ->
  Cmod (zF s) <= B * (ln (Rabs (Im s)) + 15).
Proof.
  intros s d B Hd Hd2 Hs1 Hs2 Ht HB1 HB.
  assert (H0 : 0 < Re s) by lra.
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hne1 : Cminus s C1 <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  set (z := up (Rabs (Im s))).
  destruct (archimed (Rabs (Im s))) as [Hup1 Hup2]. fold z in Hup1, Hup2.
  assert (Hz0 : (0 <= z)%Z) by (apply le_IZR; simpl; lra).
  set (N := Z.to_nat z).
  assert (HNz : INR N = IZR z)
    by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by exact Hz0; reflexivity).
  assert (HN1 : (1 <= N)%nat) by (apply INR_le; rewrite HNz, INR_1; lra).
  assert (Nlo : Rabs (Im s) <= INR N) by (rewrite HNz; lra).
  assert (Nhi : INR N <= Rabs (Im s) + 1) by (rewrite HNz; lra).
  assert (HZ : Cmod (proj1_sig (gtermC_cv s H0 Hne))
            <= B * (ln (Rabs (Im s)) + 13)).
  { pose proof (proj2_sig (gtermC_cv s H0 Hne)) as HC.
    eapply Rle_cv_lim.
    - intro M. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
      exact (psum_bound_ext s d B N M Hd Hd2 Hs1 Hs2 Ht Hne HN1 HB1 Nlo Nhi HB).
    - apply CUn_cv_Cmod. exact HC.
    - apply Un_cv_const. }
  assert (Hpole : / Cmod (Cminus s C1) <= / 2).
  { assert (Hlow : Rabs (Im s) <= Cmod (Cminus s C1)).
    { eapply Rle_trans; [ | apply (Im_le_Cmod (Cminus s C1)) ].
      assert (E : Im (Cminus s C1) = Im s) by (unfold Cminus, C1; cbn [Re Im]; ring).
      rewrite E. apply Rle_refl. }
    apply Rinv_le_contravar; lra. }
  rewrite (zF_eq s H0 Hne). unfold zetaC.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite (Cmod_Cinv _ Hne1).
  nra.
Qed.

Print Assumptions head_term_ext.
Print Assumptions tail_term_ext.
Print Assumptions psum_bound_ext.
Print Assumptions zeta_log_bound_ext.

(* ----------------------------------------------------------------- *)
(*  F.  the intended instantiation: d = 1/ln|t|, B = e^2               *)
(* ----------------------------------------------------------------- *)
(*  The hypothesis 2 <= ln|Im s| is carried rather than derived from a *)
(*  numeric threshold, so that no upper bound on e is needed anywhere. *)
Corollary zeta_log_bound_below : forall s,
  3 <= Rabs (Im s) -> 2 <= ln (Rabs (Im s)) ->
  1 - / ln (Rabs (Im s)) <= Re s -> Re s <= 2 ->
  Cmod (zF s) <= exp 2 * (ln (Rabs (Im s)) + 15).
Proof.
  intros s H3 Hln Hs1 Hs2.
  assert (HT0 : 0 < Rabs (Im s)) by lra.
  assert (HlnT : 0 < ln (Rabs (Im s))) by lra.
  assert (Hd0 : 0 <= / ln (Rabs (Im s)))
    by (left; apply Rinv_0_lt_compat; exact HlnT).
  assert (Hd2 : / ln (Rabs (Im s)) <= / 2) by (apply Rinv_le_contravar; lra).
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
  exact (zeta_log_bound_ext s (/ ln (Rabs (Im s))) (exp 2)
           Hd0 Hd2 Hs1 Hs2 ltac:(lra) HB1 HB).
Qed.

Print Assumptions zeta_log_bound_below.
