(* ================================================================= *)
(*  BaselZeta18Value.v  —  zeta(18) = 43867*pi^18/38979295480125.      *)
(*  cot^18 x < 1/x^18 < (1+cot^2 x)^9; summing with Sigma cot^2..^18   *)
(*  sandwiches Sigma 1/k^18 between two rationals both -> the limit.   *)
(*  (43867 = numerator of B_18.)  No new axioms (classical Reals).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14 BaselZeta16 BaselZeta18
        BaselZeta4Value BaselZeta6Value BaselZeta8Value BaselZeta10Value BaselZeta12Value BaselZeta14Value BaselZeta16Value
        Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm18 (k : nat) : R := / INR (S k) ^ 18.
Definition zpart18 (N : nat) : R := sum_f_R0 zterm18 N.

Lemma e9_short : forall rs, (length rs <= 8)%nat -> e9 rs = 0.
Proof.
  intros rs Hl;
  destruct rs as [| r [| r' [| r'' [| r''' [| r'''' [| r''''' [| r'''''' [| r''''''' [| r'''''''' rs']]]]]]]]];
    cbn [e9 e8 e7 e6 e5 e4 e3 e2 fold_right];
    [ ring | ring | ring | ring | ring | ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot18_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 18) (m - 1)
  = (57497354240 * INR m ^ 18 + 517476188160 * INR m ^ 17 + 1348049829888 * INR m ^ 16 - 945061625856 * INR m ^ 15 - 8729222676480 * INR m ^ 14 - 3512869355520 * INR m ^ 13 + 27870040670208 * INR m ^ 12 + 17404258222080 * INR m ^ 11 - 63854225021952 * INR m ^ 10 - 30585496898560 * INR m ^ 9 + 114647373646848 * INR m ^ 8 + 11944485550080 * INR m ^ 7 - 151382565118080 * INR m ^ 6 + 58945806642816 * INR m ^ 5 + 114858861928128 * INR m ^ 4 - 140954177203200 * INR m ^ 3 + 62637378970950 * INR m ^ 2 - 10257709336875 * INR m) / 194896477400625.
Proof.
  intros m Hm; destruct (le_lt_dec 9 m) as [H9 | H9]; [ apply cot18_sum; exact H9 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton9.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e9_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 8 m) as [H8 | H8].
  - rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m ltac:(lia)), (cot_e8_exp m H8);
      assert (m = 8%nat) by lia; subst m; simpl (INR 8); field.
  - rewrite (e8_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia)).
    destruct (le_lt_dec 7 m) as [H7 | H7].
    + rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
        (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m H7);
        assert (m = 7%nat) by lia; subst m; simpl (INR 7); field.
    + rewrite (e7_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia)).
      destruct (le_lt_dec 6 m) as [H6 | H6].
      * rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
          (cot_e5_exp m ltac:(lia)), (cot_e6_exp m H6); assert (m = 6%nat) by lia; subst m; simpl (INR 6); field.
      * rewrite (e6_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                   ltac:(rewrite length_map, length_seq; lia)).
        destruct (le_lt_dec 5 m) as [H5 | H5].
        -- rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
             (cot_e5_exp m H5); assert (m = 5%nat) by lia; subst m; simpl (INR 5); field.
        -- rewrite (e5_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                     ltac:(rewrite length_map, length_seq; lia)).
           destruct (le_lt_dec 4 m) as [H4 | H4].
           ++ rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m H4);
                assert (m = 4%nat) by lia; subst m; simpl (INR 4); field.
           ++ rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                        ltac:(rewrite length_map, length_seq; lia)).
              destruct (le_lt_dec 3 m) as [H3 | H3].
              ** rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m H3);
                   assert (m = 3%nat) by lia; subst m; simpl (INR 3); field.
              ** rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                           ltac:(rewrite length_map, length_seq; lia)).
                 destruct (le_lt_dec 2 m) as [H2 | H2].
                 --- rewrite (cot_e2_exp m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
                 --- rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                              ltac:(rewrite length_map, length_seq; lia));
                       assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot18_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 18 <= / x ^ 18.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 18) with ((Rcot x ^ 2) ^ 9) by ring.
  replace (/ x ^ 18) with ((/ x ^ 2) ^ 9) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot18_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 18 <= 1 + 9 * Rcot x ^ 2 + 36 * Rcot x ^ 4 + 84 * Rcot x ^ 6 + 126 * Rcot x ^ 8 + 126 * Rcot x ^ 10 + 84 * Rcot x ^ 12 + 36 * Rcot x ^ 14 + 9 * Rcot x ^ 16 + Rcot x ^ 18.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 18) with ((/ x ^ 2) ^ 9) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 9 * Rcot x ^ 2 + 36 * Rcot x ^ 4 + 84 * Rcot x ^ 6 + 126 * Rcot x ^ 8 + 126 * Rcot x ^ 10 + 84 * Rcot x ^ 12 + 36 * Rcot x ^ 14 + 9 * Rcot x ^ 16 + Rcot x ^ 18) with ((1 + Rcot x ^ 2) ^ 9) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c18 (M : R) : R :=
  (57497354240 * M ^ 18 + 517476188160 * M ^ 17 + 1348049829888 * M ^ 16 - 945061625856 * M ^ 15 - 8729222676480 * M ^ 14 - 3512869355520 * M ^ 13 + 27870040670208 * M ^ 12 + 17404258222080 * M ^ 11 - 63854225021952 * M ^ 10 - 30585496898560 * M ^ 9 + 114647373646848 * M ^ 8 + 11944485550080 * M ^ 7 - 151382565118080 * M ^ 6 + 58945806642816 * M ^ 5 + 114858861928128 * M ^ 4 - 140954177203200 * M ^ 3 + 62637378970950 * M ^ 2 - 10257709336875 * M) / 194896477400625.

Definition lowb18 (n : nat) : R := c18 (INR (S n)) * (PI ^ 18 / (2 * INR (S n) + 1) ^ 18).
Definition upb18 (n : nat) : R :=
  (INR (S n) + 9 * c2 (INR (S n)) + 36 * c4 (INR (S n)) + 84 * c6 (INR (S n)) + 126 * c8 (INR (S n))
   + 126 * c10 (INR (S n)) + 84 * c12 (INR (S n)) + 36 * c14 (INR (S n)) + 9 * c16 (INR (S n)) + c18 (INR (S n)))
  * (PI ^ 18 / (2 * INR (S n) + 1) ^ 18).

Lemma zpart18_bounds : forall n, lowb18 n <= zpart18 n <= upb18 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP18 : 0 < PI ^ 18) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 18) n
                 = (2 * M + 1) ^ 18 / PI ^ 18 * zpart18 n).
  { unfold zpart18; rewrite (scal_sum zterm18 n ((2 * M + 1) ^ 18 / PI ^ 18)).
    apply sum_eq; intros k Hk. unfold zterm18, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 18) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 18) n)
    by (apply sum_Rle; intros k Hk; apply cot18_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 18) n
                <= sum_f_R0 (fun k => 1 + 9 * Rcot (theta (S n) (S k)) ^ 2 + 36 * Rcot (theta (S n) (S k)) ^ 4 + 84 * Rcot (theta (S n) (S k)) ^ 6 + 126 * Rcot (theta (S n) (S k)) ^ 8 + 126 * Rcot (theta (S n) (S k)) ^ 10 + 84 * Rcot (theta (S n) (S k)) ^ 12 + 36 * Rcot (theta (S n) (S k)) ^ 14 + 9 * Rcot (theta (S n) (S k)) ^ 16 + Rcot (theta (S n) (S k)) ^ 18) n)
    by (apply sum_Rle; intros k Hk; apply cot18_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hc18 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 18) n = c18 M).
  { pose proof (cot18_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c18, M; reflexivity. }
  assert (Hc16 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 16) n = c16 M).
  { pose proof (cot16_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c16, M; reflexivity. }
  assert (Hc14 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 14) n = c14 M).
  { pose proof (cot14_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c14, M; reflexivity. }
  assert (Hc12 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n = c12 M).
  { pose proof (cot12_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c12, M; reflexivity. }
  assert (Hc10 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n = c10 M).
  { pose proof (cot10_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c10, M; reflexivity. }
  assert (Hc8 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n = c8 M).
  { pose proof (cot8_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c8, M; reflexivity. }
  assert (Hc6 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n = c6 M).
  { pose proof (cot6_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c6, M; reflexivity. }
  assert (Hc4 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n = c4 M).
  { pose proof (cot4_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c4, M; reflexivity. }
  assert (Hc2 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n = c2 M).
  { pose proof (cot_sq_sum (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c2, M; reflexivity. }
  assert (Hupsum : sum_f_R0 (fun k => 1 + 9 * Rcot (theta (S n) (S k)) ^ 2 + 36 * Rcot (theta (S n) (S k)) ^ 4 + 84 * Rcot (theta (S n) (S k)) ^ 6 + 126 * Rcot (theta (S n) (S k)) ^ 8 + 126 * Rcot (theta (S n) (S k)) ^ 10 + 84 * Rcot (theta (S n) (S k)) ^ 12 + 36 * Rcot (theta (S n) (S k)) ^ 14 + 9 * Rcot (theta (S n) (S k)) ^ 16 + Rcot (theta (S n) (S k)) ^ 18) n = M + 9 * c2 M + 36 * c4 M + 84 * c6 M + 126 * c8 M + 126 * c10 M + 84 * c12 M + 36 * c14 M + 9 * c16 M + c18 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 9 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 36 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 84 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + 126 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                  + 126 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n
                  + 84 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n
                  + 36 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 14) n
                  + 9 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 16) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 18) n).
    -       rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 9).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 36).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 84).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 8) n 126).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 10) n 126).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 12) n 84).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 14) n 36).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 16) n 9).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 9) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9) (fun k => Rcot (theta (S n) (S k)) ^ 4 * 36) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 84) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36 + Rcot (theta (S n) (S k)) ^ 6 * 84) (fun k => Rcot (theta (S n) (S k)) ^ 8 * 126) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36 + Rcot (theta (S n) (S k)) ^ 6 * 84 + Rcot (theta (S n) (S k)) ^ 8 * 126) (fun k => Rcot (theta (S n) (S k)) ^ 10 * 126) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36 + Rcot (theta (S n) (S k)) ^ 6 * 84 + Rcot (theta (S n) (S k)) ^ 8 * 126 + Rcot (theta (S n) (S k)) ^ 10 * 126) (fun k => Rcot (theta (S n) (S k)) ^ 12 * 84) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36 + Rcot (theta (S n) (S k)) ^ 6 * 84 + Rcot (theta (S n) (S k)) ^ 8 * 126 + Rcot (theta (S n) (S k)) ^ 10 * 126 + Rcot (theta (S n) (S k)) ^ 12 * 84) (fun k => Rcot (theta (S n) (S k)) ^ 14 * 36) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36 + Rcot (theta (S n) (S k)) ^ 6 * 84 + Rcot (theta (S n) (S k)) ^ 8 * 126 + Rcot (theta (S n) (S k)) ^ 10 * 126 + Rcot (theta (S n) (S k)) ^ 12 * 84 + Rcot (theta (S n) (S k)) ^ 14 * 36) (fun k => Rcot (theta (S n) (S k)) ^ 16 * 9) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 9 + Rcot (theta (S n) (S k)) ^ 4 * 36 + Rcot (theta (S n) (S k)) ^ 6 * 84 + Rcot (theta (S n) (S k)) ^ 8 * 126 + Rcot (theta (S n) (S k)) ^ 10 * 126 + Rcot (theta (S n) (S k)) ^ 12 * 84 + Rcot (theta (S n) (S k)) ^ 14 * 36 + Rcot (theta (S n) (S k)) ^ 16 * 9) (fun k => Rcot (theta (S n) (S k)) ^ 18) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8, Hc10, Hc12, Hc14, Hc16, Hc18. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc18 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb18; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 18 / PI ^ 18);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c18 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 18 / PI ^ 18 * zpart18 n); [ exact Hlow | right; ring ].
  - unfold upb18; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 18 / PI ^ 18);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 9 * c2 M + 36 * c4 M + 84 * c6 M + 126 * c8 M + 126 * c10 M + 84 * c12 M + 36 * c14 M + 9 * c16 M + c18 M).
    + apply Rle_trans with ((2 * M + 1) ^ 18 / PI ^ 18 * zpart18 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb18_cv : Un_cv lowb18 (43867 * PI ^ 18 / 38979295480125).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb18 n - 43867 * PI ^ 18 / 38979295480125) (fun n => PI ^ 18 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP18 : 0 < PI ^ 18) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD18 : 0 < (2 * M + 1) ^ 18) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 18 = 262144*M^18+2359296*M^17+10027008*M^16+26738688*M^15+50135040*M^14+70189056*M^13+76038144*M^12+65175552*M^11+44808192*M^10+24893440*M^9+11202048*M^8+4073472*M^7+1188096*M^6+274176*M^5+48960*M^4+6528*M^3+612*M^2+36*M+1) by ring.
    replace (lowb18 n - 43867 * PI ^ 18 / 38979295480125)
      with (PI ^ 18 * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18))
      by (unfold lowb18, c18; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 18 * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18) - - (PI ^ 18 * / M)); [ lra | ].
      replace (PI ^ 18 * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18) - - (PI ^ 18 * / M))
        with (PI ^ 18 * (M * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335) + 194896477400625 * (2 * M + 1) ^ 18) / (194896477400625 * M * (2 * M + 1) ^ 18))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 18 * / M - PI ^ 18 * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18)); [ lra | ].
      replace (PI ^ 18 * / M - PI ^ 18 * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18))
        with (PI ^ 18 * (194896477400625 * (2 * M + 1) ^ 18 - M * (- 851223969792*M^16 - 6809791758336*M^15 - 19725591674880*M^14 - 18907785953280*M^13 + 11192214355968*M^12 + 3108978524160*M^11 - 73682229814272*M^10 - 36045499560960*M^9 + 112190372448768*M^8 + 11051030568960*M^7 - 151643156154240*M^6 + 58885670249856*M^5 + 114848123286528*M^4 - 140955609022080*M^3 + 62637244737930*M^2 - 10257717232935*M - 219335)) / (194896477400625 * M * (2 * M + 1) ^ 18))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb18_cv : Un_cv upb18 (43867 * PI ^ 18 / 38979295480125).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb18 n - 43867 * PI ^ 18 / 38979295480125) (fun n => PI ^ 18 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP18 : 0 < PI ^ 18) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD18 : 0 < (2 * M + 1) ^ 18) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 18 = 262144*M^18+2359296*M^17+10027008*M^16+26738688*M^15+50135040*M^14+70189056*M^13+76038144*M^12+65175552*M^11+44808192*M^10+24893440*M^9+11202048*M^8+4073472*M^7+1188096*M^6+274176*M^5+48960*M^4+6528*M^3+612*M^2+36*M+1) by ring.
    replace (upb18 n - 43867 * PI ^ 18 / 38979295480125)
      with (PI ^ 18 * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18))
      by (unfold upb18, c2, c4, c6, c8, c10, c12, c14, c16, c18; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 18 * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18) - - (PI ^ 18 * / M)); [ lra | ].
      replace (PI ^ 18 * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18) - - (PI ^ 18 * / M))
        with (PI ^ 18 * (M * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335) + 194896477400625 * (2 * M + 1) ^ 18) / (194896477400625 * M * (2 * M + 1) ^ 18))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 18 * / M - PI ^ 18 * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18)); [ lra | ].
      replace (PI ^ 18 * / M - PI ^ 18 * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335) / (194896477400625 * (2 * M + 1) ^ 18))
        with (PI ^ 18 * (194896477400625 * (2 * M + 1) ^ 18 - M * (425611984896*M^16 + 3404895879168*M^15 + 14378671964160*M^14 + 41065025863680*M^13 + 89200260489216*M^12 + 156278989209600*M^11 + 230724556194816*M^10 + 294031737369600*M^9 + 331109745808896*M^8 + 331867978260480*M^7 + 301658803365120*M^6 + 246378698871552*M^5 + 188307923731776*M^4 + 127023238266240*M^3 + 99551377933380*M^2 + 55306387751940*M - 219335)) / (194896477400625 * M * (2 * M + 1) ^ 18))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart18_cv : Un_cv zpart18 (43867 * PI ^ 18 / 38979295480125).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb18 zpart18 upb18);
    [ apply lowb18_cv | apply upb18_cv | apply zpart18_bounds ].
Qed.

Lemma Zpart18_eq : forall N, Zpart 18 N = zpart18 N.
Proof.
  intro N; unfold Zpart, zpart18; apply sum_eq; intros k _; unfold zterm18.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H18 : (18:R) = INR 18) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H18, (Rpower_pow 18 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_18 : forall (Hs0 : 0 < 18) (Hs1 : (18:R) <> 1),
  zeta_cont 18 Hs0 Hs1 = 43867 * PI ^ 18 / 38979295480125.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 18)).
  - apply (zeta_hookup 18 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart18 (Zpart 18)); [ intro N; symmetry; apply Zpart18_eq | apply zpart18_cv ].
Qed.

Print Assumptions zeta_cont_18.
