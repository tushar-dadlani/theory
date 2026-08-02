(* ================================================================= *)
(*  BaselZeta20Value.v  —  zeta(20) = 174611*pi^20/1531329465290625.   *)
(*  cot^20 x < 1/x^20 < (1+cot^2 x)^10; summing with Sigma cot^2..^20  *)
(*  sandwiches Sigma 1/k^20 between two rationals both -> the limit.   *)
(*  (174611 = numerator of B_20.)  No new axioms (classical Reals).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14 BaselZeta16 BaselZeta18 BaselZeta20
        BaselZeta4Value BaselZeta6Value BaselZeta8Value BaselZeta10Value BaselZeta12Value BaselZeta14Value BaselZeta16Value BaselZeta18Value
        Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm20 (k : nat) : R := / INR (S k) ^ 20.
Definition zpart20 (N : nat) : R := sum_f_R0 zterm20 N.

Lemma e10_short : forall rs, (length rs <= 9)%nat -> e10 rs = 0.
Proof.
  intros rs Hl;
  destruct rs as [| r [| r' [| r'' [| r''' [| r'''' [| r''''' [| r'''''' [| r''''''' [| r'''''''' [| r''''''''' rs']]]]]]]]]];
    cbn [e10 e9 e8 e7 e6 e5 e4 e3 e2 fold_right];
    [ ring | ring | ring | ring | ring | ring | ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot20_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 20) (m - 1)
  = (3844950982656*INR m^20 + 38449509826560*INR m^19 + 119388082012160*INR m^18 - 21318291947520*INR m^17 - 771123004047360*INR m^16 - 718092745310208*INR m^15 + 2467296918896640*INR m^14 + 3308066966077440*INR m^13 - 5889732931153920*INR m^12 - 7865002973306880*INR m^11 + 12213336262662144*INR m^10 + 11220114565253120*INR m^9 - 21448526762288640*INR m^8 - 7029281395845120*INR m^7 + 28018193075781120*INR m^6 - 7417429978747392*INR m^5 - 21102679424539800*INR m^4 + 23032396562850000*INR m^3 - 9688684255267500*INR m^2 + 1531329465290625*INR m) / 32157918771103125.
Proof.
  intros m Hm; destruct (le_lt_dec 10 m) as [Hbig | Hbig]; [ apply cot20_sum; exact Hbig | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton10.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e10_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 9 m) as [H9 | H9].
  - rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)), (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m ltac:(lia)), (cot_e8_exp m ltac:(lia)), (cot_e9_exp m H9);
     assert (m = 9%nat) by lia; subst m; simpl (INR 9); field.
  - rewrite (e9_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
         ltac:(rewrite length_map, length_seq; lia)).
      destruct (le_lt_dec 8 m) as [H8 | H8].
      + rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)), (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m ltac:(lia)), (cot_e8_exp m H8);
         assert (m = 8%nat) by lia; subst m; simpl (INR 8); field.
      + rewrite (e8_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
          destruct (le_lt_dec 7 m) as [H7 | H7].
          * rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)), (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m H7);
             assert (m = 7%nat) by lia; subst m; simpl (INR 7); field.
          * rewrite (e7_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia)).
              destruct (le_lt_dec 6 m) as [H6 | H6].
              -- rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)), (cot_e5_exp m ltac:(lia)), (cot_e6_exp m H6);
                 assert (m = 6%nat) by lia; subst m; simpl (INR 6); field.
              -- rewrite (e6_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                     ltac:(rewrite length_map, length_seq; lia)).
                  destruct (le_lt_dec 5 m) as [H5 | H5].
                  ++ rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)), (cot_e5_exp m H5);
                     assert (m = 5%nat) by lia; subst m; simpl (INR 5); field.
                  ++ rewrite (e5_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                         ltac:(rewrite length_map, length_seq; lia)).
                      destruct (le_lt_dec 4 m) as [H4 | H4].
                      ** rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m H4);
                         assert (m = 4%nat) by lia; subst m; simpl (INR 4); field.
                      ** rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                             ltac:(rewrite length_map, length_seq; lia)).
                          destruct (le_lt_dec 3 m) as [H3 | H3].
                          --- rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m H3);
                             assert (m = 3%nat) by lia; subst m; simpl (INR 3); field.
                          --- rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                                 ltac:(rewrite length_map, length_seq; lia)).
                              destruct (le_lt_dec 2 m) as [H2 | H2].
                              +++ rewrite (cot_e2_exp m H2);
                                 assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
                              +++ rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                                     ltac:(rewrite length_map, length_seq; lia));
                                 assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot20_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 20 <= / x ^ 20.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 20) with ((Rcot x ^ 2) ^ 10) by ring.
  replace (/ x ^ 20) with ((/ x ^ 2) ^ 10) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot20_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 20 <= 1 + 10 * Rcot x ^ 2 + 45 * Rcot x ^ 4 + 120 * Rcot x ^ 6 + 210 * Rcot x ^ 8 + 252 * Rcot x ^ 10 + 210 * Rcot x ^ 12 + 120 * Rcot x ^ 14 + 45 * Rcot x ^ 16 + 10 * Rcot x ^ 18 + Rcot x ^ 20.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 20) with ((/ x ^ 2) ^ 10) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 10 * Rcot x ^ 2 + 45 * Rcot x ^ 4 + 120 * Rcot x ^ 6 + 210 * Rcot x ^ 8 + 252 * Rcot x ^ 10 + 210 * Rcot x ^ 12 + 120 * Rcot x ^ 14 + 45 * Rcot x ^ 16 + 10 * Rcot x ^ 18 + Rcot x ^ 20) with ((1 + Rcot x ^ 2) ^ 10) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c20 (M : R) : R :=
  (3844950982656*M^20 + 38449509826560*M^19 + 119388082012160*M^18 - 21318291947520*M^17 - 771123004047360*M^16 - 718092745310208*M^15 + 2467296918896640*M^14 + 3308066966077440*M^13 - 5889732931153920*M^12 - 7865002973306880*M^11 + 12213336262662144*M^10 + 11220114565253120*M^9 - 21448526762288640*M^8 - 7029281395845120*M^7 + 28018193075781120*M^6 - 7417429978747392*M^5 - 21102679424539800*M^4 + 23032396562850000*M^3 - 9688684255267500*M^2 + 1531329465290625*M) / 32157918771103125.

Definition lowb20 (n : nat) : R := c20 (INR (S n)) * (PI ^ 20 / (2 * INR (S n) + 1) ^ 20).
Definition upb20 (n : nat) : R :=
  (INR (S n) + 10 * c2 (INR (S n)) + 45 * c4 (INR (S n)) + 120 * c6 (INR (S n)) + 210 * c8 (INR (S n)) + 252 * c10 (INR (S n)) + 210 * c12 (INR (S n)) + 120 * c14 (INR (S n)) + 45 * c16 (INR (S n)) + 10 * c18 (INR (S n)) + c20 (INR (S n)))
  * (PI ^ 20 / (2 * INR (S n) + 1) ^ 20).

Lemma zpart20_bounds : forall n, lowb20 n <= zpart20 n <= upb20 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP20 : 0 < PI ^ 20) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 20) n
                 = (2 * M + 1) ^ 20 / PI ^ 20 * zpart20 n).
  { unfold zpart20; rewrite (scal_sum zterm20 n ((2 * M + 1) ^ 20 / PI ^ 20)).
    apply sum_eq; intros k Hk. unfold zterm20, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 20) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 20) n)
    by (apply sum_Rle; intros k Hk; apply cot20_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 20) n
                <= sum_f_R0 (fun k => 1 + 10 * Rcot (theta (S n) (S k)) ^ 2 + 45 * Rcot (theta (S n) (S k)) ^ 4 + 120 * Rcot (theta (S n) (S k)) ^ 6 + 210 * Rcot (theta (S n) (S k)) ^ 8 + 252 * Rcot (theta (S n) (S k)) ^ 10 + 210 * Rcot (theta (S n) (S k)) ^ 12 + 120 * Rcot (theta (S n) (S k)) ^ 14 + 45 * Rcot (theta (S n) (S k)) ^ 16 + 10 * Rcot (theta (S n) (S k)) ^ 18 + Rcot (theta (S n) (S k)) ^ 20) n)
    by (apply sum_Rle; intros k Hk; apply cot20_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hc20 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 20) n = c20 M).
  { pose proof (cot20_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c20, M; reflexivity. }
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
  assert (Hupsum : sum_f_R0 (fun k => 1 + 10 * Rcot (theta (S n) (S k)) ^ 2 + 45 * Rcot (theta (S n) (S k)) ^ 4 + 120 * Rcot (theta (S n) (S k)) ^ 6 + 210 * Rcot (theta (S n) (S k)) ^ 8 + 252 * Rcot (theta (S n) (S k)) ^ 10 + 210 * Rcot (theta (S n) (S k)) ^ 12 + 120 * Rcot (theta (S n) (S k)) ^ 14 + 45 * Rcot (theta (S n) (S k)) ^ 16 + 10 * Rcot (theta (S n) (S k)) ^ 18 + Rcot (theta (S n) (S k)) ^ 20) n = M + 10 * c2 M + 45 * c4 M + 120 * c6 M + 210 * c8 M + 252 * c10 M + 210 * c12 M + 120 * c14 M + 45 * c16 M + 10 * c18 M + c20 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 10 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 45 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 120 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + 210 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                  + 252 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n
                  + 210 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n
                  + 120 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 14) n
                  + 45 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 16) n
                  + 10 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 18) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 20) n).
    -       rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 10).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 45).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 120).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 8) n 210).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 10) n 252).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 12) n 210).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 14) n 120).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 16) n 45).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 18) n 10).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 10) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10) (fun k => Rcot (theta (S n) (S k)) ^ 4 * 45) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 120) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120) (fun k => Rcot (theta (S n) (S k)) ^ 8 * 210) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120 + Rcot (theta (S n) (S k)) ^ 8 * 210) (fun k => Rcot (theta (S n) (S k)) ^ 10 * 252) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120 + Rcot (theta (S n) (S k)) ^ 8 * 210 + Rcot (theta (S n) (S k)) ^ 10 * 252) (fun k => Rcot (theta (S n) (S k)) ^ 12 * 210) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120 + Rcot (theta (S n) (S k)) ^ 8 * 210 + Rcot (theta (S n) (S k)) ^ 10 * 252 + Rcot (theta (S n) (S k)) ^ 12 * 210) (fun k => Rcot (theta (S n) (S k)) ^ 14 * 120) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120 + Rcot (theta (S n) (S k)) ^ 8 * 210 + Rcot (theta (S n) (S k)) ^ 10 * 252 + Rcot (theta (S n) (S k)) ^ 12 * 210 + Rcot (theta (S n) (S k)) ^ 14 * 120) (fun k => Rcot (theta (S n) (S k)) ^ 16 * 45) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120 + Rcot (theta (S n) (S k)) ^ 8 * 210 + Rcot (theta (S n) (S k)) ^ 10 * 252 + Rcot (theta (S n) (S k)) ^ 12 * 210 + Rcot (theta (S n) (S k)) ^ 14 * 120 + Rcot (theta (S n) (S k)) ^ 16 * 45) (fun k => Rcot (theta (S n) (S k)) ^ 18 * 10) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 10 + Rcot (theta (S n) (S k)) ^ 4 * 45 + Rcot (theta (S n) (S k)) ^ 6 * 120 + Rcot (theta (S n) (S k)) ^ 8 * 210 + Rcot (theta (S n) (S k)) ^ 10 * 252 + Rcot (theta (S n) (S k)) ^ 12 * 210 + Rcot (theta (S n) (S k)) ^ 14 * 120 + Rcot (theta (S n) (S k)) ^ 16 * 45 + Rcot (theta (S n) (S k)) ^ 18 * 10) (fun k => Rcot (theta (S n) (S k)) ^ 20) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8, Hc10, Hc12, Hc14, Hc16, Hc18, Hc20. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc20 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb20; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 20 / PI ^ 20);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c20 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 20 / PI ^ 20 * zpart20 n); [ exact Hlow | right; ring ].
  - unfold upb20; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 20 / PI ^ 20);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 10 * c2 M + 45 * c4 M + 120 * c6 M + 210 * c8 M + 252 * c10 M + 210 * c12 M + 120 * c14 M + 45 * c16 M + 10 * c18 M + c20 M).
    + apply Rle_trans with ((2 * M + 1) ^ 20 / PI ^ 20 * zpart20 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb20_cv : Un_cv lowb20 (174611 * PI ^ 20 / 1531329465290625).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb20 n - 174611 * PI ^ 20 / 1531329465290625) (fun n => PI ^ 20 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP20 : 0 < PI ^ 20) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD20 : 0 < (2 * M + 1) ^ 20) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 20 = 1048576*M^20 + 10485760*M^19 + 49807360*M^18 + 149422080*M^17 + 317521920*M^16 + 508035072*M^15 + 635043840*M^14 + 635043840*M^13 + 515973120*M^12 + 343982080*M^11 + 189190144*M^10 + 85995520*M^9 + 32248320*M^8 + 9922560*M^7 + 2480640*M^6 + 496128*M^5 + 77520*M^4 + 9120*M^3 + 760*M^2 + 40*M + 1) by ring.
    replace (lowb20 n - 174611 * PI ^ 20 / 1531329465290625)
      with (PI ^ 20 * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20))
      by (unfold lowb20, c20; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 20 * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20) - - (PI ^ 20 * / M)); [ lra | ].
      replace (PI ^ 20 * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20) - - (PI ^ 20 * / M))
        with (PI ^ 20 * (M * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831) + 32157918771103125 * (2 * M + 1) ^ 20) / (32157918771103125 * M * (2 * M + 1) ^ 20))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 20 * / M - PI ^ 20 * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20)); [ lra | ].
      replace (PI ^ 20 * / M - PI ^ 20 * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20))
        with (PI ^ 20 * (32157918771103125 * (2 * M + 1) ^ 20 - M * (- 63247089664000*M^18 - 569223806976000*M^17 - 1935422223482880*M^16 - 2580971496407040*M^15 + 138698480025600*M^14 + 979468527206400*M^13 - 7781719162736640*M^12 - 9126327127695360*M^11 + 11519607977748480*M^10 + 10904783526656000*M^9 - 21566775901762560*M^8 - 7065665746452480*M^7 + 28009096988129280*M^6 - 7419249196277760*M^5 - 21102963677278920*M^4 + 23032363121351280*M^3 - 9688687042059060*M^2 + 1531329318617385*M - 3666831)) / (32157918771103125 * M * (2 * M + 1) ^ 20))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb20_cv : Un_cv upb20 (174611 * PI ^ 20 / 1531329465290625).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb20 n - 174611 * PI ^ 20 / 1531329465290625) (fun n => PI ^ 20 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP20 : 0 < PI ^ 20) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD20 : 0 < (2 * M + 1) ^ 20) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 20 = 1048576*M^20 + 10485760*M^19 + 49807360*M^18 + 149422080*M^17 + 317521920*M^16 + 508035072*M^15 + 635043840*M^14 + 635043840*M^13 + 515973120*M^12 + 343982080*M^11 + 189190144*M^10 + 85995520*M^9 + 32248320*M^8 + 9922560*M^7 + 2480640*M^6 + 496128*M^5 + 77520*M^4 + 9120*M^3 + 760*M^2 + 40*M + 1) by ring.
    replace (upb20 n - 174611 * PI ^ 20 / 1531329465290625)
      with (PI ^ 20 * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20))
      by (unfold upb20, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 20 * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20) - - (PI ^ 20 * / M)); [ lra | ].
      replace (PI ^ 20 * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20) - - (PI ^ 20 * / M))
        with (PI ^ 20 * (M * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831) + 32157918771103125 * (2 * M + 1) ^ 20) / (32157918771103125 * M * (2 * M + 1) ^ 20))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 20 * / M - PI ^ 20 * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20)); [ lra | ].
      replace (PI ^ 20 * / M - PI ^ 20 * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831) / (32157918771103125 * (2 * M + 1) ^ 20))
        with (PI ^ 20 * (32157918771103125 * (2 * M + 1) ^ 20 - M * (31623544832000*M^18 + 284611903488000*M^17 + 1342249658449920*M^16 + 4286794121871360*M^15 + 10405826189721600*M^14 + 20401097205350400*M^13 + 33694687825244160*M^12 + 48137354932592640*M^11 + 60765929242337280*M^10 + 68584255660544000*M^9 + 70086957881418240*M^8 + 65011793528555520*M^7 + 55439551007009280*M^6 + 43059889940451840*M^5 + 31564390870460880*M^4 + 20676238584101280*M^3 + 15801824541208440*M^2 + 8691004883726760*M - 3666831)) / (32157918771103125 * M * (2 * M + 1) ^ 20))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart20_cv : Un_cv zpart20 (174611 * PI ^ 20 / 1531329465290625).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb20 zpart20 upb20);
    [ apply lowb20_cv | apply upb20_cv | apply zpart20_bounds ].
Qed.

Lemma Zpart20_eq : forall N, Zpart 20 N = zpart20 N.
Proof.
  intro N; unfold Zpart, zpart20; apply sum_eq; intros k _; unfold zterm20.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H20 : (20:R) = INR 20) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H20, (Rpower_pow 20 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_20 : forall (Hs0 : 0 < 20) (Hs1 : (20:R) <> 1),
  zeta_cont 20 Hs0 Hs1 = 174611 * PI ^ 20 / 1531329465290625.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 20)).
  - apply (zeta_hookup 20 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart20 (Zpart 20)); [ intro N; symmetry; apply Zpart20_eq | apply zpart20_cv ].
Qed.

Print Assumptions zeta_cont_20.
