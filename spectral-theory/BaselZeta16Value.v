(* ================================================================= *)
(*  BaselZeta16Value.v  —  ζ(16) = 3617·π¹⁶/325641566250.              *)
(*                                                                    *)
(*  cot¹⁶x < 1/x¹⁶ < (1+cot²x)⁸ = 1+8cot²+28cot⁴+56cot⁶+70cot⁸         *)
(*    +56cot¹⁰+28cot¹²+8cot¹⁴+cot¹⁶; summing with Σcot²,…,Σcot¹⁶         *)
(*  sandwiches Σ1/k¹⁶ between two rationals both → 3617·π¹⁶/325641566250*)
(*  (3617 = numerator of B₁₆).  No new axioms (classical Reals only). *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14 BaselZeta16
        BaselZeta4Value BaselZeta6Value BaselZeta8Value BaselZeta10Value BaselZeta12Value BaselZeta14Value
        Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm16 (k : nat) : R := / INR (S k) ^ 16.
Definition zpart16 (N : nat) : R := sum_f_R0 zterm16 N.

Lemma e8_short : forall rs, (length rs <= 7)%nat -> e8 rs = 0.
Proof.
  intros rs Hl;
  destruct rs as [| r [| r' [| r'' [| r''' [| r'''' [| r''''' [| r'''''' [| r''''''' rs']]]]]]]];
    cbn [e8 e7 e6 e5 e4 e3 e2 fold_right];
    [ ring | ring | ring | ring | ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot16_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 16) (m - 1)
  = (355565568 * INR m ^ 16 + 2844524544 * INR m ^ 15 + 5987696640 * INR m ^ 14 - 7865303040 * INR m ^ 13
     - 37908242432 * INR m ^ 12 + 4225351680 * INR m ^ 11 + 113821052928 * INR m ^ 10 + 3943976960 * INR m ^ 9
     - 229552173312 * INR m ^ 8 + 36110638080 * INR m ^ 7 + 320686408960 * INR m ^ 6 - 178793005824 * INR m ^ 5
     - 249204536352 * INR m ^ 4 + 355069137600 * INR m ^ 3 - 168379722000 * INR m ^ 2 + 28733079375 * INR m) / 488462349375.
Proof.
  intros m Hm; destruct (le_lt_dec 8 m) as [H8 | H8]; [ apply cot16_sum; exact H8 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton8.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e8_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 7 m) as [H7 | H7].
  - rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m H7);
      assert (m = 7%nat) by lia; subst m; simpl (INR 7); field.
  - rewrite (e7_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia)).
    destruct (le_lt_dec 6 m) as [H6 | H6].
    + rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
        (cot_e5_exp m ltac:(lia)), (cot_e6_exp m H6); assert (m = 6%nat) by lia; subst m; simpl (INR 6); field.
    + rewrite (e6_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia)).
      destruct (le_lt_dec 5 m) as [H5 | H5].
      * rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
          (cot_e5_exp m H5); assert (m = 5%nat) by lia; subst m; simpl (INR 5); field.
      * rewrite (e5_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                   ltac:(rewrite length_map, length_seq; lia)).
        destruct (le_lt_dec 4 m) as [H4 | H4].
        -- rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m H4);
             assert (m = 4%nat) by lia; subst m; simpl (INR 4); field.
        -- rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                     ltac:(rewrite length_map, length_seq; lia)).
           destruct (le_lt_dec 3 m) as [H3 | H3].
           ++ rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m H3);
                assert (m = 3%nat) by lia; subst m; simpl (INR 3); field.
           ++ rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                        ltac:(rewrite length_map, length_seq; lia)).
              destruct (le_lt_dec 2 m) as [H2 | H2].
              ** rewrite (cot_e2_exp m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
              ** rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                           ltac:(rewrite length_map, length_seq; lia));
                   assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot16_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 16 <= / x ^ 16.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 16) with ((Rcot x ^ 2) ^ 8) by ring.
  replace (/ x ^ 16) with ((/ x ^ 2) ^ 8) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot16_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 16 <= 1 + 8 * Rcot x ^ 2 + 28 * Rcot x ^ 4 + 56 * Rcot x ^ 6 + 70 * Rcot x ^ 8
              + 56 * Rcot x ^ 10 + 28 * Rcot x ^ 12 + 8 * Rcot x ^ 14 + Rcot x ^ 16.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 16) with ((/ x ^ 2) ^ 8) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 8 * Rcot x ^ 2 + 28 * Rcot x ^ 4 + 56 * Rcot x ^ 6 + 70 * Rcot x ^ 8
           + 56 * Rcot x ^ 10 + 28 * Rcot x ^ 12 + 8 * Rcot x ^ 14 + Rcot x ^ 16)
    with ((1 + Rcot x ^ 2) ^ 8) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c16 (M : R) : R :=
  (355565568 * M ^ 16 + 2844524544 * M ^ 15 + 5987696640 * M ^ 14 - 7865303040 * M ^ 13
   - 37908242432 * M ^ 12 + 4225351680 * M ^ 11 + 113821052928 * M ^ 10 + 3943976960 * M ^ 9
   - 229552173312 * M ^ 8 + 36110638080 * M ^ 7 + 320686408960 * M ^ 6 - 178793005824 * M ^ 5
   - 249204536352 * M ^ 4 + 355069137600 * M ^ 3 - 168379722000 * M ^ 2 + 28733079375 * M) / 488462349375.

Definition lowb16 (n : nat) : R := c16 (INR (S n)) * (PI ^ 16 / (2 * INR (S n) + 1) ^ 16).
Definition upb16 (n : nat) : R :=
  (INR (S n) + 8 * c2 (INR (S n)) + 28 * c4 (INR (S n)) + 56 * c6 (INR (S n)) + 70 * c8 (INR (S n))
   + 56 * c10 (INR (S n)) + 28 * c12 (INR (S n)) + 8 * c14 (INR (S n)) + c16 (INR (S n)))
  * (PI ^ 16 / (2 * INR (S n) + 1) ^ 16).

Lemma zpart16_bounds : forall n, lowb16 n <= zpart16 n <= upb16 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP16 : 0 < PI ^ 16) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 16) n
                 = (2 * M + 1) ^ 16 / PI ^ 16 * zpart16 n).
  { unfold zpart16; rewrite (scal_sum zterm16 n ((2 * M + 1) ^ 16 / PI ^ 16)).
    apply sum_eq; intros k Hk. unfold zterm16, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 16) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 16) n)
    by (apply sum_Rle; intros k Hk; apply cot16_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 16) n
                <= sum_f_R0 (fun k => 1 + 8 * Rcot (theta (S n) (S k)) ^ 2 + 28 * Rcot (theta (S n) (S k)) ^ 4
                     + 56 * Rcot (theta (S n) (S k)) ^ 6 + 70 * Rcot (theta (S n) (S k)) ^ 8
                     + 56 * Rcot (theta (S n) (S k)) ^ 10 + 28 * Rcot (theta (S n) (S k)) ^ 12
                     + 8 * Rcot (theta (S n) (S k)) ^ 14 + Rcot (theta (S n) (S k)) ^ 16) n)
    by (apply sum_Rle; intros k Hk; apply cot16_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
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
  assert (Hupsum : sum_f_R0 (fun k => 1 + 8 * Rcot (theta (S n) (S k)) ^ 2 + 28 * Rcot (theta (S n) (S k)) ^ 4
                     + 56 * Rcot (theta (S n) (S k)) ^ 6 + 70 * Rcot (theta (S n) (S k)) ^ 8
                     + 56 * Rcot (theta (S n) (S k)) ^ 10 + 28 * Rcot (theta (S n) (S k)) ^ 12
                     + 8 * Rcot (theta (S n) (S k)) ^ 14 + Rcot (theta (S n) (S k)) ^ 16) n
                   = M + 8 * c2 M + 28 * c4 M + 56 * c6 M + 70 * c8 M + 56 * c10 M + 28 * c12 M + 8 * c14 M + c16 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 8 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 28 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 56 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + 70 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                  + 56 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n
                  + 28 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n
                  + 8 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 14) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 16) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 8).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 28).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 56).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 8) n 70).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 10) n 56).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 12) n 28).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 14) n 8).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 8) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4 * 28) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8
                     + Rcot (theta (S n) (S k)) ^ 4 * 28) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 56) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8
                     + Rcot (theta (S n) (S k)) ^ 4 * 28 + Rcot (theta (S n) (S k)) ^ 6 * 56)
                    (fun k => Rcot (theta (S n) (S k)) ^ 8 * 70) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8
                     + Rcot (theta (S n) (S k)) ^ 4 * 28 + Rcot (theta (S n) (S k)) ^ 6 * 56
                     + Rcot (theta (S n) (S k)) ^ 8 * 70) (fun k => Rcot (theta (S n) (S k)) ^ 10 * 56) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8
                     + Rcot (theta (S n) (S k)) ^ 4 * 28 + Rcot (theta (S n) (S k)) ^ 6 * 56
                     + Rcot (theta (S n) (S k)) ^ 8 * 70 + Rcot (theta (S n) (S k)) ^ 10 * 56)
                    (fun k => Rcot (theta (S n) (S k)) ^ 12 * 28) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8
                     + Rcot (theta (S n) (S k)) ^ 4 * 28 + Rcot (theta (S n) (S k)) ^ 6 * 56
                     + Rcot (theta (S n) (S k)) ^ 8 * 70 + Rcot (theta (S n) (S k)) ^ 10 * 56
                     + Rcot (theta (S n) (S k)) ^ 12 * 28) (fun k => Rcot (theta (S n) (S k)) ^ 14 * 8) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 8
                     + Rcot (theta (S n) (S k)) ^ 4 * 28 + Rcot (theta (S n) (S k)) ^ 6 * 56
                     + Rcot (theta (S n) (S k)) ^ 8 * 70 + Rcot (theta (S n) (S k)) ^ 10 * 56
                     + Rcot (theta (S n) (S k)) ^ 12 * 28 + Rcot (theta (S n) (S k)) ^ 14 * 8)
                    (fun k => Rcot (theta (S n) (S k)) ^ 16) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8, Hc10, Hc12, Hc14, Hc16.
      replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc16 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb16; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 16 / PI ^ 16);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c16 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 16 / PI ^ 16 * zpart16 n); [ exact Hlow | right; ring ].
  - unfold upb16; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 16 / PI ^ 16);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 8 * c2 M + 28 * c4 M + 56 * c6 M + 70 * c8 M + 56 * c10 M + 28 * c12 M + 8 * c14 M + c16 M).
    + apply Rle_trans with ((2 * M + 1) ^ 16 / PI ^ 16 * zpart16 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb16_cv : Un_cv lowb16 (3617 * PI ^ 16 / 325641566250).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb16 n - 3617 * PI ^ 16 / 325641566250) (fun n => PI ^ 16 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP16 : 0 < PI ^ 16) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD16 : 0 < (2 * M + 1) ^ 16) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 16 = 65536*M^16+524288*M^15+1966080*M^14+4587520*M^13+7454720*M^12+8945664*M^11+8200192*M^10+5857280*M^9+3294720*M^8+1464320*M^7+512512*M^6+139776*M^5+29120*M^4+4480*M^3+480*M^2+32*M+1) by ring.
    replace (lowb16 n - 3617 * PI ^ 16 / 325641566250)
      with (PI ^ 16 * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851) / (976924698750 * (2 * M + 1) ^ 16))
      by (unfold lowb16, c16; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 16 * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851) / (976924698750 * (2 * M + 1) ^ 16) - - (PI ^ 16 * / M)); [ lra | ].
      replace (PI ^ 16 * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851) / (976924698750 * (2 * M + 1) ^ 16) - - (PI ^ 16 * / M))
        with (PI ^ 16 * (M * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851) + 976924698750 * (2 * M + 1) ^ 16) / (976924698750 * M * (2 * M + 1) ^ 16))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 16 * / M - PI ^ 16 * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851) / (976924698750 * (2 * M + 1) ^ 16)); [ lra | ].
      replace (PI ^ 16 * / M - PI ^ 16 * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851) / (976924698750 * (2 * M + 1) ^ 16))
        with (PI ^ 16 * (976924698750 * (2 * M + 1) ^ 16 - M * (- 9358540800*M^14 - 65509785600*M^13 - 156707651584*M^12 - 88618696704*M^11 + 138661822464*M^10 - 55669391360*M^9 - 494855353344*M^8 + 56331939840*M^7 + 635811550208*M^6 - 359102721024*M^5 - 498725053824*M^4 + 710089662720*M^3 - 336764652480*M^2 + 57465811518*M - 10851)) / (976924698750 * M * (2 * M + 1) ^ 16))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb16_cv : Un_cv upb16 (3617 * PI ^ 16 / 325641566250).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb16 n - 3617 * PI ^ 16 / 325641566250) (fun n => PI ^ 16 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP16 : 0 < PI ^ 16) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD16 : 0 < (2 * M + 1) ^ 16) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 16 = 65536*M^16+524288*M^15+1966080*M^14+4587520*M^13+7454720*M^12+8945664*M^11+8200192*M^10+5857280*M^9+3294720*M^8+1464320*M^7+512512*M^6+139776*M^5+29120*M^4+4480*M^3+480*M^2+32*M+1) by ring.
    replace (upb16 n - 3617 * PI ^ 16 / 325641566250)
      with (PI ^ 16 * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851) / (976924698750 * (2 * M + 1) ^ 16))
      by (unfold upb16, c2, c4, c6, c8, c10, c12, c14, c16; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 16 * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851) / (976924698750 * (2 * M + 1) ^ 16) - - (PI ^ 16 * / M)); [ lra | ].
      replace (PI ^ 16 * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851) / (976924698750 * (2 * M + 1) ^ 16) - - (PI ^ 16 * / M))
        with (PI ^ 16 * (M * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851) + 976924698750 * (2 * M + 1) ^ 16) / (976924698750 * M * (2 * M + 1) ^ 16))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 16 * / M - PI ^ 16 * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851) / (976924698750 * (2 * M + 1) ^ 16)); [ lra | ].
      replace (PI ^ 16 * / M - PI ^ 16 * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851) / (976924698750 * (2 * M + 1) ^ 16))
        with (PI ^ 16 * (976924698750 * (2 * M + 1) ^ 16 - M * (4679270400*M^14 + 32754892800*M^13 + 122235355136*M^12 + 307598524416*M^11 + 589538770944*M^10 + 908698992640*M^9 + 1181837815296*M^8 + 1320469739520*M^7 + 1307903748608*M^6 + 1140204059136*M^5 + 919149740736*M^4 + 643211967360*M^3 + 520219559520*M^2 + 292626084768*M - 10851)) / (976924698750 * M * (2 * M + 1) ^ 16))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart16_cv : Un_cv zpart16 (3617 * PI ^ 16 / 325641566250).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb16 zpart16 upb16);
    [ apply lowb16_cv | apply upb16_cv | apply zpart16_bounds ].
Qed.

Lemma Zpart16_eq : forall N, Zpart 16 N = zpart16 N.
Proof.
  intro N; unfold Zpart, zpart16; apply sum_eq; intros k _; unfold zterm16.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H16 : (16:R) = INR 16) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H16, (Rpower_pow 16 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_16 : forall (Hs0 : 0 < 16) (Hs1 : (16:R) <> 1),
  zeta_cont 16 Hs0 Hs1 = 3617 * PI ^ 16 / 325641566250.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 16)).
  - apply (zeta_hookup 16 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart16 (Zpart 16)); [ intro N; symmetry; apply Zpart16_eq | apply zpart16_cv ].
Qed.

Print Assumptions zeta_cont_16.

(* ================================================================= *)
(*  END BaselZeta16Value.v.  ζ(16) = 3617·π¹⁶/325641566250.           *)
(* ================================================================= *)
