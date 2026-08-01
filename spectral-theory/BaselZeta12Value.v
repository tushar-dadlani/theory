(* ================================================================= *)
(*  BaselZeta12Value.v  —  ζ(12) = 691·π¹²/638512875.                  *)
(*                                                                    *)
(*  cot¹²x < 1/x¹² < (1+cot²x)⁶ = 1+6cot²+15cot⁴+20cot⁶+15cot⁸         *)
(*    +6cot¹⁰+cot¹²; summing with Σcot²,…,Σcot¹² sandwiches Σ1/k¹²      *)
(*  between two rationals both → 691·π¹²/638512875 (the Bernoulli      *)
(*  irregular prime 691 first appears here).                          *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12
        BaselZeta4Value BaselZeta6Value BaselZeta8Value BaselZeta10Value Ell2Zeta Ell2ZetaCont
        HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm12 (k : nat) : R := / INR (S k) ^ 12.
Definition zpart12 (N : nat) : R := sum_f_R0 zterm12 N.

Lemma e6_short : forall rs, (length rs <= 5)%nat -> e6 rs = 0.
Proof.
  intros rs Hl; destruct rs as [| r [| r' [| r'' [| r''' [| r'''' [| r''''' rs']]]]]];
    cbn [e6 e5 e4 e3 e2 fold_right]; [ ring | ring | ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot12_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 12) (m - 1)
  = (2830336 * INR m ^ 12 + 16982016 * INR m ^ 11 + 18745344 * INR m ^ 10
     - 61941760 * INR m ^ 9 - 104698368 * INR m ^ 8 + 139659264 * INR m ^ 7
     + 218421760 * INR m ^ 6 - 280499712 * INR m ^ 5 - 195670872 * INR m ^ 4
     + 456378192 * INR m ^ 3 - 258446700 * INR m ^ 2 + 49116375 * INR m) / 638512875.
Proof.
  intros m Hm; destruct (le_lt_dec 6 m) as [H6 | H6]; [ apply cot12_sum; exact H6 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton6.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e6_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 5 m) as [H5 | H5].
  - rewrite (cot_e2 m ltac:(lia)), (cot_e3 m ltac:(lia)), (cot_e4 m ltac:(lia)), (cot_e5 m H5);
      assert (m = 5%nat) by lia; subst m; simpl (INR 5); field.
  - rewrite (e5_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia)).
    destruct (le_lt_dec 4 m) as [H4 | H4].
    + rewrite (cot_e2 m ltac:(lia)), (cot_e3 m ltac:(lia)), (cot_e4 m H4);
        assert (m = 4%nat) by lia; subst m; simpl (INR 4); field.
    + rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia)).
      destruct (le_lt_dec 3 m) as [H3 | H3].
      * rewrite (cot_e2 m ltac:(lia)), (cot_e3 m H3);
          assert (m = 3%nat) by lia; subst m; simpl (INR 3); field.
      * rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                   ltac:(rewrite length_map, length_seq; lia)).
        destruct (le_lt_dec 2 m) as [H2 | H2].
        -- rewrite (cot_e2 m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
        -- rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                     ltac:(rewrite length_map, length_seq; lia));
             assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot12_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 12 <= / x ^ 12.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 12) with ((Rcot x ^ 2) ^ 6) by ring.
  replace (/ x ^ 12) with ((/ x ^ 2) ^ 6) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot12_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 12 <= 1 + 6 * Rcot x ^ 2 + 15 * Rcot x ^ 4 + 20 * Rcot x ^ 6 + 15 * Rcot x ^ 8
              + 6 * Rcot x ^ 10 + Rcot x ^ 12.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 12) with ((/ x ^ 2) ^ 6) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 6 * Rcot x ^ 2 + 15 * Rcot x ^ 4 + 20 * Rcot x ^ 6 + 15 * Rcot x ^ 8
           + 6 * Rcot x ^ 10 + Rcot x ^ 12)
    with ((1 + Rcot x ^ 2) ^ 6) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c12 (M : R) : R :=
  (2830336 * M ^ 12 + 16982016 * M ^ 11 + 18745344 * M ^ 10 - 61941760 * M ^ 9
   - 104698368 * M ^ 8 + 139659264 * M ^ 7 + 218421760 * M ^ 6 - 280499712 * M ^ 5
   - 195670872 * M ^ 4 + 456378192 * M ^ 3 - 258446700 * M ^ 2 + 49116375 * M) / 638512875.

Definition lowb12 (n : nat) : R := c12 (INR (S n)) * (PI ^ 12 / (2 * INR (S n) + 1) ^ 12).
Definition upb12 (n : nat) : R :=
  (INR (S n) + 6 * c2 (INR (S n)) + 15 * c4 (INR (S n)) + 20 * c6 (INR (S n))
   + 15 * c8 (INR (S n)) + 6 * c10 (INR (S n)) + c12 (INR (S n)))
  * (PI ^ 12 / (2 * INR (S n) + 1) ^ 12).

Lemma zpart12_bounds : forall n, lowb12 n <= zpart12 n <= upb12 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP12 : 0 < PI ^ 12) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 12) n
                 = (2 * M + 1) ^ 12 / PI ^ 12 * zpart12 n).
  { unfold zpart12; rewrite (scal_sum zterm12 n ((2 * M + 1) ^ 12 / PI ^ 12)).
    apply sum_eq; intros k Hk. unfold zterm12, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 12) n)
    by (apply sum_Rle; intros k Hk; apply cot12_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 12) n
                <= sum_f_R0 (fun k => 1 + 6 * Rcot (theta (S n) (S k)) ^ 2 + 15 * Rcot (theta (S n) (S k)) ^ 4
                     + 20 * Rcot (theta (S n) (S k)) ^ 6 + 15 * Rcot (theta (S n) (S k)) ^ 8
                     + 6 * Rcot (theta (S n) (S k)) ^ 10 + Rcot (theta (S n) (S k)) ^ 12) n)
    by (apply sum_Rle; intros k Hk; apply cot12_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
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
  assert (Hupsum : sum_f_R0 (fun k => 1 + 6 * Rcot (theta (S n) (S k)) ^ 2 + 15 * Rcot (theta (S n) (S k)) ^ 4
                     + 20 * Rcot (theta (S n) (S k)) ^ 6 + 15 * Rcot (theta (S n) (S k)) ^ 8
                     + 6 * Rcot (theta (S n) (S k)) ^ 10 + Rcot (theta (S n) (S k)) ^ 12) n
                   = M + 6 * c2 M + 15 * c4 M + 20 * c6 M + 15 * c8 M + 6 * c10 M + c12 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 6 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 15 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 20 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + 15 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                  + 6 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 6).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 15).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 20).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 8) n 15).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 10) n 6).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 6) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 6)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4 * 15) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 6
                     + Rcot (theta (S n) (S k)) ^ 4 * 15) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 20) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 6
                     + Rcot (theta (S n) (S k)) ^ 4 * 15 + Rcot (theta (S n) (S k)) ^ 6 * 20)
                    (fun k => Rcot (theta (S n) (S k)) ^ 8 * 15) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 6
                     + Rcot (theta (S n) (S k)) ^ 4 * 15 + Rcot (theta (S n) (S k)) ^ 6 * 20
                     + Rcot (theta (S n) (S k)) ^ 8 * 15) (fun k => Rcot (theta (S n) (S k)) ^ 10 * 6) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 6
                     + Rcot (theta (S n) (S k)) ^ 4 * 15 + Rcot (theta (S n) (S k)) ^ 6 * 20
                     + Rcot (theta (S n) (S k)) ^ 8 * 15 + Rcot (theta (S n) (S k)) ^ 10 * 6)
                    (fun k => Rcot (theta (S n) (S k)) ^ 12) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8, Hc10, Hc12. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc12 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb12; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 12 / PI ^ 12);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c12 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 12 / PI ^ 12 * zpart12 n); [ exact Hlow | right; ring ].
  - unfold upb12; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 12 / PI ^ 12);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 6 * c2 M + 15 * c4 M + 20 * c6 M + 15 * c8 M + 6 * c10 M + c12 M).
    + apply Rle_trans with ((2 * M + 1) ^ 12 / PI ^ 12 * zpart12 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb12_cv : Un_cv lowb12 (691 * PI ^ 12 / 638512875).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb12 n - 691 * PI ^ 12 / 638512875) (fun n => PI ^ 12 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP12 : 0 < PI ^ 12) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD12 : 0 < (2 * M + 1) ^ 12) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 12 = 4096*M^12+24576*M^11+67584*M^10+112640*M^9+126720*M^8+101376*M^7+59136*M^6+25344*M^5+7920*M^4+1760*M^3+264*M^2+24*M+1) by ring.
    replace (lowb12 n - 691 * PI ^ 12 / 638512875)
      with (PI ^ 12 * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691) / (638512875 * (2 * M + 1) ^ 12))
      by (unfold lowb12, c12; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 12 * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691) / (638512875 * (2 * M + 1) ^ 12) - - (PI ^ 12 * / M)); [ lra | ].
      replace (PI ^ 12 * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691) / (638512875 * (2 * M + 1) ^ 12) - - (PI ^ 12 * / M))
        with (PI ^ 12 * (M * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691) + 638512875 * (2 * M + 1) ^ 12) / (638512875 * M * (2 * M + 1) ^ 12))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 12 * / M - PI ^ 12 * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691) / (638512875 * (2 * M + 1) ^ 12)); [ lra | ].
      replace (PI ^ 12 * / M - PI ^ 12 * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691) / (638512875 * (2 * M + 1) ^ 12))
        with (PI ^ 12 * (638512875 * (2 * M + 1) ^ 12 - M * (- 27955200*M^10 - 139776000*M^9 - 192261888*M^8 + 69608448*M^7 + 177558784*M^6 - 298012416*M^5 - 201143592*M^4 + 455162032*M^3 - 258629124*M^2 + 49099791*M - 691)) / (638512875 * M * (2 * M + 1) ^ 12))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb12_cv : Un_cv upb12 (691 * PI ^ 12 / 638512875).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb12 n - 691 * PI ^ 12 / 638512875) (fun n => PI ^ 12 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP12 : 0 < PI ^ 12) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD12 : 0 < (2 * M + 1) ^ 12) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 12 = 4096*M^12+24576*M^11+67584*M^10+112640*M^9+126720*M^8+101376*M^7+59136*M^6+25344*M^5+7920*M^4+1760*M^3+264*M^2+24*M+1) by ring.
    replace (upb12 n - 691 * PI ^ 12 / 638512875)
      with (PI ^ 12 * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691) / (638512875 * (2 * M + 1) ^ 12))
      by (unfold upb12, c2, c4, c6, c8, c10, c12; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 12 * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691) / (638512875 * (2 * M + 1) ^ 12) - - (PI ^ 12 * / M)); [ lra | ].
      replace (PI ^ 12 * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691) / (638512875 * (2 * M + 1) ^ 12) - - (PI ^ 12 * / M))
        with (PI ^ 12 * (M * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691) + 638512875 * (2 * M + 1) ^ 12) / (638512875 * M * (2 * M + 1) ^ 12))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 12 * / M - PI ^ 12 * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691) / (638512875 * (2 * M + 1) ^ 12)); [ lra | ].
      replace (PI ^ 12 * / M - PI ^ 12 * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691) / (638512875 * (2 * M + 1) ^ 12))
        with (PI ^ 12 * (638512875 * (2 * M + 1) ^ 12 - M * (13977600*M^10 + 69888000*M^9 + 192995712*M^8 + 352654848*M^7 + 497296384*M^6 + 551126784*M^5 + 532844208*M^4 + 418798432*M^3 + 373065576*M^2 + 217711416*M - 691)) / (638512875 * M * (2 * M + 1) ^ 12))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart12_cv : Un_cv zpart12 (691 * PI ^ 12 / 638512875).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb12 zpart12 upb12);
    [ apply lowb12_cv | apply upb12_cv | apply zpart12_bounds ].
Qed.

Lemma Zpart12_eq : forall N, Zpart 12 N = zpart12 N.
Proof.
  intro N; unfold Zpart, zpart12; apply sum_eq; intros k _; unfold zterm12.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H12 : (12:R) = INR 12) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H12, (Rpower_pow 12 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_12 : forall (Hs0 : 0 < 12) (Hs1 : (12:R) <> 1),
  zeta_cont 12 Hs0 Hs1 = 691 * PI ^ 12 / 638512875.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 12)).
  - apply (zeta_hookup 12 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart12 (Zpart 12)); [ intro N; symmetry; apply Zpart12_eq | apply zpart12_cv ].
Qed.

Print Assumptions zeta_cont_12.

(* ================================================================= *)
(*  END BaselZeta12Value.v.  ζ(12) = 691·π¹²/638512875.               *)
(* ================================================================= *)
