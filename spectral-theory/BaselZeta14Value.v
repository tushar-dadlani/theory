(* ================================================================= *)
(*  BaselZeta14Value.v  —  ζ(14) = 2·π¹⁴/18243225.                     *)
(*                                                                    *)
(*  cot¹⁴x < 1/x¹⁴ < (1+cot²x)⁷ = 1+7cot²+21cot⁴+35cot⁶+35cot⁸         *)
(*    +21cot¹⁰+7cot¹²+cot¹⁴; summing with Σcot²,…,Σcot¹⁴ sandwiches     *)
(*  Σ1/k¹⁴ between two rationals both → 2·π¹⁴/18243225.                 *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14
        BaselZeta4Value BaselZeta6Value BaselZeta8Value BaselZeta10Value BaselZeta12Value
        Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm14 (k : nat) : R := / INR (S k) ^ 14.
Definition zpart14 (N : nat) : R := sum_f_R0 zterm14 N.

Lemma e7_short : forall rs, (length rs <= 6)%nat -> e7 rs = 0.
Proof.
  intros rs Hl; destruct rs as [| r [| r' [| r'' [| r''' [| r'''' [| r''''' [| r'''''' rs']]]]]]];
    cbn [e7 e6 e5 e4 e3 e2 fold_right]; [ ring | ring | ring | ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot14_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 14) (m - 1)
  = (491520 * INR m ^ 14 + 3440640 * INR m ^ 13 + 5521408 * INR m ^ 12 - 11599872 * INR m ^ 11
     - 33297408 * INR m ^ 10 + 21847040 * INR m ^ 9 + 87991296 * INR m ^ 8 - 47290368 * INR m ^ 7
     - 139644800 * INR m ^ 6 + 113541504 * INR m ^ 5 + 113995584 * INR m ^ 4 - 198457344 * INR m ^ 3
     + 101829150 * INR m ^ 2 - 18243225 * INR m) / 273648375.
Proof.
  intros m Hm; destruct (le_lt_dec 7 m) as [H7 | H7]; [ apply cot14_sum; exact H7 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton7.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e7_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 6 m) as [H6 | H6].
  - rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m H6);
      assert (m = 6%nat) by lia; subst m; simpl (INR 6); field.
  - rewrite (e6_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia)).
    destruct (le_lt_dec 5 m) as [H5 | H5].
    + rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
        (cot_e5_exp m H5); assert (m = 5%nat) by lia; subst m; simpl (INR 5); field.
    + rewrite (e5_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia)).
      destruct (le_lt_dec 4 m) as [H4 | H4].
      * rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m H4);
          assert (m = 4%nat) by lia; subst m; simpl (INR 4); field.
      * rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                   ltac:(rewrite length_map, length_seq; lia)).
        destruct (le_lt_dec 3 m) as [H3 | H3].
        -- rewrite (cot_e2_exp m ltac:(lia)), (cot_e3_exp m H3);
             assert (m = 3%nat) by lia; subst m; simpl (INR 3); field.
        -- rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                     ltac:(rewrite length_map, length_seq; lia)).
           destruct (le_lt_dec 2 m) as [H2 | H2].
           ++ rewrite (cot_e2_exp m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
           ++ rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                        ltac:(rewrite length_map, length_seq; lia));
                assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot14_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 14 <= / x ^ 14.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 14) with ((Rcot x ^ 2) ^ 7) by ring.
  replace (/ x ^ 14) with ((/ x ^ 2) ^ 7) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot14_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 14 <= 1 + 7 * Rcot x ^ 2 + 21 * Rcot x ^ 4 + 35 * Rcot x ^ 6 + 35 * Rcot x ^ 8
              + 21 * Rcot x ^ 10 + 7 * Rcot x ^ 12 + Rcot x ^ 14.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 14) with ((/ x ^ 2) ^ 7) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 7 * Rcot x ^ 2 + 21 * Rcot x ^ 4 + 35 * Rcot x ^ 6 + 35 * Rcot x ^ 8
           + 21 * Rcot x ^ 10 + 7 * Rcot x ^ 12 + Rcot x ^ 14)
    with ((1 + Rcot x ^ 2) ^ 7) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c14 (M : R) : R :=
  (491520 * M ^ 14 + 3440640 * M ^ 13 + 5521408 * M ^ 12 - 11599872 * M ^ 11 - 33297408 * M ^ 10
   + 21847040 * M ^ 9 + 87991296 * M ^ 8 - 47290368 * M ^ 7 - 139644800 * M ^ 6 + 113541504 * M ^ 5
   + 113995584 * M ^ 4 - 198457344 * M ^ 3 + 101829150 * M ^ 2 - 18243225 * M) / 273648375.

Definition lowb14 (n : nat) : R := c14 (INR (S n)) * (PI ^ 14 / (2 * INR (S n) + 1) ^ 14).
Definition upb14 (n : nat) : R :=
  (INR (S n) + 7 * c2 (INR (S n)) + 21 * c4 (INR (S n)) + 35 * c6 (INR (S n)) + 35 * c8 (INR (S n))
   + 21 * c10 (INR (S n)) + 7 * c12 (INR (S n)) + c14 (INR (S n)))
  * (PI ^ 14 / (2 * INR (S n) + 1) ^ 14).

Lemma zpart14_bounds : forall n, lowb14 n <= zpart14 n <= upb14 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP14 : 0 < PI ^ 14) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 14) n
                 = (2 * M + 1) ^ 14 / PI ^ 14 * zpart14 n).
  { unfold zpart14; rewrite (scal_sum zterm14 n ((2 * M + 1) ^ 14 / PI ^ 14)).
    apply sum_eq; intros k Hk. unfold zterm14, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 14) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 14) n)
    by (apply sum_Rle; intros k Hk; apply cot14_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 14) n
                <= sum_f_R0 (fun k => 1 + 7 * Rcot (theta (S n) (S k)) ^ 2 + 21 * Rcot (theta (S n) (S k)) ^ 4
                     + 35 * Rcot (theta (S n) (S k)) ^ 6 + 35 * Rcot (theta (S n) (S k)) ^ 8
                     + 21 * Rcot (theta (S n) (S k)) ^ 10 + 7 * Rcot (theta (S n) (S k)) ^ 12
                     + Rcot (theta (S n) (S k)) ^ 14) n)
    by (apply sum_Rle; intros k Hk; apply cot14_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
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
  assert (Hupsum : sum_f_R0 (fun k => 1 + 7 * Rcot (theta (S n) (S k)) ^ 2 + 21 * Rcot (theta (S n) (S k)) ^ 4
                     + 35 * Rcot (theta (S n) (S k)) ^ 6 + 35 * Rcot (theta (S n) (S k)) ^ 8
                     + 21 * Rcot (theta (S n) (S k)) ^ 10 + 7 * Rcot (theta (S n) (S k)) ^ 12
                     + Rcot (theta (S n) (S k)) ^ 14) n
                   = M + 7 * c2 M + 21 * c4 M + 35 * c6 M + 35 * c8 M + 21 * c10 M + 7 * c12 M + c14 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 7 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 21 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 35 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + 35 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                  + 21 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n
                  + 7 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 12) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 14) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 7).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 21).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 35).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 8) n 35).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 10) n 21).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 12) n 7).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 7) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 7)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4 * 21) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 7
                     + Rcot (theta (S n) (S k)) ^ 4 * 21) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 35) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 7
                     + Rcot (theta (S n) (S k)) ^ 4 * 21 + Rcot (theta (S n) (S k)) ^ 6 * 35)
                    (fun k => Rcot (theta (S n) (S k)) ^ 8 * 35) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 7
                     + Rcot (theta (S n) (S k)) ^ 4 * 21 + Rcot (theta (S n) (S k)) ^ 6 * 35
                     + Rcot (theta (S n) (S k)) ^ 8 * 35) (fun k => Rcot (theta (S n) (S k)) ^ 10 * 21) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 7
                     + Rcot (theta (S n) (S k)) ^ 4 * 21 + Rcot (theta (S n) (S k)) ^ 6 * 35
                     + Rcot (theta (S n) (S k)) ^ 8 * 35 + Rcot (theta (S n) (S k)) ^ 10 * 21)
                    (fun k => Rcot (theta (S n) (S k)) ^ 12 * 7) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 7
                     + Rcot (theta (S n) (S k)) ^ 4 * 21 + Rcot (theta (S n) (S k)) ^ 6 * 35
                     + Rcot (theta (S n) (S k)) ^ 8 * 35 + Rcot (theta (S n) (S k)) ^ 10 * 21
                     + Rcot (theta (S n) (S k)) ^ 12 * 7) (fun k => Rcot (theta (S n) (S k)) ^ 14) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8, Hc10, Hc12, Hc14.
      replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc14 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb14; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 14 / PI ^ 14);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c14 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 14 / PI ^ 14 * zpart14 n); [ exact Hlow | right; ring ].
  - unfold upb14; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 14 / PI ^ 14);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 7 * c2 M + 21 * c4 M + 35 * c6 M + 35 * c8 M + 21 * c10 M + 7 * c12 M + c14 M).
    + apply Rle_trans with ((2 * M + 1) ^ 14 / PI ^ 14 * zpart14 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb14_cv : Un_cv lowb14 (2 * PI ^ 14 / 18243225).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb14 n - 2 * PI ^ 14 / 18243225) (fun n => PI ^ 14 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP14 : 0 < PI ^ 14) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD14 : 0 < (2 * M + 1) ^ 14) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 14 = 16384*M^14+114688*M^13+372736*M^12+745472*M^11+1025024*M^10+1025024*M^9+768768*M^8+439296*M^7+192192*M^6+64064*M^5+16016*M^4+2912*M^3+364*M^2+28*M+1) by ring.
    replace (lowb14 n - 2 * PI ^ 14 / 18243225)
      with (PI ^ 14 * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30) / (273648375 * (2 * M + 1) ^ 14))
      by (unfold lowb14, c14; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 14 * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30) / (273648375 * (2 * M + 1) ^ 14) - - (PI ^ 14 * / M)); [ lra | ].
      replace (PI ^ 14 * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30) / (273648375 * (2 * M + 1) ^ 14) - - (PI ^ 14 * / M))
        with (PI ^ 14 * (M * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30) + 273648375 * (2 * M + 1) ^ 14) / (273648375 * M * (2 * M + 1) ^ 14))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 14 * / M - PI ^ 14 * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30) / (273648375 * (2 * M + 1) ^ 14)); [ lra | ].
      replace (PI ^ 14 * / M - PI ^ 14 * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30) / (273648375 * (2 * M + 1) ^ 14))
        with (PI ^ 14 * (273648375 * (2 * M + 1) ^ 14 - M * (- 5660672*M^12 - 33964032*M^11 - 64048128*M^10 - 8903680*M^9 + 64928256*M^8 - 60469248*M^7 - 145410560*M^6 + 111619584*M^5 + 113515104*M^4 - 198544704*M^3 + 101818230*M^2 - 18244065*M - 30)) / (273648375 * M * (2 * M + 1) ^ 14))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb14_cv : Un_cv upb14 (2 * PI ^ 14 / 18243225).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb14 n - 2 * PI ^ 14 / 18243225) (fun n => PI ^ 14 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP14 : 0 < PI ^ 14) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD14 : 0 < (2 * M + 1) ^ 14) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 14 = 16384*M^14+114688*M^13+372736*M^12+745472*M^11+1025024*M^10+1025024*M^9+768768*M^8+439296*M^7+192192*M^6+64064*M^5+16016*M^4+2912*M^3+364*M^2+28*M+1) by ring.
    replace (upb14 n - 2 * PI ^ 14 / 18243225)
      with (PI ^ 14 * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30) / (273648375 * (2 * M + 1) ^ 14))
      by (unfold upb14, c2, c4, c6, c8, c10, c12, c14; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 14 * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30) / (273648375 * (2 * M + 1) ^ 14) - - (PI ^ 14 * / M)); [ lra | ].
      replace (PI ^ 14 * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30) / (273648375 * (2 * M + 1) ^ 14) - - (PI ^ 14 * / M))
        with (PI ^ 14 * (M * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30) + 273648375 * (2 * M + 1) ^ 14) / (273648375 * M * (2 * M + 1) ^ 14))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 14 * / M - PI ^ 14 * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30) / (273648375 * (2 * M + 1) ^ 14)); [ lra | ].
      replace (PI ^ 14 * / M - PI ^ 14 * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30) / (273648375 * (2 * M + 1) ^ 14))
        with (PI ^ 14 * (273648375 * (2 * M + 1) ^ 14 - M * (2830336*M^12 + 16982016*M^11 + 55087104*M^10 + 119767040*M^9 + 198989952*M^8 + 264159744*M^7 + 297569920*M^6 + 284370048*M^5 + 246403488*M^4 + 180910272*M^3 + 152398680*M^2 + 87090360*M - 30)) / (273648375 * M * (2 * M + 1) ^ 14))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart14_cv : Un_cv zpart14 (2 * PI ^ 14 / 18243225).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb14 zpart14 upb14);
    [ apply lowb14_cv | apply upb14_cv | apply zpart14_bounds ].
Qed.

Lemma Zpart14_eq : forall N, Zpart 14 N = zpart14 N.
Proof.
  intro N; unfold Zpart, zpart14; apply sum_eq; intros k _; unfold zterm14.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H14 : (14:R) = INR 14) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H14, (Rpower_pow 14 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_14 : forall (Hs0 : 0 < 14) (Hs1 : (14:R) <> 1),
  zeta_cont 14 Hs0 Hs1 = 2 * PI ^ 14 / 18243225.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 14)).
  - apply (zeta_hookup 14 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart14 (Zpart 14)); [ intro N; symmetry; apply Zpart14_eq | apply zpart14_cv ].
Qed.

Print Assumptions zeta_cont_14.

(* ================================================================= *)
(*  END BaselZeta14Value.v.  ζ(14) = 2·π¹⁴/18243225.                  *)
(* ================================================================= *)
