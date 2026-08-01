(* ================================================================= *)
(*  BaselZeta10Value.v  —  ζ(10) = π¹⁰/93555.                          *)
(*                                                                    *)
(*  cot¹⁰x < 1/x¹⁰ < (1+cot²x)⁵ = 1+5cot²+10cot⁴+10cot⁶+5cot⁸+cot¹⁰;   *)
(*  summing with Σcot²,…,Σcot¹⁰ sandwiches Σ1/k¹⁰ between two           *)
(*  rationals both → π¹⁰/93555.  No new axioms (classical Reals only). *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10
        BaselZeta4Value BaselZeta6Value BaselZeta8Value Ell2Zeta Ell2ZetaCont
        HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm10 (k : nat) : R := / INR (S k) ^ 10.
Definition zpart10 (N : nat) : R := sum_f_R0 zterm10 N.

Lemma e5_short : forall rs, (length rs <= 4)%nat -> e5 rs = 0.
Proof.
  intros rs Hl; destruct rs as [| r [| r' [| r'' [| r''' [| r'''' rs']]]]];
    cbn [e5 e4 e3 e2 fold_right]; [ ring | ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot10_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 10) (m - 1)
  = (1024 * INR m ^ 10 + 5120 * INR m ^ 9 + 3072 * INR m ^ 8 - 18432 * INR m ^ 7
     - 15424 * INR m ^ 6 + 39744 * INR m ^ 5 + 16736 * INR m ^ 4 - 64512 * INR m ^ 3
     + 41562 * INR m ^ 2 - 8505 * INR m) / 93555.
Proof.
  intros m Hm; destruct (le_lt_dec 5 m) as [H5 | H5]; [ apply cot10_sum; exact H5 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton5.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e5_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 4 m) as [H4 | H4].
  - rewrite (cot_e2 m ltac:(lia)), (cot_e3 m ltac:(lia)), (cot_e4 m H4);
      assert (m = 4%nat) by lia; subst m; simpl (INR 4); field.
  - rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia)).
    destruct (le_lt_dec 3 m) as [H3 | H3].
    + rewrite (cot_e2 m ltac:(lia)), (cot_e3 m H3);
        assert (m = 3%nat) by lia; subst m; simpl (INR 3); field.
    + rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia)).
      destruct (le_lt_dec 2 m) as [H2 | H2].
      * rewrite (cot_e2 m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
      * rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                   ltac:(rewrite length_map, length_seq; lia));
          assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot10_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 10 <= / x ^ 10.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 10) with ((Rcot x ^ 2) ^ 5) by ring.
  replace (/ x ^ 10) with ((/ x ^ 2) ^ 5) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot10_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 10 <= 1 + 5 * Rcot x ^ 2 + 10 * Rcot x ^ 4 + 10 * Rcot x ^ 6 + 5 * Rcot x ^ 8 + Rcot x ^ 10.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 10) with ((/ x ^ 2) ^ 5) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 5 * Rcot x ^ 2 + 10 * Rcot x ^ 4 + 10 * Rcot x ^ 6 + 5 * Rcot x ^ 8 + Rcot x ^ 10)
    with ((1 + Rcot x ^ 2) ^ 5) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c10 (M : R) : R :=
  (1024 * M ^ 10 + 5120 * M ^ 9 + 3072 * M ^ 8 - 18432 * M ^ 7 - 15424 * M ^ 6
   + 39744 * M ^ 5 + 16736 * M ^ 4 - 64512 * M ^ 3 + 41562 * M ^ 2 - 8505 * M) / 93555.

Definition lowb10 (n : nat) : R := c10 (INR (S n)) * (PI ^ 10 / (2 * INR (S n) + 1) ^ 10).
Definition upb10 (n : nat) : R :=
  (INR (S n) + 5 * c2 (INR (S n)) + 10 * c4 (INR (S n)) + 10 * c6 (INR (S n))
   + 5 * c8 (INR (S n)) + c10 (INR (S n)))
  * (PI ^ 10 / (2 * INR (S n) + 1) ^ 10).

Lemma zpart10_bounds : forall n, lowb10 n <= zpart10 n <= upb10 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP10 : 0 < PI ^ 10) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 10) n
                 = (2 * M + 1) ^ 10 / PI ^ 10 * zpart10 n).
  { unfold zpart10; rewrite (scal_sum zterm10 n ((2 * M + 1) ^ 10 / PI ^ 10)).
    apply sum_eq; intros k Hk. unfold zterm10, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 10) n)
    by (apply sum_Rle; intros k Hk; apply cot10_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 10) n
                <= sum_f_R0 (fun k => 1 + 5 * Rcot (theta (S n) (S k)) ^ 2 + 10 * Rcot (theta (S n) (S k)) ^ 4
                     + 10 * Rcot (theta (S n) (S k)) ^ 6 + 5 * Rcot (theta (S n) (S k)) ^ 8
                     + Rcot (theta (S n) (S k)) ^ 10) n)
    by (apply sum_Rle; intros k Hk; apply cot10_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
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
  assert (Hupsum : sum_f_R0 (fun k => 1 + 5 * Rcot (theta (S n) (S k)) ^ 2 + 10 * Rcot (theta (S n) (S k)) ^ 4
                     + 10 * Rcot (theta (S n) (S k)) ^ 6 + 5 * Rcot (theta (S n) (S k)) ^ 8
                     + Rcot (theta (S n) (S k)) ^ 10) n
                   = M + 5 * c2 M + 10 * c4 M + 10 * c6 M + 5 * c8 M + c10 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 5 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 10 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 10 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + 5 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 10) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 5).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 10).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 10).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 8) n 5).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 5) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 5)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4 * 10) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 5
                     + Rcot (theta (S n) (S k)) ^ 4 * 10) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 10) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 5
                     + Rcot (theta (S n) (S k)) ^ 4 * 10 + Rcot (theta (S n) (S k)) ^ 6 * 10)
                    (fun k => Rcot (theta (S n) (S k)) ^ 8 * 5) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 5
                     + Rcot (theta (S n) (S k)) ^ 4 * 10 + Rcot (theta (S n) (S k)) ^ 6 * 10
                     + Rcot (theta (S n) (S k)) ^ 8 * 5) (fun k => Rcot (theta (S n) (S k)) ^ 10) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8, Hc10. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc10 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb10; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 10 / PI ^ 10);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c10 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 10 / PI ^ 10 * zpart10 n); [ exact Hlow | right; ring ].
  - unfold upb10; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 10 / PI ^ 10);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 5 * c2 M + 10 * c4 M + 10 * c6 M + 5 * c8 M + c10 M).
    + apply Rle_trans with ((2 * M + 1) ^ 10 / PI ^ 10 * zpart10 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb10_cv : Un_cv lowb10 (PI ^ 10 / 93555).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb10 n - PI ^ 10 / 93555) (fun n => PI ^ 10 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP10 : 0 < PI ^ 10) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD10 : 0 < (2 * M + 1) ^ 10) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 10 = 1024*M^10+5120*M^9+11520*M^8+15360*M^7+13440*M^6+8064*M^5+3360*M^4+960*M^3+180*M^2+20*M+1) by ring.
    replace (lowb10 n - PI ^ 10 / 93555)
      with (PI ^ 10 * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1) / (93555 * (2 * M + 1) ^ 10))
      by (unfold lowb10, c10; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 10 * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1) / (93555 * (2 * M + 1) ^ 10) - - (PI ^ 10 * / M)); [ lra | ].
      replace (PI ^ 10 * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1) / (93555 * (2 * M + 1) ^ 10) - - (PI ^ 10 * / M))
        with (PI ^ 10 * (M * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1) + 93555 * (2 * M + 1) ^ 10) / (93555 * M * (2 * M + 1) ^ 10))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 10 * / M - PI ^ 10 * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1) / (93555 * (2 * M + 1) ^ 10)); [ lra | ].
      replace (PI ^ 10 * / M - PI ^ 10 * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1) / (93555 * (2 * M + 1) ^ 10))
        with (PI ^ 10 * (93555 * (2 * M + 1) ^ 10 - M * (- 8448*M^8 - 33792*M^7 - 28864*M^6 + 31680*M^5 + 13376*M^4 - 65472*M^3 + 41382*M^2 - 8525*M - 1)) / (93555 * M * (2 * M + 1) ^ 10))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb10_cv : Un_cv upb10 (PI ^ 10 / 93555).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb10 n - PI ^ 10 / 93555) (fun n => PI ^ 10 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP10 : 0 < PI ^ 10) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD10 : 0 < (2 * M + 1) ^ 10) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 10 = 1024*M^10+5120*M^9+11520*M^8+15360*M^7+13440*M^6+8064*M^5+3360*M^4+960*M^3+180*M^2+20*M+1) by ring.
    replace (upb10 n - PI ^ 10 / 93555)
      with (PI ^ 10 * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5) / (467775 * (2 * M + 1) ^ 10))
      by (unfold upb10, c2, c4, c6, c8, c10; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 10 * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5) / (467775 * (2 * M + 1) ^ 10) - - (PI ^ 10 * / M)); [ lra | ].
      replace (PI ^ 10 * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5) / (467775 * (2 * M + 1) ^ 10) - - (PI ^ 10 * / M))
        with (PI ^ 10 * (M * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5) + 467775 * (2 * M + 1) ^ 10) / (467775 * M * (2 * M + 1) ^ 10))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 10 * / M - PI ^ 10 * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5) / (467775 * (2 * M + 1) ^ 10)); [ lra | ].
      replace (PI ^ 10 * / M - PI ^ 10 * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5) / (467775 * (2 * M + 1) ^ 10))
        with (PI ^ 10 * (467775 * (2 * M + 1) ^ 10 - M * (21120*M^8 + 84480*M^7 + 193600*M^6 + 285120*M^5 + 336160*M^4 + 295680*M^3 + 287100*M^2 + 172700*M - 5)) / (467775 * M * (2 * M + 1) ^ 10))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart10_cv : Un_cv zpart10 (PI ^ 10 / 93555).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb10 zpart10 upb10);
    [ apply lowb10_cv | apply upb10_cv | apply zpart10_bounds ].
Qed.

Lemma Zpart10_eq : forall N, Zpart 10 N = zpart10 N.
Proof.
  intro N; unfold Zpart, zpart10; apply sum_eq; intros k _; unfold zterm10.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H10 : (10:R) = INR 10) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H10, (Rpower_pow 10 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_10 : forall (Hs0 : 0 < 10) (Hs1 : (10:R) <> 1), zeta_cont 10 Hs0 Hs1 = PI ^ 10 / 93555.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 10)).
  - apply (zeta_hookup 10 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart10 (Zpart 10)); [ intro N; symmetry; apply Zpart10_eq | apply zpart10_cv ].
Qed.

Print Assumptions zeta_cont_10.

(* ================================================================= *)
(*  END BaselZeta10Value.v.  ζ(10) = π¹⁰/93555.                        *)
(* ================================================================= *)
