(* ================================================================= *)
(*  BaselZeta8Value.v  —  ζ(8) = π⁸/9450.                             *)
(*                                                                    *)
(*  cot⁸x < 1/x⁸ < (1+cot²x)⁴ = 1+4cot²+6cot⁴+4cot⁶+cot⁸; summing     *)
(*  with Σcot²,…,Σcot⁸ sandwiches Σ1/k⁸ between two rationals          *)
(*  both → π⁸/9450.  No new axioms (classical Reals only).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6 BaselZeta8
        BaselZeta4Value BaselZeta6Value Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm8 (k : nat) : R := / INR (S k) ^ 8.
Definition zpart8 (N : nat) : R := sum_f_R0 zterm8 N.

Lemma e4_short : forall rs, (length rs <= 3)%nat -> e4 rs = 0.
Proof.
  intros rs Hl; destruct rs as [| r [| r' [| r'' [| r''' rs']]]];
    cbn [e4 e3 e2 fold_right]; [ ring | ring | ring | ring | cbn in Hl; lia ].
Qed.

Lemma cot8_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 8) (m - 1)
  = (384 * INR m ^ 8 + 1536 * INR m ^ 7 + 128 * INR m ^ 6 - 4992 * INR m ^ 5
     - 528 * INR m ^ 4 + 9056 * INR m ^ 3 - 6984 * INR m ^ 2 + 1575 * INR m) / 14175.
Proof.
  intros m Hm; destruct (le_lt_dec 4 m) as [H4 | H4]; [ apply cot8_sum; exact H4 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton4.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e4_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 3 m) as [H3 | H3].
  - rewrite (cot_e2 m ltac:(lia)), (cot_e3 m H3); assert (m = 3%nat) by lia; subst m;
      simpl (INR 3); field.
  - rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia)).
    destruct (le_lt_dec 2 m) as [H2 | H2].
    + rewrite (cot_e2 m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
    + rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                 ltac:(rewrite length_map, length_seq; lia));
        assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

Lemma cot8_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 8 <= / x ^ 8.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 8) with ((Rcot x ^ 2) ^ 4) by ring.
  replace (/ x ^ 8) with ((/ x ^ 2) ^ 4) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot8_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 8 <= 1 + 4 * Rcot x ^ 2 + 6 * Rcot x ^ 4 + 4 * Rcot x ^ 6 + Rcot x ^ 8.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 8) with ((/ x ^ 2) ^ 4) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 4 * Rcot x ^ 2 + 6 * Rcot x ^ 4 + 4 * Rcot x ^ 6 + Rcot x ^ 8)
    with ((1 + Rcot x ^ 2) ^ 4) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

Definition c8 (M : R) : R :=
  (384 * M ^ 8 + 1536 * M ^ 7 + 128 * M ^ 6 - 4992 * M ^ 5 - 528 * M ^ 4 + 9056 * M ^ 3
   - 6984 * M ^ 2 + 1575 * M) / 14175.

Definition lowb8 (n : nat) : R := c8 (INR (S n)) * (PI ^ 8 / (2 * INR (S n) + 1) ^ 8).
Definition upb8 (n : nat) : R :=
  (INR (S n) + 4 * c2 (INR (S n)) + 6 * c4 (INR (S n)) + 4 * c6 (INR (S n)) + c8 (INR (S n)))
  * (PI ^ 8 / (2 * INR (S n) + 1) ^ 8).

Lemma zpart8_bounds : forall n, lowb8 n <= zpart8 n <= upb8 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP8 : 0 < PI ^ 8) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 8) n
                 = (2 * M + 1) ^ 8 / PI ^ 8 * zpart8 n).
  { unfold zpart8; rewrite (scal_sum zterm8 n ((2 * M + 1) ^ 8 / PI ^ 8)).
    apply sum_eq; intros k Hk. unfold zterm8, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 8) n)
    by (apply sum_Rle; intros k Hk; apply cot8_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 8) n
                <= sum_f_R0 (fun k => 1 + 4 * Rcot (theta (S n) (S k)) ^ 2 + 6 * Rcot (theta (S n) (S k)) ^ 4
                     + 4 * Rcot (theta (S n) (S k)) ^ 6 + Rcot (theta (S n) (S k)) ^ 8) n)
    by (apply sum_Rle; intros k Hk; apply cot8_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
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
  assert (Hupsum : sum_f_R0 (fun k => 1 + 4 * Rcot (theta (S n) (S k)) ^ 2 + 6 * Rcot (theta (S n) (S k)) ^ 4
                     + 4 * Rcot (theta (S n) (S k)) ^ 6 + Rcot (theta (S n) (S k)) ^ 8) n
                   = M + 4 * c2 M + 6 * c4 M + 4 * c6 M + c8 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 4 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 6 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + 4 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 8) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 4).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 6).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 6) n 4).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 4) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 4)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4 * 6) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 4
                     + Rcot (theta (S n) (S k)) ^ 4 * 6) (fun k => Rcot (theta (S n) (S k)) ^ 6 * 4) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 4
                     + Rcot (theta (S n) (S k)) ^ 4 * 6 + Rcot (theta (S n) (S k)) ^ 6 * 4)
                    (fun k => Rcot (theta (S n) (S k)) ^ 8) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6, Hc8. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc8 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb8; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 8 / PI ^ 8);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c8 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 8 / PI ^ 8 * zpart8 n); [ exact Hlow | right; ring ].
  - unfold upb8; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 8 / PI ^ 8);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 4 * c2 M + 6 * c4 M + 4 * c6 M + c8 M).
    + apply Rle_trans with ((2 * M + 1) ^ 8 / PI ^ 8 * zpart8 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

Lemma lowb8_cv : Un_cv lowb8 (PI ^ 8 / 9450).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb8 n - PI ^ 8 / 9450) (fun n => PI ^ 8 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP8 : 0 < PI ^ 8) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD8 : 0 < (2 * M + 1) ^ 8) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 8 = 256*M^8+1024*M^7+1792*M^6+1792*M^5+1120*M^4+448*M^3+112*M^2+16*M+1) by ring.
    replace (lowb8 n - PI ^ 8 / 9450)
      with (PI ^ 8 * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3) / (28350 * (2 * M + 1) ^ 8))
      by (unfold lowb8, c8; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 8 * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3) / (28350 * (2 * M + 1) ^ 8) - - (PI ^ 8 * / M)); [ lra | ].
      replace (PI ^ 8 * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3) / (28350 * (2 * M + 1) ^ 8) - - (PI ^ 8 * / M))
        with (PI ^ 8 * (M * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3) + 28350 * (2 * M + 1) ^ 8) / (28350 * M * (2 * M + 1) ^ 8))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 8 * / M - PI ^ 8 * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3) / (28350 * (2 * M + 1) ^ 8)); [ lra | ].
      replace (PI ^ 8 * / M - PI ^ 8 * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3) / (28350 * (2 * M + 1) ^ 8))
        with (PI ^ 8 * (28350 * (2 * M + 1) ^ 8 - M * (- 5120*M^6 - 15360*M^5 - 4416*M^4 + 16768*M^3 - 14304*M^2 + 3102*M - 3)) / (28350 * M * (2 * M + 1) ^ 8))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb8_cv : Un_cv upb8 (PI ^ 8 / 9450).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb8 n - PI ^ 8 / 9450) (fun n => PI ^ 8 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP8 : 0 < PI ^ 8) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD8 : 0 < (2 * M + 1) ^ 8) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 8 = 256*M^8+1024*M^7+1792*M^6+1792*M^5+1120*M^4+448*M^3+112*M^2+16*M+1) by ring.
    replace (upb8 n - PI ^ 8 / 9450)
      with (PI ^ 8 * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3) / (28350 * (2 * M + 1) ^ 8))
      by (unfold upb8, c2, c4, c6, c8; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 8 * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3) / (28350 * (2 * M + 1) ^ 8) - - (PI ^ 8 * / M)); [ lra | ].
      replace (PI ^ 8 * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3) / (28350 * (2 * M + 1) ^ 8) - - (PI ^ 8 * / M))
        with (PI ^ 8 * (M * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3) + 28350 * (2 * M + 1) ^ 8) / (28350 * M * (2 * M + 1) ^ 8))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 8 * / M - PI ^ 8 * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3) / (28350 * (2 * M + 1) ^ 8)); [ lra | ].
      replace (PI ^ 8 * / M - PI ^ 8 * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3) / (28350 * (2 * M + 1) ^ 8))
        with (PI ^ 8 * (28350 * (2 * M + 1) ^ 8 - M * (2560*M^6 + 7680*M^5 + 14304*M^4 + 15808*M^3 + 18096*M^2 + 11472*M - 3)) / (28350 * M * (2 * M + 1) ^ 8))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart8_cv : Un_cv zpart8 (PI ^ 8 / 9450).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb8 zpart8 upb8);
    [ apply lowb8_cv | apply upb8_cv | apply zpart8_bounds ].
Qed.

Lemma Zpart8_eq : forall N, Zpart 8 N = zpart8 N.
Proof.
  intro N; unfold Zpart, zpart8; apply sum_eq; intros k _; unfold zterm8.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H8 : (8:R) = INR 8) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H8, (Rpower_pow 8 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_8 : forall (Hs0 : 0 < 8) (Hs1 : (8:R) <> 1), zeta_cont 8 Hs0 Hs1 = PI ^ 8 / 9450.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 8)).
  - apply (zeta_hookup 8 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart8 (Zpart 8)); [ intro N; symmetry; apply Zpart8_eq | apply zpart8_cv ].
Qed.

Print Assumptions zeta_cont_8.

(* ================================================================= *)
(*  END BaselZeta8Value.v.  ζ(8) = π⁸/9450.                           *)
(* ================================================================= *)
