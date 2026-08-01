(* ================================================================= *)
(*  BaselZeta6Value.v  —  ζ(6) = π⁶/945.                              *)
(*                                                                    *)
(*  The Cauchy squeeze at the sixth power: cubing cot²x<1/x²<1+cot²x   *)
(*  gives cot⁶x < 1/x⁶ < (1+cot²x)³ = 1+3cot²x+3cot⁴x+cot⁶x.  Summing  *)
(*  with Σcot²,Σcot⁴,Σcot⁶ (BaselVieta/BaselZeta4/BaselZeta6)          *)
(*  sandwiches Σ1/k⁶ between two rationals both → π⁶/945.             *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4 BaselZeta6
        BaselZeta4Value Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm6 (k : nat) : R := / INR (S k) ^ 6.
Definition zpart6 (N : nat) : R := sum_f_R0 zterm6 N.

(* --- e₂,e₃ vanish on short lists (m = 1, 2) --- *)

Lemma e2_short : forall rs, (length rs <= 1)%nat -> e2 rs = 0.
Proof.
  intros rs Hl; destruct rs as [| r [| r' rs']]; cbn [e2 fold_right]; [ ring | ring | cbn in Hl; lia ].
Qed.

Lemma e3_short : forall rs, (length rs <= 2)%nat -> e3 rs = 0.
Proof.
  intros rs Hl; destruct rs as [| r [| r' [| r'' rs']]];
    cbn [e3 e2 fold_right]; [ ring | ring | ring | cbn in Hl; lia ].
Qed.

(* --- Σcot⁶ for m ≥ 1 --- *)

Lemma cot6_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 6) (m - 1)
  = (64 * INR m ^ 6 + 192 * INR m ^ 5 - 96 * INR m ^ 4 - 512 * INR m ^ 3
     + 522 * INR m ^ 2 - 135 * INR m) / 945.
Proof.
  intros m Hm; destruct (le_lt_dec 3 m) as [H3 | H3]; [ apply cot6_sum; exact H3 | ].
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  { rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2))
               m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring. }
  rewrite newton3.
  assert (Hsm : fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
                = INR m * (2 * INR m - 1) / 3).
  { rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
    rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
  rewrite Hsm.
  rewrite (e3_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
             ltac:(rewrite length_map, length_seq; lia)).
  destruct (le_lt_dec 2 m) as [H2 | H1].
  - rewrite (cot_e2 m H2); assert (m = 2%nat) by lia; subst m; simpl (INR 2); field.
  - rewrite (e2_short (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
               ltac:(rewrite length_map, length_seq; lia));
      assert (m = 1%nat) by lia; subst m; simpl (INR 1); field.
Qed.

(* --- cubed pointwise bounds --- *)

Lemma cot6_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 6 <= / x ^ 6.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  replace (Rcot x ^ 6) with ((Rcot x ^ 2) ^ 3) by ring.
  replace (/ x ^ 6) with ((/ x ^ 2) ^ 3) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split;
    [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr
    | apply Rlt_le; exact Hl ].
Qed.

Lemma cot6_hi : forall x, 0 < x -> x < PI / 2 ->
  / x ^ 6 <= 1 + 3 * Rcot x ^ 2 + 3 * Rcot x ^ 4 + Rcot x ^ 6.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 6) with ((/ x ^ 2) ^ 3) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 3 * Rcot x ^ 2 + 3 * Rcot x ^ 4 + Rcot x ^ 6) with ((1 + Rcot x ^ 2) ^ 3) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

(* --- the two bounding sequences --- *)

Definition c6 (M : R) : R :=
  (64 * M ^ 6 + 192 * M ^ 5 - 96 * M ^ 4 - 512 * M ^ 3 + 522 * M ^ 2 - 135 * M) / 945.
Definition c4 (M : R) : R := M * (2 * M - 1) * (4 * M ^ 2 + 10 * M - 9) / 45.
Definition c2 (M : R) : R := M * (2 * M - 1) / 3.

Definition lowb6 (n : nat) : R := c6 (INR (S n)) * (PI ^ 6 / (2 * INR (S n) + 1) ^ 6).
Definition upb6 (n : nat) : R :=
  (INR (S n) + 3 * c2 (INR (S n)) + 3 * c4 (INR (S n)) + c6 (INR (S n)))
  * (PI ^ 6 / (2 * INR (S n) + 1) ^ 6).

Lemma zpart6_bounds : forall n, lowb6 n <= zpart6 n <= upb6 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP6 : 0 < PI ^ 6) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 6) n
                 = (2 * M + 1) ^ 6 / PI ^ 6 * zpart6 n).
  { unfold zpart6; rewrite (scal_sum zterm6 n ((2 * M + 1) ^ 6 / PI ^ 6)).
    apply sum_eq; intros k Hk. unfold zterm6, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 6) n)
    by (apply sum_Rle; intros k Hk; apply cot6_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 6) n
                <= sum_f_R0 (fun k => 1 + 3 * Rcot (theta (S n) (S k)) ^ 2
                     + 3 * Rcot (theta (S n) (S k)) ^ 4 + Rcot (theta (S n) (S k)) ^ 6) n)
    by (apply sum_Rle; intros k Hk; apply cot6_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]).
  assert (Hc6 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n = c6 M).
  { pose proof (cot6_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c6, M; reflexivity. }
  assert (Hc4 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n = c4 M).
  { pose proof (cot4_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c4, M; reflexivity. }
  assert (Hc2 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n = c2 M).
  { pose proof (cot_sq_sum (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH; unfold c2, M; reflexivity. }
  assert (Hupsum : sum_f_R0 (fun k => 1 + 3 * Rcot (theta (S n) (S k)) ^ 2
                     + 3 * Rcot (theta (S n) (S k)) ^ 4 + Rcot (theta (S n) (S k)) ^ 6) n
                   = M + 3 * c2 M + 3 * c4 M + c6 M).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 3 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + 3 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 6) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 3).
      rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 4) n 3).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 3) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 3)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4 * 3) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 3
                     + Rcot (theta (S n) (S k)) ^ 4 * 3) (fun k => Rcot (theta (S n) (S k)) ^ 6) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4, Hc6. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc6 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb6; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 6 / PI ^ 6);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (c6 M); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 6 / PI ^ 6 * zpart6 n); [ exact Hlow | right; ring ].
  - unfold upb6; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 6 / PI ^ 6);
      [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 3 * c2 M + 3 * c4 M + c6 M).
    + apply Rle_trans with ((2 * M + 1) ^ 6 / PI ^ 6 * zpart6 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

(* --- both bounds → π⁶/945 --- *)

Lemma lowb6_cv : Un_cv lowb6 (PI ^ 6 / 945).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb6 n - PI ^ 6 / 945) (fun n => PI ^ 6 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP6 : 0 < PI ^ 6) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD6 : 0 < (2 * M + 1) ^ 6) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 6 = 64*M^6+192*M^5+240*M^4+160*M^3+60*M^2+12*M+1) by ring.
    replace (lowb6 n - PI ^ 6 / 945)
      with (PI ^ 6 * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1) / (945 * (2 * M + 1) ^ 6))
      by (unfold lowb6, c6; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 6 * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1) / (945 * (2 * M + 1) ^ 6) - - (PI ^ 6 * / M)); [ lra | ].
      replace (PI ^ 6 * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1) / (945 * (2 * M + 1) ^ 6) - - (PI ^ 6 * / M))
        with (PI ^ 6 * (M * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1) + 945 * (2 * M + 1) ^ 6) / (945 * M * (2 * M + 1) ^ 6))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 6 * / M - PI ^ 6 * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1) / (945 * (2 * M + 1) ^ 6)); [ lra | ].
      replace (PI ^ 6 * / M - PI ^ 6 * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1) / (945 * (2 * M + 1) ^ 6))
        with (PI ^ 6 * (945 * (2 * M + 1) ^ 6 - M * (- 336*M^4 - 672*M^3 + 462*M^2 - 147*M - 1)) / (945 * M * (2 * M + 1) ^ 6))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb6_cv : Un_cv upb6 (PI ^ 6 / 945).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb6 n - PI ^ 6 / 945) (fun n => PI ^ 6 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP6 : 0 < PI ^ 6) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD6 : 0 < (2 * M + 1) ^ 6) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 6 = 64*M^6+192*M^5+240*M^4+160*M^3+60*M^2+12*M+1) by ring.
    replace (upb6 n - PI ^ 6 / 945)
      with (PI ^ 6 * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1) / (945 * (2 * M + 1) ^ 6))
      by (unfold upb6, c2, c4, c6; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 6 * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1) / (945 * (2 * M + 1) ^ 6) - - (PI ^ 6 * / M)); [ lra | ].
      replace (PI ^ 6 * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1) / (945 * (2 * M + 1) ^ 6) - - (PI ^ 6 * / M))
        with (PI ^ 6 * (M * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1) + 945 * (2 * M + 1) ^ 6) / (945 * M * (2 * M + 1) ^ 6))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 6 * / M - PI ^ 6 * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1) / (945 * (2 * M + 1) ^ 6)); [ lra | ].
      replace (PI ^ 6 * / M - PI ^ 6 * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1) / (945 * (2 * M + 1) ^ 6))
        with (PI ^ 6 * (945 * (2 * M + 1) ^ 6 - M * (168*M^4 + 336*M^3 + 588*M^2 + 420*M - 1)) / (945 * M * (2 * M + 1) ^ 6))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart6_cv : Un_cv zpart6 (PI ^ 6 / 945).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb6 zpart6 upb6);
    [ apply lowb6_cv | apply upb6_cv | apply zpart6_bounds ].
Qed.

(* --- ζ(6) = π⁶/945 --- *)

Lemma Zpart6_eq : forall N, Zpart 6 N = zpart6 N.
Proof.
  intro N; unfold Zpart, zpart6; apply sum_eq; intros k _; unfold zterm6.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H6 : (6:R) = INR 6) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H6, (Rpower_pow 6 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_6 : forall (Hs0 : 0 < 6) (Hs1 : (6:R) <> 1), zeta_cont 6 Hs0 Hs1 = PI ^ 6 / 945.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 6)).
  - apply (zeta_hookup 6 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart6 (Zpart 6)); [ intro N; symmetry; apply Zpart6_eq | apply zpart6_cv ].
Qed.

Print Assumptions zeta_cont_6.

(* ================================================================= *)
(*  END BaselZeta6Value.v.  ζ(6) = π⁶/945.                            *)
(* ================================================================= *)
