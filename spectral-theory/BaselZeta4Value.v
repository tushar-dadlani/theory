(* ================================================================= *)
(*  BaselZeta4Value.v  —  ζ(4) = π⁴/90.                               *)
(*                                                                    *)
(*  The Cauchy squeeze at the fourth power: from cot²x<1/x²<1+cot²x    *)
(*  (BaselTrig), squaring gives cot⁴x < 1/x⁴ < (1+cot²x)² =            *)
(*  1+2cot²x+cot⁴x.  Summing over x=kπ/(2m+1), k=1..m, with            *)
(*  Σcot² = m(2m−1)/3 (BaselVieta) and Σcot⁴ = m(2m−1)(4m²+10m−9)/45   *)
(*  (BaselZeta4.cot4_sum) sandwiches Σ1/k⁴ between two rational        *)
(*  sequences both → π⁴/90.  Hence zeta_cont 4 = π⁴/90.               *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta BaselZeta BaselZeta4
        Ell2Zeta Ell2ZetaCont HagedornTransition ZetaCompleted.
Require BaselTrig.
Open Scope R_scope.

Definition zterm4 (k : nat) : R := / INR (S k) ^ 4.
Definition zpart4 (N : nat) : R := sum_f_R0 zterm4 N.

(* --- Σcot⁴ for m ≥ 1 (the m=1 case has e₂=0) --- *)

Lemma cot4_sum_ge1 : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 4) (m - 1)
  = INR m * (2 * INR m - 1) * (4 * INR m ^ 2 + 10 * INR m - 9) / 45.
Proof.
  intros m Hm; destruct (le_lt_dec 2 m) as [H2 | H1]; [ apply cot4_sum; exact H2 | ].
  assert (Hm1 : m = 1%nat) by lia; subst m.
  pose proof (cot_sq_sum 1 ltac:(lia)) as Hsq.
  cbn [Nat.sub] in Hsq |- *; cbn [sum_f_R0] in Hsq |- *.
  replace (Rcot (INR 1 * PI / INR (2 * 1 + 1)) ^ 4)
    with ((Rcot (INR 1 * PI / INR (2 * 1 + 1)) ^ 2) ^ 2) by ring.
  rewrite Hsq; simpl (INR 1); field.
Qed.

(* --- squared pointwise bounds --- *)

Lemma cot4_lo : forall x, 0 < x -> x < PI / 2 -> Rcot x ^ 4 <= / x ^ 4.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [Hl _].
  rewrite BaselZeta.Rcot_eq in Hl.
  assert (Hxpos : 0 < x ^ 2) by (apply pow_lt; exact H1).
  replace (Rcot x ^ 4) with ((Rcot x ^ 2) ^ 2) by ring.
  replace (/ x ^ 4) with ((/ x ^ 2) ^ 2) by (field; apply Rgt_not_eq; exact H1).
  apply pow_incr; split; [ replace (Rcot x ^ 2) with (Rsqr (Rcot x)) by (unfold Rsqr; ring); apply Rle_0_sqr | apply Rlt_le; exact Hl ].
Qed.

Lemma cot4_hi : forall x, 0 < x -> x < PI / 2 -> / x ^ 4 <= 1 + 2 * Rcot x ^ 2 + Rcot x ^ 4.
Proof.
  intros x H1 H2; destruct (BaselTrig.cot_sq_bounds x H1 H2) as [_ Hu].
  rewrite BaselZeta.Rcot_eq in Hu.
  assert (Hxpos : 0 < / x ^ 2) by (apply Rinv_0_lt_compat; apply pow_lt; exact H1).
  replace (/ x ^ 4) with ((/ x ^ 2) ^ 2) by (field; apply Rgt_not_eq; exact H1).
  replace (1 + 2 * Rcot x ^ 2 + Rcot x ^ 4) with ((1 + Rcot x ^ 2) ^ 2) by ring.
  apply pow_incr; split; [ apply Rlt_le; exact Hxpos | apply Rlt_le; exact Hu ].
Qed.

(* --- the two bounding sequences --- *)

Definition lowb4 (n : nat) : R :=
  INR (S n) * (2 * INR (S n) - 1) * (4 * INR (S n) ^ 2 + 10 * INR (S n) - 9) / 45
  * (PI ^ 4 / (2 * INR (S n) + 1) ^ 4).
Definition upb4 (n : nat) : R :=
  (INR (S n) + 2 * (INR (S n) * (2 * INR (S n) - 1) / 3)
   + INR (S n) * (2 * INR (S n) - 1) * (4 * INR (S n) ^ 2 + 10 * INR (S n) - 9) / 45)
  * (PI ^ 4 / (2 * INR (S n) + 1) ^ 4).

Lemma zpart4_bounds : forall n, lowb4 n <= zpart4 n <= upb4 n.
Proof.
  intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP4 : 0 < PI ^ 4) by (apply pow_lt; exact HP).
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 4) n
                 = (2 * M + 1) ^ 4 / PI ^ 4 * zpart4 n).
  { unfold zpart4; rewrite (scal_sum zterm4 n ((2 * M + 1) ^ 4 / PI ^ 4)).
    apply sum_eq; intros k Hk. unfold zterm4, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 4) n).
  { apply sum_Rle; intros k Hk; apply cot4_lo; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]. }
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 4) n
                <= sum_f_R0 (fun k => 1 + 2 * Rcot (theta (S n) (S k)) ^ 2 + Rcot (theta (S n) (S k)) ^ 4) n).
  { apply sum_Rle; intros k Hk; apply cot4_hi; [ apply (proj1 (Hgeo k Hk)) | apply (proj2 (Hgeo k Hk)) ]. }
  assert (Hc4 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n
                = M * (2 * M - 1) * (4 * M ^ 2 + 10 * M - 9) / 45).
  { pose proof (cot4_sum_ge1 (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH.
    unfold M; reflexivity. }
  assert (Hc2 : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n = M * (2 * M - 1) / 3).
  { pose proof (cot_sq_sum (S n) ltac:(lia)) as HH.
    replace (S n - 1)%nat with n in HH by lia. unfold theta; rewrite HH.
    unfold M; reflexivity. }
  assert (Hupsum : sum_f_R0 (fun k => 1 + 2 * Rcot (theta (S n) (S k)) ^ 2 + Rcot (theta (S n) (S k)) ^ 4) n
                   = M + 2 * (M * (2 * M - 1) / 3) + M * (2 * M - 1) * (4 * M ^ 2 + 10 * M - 9) / 45).
  { transitivity (sum_f_R0 (fun _ => 1) n
                  + 2 * sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                  + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 4) n).
    - rewrite (scal_sum (fun k => Rcot (theta (S n) (S k)) ^ 2) n 2).
      rewrite <- (plus_sum (fun _ => 1) (fun k => Rcot (theta (S n) (S k)) ^ 2 * 2) n).
      rewrite <- (plus_sum (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2 * 2)
                    (fun k => Rcot (theta (S n) (S k)) ^ 4) n).
      apply sum_eq; intros k _; ring.
    - rewrite sum_cte, Hc2, Hc4. replace (INR (S n)) with M by reflexivity. field. }
  rewrite Hc4 in Hlow. rewrite Hupsum in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb4; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 4 / PI ^ 4); [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M * (2 * M - 1) * (4 * M ^ 2 + 10 * M - 9) / 45); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 4 / PI ^ 4 * zpart4 n); [ exact Hlow | right; ring ].
  - unfold upb4; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 4 / PI ^ 4); [ apply Rdiv_lt_0_compat; apply pow_lt; nra | ].
    apply Rle_trans with (M + 2 * (M * (2 * M - 1) / 3) + M * (2 * M - 1) * (4 * M ^ 2 + 10 * M - 9) / 45).
    + apply Rle_trans with ((2 * M + 1) ^ 4 / PI ^ 4 * zpart4 n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

(* --- both bounds → π⁴/90 --- *)

Lemma lowb4_cv : Un_cv lowb4 (PI ^ 4 / 90).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb4 n - PI ^ 4 / 90) (fun n => PI ^ 4 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP4 : 0 < PI ^ 4) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD4 : 0 < (2 * M + 1) ^ 4) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 4 = 16*M^4+32*M^3+24*M^2+8*M+1) by ring.
    replace (lowb4 n - PI ^ 4 / 90)
      with (PI ^ 4 * (- 80 * M ^ 2 + 10 * M - 1) / (90 * (2 * M + 1) ^ 4))
      by (unfold lowb4; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 4 * (- 80 * M ^ 2 + 10 * M - 1) / (90 * (2 * M + 1) ^ 4) - - (PI ^ 4 * / M)); [ lra | ].
      replace (PI ^ 4 * (- 80 * M ^ 2 + 10 * M - 1) / (90 * (2 * M + 1) ^ 4) - - (PI ^ 4 * / M))
        with (PI ^ 4 * (M * (- 80 * M ^ 2 + 10 * M - 1) + 90 * (2 * M + 1) ^ 4) / (90 * M * (2 * M + 1) ^ 4))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 4 * / M - PI ^ 4 * (- 80 * M ^ 2 + 10 * M - 1) / (90 * (2 * M + 1) ^ 4)); [ lra | ].
      replace (PI ^ 4 * / M - PI ^ 4 * (- 80 * M ^ 2 + 10 * M - 1) / (90 * (2 * M + 1) ^ 4))
        with (PI ^ 4 * (90 * (2 * M + 1) ^ 4 - M * (- 80 * M ^ 2 + 10 * M - 1)) / (90 * M * (2 * M + 1) ^ 4))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb4_cv : Un_cv upb4 (PI ^ 4 / 90).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb4 n - PI ^ 4 / 90) (fun n => PI ^ 4 * / INR (S n))).
  - intro n; set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP4 : 0 < PI ^ 4) by (apply pow_lt; exact HP).
    assert (HMpos : 0 < M) by lra.
    assert (HD4 : 0 < (2 * M + 1) ^ 4) by (apply pow_lt; nra).
    assert (Hexp : (2 * M + 1) ^ 4 = 16*M^4+32*M^3+24*M^2+8*M+1) by ring.
    replace (upb4 n - PI ^ 4 / 90)
      with (PI ^ 4 * (40 * M ^ 2 + 40 * M - 1) / (90 * (2 * M + 1) ^ 4))
      by (unfold upb4; fold M; field; nra).
    apply Rabs_le; split.
    + cut (0 <= PI ^ 4 * (40 * M ^ 2 + 40 * M - 1) / (90 * (2 * M + 1) ^ 4) - - (PI ^ 4 * / M)); [ lra | ].
      replace (PI ^ 4 * (40 * M ^ 2 + 40 * M - 1) / (90 * (2 * M + 1) ^ 4) - - (PI ^ 4 * / M))
        with (PI ^ 4 * (M * (40 * M ^ 2 + 40 * M - 1) + 90 * (2 * M + 1) ^ 4) / (90 * M * (2 * M + 1) ^ 4))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
    + cut (0 <= PI ^ 4 * / M - PI ^ 4 * (40 * M ^ 2 + 40 * M - 1) / (90 * (2 * M + 1) ^ 4)); [ lra | ].
      replace (PI ^ 4 * / M - PI ^ 4 * (40 * M ^ 2 + 40 * M - 1) / (90 * (2 * M + 1) ^ 4))
        with (PI ^ 4 * (90 * (2 * M + 1) ^ 4 - M * (40 * M ^ 2 + 40 * M - 1)) / (90 * M * (2 * M + 1) ^ 4))
        by (field; nra).
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | rewrite Hexp; nra ] | apply Rlt_le, Rinv_0_lt_compat; nra ].
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma zpart4_cv : Un_cv zpart4 (PI ^ 4 / 90).
Proof.
  apply (BaselTrig.Un_cv_squeeze lowb4 zpart4 upb4);
    [ apply lowb4_cv | apply upb4_cv | apply zpart4_bounds ].
Qed.

(* --- ζ(4) = π⁴/90 for the completed zeta's ζ --- *)

Lemma Zpart4_eq : forall N, Zpart 4 N = zpart4 N.
Proof.
  intro N; unfold Zpart, zpart4; apply sum_eq; intros k _; unfold zterm4.
  assert (Hpos : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (H4 : (4:R) = INR 4) by (simpl; ring).
  rewrite Rpower_Ropp; f_equal.
  rewrite H4, (Rpower_pow 4 (INR (S k)) Hpos); reflexivity.
Qed.

Theorem zeta_cont_4 : forall (Hs0 : 0 < 4) (Hs1 : (4:R) <> 1), zeta_cont 4 Hs0 Hs1 = PI ^ 4 / 90.
Proof.
  intros Hs0 Hs1; apply (UL_sequence (Zpart 4)).
  - apply (zeta_hookup 4 Hs0 Hs1); lra.
  - apply (Un_cv_ext zpart4 (Zpart 4)); [ intro N; symmetry; apply Zpart4_eq | apply zpart4_cv ].
Qed.

Print Assumptions zeta_cont_4.

(* ================================================================= *)
(*  END BaselZeta4Value.v.  ζ(4) = π⁴/90.                             *)
(* ================================================================= *)
