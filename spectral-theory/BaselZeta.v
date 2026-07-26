(* ================================================================= *)
(*  BaselZeta.v  —  ζ(2) = π²/6  (the Basel problem).                 *)
(*                                                                    *)
(*  The Cauchy squeeze: from cot²x < 1/x² < 1+cot²x (BaselTrig) and   *)
(*  Σ cot²(kπ/(2m+1)) = m(2m−1)/3 (BaselVieta), summing over          *)
(*  k=1..m at x=kπ/(2m+1) sandwiches the partial sums Σ1/k² between   *)
(*  two rational sequences both → π²/6.  Hence the value the whole    *)
(*  ζ(2) arc converges to:                                            *)
(*      basel : proj1_sig zeta2_converges = (PI² / 6).                *)
(*  Over the classical `Reals` (quarantined).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Arith.
Require Import BaselCotPoly BaselVieta ZetaConverge.
Require BaselTrig.
Local Open Scope R_scope.

Lemma Rcot_eq : forall x, BaselTrig.Rcot x = Rcot x.
Proof. intro x; unfold BaselTrig.Rcot, Rcot; reflexivity. Qed.

(* ---- limit toolkit ---- *)
Lemma Un_cv_maj_0 : forall (a b : nat -> R), (forall n, Rabs (a n) <= b n) -> Un_cv b 0 -> Un_cv a 0.
Proof.
  intros a b Hab Hb eps Heps; destruct (Hb eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); specialize (Hab n); unfold R_dist in *; rewrite Rminus_0_r in *.
  apply Rle_lt_trans with (b n); [ exact Hab | ].
  apply Rle_lt_trans with (Rabs (b n)); [ apply Rle_abs | exact HN ].
Qed.

Lemma Un_cv_scal_0 : forall (a : nat -> R) c, Un_cv a 0 -> Un_cv (fun n => c * a n) 0.
Proof.
  intros a c Ha eps Heps.
  assert (Hc1 : 0 < Rabs c + 1) by (pose proof (Rabs_pos c); lra).
  destruct (Ha (eps / (Rabs c + 1)) ltac:(apply Rdiv_lt_0_compat; assumption)) as [N HN].
  exists N; intros n Hn; specialize (HN n Hn); unfold R_dist in *; rewrite Rminus_0_r in *.
  rewrite Rabs_mult.
  apply Rle_lt_trans with ((Rabs c + 1) * Rabs (a n)).
  - apply Rmult_le_compat_r; [ apply Rabs_pos | lra ].
  - replace eps with ((Rabs c + 1) * (eps / (Rabs c + 1))) by (field; lra).
    apply Rmult_lt_compat_l; [ lra | exact HN ].
Qed.

Lemma Un_cv_shift : forall (a : nat -> R) L, Un_cv (fun n => a n - L) 0 -> Un_cv a L.
Proof.
  intros a L H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); unfold R_dist in *; rewrite Rminus_0_r in HN; exact HN.
Qed.

Lemma Un_cv_inv_Sn : Un_cv (fun n => / INR (S n)) 0.
Proof.
  intros eps Heps; destruct (INR_unbounded (/ eps)) as [N HN]; exists N; intros n Hn.
  unfold R_dist; rewrite Rminus_0_r, Rabs_right
    by (apply Rle_ge, Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia).
  assert (H1 : / eps < INR (S n)) by (apply Rlt_le_trans with (INR N); [ exact HN | apply le_INR; lia ]).
  apply Rinv_lt_contravar in H1.
  - rewrite Rinv_inv in H1; exact H1.
  - apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact Heps | apply lt_0_INR; lia ].
Qed.

Lemma SnM_ge1 : forall n, 1 <= INR (S n).
Proof. intro n; replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia. Qed.

(* ---- the two bounding sequences ---- *)
Definition lowb (n : nat) : R :=
  INR (S n) * (2 * INR (S n) - 1) / 3 * (PI ^ 2 / (2 * INR (S n) + 1) ^ 2).
Definition upb (n : nat) : R :=
  2 * INR (S n) * (INR (S n) + 1) / 3 * (PI ^ 2 / (2 * INR (S n) + 1) ^ 2).

Lemma lowb_cv : Un_cv lowb (PI ^ 2 / 6).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => lowb n - PI ^ 2 / 6) (fun n => 7 * PI ^ 2 / 24 * / INR (S n))).
  - intro n. set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP2 : 0 < PI ^ 2) by nra.
    replace (lowb n - PI ^ 2 / 6) with (- (PI ^ 2 * (6 * M + 1) / (6 * (2 * M + 1) ^ 2)))
      by (unfold lowb; fold M; field; nra).
    rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge, Rlt_le, Rdiv_lt_0_compat; nra).
    cut (0 <= 7 * PI ^ 2 / 24 * / M - PI ^ 2 * (6 * M + 1) / (6 * (2 * M + 1) ^ 2)); [ lra | ].
    replace (7 * PI ^ 2 / 24 * / M - PI ^ 2 * (6 * M + 1) / (6 * (2 * M + 1) ^ 2))
      with (PI ^ 2 * (7 * (2 * M + 1) ^ 2 - 4 * M * (6 * M + 1)) / (24 * M * (2 * M + 1) ^ 2))
      by (field; nra).
    apply Rlt_le, Rdiv_lt_0_compat; nra.
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

Lemma upb_cv : Un_cv upb (PI ^ 2 / 6).
Proof.
  apply Un_cv_shift.
  apply (Un_cv_maj_0 (fun n => upb n - PI ^ 2 / 6) (fun n => PI ^ 2 / 24 * / INR (S n))).
  - intro n. set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
    pose proof PI_RGT_0 as HP. assert (HP2 : 0 < PI ^ 2) by nra.
    replace (upb n - PI ^ 2 / 6) with (- (PI ^ 2 / (6 * (2 * M + 1) ^ 2)))
      by (unfold upb; fold M; field; nra).
    rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge, Rlt_le, Rdiv_lt_0_compat; nra).
    cut (0 <= PI ^ 2 / 24 * / M - PI ^ 2 / (6 * (2 * M + 1) ^ 2)); [ lra | ].
    replace (PI ^ 2 / 24 * / M - PI ^ 2 / (6 * (2 * M + 1) ^ 2))
      with (PI ^ 2 * ((2 * M + 1) ^ 2 - 4 * M) / (24 * M * (2 * M + 1) ^ 2))
      by (field; nra).
    apply Rlt_le, Rdiv_lt_0_compat; nra.
  - apply Un_cv_scal_0, Un_cv_inv_Sn.
Qed.

(* ---- the summed squeeze on zpart ---- *)
Lemma cot_sum_val : forall n,
  sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n = INR (S n) * (2 * INR (S n) - 1) / 3.
Proof.
  intro n; pose proof (cot_sq_sum (S n) ltac:(lia)) as H.
  replace (S n - 1)%nat with n in H by lia.
  rewrite <- H; apply sum_eq; intros k Hk; unfold theta; reflexivity.
Qed.

Lemma zpart_bounds : forall n, lowb n <= zpart n <= upb n.
Proof.
  intro n. set (M := INR (S n)). pose proof (SnM_ge1 n) as HM. fold M in HM.
  pose proof PI_RGT_0 as HP. assert (HP2 : 0 < PI ^ 2) by nra.
  assert (HdenM : INR (2 * S n + 1) = 2 * M + 1)
    by (unfold M; rewrite plus_INR, mult_INR; simpl; ring).
  assert (Hgeo : forall k, (k <= n)%nat -> 0 < theta (S n) (S k) < PI / 2)
    by (intros k Hk; split; [ apply theta_pos; lia | apply theta_lt; lia ]).
  assert (Hmid : sum_f_R0 (fun k => / theta (S n) (S k) ^ 2) n = (2 * M + 1) ^ 2 / PI ^ 2 * zpart n).
  { unfold zpart. rewrite (scal_sum zterm n ((2 * M + 1) ^ 2 / PI ^ 2)).
    apply sum_eq; intros k Hk. unfold zterm, theta. rewrite HdenM.
    field; repeat split; first [ apply not_0_INR; lia | apply Rgt_not_eq; nra ]. }
  assert (Hlow : sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n
                 <= sum_f_R0 (fun k => / theta (S n) (S k) ^ 2) n).
  { apply sum_Rle; intros k Hk; apply Rlt_le.
    destruct (BaselTrig.cot_sq_bounds (theta (S n) (S k)) (proj1 (Hgeo k Hk)) (proj2 (Hgeo k Hk))) as [Hlb _].
    rewrite Rcot_eq in Hlb; exact Hlb. }
  assert (Hup : sum_f_R0 (fun k => / theta (S n) (S k) ^ 2) n
                <= sum_f_R0 (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2) n).
  { apply sum_Rle; intros k Hk; apply Rlt_le.
    destruct (BaselTrig.cot_sq_bounds (theta (S n) (S k)) (proj1 (Hgeo k Hk)) (proj2 (Hgeo k Hk))) as [_ Hub].
    rewrite Rcot_eq in Hub; exact Hub. }
  rewrite cot_sum_val in Hlow.
  assert (Hone : sum_f_R0 (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2) n = M + M * (2 * M - 1) / 3).
  { replace (sum_f_R0 (fun k => 1 + Rcot (theta (S n) (S k)) ^ 2) n)
      with (sum_f_R0 (fun _ => 1) n + sum_f_R0 (fun k => Rcot (theta (S n) (S k)) ^ 2) n)
      by (rewrite <- plus_sum; apply sum_eq; intros k Hk; ring).
    rewrite sum_cte, cot_sum_val. replace (INR (S n)) with M by reflexivity. ring. }
  rewrite Hone in Hup. rewrite Hmid in Hlow, Hup.
  split.
  - unfold lowb; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 2 / PI ^ 2); [ apply Rdiv_lt_0_compat; nra | ].
    apply Rle_trans with (M * (2 * M - 1) / 3); [ right; field; nra | ].
    apply Rle_trans with ((2 * M + 1) ^ 2 / PI ^ 2 * zpart n); [ exact Hlow | right; ring ].
  - unfold upb; fold M.
    apply Rmult_le_reg_r with (r := (2 * M + 1) ^ 2 / PI ^ 2); [ apply Rdiv_lt_0_compat; nra | ].
    apply Rle_trans with (M + M * (2 * M - 1) / 3).
    + apply Rle_trans with ((2 * M + 1) ^ 2 / PI ^ 2 * zpart n); [ right; ring | exact Hup ].
    + right; field; nra.
Qed.

(* ---- the value of ζ(2) ---- *)
Theorem basel : proj1_sig zeta2_converges = PI ^ 2 / 6.
Proof.
  destruct zeta2_converges as [l Hl]; simpl.
  assert (Hcv : Un_cv zpart (PI ^ 2 / 6))
    by (apply (BaselTrig.Un_cv_squeeze lowb zpart upb); [ apply lowb_cv | apply upb_cv | apply zpart_bounds ]).
  apply (UL_sequence zpart); assumption.
Qed.

Print Assumptions basel.

(* ================================================================= *)
(*  END BaselZeta.v.   ζ(2) = Σ 1/n² = π²/6.                          *)
(* ================================================================= *)
