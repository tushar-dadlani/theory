(* ================================================================= *)
(*  LnSeries.v  --  a certified logarithm from the atanh series.      *)
(*                                                                    *)
(*     Lfun h = (1/2)(ln(1+h) - ln(1-h)) = atanh h,                   *)
(*     ln x   = 2 * Lfun ((x-1)/(x+1))          for x > 0,            *)
(*     Lfun h = Lser K h + R,  0 <= R <= h^(2K+3)/(1-h^2).            *)
(*                                                                    *)
(*  The remainder is one MVT, exactly as in GammaDir.atan_sandwich:    *)
(*  Lfun' - Lser K' = 1/(1-x^2) - (1-x^(2K+2))/(1-x^2) = x^(2K+2)/    *)
(*  (1-x^2), which is between 0 and h^(2K+2)/(1-h^2) on [0,h].         *)
(*                                                                    *)
(*  Since Lser K h is a POLYNOMIAL with rational coefficients, this    *)
(*  gives rational two-sided enclosures of ln at rational points, and  *)
(*  the argument reduction x = 2^m y keeps h small, so a handful of    *)
(*  terms suffices: at h = 1/3 (ln 2) ten terms already give 1e-10.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Open Scope R_scope.

Lemma div_nonneg_aux : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros a b Ha Hb. unfold Rdiv. apply Rmult_le_pos;
    [ exact Ha | left; apply Rinv_0_lt_compat; exact Hb ].
Qed.

Definition Lfun (h : R) : R := / 2 * (ln (1 + h) - ln (1 - h)).

Definition Lser (K : nat) (h : R) : R :=
  sum_f_R0 (fun k => / INR (2 * k + 1) * h ^ (2 * k + 1)) K.

Definition Gser (K : nat) (h : R) : R := sum_f_R0 (fun k => h ^ (2 * k)) K.

(* ---- derivative of the closed form ---- *)

Lemma d_affine_p : forall c h, derivable_pt_lim (fun x => c + x) h 1.
Proof.
  intros c h. replace 1 with (0 + 1) by ring.
  apply derivable_pt_lim_plus;
    [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ].
Qed.

Lemma d_affine_m : forall c h, derivable_pt_lim (fun x => c - x) h (-1).
Proof.
  intros c h. replace (-1) with (0 - 1) by ring.
  apply derivable_pt_lim_minus;
    [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ].
Qed.

Lemma Lfun_deriv : forall h, -1 < h < 1 -> derivable_pt_lim Lfun h (/ (1 - h ^ 2)).
Proof.
  intros h [Hlo Hhi].
  assert (Hp : 0 < 1 + h) by lra.
  assert (Hm : 0 < 1 - h) by lra.
  assert (D1 : derivable_pt_lim (fun x => ln (1 + x)) h (/ (1 + h))).
  { pose proof (derivable_pt_lim_comp (fun x => 1 + x) ln h 1 (/ (1 + h))
                  (d_affine_p 1 h) (derivable_pt_lim_ln (1 + h) Hp)) as Hc.
    unfold comp in Hc; cbv beta in Hc.
    replace (/ (1 + h)) with (/ (1 + h) * 1) by ring. exact Hc. }
  assert (D2 : derivable_pt_lim (fun x => ln (1 - x)) h (- / (1 - h))).
  { pose proof (derivable_pt_lim_comp (fun x => 1 - x) ln h (-1) (/ (1 - h))
                  (d_affine_m 1 h) (derivable_pt_lim_ln (1 - h) Hm)) as Hc.
    unfold comp in Hc; cbv beta in Hc.
    replace (- / (1 - h)) with (/ (1 - h) * -1) by ring. exact Hc. }
  assert (Dd : derivable_pt_lim (fun x => ln (1 + x) - ln (1 - x)) h
                 (/ (1 + h) - - / (1 - h)))
    by (apply derivable_pt_lim_minus; assumption).
  pose proof (derivable_pt_lim_scal (fun x => ln (1 + x) - ln (1 - x)) (/ 2) h
                (/ (1 + h) - - / (1 - h)) Dd) as Hs.
  unfold mult_real_fct in Hs.
  assert (Hne1 : 1 + h <> 0) by (apply Rgt_not_eq; lra).
  assert (Hne2 : 1 - h <> 0) by (apply Rgt_not_eq; lra).
  assert (Hne3 : 1 - h ^ 2 <> 0) by (apply Rgt_not_eq; nra).
  replace (/ (1 - h ^ 2)) with (/ 2 * (/ (1 + h) - - / (1 - h)))
    by (field; repeat split; assumption).
  exact Hs.
Qed.

(* ---- derivative of the partial sum ---- *)

Lemma Lser_deriv : forall K h, derivable_pt_lim (fun x => Lser K x) h (Gser K h).
Proof.
  intros K h. induction K as [| K IH].
  - unfold Lser, Gser; cbn [sum_f_R0].
    replace (/ INR (2 * 0 + 1) * h ^ (2 * 0 + 1)) with h by (simpl; field).
    replace (h ^ (2 * 0)) with 1 by (simpl; ring).
    assert (E : (fun x : R => / INR (2 * 0 + 1) * x ^ (2 * 0 + 1)) = (fun x : R => x)).
    { apply functional_extensionality. intro x. simpl. field. }
    rewrite E. apply derivable_pt_lim_id.
  - unfold Lser, Gser in *. rewrite tech5.
    assert (E : (fun x : R => sum_f_R0 (fun k => / INR (2 * k + 1) * x ^ (2 * k + 1)) (S K))
                = (fun x : R => sum_f_R0 (fun k => / INR (2 * k + 1) * x ^ (2 * k + 1)) K
                                + / INR (2 * S K + 1) * x ^ (2 * S K + 1))).
    { apply functional_extensionality. intro x. rewrite tech5. reflexivity. }
    rewrite E.
    apply derivable_pt_lim_plus; [ exact IH | ].
    assert (Hn : INR (2 * S K + 1) <> 0).
    { assert (0 < INR (2 * S K + 1)) by (apply lt_0_INR; lia). lra. }
    pose proof (derivable_pt_lim_pow h (2 * S K + 1)) as Hp.
    pose proof (derivable_pt_lim_scal (fun y => y ^ (2 * S K + 1))
                  (/ INR (2 * S K + 1)) h
                  (INR (2 * S K + 1) * h ^ Init.Nat.pred (2 * S K + 1)) Hp) as Hs.
    unfold mult_real_fct in Hs.
    replace (h ^ (2 * S K)) with
      (/ INR (2 * S K + 1) * (INR (2 * S K + 1) * h ^ Init.Nat.pred (2 * S K + 1))).
    + exact Hs.
    + replace (Init.Nat.pred (2 * S K + 1)) with (2 * S K)%nat by lia. field; exact Hn.
Qed.

(* ---- the geometric identity ---- *)

Lemma geo_sum : forall K h, h ^ 2 <> 1 ->
  Gser K h = (1 - h ^ (2 * K + 2)) / (1 - h ^ 2).
Proof.
  intros K h Hh.
  assert (Hne : 1 - h ^ 2 <> 0) by lra.
  induction K as [| K IH].
  - unfold Gser; cbn [sum_f_R0].
    replace (h ^ (2 * 0)) with 1 by (simpl; ring).
    replace (2 * 0 + 2)%nat with 2%nat by lia. field; exact Hne.
  - unfold Gser in *. rewrite tech5, IH.
    replace (2 * S K + 2)%nat with (2 * K + 2 + 2)%nat by lia.
    replace (2 * S K)%nat with (2 * K + 2)%nat by lia.
    rewrite !pow_add. field; exact Hne.
Qed.

(* ---- values at 0 ---- *)

Lemma Lfun_0 : Lfun 0 = 0.
Proof. unfold Lfun. rewrite Rplus_0_r, Rminus_0_r, ln_1. ring. Qed.

Lemma Lser_0 : forall K, Lser K 0 = 0.
Proof.
  intro K. unfold Lser. induction K as [| K IH].
  - cbn [sum_f_R0].
    assert (H : (0:R) ^ (2 * 0 + 1) = 0) by (apply pow_i; lia).
    rewrite H. ring.
  - rewrite tech5, IH.
    assert (H : (0:R) ^ (2 * S K + 1) = 0) by (apply pow_i; lia).
    rewrite H. ring.
Qed.

(* ---- the remainder, by one MVT ---- *)

Theorem Lser_remainder : forall K h, 0 <= h < 1 ->
  0 <= Lfun h - Lser K h <= h ^ (2 * K + 3) / (1 - h ^ 2).
Proof.
  intros K h [Hh0 Hh1].
  assert (Hd : 0 < 1 - h ^ 2) by nra.
  destruct (Rle_lt_or_eq_dec 0 h Hh0) as [Hpos | Heq].
  - set (F := fun x : R => Lfun x - Lser K x).
    set (F' := fun x : R => x ^ (2 * K + 2) / (1 - x ^ 2)).
    assert (HD : forall c, 0 <= c <= h -> derivable_pt_lim F c (F' c)).
    { intros c Hc.
      assert (Hc1 : -1 < c < 1) by lra.
      assert (Hcd : 0 < 1 - c ^ 2) by nra.
      pose proof (derivable_pt_lim_minus Lfun (fun x => Lser K x) c
                    (/ (1 - c ^ 2)) (Gser K c) (Lfun_deriv c Hc1)
                    (Lser_deriv K c)) as Hm.
      unfold F, F'.
      replace (c ^ (2 * K + 2) / (1 - c ^ 2)) with (/ (1 - c ^ 2) - Gser K c);
        [ exact Hm | ].
      rewrite (geo_sum K c ltac:(nra)). field. lra. }
    destruct (MVT_cor2 F F' 0 h Hpos HD) as [c [Hfc [Hc0 Hch]]].
    assert (HF0 : F 0 = 0)
      by (unfold F; rewrite Lfun_0, Lser_0; ring).
    assert (Hfc' : Lfun h - Lser K h = F' c * h).
    { rewrite HF0 in Hfc.
      replace (h - 0) with h in Hfc by ring.
      replace (F h - 0) with (F h) in Hfc by ring.
      unfold F in Hfc. exact Hfc. }
    assert (Hcd : 0 < 1 - c ^ 2) by nra.
    assert (Hnum : 0 <= c ^ (2 * K + 2) <= h ^ (2 * K + 2)).
    { split; [ apply pow_le; lra | apply pow_incr; lra ]. }
    assert (Hden : 1 - h ^ 2 <= 1 - c ^ 2) by nra.
    assert (HF'lo : 0 <= F' c)
      by (unfold F'; apply div_nonneg_aux; lra).
    assert (HF'hi : F' c <= h ^ (2 * K + 2) / (1 - h ^ 2)).
    { unfold F'.
      apply Rle_trans with (h ^ (2 * K + 2) / (1 - c ^ 2)).
      - unfold Rdiv. apply Rmult_le_compat_r;
          [ left; apply Rinv_0_lt_compat; lra | lra ].
      - unfold Rdiv. apply Rmult_le_compat_l; [ lra | ].
        apply Rinv_le_contravar; lra. }
    assert (Hpow : h ^ (2 * K + 2) * h = h ^ (2 * K + 3)).
    { replace (2 * K + 3)%nat with (S (2 * K + 2)) by lia.
      rewrite <- tech_pow_Rmult. ring. }
    rewrite Hfc'. split.
    + apply Rmult_le_pos; lra.
    + apply Rle_trans with (h ^ (2 * K + 2) / (1 - h ^ 2) * h).
      * apply Rmult_le_compat_r; lra.
      * apply Req_le. unfold Rdiv. rewrite <- Hpow. ring.
  - rewrite <- Heq. rewrite Lfun_0, Lser_0.
    assert (H : (0:R) ^ (2 * K + 3) = 0) by (apply pow_i; lia).
    rewrite H. replace ((0:R) ^ 2) with 0 by ring.
    rewrite Rminus_0_r. unfold Rdiv. rewrite Rmult_0_l. lra.
Qed.

(* ---- reduction  ln x = 2 Lfun ((x-1)/(x+1)) ---- *)

Lemma ln_quot2 : forall a b, 0 < a -> 0 < b -> ln a - ln b = ln (a / b).
Proof.
  intros a b Ha Hb. unfold Rdiv.
  rewrite ln_mult; [ | exact Ha | apply Rinv_0_lt_compat; exact Hb ].
  rewrite ln_Rinv; [ ring | exact Hb ].
Qed.

Theorem ln_from_L : forall x, 0 < x -> ln x = 2 * Lfun ((x - 1) / (x + 1)).
Proof.
  intros x Hx.
  assert (Hxp : 0 < x + 1) by lra.
  assert (E1 : 1 + (x - 1) / (x + 1) = 2 * x / (x + 1)) by (field; lra).
  assert (E2 : 1 - (x - 1) / (x + 1) = 2 / (x + 1)) by (field; lra).
  unfold Lfun. rewrite E1, E2.
  assert (P1 : 0 < 2 * x / (x + 1)).
  { unfold Rdiv. apply Rmult_lt_0_compat;
      [ lra | apply Rinv_0_lt_compat; lra ]. }
  assert (P2 : 0 < 2 / (x + 1)).
  { unfold Rdiv. apply Rmult_lt_0_compat;
      [ lra | apply Rinv_0_lt_compat; lra ]. }
  rewrite (ln_quot2 _ _ P1 P2).
  replace (2 * x / (x + 1) / (2 / (x + 1))) with x by (field; lra).
  field.
Qed.

(* ---- the enclosure we actually use ---- *)

Theorem ln_enclosure : forall x K, 1 <= x ->
  2 * Lser K ((x - 1) / (x + 1)) <= ln x <=
  2 * Lser K ((x - 1) / (x + 1))
  + 2 * (((x - 1) / (x + 1)) ^ (2 * K + 3) / (1 - ((x - 1) / (x + 1)) ^ 2)).
Proof.
  intros x K Hx.
  assert (Hxp : 0 < x + 1) by lra.
  set (h := (x - 1) / (x + 1)).
  assert (Hh0 : 0 <= h).
  { unfold h, Rdiv. apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ]. }
  assert (Hh1 : h < 1).
  { unfold h. apply Rmult_lt_reg_r with (x + 1); [ lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  destruct (Lser_remainder K h (conj Hh0 Hh1)) as [Hlo Hhi].
  rewrite (ln_from_L x ltac:(lra)). fold h. lra.
Qed.
