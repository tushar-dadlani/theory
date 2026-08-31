(* ================================================================= *)
(*  LnConstants.v  --  certified rational bounds for ln 2 and ln pi.  *)
(*                                                                    *)
(*  ln 2  : one call of ln_enclosure at h = (2-1)/(2+1) = 1/3, K = 5.  *)
(*  ln pi : split as ln 2 + ln(pi/2) and bracket pi/2 in [1.5707,      *)
(*          1.5708] using CertifiedPi, then ln_enclosure at each       *)
(*          rational endpoint (h ~ 0.222, K = 3).                      *)
(*                                                                    *)
(*  The reduction matters: applied to pi directly the series argument  *)
(*  would be h ~ 0.517 and the rational arithmetic would blow up.      *)
(*  Halving once brings h to 0.222, where four terms already beat the  *)
(*  width of the pi bracket itself.                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import LnSeries CertifiedPi.
Open Scope R_scope.

Lemma ln_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [H|H];
    [ left; apply ln_increasing; assumption | rewrite H; apply Rle_refl ].
Qed.

Lemma Lser_3 : forall h, Lser 3 h = h + h^3/3 + h^5/5 + h^7/7.
Proof. intro h. unfold Lser. simpl. lra. Qed.

Lemma Lser_5 : forall h,
  Lser 5 h = h + h^3/3 + h^5/5 + h^7/7 + h^9/9 + h^11/11.
Proof. intro h. unfold Lser. simpl. lra. Qed.

(* ---- ln 2 ---- *)

Theorem ln2_bounds : 6931470 / 10000000 <= ln 2 <= 6931486 / 10000000.
Proof.
  destruct (ln_enclosure 2 5 ltac:(lra)) as [Hlo Hhi].
  assert (Hh : (2 - 1) / (2 + 1) = / 3) by field.
  rewrite Hh in Hlo, Hhi. rewrite Lser_5 in Hlo, Hhi.
  simpl in Hhi. lra.
Qed.

(* ---- ln (pi/2) at the two rational endpoints ---- *)

Lemma ln_15707 : 4515210 / 10000000 <= ln (15707 / 10000).
Proof.
  destruct (ln_enclosure (15707 / 10000) 3 ltac:(lra)) as [Hlo _].
  assert (Hh : (15707 / 10000 - 1) / (15707 / 10000 + 1) = 5707 / 25707)
    by field.
  rewrite Hh in Hlo. rewrite Lser_3 in Hlo. lra.
Qed.

Lemma ln_15708 : ln (15708 / 10000) <= 4515876 / 10000000.
Proof.
  destruct (ln_enclosure (15708 / 10000) 3 ltac:(lra)) as [_ Hhi].
  assert (Hh : (15708 / 10000 - 1) / (15708 / 10000 + 1) = 5708 / 25708)
    by field.
  rewrite Hh in Hhi. rewrite Lser_3 in Hhi. simpl in Hhi. lra.
Qed.

(* ---- ln pi ---- *)

Theorem lnPI_bounds : 1144668 / 1000000 <= ln PI <= 1144737 / 1000000.
Proof.
  pose proof PI_lower as HPl. pose proof PI_upper as HPu.
  assert (Hpos : 0 < PI / 2) by lra.
  assert (Hsplit : ln PI = ln 2 + ln (PI / 2)).
  { replace (ln PI) with (ln (2 * (PI / 2))) by (f_equal; field).
    apply ln_mult; lra. }
  assert (Hlo : ln (15707 / 10000) <= ln (PI / 2))
    by (apply ln_mono; lra).
  assert (Hhi : ln (PI / 2) <= ln (15708 / 10000))
    by (apply ln_mono; lra).
  pose proof ln_15707 as H1. pose proof ln_15708 as H2.
  pose proof ln2_bounds as [H3 H4].
  rewrite Hsplit. lra.
Qed.
