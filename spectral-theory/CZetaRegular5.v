(* ================================================================= *)
(*  CZetaRegular5.v   (Phase B2, part 4: the limit  G(z) -> ellsum)     *)
(*                                                                    *)
(*  proj1_sig (gtermC_cv s ..)  ->  RtoC ellsum   as  s -> 1.          *)
(*                                                                    *)
(*  eps/3 argument: a uniform majorant  |gtermC s n| <= 3 (n+1)^{-3/2}  *)
(*  (for |s-1|<=1/2) controls the tail (cseries_remainder_bound); the   *)
(*  finite head converges by the per-term limit gtermC_term_limit.      *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CexpFull CPower
        CSeries CSeriesLin CZetaTerm CZetaRegular CZetaRegular2 CZetaRegular3
        CZetaRegular4.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Rpower is monotone in the exponent for base >= 1                  *)
(* ----------------------------------------------------------------- *)
Lemma lnbase_nonneg : forall base, 1 <= base -> 0 <= ln base.
Proof.
  intros base Hb. rewrite <- ln_1.
  destruct (Rle_lt_or_eq_dec 1 base Hb) as [H | H].
  - left. apply ln_increasing; lra.
  - right. rewrite H; reflexivity.
Qed.

Lemma Rpower_exp_le : forall base x y, 1 <= base -> x <= y ->
  Rpower base x <= Rpower base y.
Proof.
  intros base x y Hb Hxy. unfold Rpower.
  assert (Hln : 0 <= ln base) by (apply lnbase_nonneg; exact Hb).
  assert (Hle : x * ln base <= y * ln base) by (apply Rmult_le_compat_r; assumption).
  destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt | Heq].
  - left. apply exp_increasing; exact Hlt.
  - rewrite Heq; right; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  the uniform majorant  Bmaj n = 3 (n+1)^{-3/2}                     *)
(* ----------------------------------------------------------------- *)
Definition Bmaj (n : nat) : R := 3 * Rpower (INR (S n)) (- (3 / 2)).

Lemma sum_scal3 : forall f N, sum_f_R0 (fun n => 3 * f n) N = 3 * sum_f_R0 f N.
Proof.
  intros f N. induction N as [| N IH]; [ reflexivity | rewrite !tech5, IH; ring ].
Qed.

Lemma Bmaj_cv : { TB | Un_cv (sum_f_R0 Bmaj) TB }.
Proof.
  destruct (pseries_cv (3 / 2) ltac:(lra)) as [T HT].
  exists (3 * T).
  apply (Un_cv_ext (fun N => 3 * sum_f_R0 (fun n => Rpower (INR (S n)) (- (3/2))) N)).
  - intro N. unfold Bmaj. rewrite sum_scal3. reflexivity.
  - apply (CV_mult (fun _ => 3) (fun n => sum_f_R0 (fun k => Rpower (INR (S k)) (- (3/2))) n) 3 T);
      [ apply Un_cv_const | exact HT ].
Qed.

Lemma INR_S_ge1 : forall n, 1 <= INR (S n).
Proof. intro n. rewrite S_INR. pose proof (pos_INR n); lra. Qed.

Lemma gtermC_unif_bound : forall s n,
  Cmod (Cminus s C1) <= / 2 -> Cminus C1 s <> C0 ->
  Cmod (gtermC s n) <= Bmaj n.
Proof.
  intros s n Hs H1.
  assert (HRe1 : Rabs (Re (Cminus s C1)) <= Cmod (Cminus s C1)) by apply Cmod_Re_le.
  assert (HReval : Re (Cminus s C1) = Re s - 1)
    by (unfold Cminus, Cadd, Copp, C1; cbn [Re Im]; ring).
  assert (HRe : / 2 <= Re s).
  { assert (Hr : Rabs (Re s - 1) <= / 2) by (rewrite HReval in HRe1; lra).
    unfold Rabs in Hr; destruct (Rcase_abs (Re s - 1)); lra. }
  assert (HCs : Cmod s <= 3 / 2).
  { assert (Ht : Cmod s <= Cmod (Cminus s C1) + Cmod C1).
    { apply Rle_trans with (Cmod (Cadd (Cminus s C1) C1));
        [ apply Req_le; f_equal; ring | apply Cmod_triangle ]. }
    assert (HC1 : Cmod C1 = 1)
      by (replace C1 with (RtoC 1) by reflexivity; rewrite Cmod_RtoC; apply Rabs_R1).
    lra. }
  eapply Rle_trans; [ apply (Cmod_gtermC_bound s n ltac:(lra) H1) | ].
  unfold Bmaj.
  apply Rle_trans with (2 * (3 / 2 * Rpower (INR (S n)) (- (3/2)))); [ | lra ].
  apply Rmult_le_compat_l; [ lra | ].
  apply Rmult_le_compat.
  - apply Cmod_nonneg.
  - apply Rlt_le; unfold Rpower; apply exp_pos.
  - exact HCs.
  - apply Rpower_exp_le; [ apply INR_S_ge1 | lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  small algebraic helpers                                           *)
(* ----------------------------------------------------------------- *)
Lemma Cpsum_minus : forall a b N,
  Cpsum (fun k => Cminus (a k) (b k)) N = Cminus (Cpsum a N) (Cpsum b N).
Proof.
  intros a b N; induction N as [| N IH]; simpl; [ reflexivity | rewrite IH; ring ].
Qed.

Lemma RtoC_minus : forall a b, RtoC (a - b) = Cminus (RtoC a) (RtoC b).
Proof. intros a b; apply Ceq; unfold Cminus, Cadd, Copp, RtoC; cbn [Re Im]; ring. Qed.

Lemma RtoC_Cpsum : forall f N, Cpsum (fun k => RtoC (f k)) N = RtoC (sum_f_R0 f N).
Proof.
  intros f N; induction N as [| N IH]; [ reflexivity | ].
  simpl Cpsum. rewrite IH. rewrite (tech5 f N). rewrite RtoC_add. reflexivity.
Qed.

Lemma Cmod_minus3 : forall a b c,
  Cmod (Cminus a c) <= Cmod (Cminus a b) + Cmod (Cminus b c).
Proof.
  intros a b c.
  replace (Cminus a c) with (Cadd (Cminus a b) (Cminus b c)) by ring.
  apply Cmod_triangle.
Qed.

(* ----------------------------------------------------------------- *)
(*  the finite head converges to 0 as s -> 1                         *)
(* ----------------------------------------------------------------- *)
Lemma finite_sum_limit : forall M eps, 0 < eps -> exists del, 0 < del /\
  forall s, Cmod (Cminus s C1) < del -> Cminus s C1 <> C0 ->
    sum_f_R0 (fun k => Cmod (Cminus (gtermC s k) (RtoC (ell k)))) M < eps.
Proof.
  induction M as [| M IH]; intros eps Heps.
  - destruct (gtermC_term_limit 0 eps Heps) as [del [Hdel Hb]].
    exists del; split; [ exact Hdel | ]. intros s Hs Hne. simpl. apply Hb; assumption.
  - destruct (IH (eps / 2) ltac:(lra)) as [del1 [Hd1 Hb1]].
    destruct (gtermC_term_limit (S M) (eps / 2) ltac:(lra)) as [del2 [Hd2 Hb2]].
    exists (Rmin del1 del2); split; [ apply Rmin_pos; assumption | ].
    intros s Hs Hne. rewrite tech5.
    assert (Hs1 : Cmod (Cminus s C1) < del1) by (eapply Rlt_le_trans; [ exact Hs | apply Rmin_l ]).
    assert (Hs2 : Cmod (Cminus s C1) < del2) by (eapply Rlt_le_trans; [ exact Hs | apply Rmin_r ]).
    pose proof (Hb1 s Hs1 Hne). pose proof (Hb2 s Hs2 Hne). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE LIMIT:  G(s) = sum gtermC s  ->  RtoC ellsum   as  s -> 1     *)
(* ----------------------------------------------------------------- *)
Theorem G_limit : forall eps, 0 < eps -> exists del, 0 < del /\
  forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
    Cmod (Cminus s C1) < del ->
    Cmod (Cminus (proj1_sig (gtermC_cv s H0 H1)) (RtoC ellsum)) < eps.
Proof.
  intros eps Heps.
  destruct Bmaj_cv as [TB HTB].
  destruct (HTB (eps / 3) ltac:(lra)) as [M0 HM0].
  destruct (ellsum_cv (eps / 3) ltac:(lra)) as [M1 HM1].
  set (M := max M0 M1).
  destruct (finite_sum_limit M (eps / 3) ltac:(lra)) as [del2 [Hd2 Hb2]].
  exists (Rmin del2 (/ 2)); split; [ apply Rmin_pos; lra | ].
  intros s H0 H1 Hs.
  assert (Hsd2 : Cmod (Cminus s C1) < del2)
    by (eapply Rlt_le_trans; [ exact Hs | apply Rmin_l ]).
  assert (Hshalf : Cmod (Cminus s C1) <= / 2)
    by (apply Rlt_le; eapply Rlt_le_trans; [ exact Hs | apply Rmin_r ]).
  assert (HneC : Cminus s C1 <> C0).
  { intro Hc. apply H1. apply Ceq;
      [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
      unfold Cminus, Cadd, Copp, C0 in *; cbn [Re Im] in *; lra. }
  set (G := proj1_sig (gtermC_cv s H0 H1)).
  assert (HGcv : Cseries_cv (gtermC s) G) by (exact (proj2_sig (gtermC_cv s H0 H1))).
  (* Term1: the tail *)
  assert (HT1 : Cmod (Cminus G (Cpsum (gtermC s) M)) < eps / 3).
  { eapply Rle_lt_trans.
    - apply (cseries_remainder_bound (gtermC s) Bmaj G TB HGcv
               (fun n => gtermC_unif_bound s n Hshalf H1) HTB M).
    - pose proof (HM0 M (Nat.le_max_l M0 M1)) as HH. unfold R_dist in HH.
      pose proof (Rle_abs (TB - sum_f_R0 Bmaj M)) as HA.
      rewrite Rabs_minus_sym in HH. lra. }
  (* Term3: the ell tail *)
  assert (HT3 : Cmod (Cminus (Cpsum (fun k => RtoC (ell k)) M) (RtoC ellsum)) < eps / 3).
  { rewrite RtoC_Cpsum, <- RtoC_minus, Cmod_RtoC.
    pose proof (HM1 M (Nat.le_max_r M0 M1)) as HH. unfold R_dist in HH. exact HH. }
  (* Term2: the head *)
  assert (HT2 : Cmod (Cminus (Cpsum (gtermC s) M) (Cpsum (fun k => RtoC (ell k)) M)) < eps / 3).
  { rewrite <- Cpsum_minus. eapply Rle_lt_trans; [ apply Cmod_Cpsum_le | ].
    apply Hb2; assumption. }
  (* combine *)
  eapply Rle_lt_trans; [ apply (Cmod_minus3 G (Cpsum (gtermC s) M) (RtoC ellsum)) | ].
  eapply Rlt_le_trans.
  - apply Rplus_lt_compat_l with (r := Cmod (Cminus G (Cpsum (gtermC s) M))).
    eapply Rle_lt_trans; [ apply (Cmod_minus3 (Cpsum (gtermC s) M) (Cpsum (fun k => RtoC (ell k)) M) (RtoC ellsum)) | ].
    apply Rplus_lt_compat; [ exact HT2 | exact HT3 ].
  - lra.
Qed.

Print Assumptions G_limit.
