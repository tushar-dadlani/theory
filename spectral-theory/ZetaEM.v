(* ================================================================= *)
(*  ZetaEM.v  --  the trapezoid representation of zeta.               *)
(*                                                                    *)
(*  gtermC - htermC = (g(n+1) - g(n+2))/2 telescopes, so replacing    *)
(*  the first-order Euler-Maclaurin defect by the trapezoid one costs  *)
(*  exactly the single boundary term g(1)/2 = 1/2:                    *)
(*                                                                    *)
(*      zetaC s = 1/(s-1) + 1/2 + sum_{n>=0} htermC s n,              *)
(*                                                                    *)
(*  where the new terms are O(n^{-Re s-2}) instead of O(n^{-Re s-1}).  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CexpFull CPowBase CSeries
        CZetaTerm CZeta ZetaTrap CZetaRegular4.
Open Scope R_scope.

Lemma Cexpf_C0' : Cexpf C0 = C1.
Proof.
  replace C0 with (RtoC 0) by reflexivity.
  rewrite Cexpf_RtoC, exp_0. reflexivity.
Qed.

Lemma gtermC_htermC : forall s n,
  gtermC s n
  = Cadd (htermC s n)
      (Cmul (RtoC (/ 2))
         (Cminus (gC s (INR (S n))) (gC s (INR (S (S n)))))).
Proof.
  intros s n. unfold gtermC, htermC.
  apply Ceq; unfold Cadd, Cminus, Cmul, Copp, RtoC; cbn [Re Im]; field.
Qed.

Lemma gC_one : forall s, gC s (INR 1) = C1.
Proof.
  intro s. unfold gC, Cpw.
  replace (INR 1) with 1 by (simpl; ring).
  rewrite ln_1.
  replace (Cmul (Copp s) (RtoC 0)) with C0
    by (apply Ceq; unfold Cmul, Copp, RtoC, C0; cbn [Re Im]; ring).
  apply Cexpf_C0'.
Qed.

Theorem telescope : forall s M,
  Cpsum (gtermC s) M
  = Cadd (Cpsum (htermC s) M)
      (Cmul (RtoC (/ 2)) (Cminus C1 (gC s (INR (S (S M)))))).
Proof.
  intros s M. induction M as [| M IH].
  - cbn [Cpsum]. rewrite (gtermC_htermC s 0), gC_one. reflexivity.
  - cbn [Cpsum]. rewrite IH, (gtermC_htermC s (S M)). ring.
Qed.

(* ---- the boundary term dies ---- *)

Lemma Rpower_to_0 : forall a, 0 < a ->
  Un_cv (fun n => Rpower (INR (S n)) (- a)) 0.
Proof.
  intros a Ha eps Heps.
  set (B := Rpower (2 / eps) (/ a)).
  assert (HB : 0 < B) by (unfold B, Rpower; apply exp_pos).
  destruct (archimed B) as [Hup _].
  assert (Hup0 : (0 <= up B)%Z).
  { apply Z.lt_le_incl, lt_IZR. simpl. lra. }
  set (N := Z.to_nat (up B)).
  assert (HNB : B < INR N)
    by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by exact Hup0; lra).
  exists N. intros n Hn.
  unfold R_dist. rewrite Rminus_0_r.
  assert (Hpos : 0 < Rpower (INR (S n)) (- a)) by (unfold Rpower; apply exp_pos).
  rewrite Rabs_right by lra.
  assert (HB2 : B <= INR (S n)).
  { apply Rle_trans with (INR N); [ lra | apply le_INR; lia ]. }
  assert (Hval : Rpower B (- a) = eps / 2).
  { unfold B. rewrite Rpower_mult.
    assert (Ea : / a * - a = - (1)) by (field; lra).
    rewrite Ea. unfold Rpower.
    replace (- (1) * ln (2 / eps)) with (- ln (2 / eps)) by ring.
    rewrite exp_Ropp, exp_ln by (apply Rdiv_lt_0_compat; lra).
    field. lra. }
  assert (Hmono : Rpower (INR (S n)) (- a) <= Rpower B (- a))
    by (apply Rpow_negexp_anti; [ exact HB | exact HB2 | lra ]).
  lra.
Qed.

Lemma gC_to_0 : forall s, 0 < Re s ->
  CUn_cv (fun M => gC s (INR (S (S M)))) C0.
Proof.
  intros s Hs eps Heps.
  destruct (Rpower_to_0 (Re s) Hs eps Heps) as [N HN].
  exists N. intros n Hn.
  assert (Hm : Cmod (Cminus (gC s (INR (S (S n)))) C0)
               = Rpower (INR (S (S n))) (- Re s)).
  { replace (Cminus (gC s (INR (S (S n)))) C0) with (gC s (INR (S (S n))))
      by ring.
    unfold gC. rewrite Cpw_mod. f_equal; unfold Copp; cbn [Re]; ring. }
  rewrite Hm.
  pose proof (HN (S n) ltac:(lia)) as H.
  unfold R_dist in H. rewrite Rminus_0_r in H.
  assert (Hpos : 0 < Rpower (INR (S (S n))) (- Re s))
    by (unfold Rpower; apply exp_pos).
  rewrite Rabs_right in H by lra. exact H.
Qed.

(* ---- the trapezoid series and its sum ---- *)

Definition Hsum (s : C) (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) : C :=
  Cminus (proj1_sig (gtermC_cv s H0 H1)) (RtoC (/ 2)).

Theorem htermC_cv : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cseries_cv (htermC s) (Hsum s H0 H1).
Proof.
  intros s H0 H1.
  assert (HZ : Cseries_cv (gtermC s) (proj1_sig (gtermC_cv s H0 H1)))
    by (exact (proj2_sig (gtermC_cv s H0 H1))).
  assert (Hg : CUn_cv (fun M => gC s (INR (S (S M)))) C0)
    by (apply gC_to_0; exact H0).
  unfold Cseries_cv, CUn_cv in *. intros eps Heps.
  destruct (HZ (eps / 2) ltac:(lra)) as [N1 HN1].
  destruct (Hg (eps / 2) ltac:(lra)) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  assert (Ht := telescope s n).
  unfold Hsum.
  assert (E : Cminus (Cpsum (htermC s) n)
                (Cminus (proj1_sig (gtermC_cv s H0 H1)) (RtoC (/ 2)))
              = Cadd (Cminus (Cpsum (gtermC s) n)
                        (proj1_sig (gtermC_cv s H0 H1)))
                  (Cmul (RtoC (/ 2)) (gC s (INR (S (S n)))))).
  { rewrite Ht.
    apply Ceq; unfold Cadd, Cminus, Cmul, Copp, RtoC, C1; cbn [Re Im]; ring. }
  rewrite E.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  assert (A1 : Cmod (Cminus (Cpsum (gtermC s) n)
                       (proj1_sig (gtermC_cv s H0 H1))) < eps / 2)
    by (apply HN1; lia).
  assert (A2 : Cmod (Cmul (RtoC (/ 2)) (gC s (INR (S (S n))))) < eps / 4).
  { rewrite Cmod_mul, Cmod_RtoC, Rabs_right by lra.
    assert (B2 : Cmod (Cminus (gC s (INR (S (S n)))) C0) < eps / 2)
      by (apply HN2; lia).
    replace (Cminus (gC s (INR (S (S n)))) C0) with (gC s (INR (S (S n))))
      in B2 by ring.
    lra. }
  lra.
Qed.

Theorem zetaC_trapezoid : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  zetaC s H0 H1
  = Cadd (Cadd (Cinv (Cminus s C1)) (RtoC (/ 2))) (Hsum s H0 H1).
Proof.
  intros s H0 H1. unfold zetaC, Hsum. ring.
Qed.

(* ================================================================= *)
(*  The truncation error.                                             *)
(*                                                                    *)
(*  Splitting  x^{-Re s-2} = x^{-Re s} . x^{-2}  lets the first factor *)
(*  be frozen at its value on the left endpoint (it is antitone) and   *)
(*  the second telescope by 1/m^2 <= 1/(m-1) - 1/m.  So the tail after *)
(*  M terms is at most  Kh(s) . (M+1)^{-Re s} / (M+1).                *)
(* ================================================================= *)

Definition Kh (s : C) : R := / 6 * (Cmod s * Cmod (Cadd s C1)).

Definition hmaj (s : C) (n : nat) : R :=
  Kh s * Rpower (INR (S n)) (- Re s - 2).

Lemma Kh_nonneg : forall s, 0 <= Kh s.
Proof.
  intro s. unfold Kh. apply Rmult_le_pos; [ lra | ].
  apply Rmult_le_pos; apply Cmod_nonneg.
Qed.

Lemma Rpower_pos' : forall x y, 0 < Rpower x y.
Proof. intros x y. unfold Rpower. apply exp_pos. Qed.

Lemma hmaj_nonneg : forall s n, 0 <= hmaj s n.
Proof.
  intros s n. unfold hmaj. apply Rmult_le_pos;
    [ apply Kh_nonneg | left; apply Rpower_pos' ].
Qed.

Lemma hmaj_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (htermC s n) <= hmaj s n.
Proof.
  intros s n Hs Hs1. pose proof (Cmod_htermC_bound s n Hs Hs1) as H.
  unfold hmaj, Kh. lra.
Qed.

Lemma Rpower_m2 : forall x, 0 < x -> Rpower x (- 2) = / (x * x).
Proof.
  intros x Hx.
  replace (-2) with (- (INR 2)) by (simpl; ring).
  rewrite Rpower_Ropp, Rpower_pow by exact Hx.
  simpl. f_equal. ring.
Qed.

Lemma cv_le_ub' : forall u l M, Un_cv u l -> (forall n, u n <= M) -> l <= M.
Proof.
  intros u l M Hcv Hub. destruct (Rle_or_lt l M) as [Hle | Hlt]; [ exact Hle | ].
  exfalso. destruct (Hcv ((l - M) / 2) ltac:(lra)) as [N HN].
  specialize (HN N (Nat.le_refl N)). specialize (Hub N).
  unfold R_dist in HN. apply Rabs_def2 in HN. lra.
Qed.

Lemma sum_hmaj_mono : forall s n m, (n <= m)%nat ->
  sum_f_R0 (hmaj s) n <= sum_f_R0 (hmaj s) m.
Proof.
  intros s n m H. induction H as [| m H IH]; [ lra | ].
  rewrite tech5. pose proof (hmaj_nonneg s (S m)). lra.
Qed.

Lemma hmaj_step : forall s M J, 0 <= Re s ->
  sum_f_R0 (hmaj s) (M + J) - sum_f_R0 (hmaj s) M
  <= Kh s * Rpower (INR (S M)) (- Re s)
     * (/ INR (S M) - / INR (S (M + J))).
Proof.
  intros s M J Hs.
  assert (HK : 0 <= Kh s) by apply Kh_nonneg.
  set (R0 := Rpower (INR (S M)) (- Re s)).
  assert (HR0 : 0 < R0) by (unfold R0; apply Rpower_pos').
  induction J as [| J IH].
  - rewrite Nat.add_0_r. lra.
  - assert (Hm1 : 1 <= INR (S (M + J)))
      by (rewrite <- INR_1; apply le_INR; lia).
    set (m := INR (S (M + J))) in *.
    assert (Hm0 : 0 < m) by lra.
    assert (Hsucc : INR (S (S (M + J))) = m + 1)
      by (rewrite S_INR; reflexivity).
    assert (Hidx : (M + S J)%nat = S (M + J)) by lia.
    rewrite Hidx, tech5.
    (* the new term *)
    assert (Hterm : hmaj s (S (M + J)) <= Kh s * R0 * / ((m + 1) * (m + 1))).
    { unfold hmaj.
      assert (Hx : INR (S (S (M + J))) = m + 1) by (rewrite S_INR; reflexivity).
      rewrite Hx.
      replace (- Re s - 2) with (- Re s + - 2) by ring.
      rewrite Rpower_plus, Rpower_m2 by lra.
      assert (HA : Rpower (m + 1) (- Re s) <= R0).
      { unfold R0. replace (- Re s) with (- (Re s)) by ring.
        apply Rpow_negexp_anti; [ | | exact Hs ].
        - assert (0 < INR (S M)) by (apply lt_0_INR; lia). lra.
        - assert (Hle : INR (S M) <= m)
            by (unfold m; apply le_INR; lia). lra. }
      assert (HB : 0 < / ((m + 1) * (m + 1)))
        by (apply Rinv_0_lt_compat; nra).
      replace (Kh s * R0 * / ((m + 1) * (m + 1)))
        with (Kh s * (R0 * / ((m + 1) * (m + 1)))) by ring.
      apply Rmult_le_compat_l; [ exact HK | ].
      apply Rmult_le_compat_r; [ lra | exact HA ]. }
    (* the telescoping increment *)
    assert (Htel : Kh s * R0 * / ((m + 1) * (m + 1))
                   <= Kh s * R0 * (/ m - / (m + 1))).
    { assert (HE : / m - / (m + 1) = / (m * (m + 1)))
        by (field; split; apply Rgt_not_eq; lra).
      rewrite HE.
      assert (HI : / ((m + 1) * (m + 1)) <= / (m * (m + 1)))
        by (apply Rinv_le_contravar; nra).
      apply Rmult_le_compat_l; [ apply Rmult_le_pos; lra | exact HI ]. }
    rewrite Hsucc. lra.
Qed.

Lemma sum_scal_hmaj : forall (f : nat -> R) c N,
  sum_f_R0 (fun k => c * f k) N = c * sum_f_R0 f N.
Proof. intros f c N. induction N; simpl; [ ring | rewrite IHN; ring ]. Qed.

Theorem htermC_tail : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) M,
  Cmod (Cminus (Hsum s H0 H1) (Cpsum (htermC s) M))
  <= Kh s * Rpower (INR (S M)) (- Re s) / INR (S M).
Proof.
  intros s H0 H1 M.
  assert (HK : 0 <= Kh s) by apply Kh_nonneg.
  assert (HM0 : 0 < INR (S M)) by (apply lt_0_INR; lia).
  set (R0 := Rpower (INR (S M)) (- Re s)).
  assert (HR0 : 0 < R0) by (unfold R0; apply Rpower_pos').
  set (B := Kh s * R0 / INR (S M)).
  assert (HB : 0 <= B).
  { unfold B. unfold Rdiv. apply Rmult_le_pos;
      [ apply Rmult_le_pos; lra | left; apply Rinv_0_lt_compat; exact HM0 ]. }
  destruct (pseries_cv (Re s + 2) ltac:(lra)) as [T HT].
  assert (HTb : Un_cv (sum_f_R0 (hmaj s)) (Kh s * T)).
  { assert (E : forall N, sum_f_R0 (hmaj s) N
                  = Kh s * sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 2))) N).
    { intro N. rewrite <- sum_scal_hmaj. apply sum_eq. intros k _.
      unfold hmaj. f_equal. f_equal. ring. }
    intros eps Heps. destruct (HT eps Heps) as [N HN].
    (* transport through the scaling *)
    assert (HT' : Un_cv (fun N => Kh s
                    * sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 2))) N)
                    (Kh s * T)).
    { pose proof (CV_mult (fun _ => Kh s)
                    (sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 2))))
                    (Kh s) T) as H.
      apply H; [ | exact HT ].
      intros e He. exists 0%nat. intros p _. unfold R_dist.
      rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. exact He. }
    destruct (HT' eps Heps) as [N2 HN2]. exists N2. intros n Hn.
    rewrite E. apply HN2; exact Hn. }
  pose proof (cseries_remainder_bound (htermC s) (hmaj s) (Hsum s H0 H1)
                (Kh s * T) (htermC_cv s H0 H1)
                (fun n => hmaj_bound s n (Rlt_le _ _ H0) H1) HTb M) as Hrem.
  (* the majorant remainder is at most B *)
  assert (Hall : forall n, sum_f_R0 (hmaj s) n <= sum_f_R0 (hmaj s) M + B).
  { intro n. destruct (Nat.le_gt_cases n M) as [Hc | Hc].
    - pose proof (sum_hmaj_mono s n M Hc). lra.
    - assert (Hj : n = (M + (n - M))%nat) by lia.
      rewrite Hj.
      pose proof (hmaj_step s M (n - M) (Rlt_le _ _ H0)) as Hs.
      fold R0 in Hs.
      assert (Hpos : 0 < INR (S (M + (n - M)))) by (apply lt_0_INR; lia).
      assert (Hinv : 0 <= / INR (S (M + (n - M))))
        by (left; apply Rinv_0_lt_compat; exact Hpos).
      assert (Hle : Kh s * R0 * (/ INR (S M) - / INR (S (M + (n - M)))) <= B).
      { unfold B, Rdiv.
        apply Rmult_le_compat_l; [ apply Rmult_le_pos; lra | lra ]. }
      lra. }
  assert (Hlim : Kh s * T <= sum_f_R0 (hmaj s) M + B)
    by (apply (cv_le_ub' (sum_f_R0 (hmaj s))); assumption).
  unfold B in *. lra.
Qed.
