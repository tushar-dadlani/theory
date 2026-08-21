(* ================================================================= *)
(*  ZetaLogBound.v  --  |zeta| = O(ln t) in the strip.                 *)
(*                                                                    *)
(*    zeta_log_bound : 1 <= Re s <= 2,  2 <= |Im s|  ==>               *)
(*        Cmod (zF s)  <=  ln |Im s| + 10                              *)
(*                                                                    *)
(*  ZetaStripBound gave |zeta(s)| <= 1/|s-1| + 2|s|(1+1/sigma), which  *)
(*  is O(|s|) -- polynomial, and enough to be USED, but far from the   *)
(*  truth.  The logarithmic bound is what turns the zero-free region   *)
(*  from a vacuous sliver (width ~ t^-5) into one of PNT-usable shape  *)
(*  (width ~ ln^-9 t).  At t = 10^4 the old bound is 40000 and this    *)
(*  one is 19.2.                                                      *)
(*                                                                    *)
(*  No new representation of zeta is needed: this is a RE-ESTIMATION   *)
(*  of the same first-order Euler-Maclaurin series CZeta already uses, *)
(*  split at N ~ |t|.                                                 *)
(*                                                                    *)
(*    head (n < N)   each term bounded by its own three pieces,        *)
(*                   |g(n+1)| + |G(n+2)| + |G(n+1)| <= 1/(n+1) + 2/|t|,*)
(*                   summing to ln N + 1 + 2N/|t| = O(ln t).           *)
(*                   The 2/|t| comes from |1-s| >= |Im s|: it is the   *)
(*                   HEIGHT, not the abscissa, that tames G.           *)
(*                                                                    *)
(*    tail (n >= N)  the existing CZetaTerm.Cmod_gtermC_bound, which   *)
(*                   is 2|s|(n+1)^{-sigma-1} <= 2|s|/(n+1)^2, summing  *)
(*                   by telescoping to 2|s|/N = O(1) at N ~ |t|.       *)
(*                                                                    *)
(*  The two estimates cross over exactly at n ~ |t|, which is why the  *)
(*  split is placed there and why neither alone suffices: the head     *)
(*  bound is useless for large n and the tail bound carries a factor   *)
(*  |s| that only the 1/N can absorb.  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CexpFull CSeries HarmonicSum
        CZetaTerm CZeta ZetaFn ZetaStripBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  Rpower helpers                                                 *)
(* ----------------------------------------------------------------- *)
Lemma ln_nonneg : forall x, 1 <= x -> 0 <= ln x.
Proof.
  intros x Hx. destruct (Rle_lt_or_eq_dec 1 x Hx) as [H | H].
  - rewrite <- ln_1. left. apply ln_increasing; lra.
  - subst x. rewrite ln_1. lra.
Qed.

Lemma Rpower_exp_le : forall x a b, 1 <= x -> a <= b -> Rpower x a <= Rpower x b.
Proof.
  intros x a b Hx Hab. unfold Rpower. apply exp_le.
  pose proof (ln_nonneg x Hx). nra.
Qed.

Lemma Rpower_m1 : forall x, 0 < x -> Rpower x (-1) = / x.
Proof.
  intros x Hx. unfold Rpower.
  replace (-1 * ln x) with (- ln x) by ring.
  rewrite exp_Ropp, exp_ln by exact Hx. reflexivity.
Qed.

Lemma Rpower_0' : forall x, Rpower x 0 = 1.
Proof. intro x. unfold Rpower. rewrite Rmult_0_l. apply exp_0. Qed.

Lemma Rpower_m2 : forall x, 0 < x -> Rpower x (-2) = / (x * x).
Proof.
  intros x Hx. unfold Rpower.
  replace (-2 * ln x) with (- (ln x + ln x)) by ring.
  rewrite exp_Ropp, exp_plus, exp_ln by exact Hx. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Cmod helpers                                                   *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_sub_le : forall a b, Cmod (Cminus a b) <= Cmod a + Cmod b.
Proof.
  intros a b.
  assert (E : Cminus a b = Cadd a (Copp b))
    by (apply Ceq; unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
  rewrite E. eapply Rle_trans; [ apply Cmod_triangle | ].
  assert (E2 : Cmod (Copp b) = Cmod b)
    by (unfold Cmod, Cnorm2, Copp; cbn [Re Im]; f_equal; ring).
  lra.
Qed.

Lemma Im_le_Cmod : forall w, Rabs (Im w) <= Cmod w.
Proof.
  intro w. unfold Cmod, Cnorm2. rewrite <- (sqrt_Rsqr_abs (Im w)).
  apply sqrt_le_1_alt. unfold Rsqr. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  a harmonic bound in sum_f_R0 form                              *)
(* ----------------------------------------------------------------- *)
Lemma harm_sum_le : forall m,
  sum_f_R0 (fun n => / INR (S n)) m <= ln (INR (S m)) + 1.
Proof.
  induction m as [| m IH].
  - cbn [sum_f_R0]. rewrite INR_1, ln_1, Rinv_1. lra.
  - rewrite tech5.
    pose proof (harm_step (S m) ltac:(lia)) as [Hlo _].
    lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the telescoping tail                                           *)
(* ----------------------------------------------------------------- *)
Lemma tail_tele : forall N K, (1 <= N)%nat ->
  sum_f_R0 (fun i => / (INR (S (N + i)) * INR (S (N + i)))) K <= / INR N.
Proof.
  intros N K HN.
  assert (Hkey : forall i, / (INR (S (N + i)) * INR (S (N + i)))
                        <= / INR (N + i) - / INR (S (N + i))).
  { intro i.
    assert (H1 : 0 < INR (N + i)) by (apply lt_0_INR; lia).
    assert (H2 : INR (S (N + i)) = INR (N + i) + 1) by (rewrite S_INR; ring).
    rewrite H2.
    assert (H3 : / INR (N + i) - / (INR (N + i) + 1)
               = / (INR (N + i) * (INR (N + i) + 1))) by (field; lra).
    rewrite H3. apply Rinv_le_contravar; nra. }
  assert (Htel : forall K', sum_f_R0 (fun i => / INR (N + i) - / INR (S (N + i))) K'
                          = / INR N - / INR (S (N + K'))).
  { induction K' as [| K' IHK].
    - cbn [sum_f_R0]. rewrite Nat.add_0_r. reflexivity.
    - rewrite tech5, IHK.
      assert (E : (S (N + K') = N + S K')%nat) by lia. rewrite E. ring. }
  eapply Rle_trans; [ apply sum_Rle; intros n _; apply Hkey | ].
  rewrite Htel.
  assert (H4 : 0 < / INR (S (N + K)))
    by (apply Rinv_0_lt_compat; apply lt_0_INR; lia).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the HEAD per-term bound                                        *)
(* ----------------------------------------------------------------- *)
(*  Bound each Euler-Maclaurin summand by its own three pieces.  The   *)
(*  2/|Im s| is the point: |1 - s| >= |Im s|, so it is the HEIGHT that *)
(*  tames the antiderivative term G, not the abscissa.                 *)
Lemma head_term : forall s n, 1 <= Re s -> 2 <= Rabs (Im s) ->
  Cmod (gtermC s n) <= / INR (S n) + 2 / Rabs (Im s).
Proof.
  intros s n Hs Ht.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hy : 1 <= INR (S (S n))) by (rewrite S_INR; pose proof (pos_INR (S n)); lra).
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hlow : Rabs (Im s) <= Cmod (Cminus C1 s)).
  { eapply Rle_trans; [ | apply (Im_le_Cmod (Cminus C1 s)) ].
    assert (E : Im (Cminus C1 s) = - Im s)
      by (unfold Cminus, C1; cbn [Re Im]; ring).
    rewrite E, Rabs_Ropp. apply Rle_refl. }
  assert (HRe : Re (Cminus C1 s) = 1 - Re s)
    by (unfold Cminus, C1; cbn [Re Im]; ring).
  assert (Hg : Cmod (gC s (INR (S n))) <= / INR (S n)).
  { unfold gC. rewrite Cpw_mod.
    assert (E : Re (Copp s) = - Re s) by (unfold Copp; cbn [Re]; ring).
    rewrite E, <- (Rpower_m1 (INR (S n)) ltac:(lra)).
    apply Rpower_exp_le; lra. }
  assert (HG : forall x, 1 <= x -> Cmod (GC s x) <= / Rabs (Im s)).
  { intros x Hx1. unfold GC. rewrite Cmod_mul, (Cmod_Cinv _ Hne), Cpw_mod, HRe.
    assert (H1 : Rpower x (1 - Re s) <= 1).
    { eapply Rle_trans; [ apply (Rpower_exp_le x (1 - Re s) 0); lra | ].
      rewrite Rpower_0'. lra. }
    assert (H2 : 0 < Rpower x (1 - Re s)) by (unfold Rpower; apply exp_pos).
    assert (H3 : 0 < Rabs (Im s)) by lra.
    assert (H4 : / Cmod (Cminus C1 s) <= / Rabs (Im s))
      by (apply Rinv_le_contravar; lra).
    assert (H5 : 0 < / Cmod (Cminus C1 s)) by (apply Rinv_0_lt_compat; lra).
    assert (Hstep : Rpower x (1 - Re s) * / Cmod (Cminus C1 s)
                 <= 1 * / Cmod (Cminus C1 s))
      by (apply Rmult_le_compat_r; lra).
    lra. }
  unfold gtermC.
  eapply Rle_trans; [ apply Cmod_sub_le | ].
  assert (Hsub : Cmod (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n))))
              <= / Rabs (Im s) + / Rabs (Im s)).
  { eapply Rle_trans; [ apply Cmod_sub_le | ].
    pose proof (HG _ Hy); pose proof (HG _ Hx); lra. }
  assert (Hd : 2 / Rabs (Im s) = / Rabs (Im s) + / Rabs (Im s)) by (field; lra).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  the TAIL per-term bound                                        *)
(* ----------------------------------------------------------------- *)
Lemma tail_term : forall s n, 1 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (gtermC s n) <= 2 * Cmod s * / (INR (S n) * INR (S n)).
Proof.
  intros s n Hs Hne.
  assert (Hx : 1 <= INR (S n)) by (rewrite S_INR; pose proof (pos_INR n); lra).
  pose proof (Cmod_gtermC_bound s n ltac:(lra) Hne) as HB.
  assert (Hp : Rpower (INR (S n)) (- Re s - 1) <= / (INR (S n) * INR (S n))).
  { rewrite <- (Rpower_m2 (INR (S n)) ltac:(lra)).
    apply Rpower_exp_le; lra. }
  pose proof (Cmod_nonneg s) as Hs0.
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  G.  the partial sums, split at N ~ |Im s|                          *)
(* ----------------------------------------------------------------- *)
Lemma ln_le' : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [H | H].
  - left. apply ln_increasing; assumption.
  - subst y. lra.
Qed.

Lemma ln_shift : forall t, 2 <= t -> ln (t + 1) <= ln t + 1.
Proof.
  intros t Ht.
  assert (H15 : t + 1 <= 3 / 2 * t) by lra.
  eapply Rle_trans; [ apply ln_le'; [ lra | exact H15 ] | ].
  rewrite ln_mult by lra.
  assert (Hl : ln (3 / 2) <= 1).
  { pose proof (exp_ineq1_le 1) as H.
    rewrite <- (ln_exp 1). apply ln_le'; lra. }
  lra.
Qed.

(*  The head estimate, used in both branches: the first m+1 terms.     *)
Lemma head_sum : forall s m, 1 <= Re s -> 2 <= Rabs (Im s) ->
  sum_f_R0 (fun n => Cmod (gtermC s n)) m
  <= ln (INR (S m)) + 1 + 2 / Rabs (Im s) * INR (S m).
Proof.
  intros s m Hs Ht.
  eapply Rle_trans.
  - apply sum_Rle. intros n _. apply head_term; assumption.
  - rewrite sum_plus, sum_cte.
    pose proof (harm_sum_le m). lra.
Qed.

Lemma psum_bound_N : forall s N M, 1 <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  Cminus C1 s <> C0 -> (1 <= N)%nat ->
  Rabs (Im s) <= INR N -> INR N <= Rabs (Im s) + 1 ->
  sum_f_R0 (fun n => Cmod (gtermC s n)) M <= ln (Rabs (Im s)) + 9.
Proof.
  intros s N M Hs1 Hs2 Ht Hne HN Nlo Nhi.
  set (T := Rabs (Im s)) in *.
  assert (HT0 : 0 < T) by lra.
  assert (HNpos : 0 < INR N) by lra.
  (* the head estimate at any cut m with INR (S m) <= INR N *)
  assert (Hhead : forall m, INR (S m) <= INR N ->
            sum_f_R0 (fun n => Cmod (gtermC s n)) m <= ln T + 5).
  { intros m Hm.
    pose proof (head_sum s m Hs1 Ht) as HS. fold T in HS.
    assert (HSm0 : 0 < INR (S m)) by (apply lt_0_INR; lia).
    assert (Hl1 : ln (INR (S m)) <= ln (T + 1))
      by (apply ln_le'; lra).
    pose proof (ln_shift T Ht) as Hl2.
    assert (Hlin : 2 / T * INR (S m) <= 3).
    { assert (H1 : 2 / T * INR (S m) <= 2 / T * (T + 1))
        by (apply Rmult_le_compat_l; [ apply Rle_mult_inv_pos; lra | lra ]).
      assert (H2 : 2 / T * (T + 1) = 2 + 2 / T) by (field; lra).
      assert (H3 : 2 / T <= 1) by (apply Rmult_le_reg_r with T; [ lra | ];
                                   unfold Rdiv; rewrite Rmult_assoc, Rinv_l; lra).
      lra. }
    lra. }
  (* |s| <= 2 + T *)
  assert (Hsmod : Cmod s <= 2 + T).
  { pose proof (Cmod_le_sum s) as H.
    rewrite (Rabs_right (Re s) ltac:(lra)) in H. unfold T. lra. }
  assert (Hs0 : 0 <= Cmod s) by apply Cmod_nonneg.
  destruct (Nat.le_gt_cases N M) as [Hge | Hlt].
  - (* M >= N : split *)
    destruct N as [| Nm1]; [ exfalso; lia | ].
    assert (Hlt' : (Nm1 < M)%nat) by lia.
    rewrite (tech2 (fun n => Cmod (gtermC s n)) Nm1 M Hlt').
    assert (Hh : sum_f_R0 (fun n => Cmod (gtermC s n)) Nm1 <= ln T + 5)
      by (apply Hhead; lra).
    assert (Htail : sum_f_R0 (fun i => Cmod (gtermC s (S Nm1 + i))) (M - S Nm1)
                 <= 2 * Cmod s * / INR (S Nm1)).
    { eapply Rle_trans.
      - apply sum_Rle. intros i _. apply tail_term; assumption.
      - set (K := (M - S Nm1)%nat).
        assert (E : sum_f_R0 (fun i => 2 * Cmod s
                      * / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))) K
                  = 2 * Cmod s * sum_f_R0 (fun i =>
                      / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i)))) K).
        { rewrite (scal_sum (fun i => / (INR (S (S Nm1 + i)) * INR (S (S Nm1 + i))))
                     K (2 * Cmod s)).
          apply sum_eq; intros i _; ring. }
        rewrite E.
        pose proof (tail_tele (S Nm1) K ltac:(lia)) as HTT.
        apply Rmult_le_compat_l; [ lra | exact HTT ]. }
    assert (Hnum : 2 * Cmod s * / INR (S Nm1) <= 4).
    { assert (H1 : 2 * Cmod s <= 2 * (2 + T)) by lra.
      assert (H2 : / INR (S Nm1) <= / T)
        by (apply Rinv_le_contravar; lra).
      assert (H3 : 0 < / INR (S Nm1)) by (apply Rinv_0_lt_compat; lra).
      assert (H4 : 2 * Cmod s * / INR (S Nm1) <= 2 * (2 + T) * / T)
        by (apply Rmult_le_compat; lra).
      assert (H5 : 2 * (2 + T) * / T = 2 + 4 / T) by (field; lra).
      assert (H6 : 4 / T <= 2) by (apply Rmult_le_reg_r with T; [ lra | ];
                                   unfold Rdiv; rewrite Rmult_assoc, Rinv_l; lra).
      lra. }
    lra.
  - (* M < N : all head *)
    apply Rle_trans with (ln T + 5); [ | lra ].
    apply Hhead. apply le_INR. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  H.  THE LOGARITHMIC BOUND                                          *)
(* ----------------------------------------------------------------- *)
Theorem zeta_log_bound : forall s, 1 <= Re s -> Re s <= 2 -> 2 <= Rabs (Im s) ->
  Cmod (zF s) <= ln (Rabs (Im s)) + 10.
Proof.
  intros s Hs1 Hs2 Ht.
  assert (H0 : 0 < Re s) by lra.
  assert (HIm : forall w, Im w = Im s -> Rabs (Im s) <= Cmod w).
  { intros w Hw. eapply Rle_trans; [ | apply (Im_le_Cmod w) ].
    rewrite Hw. apply Rle_refl. }
  assert (Hne : Cminus C1 s <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  assert (Hne1 : Cminus s C1 <> C0).
  { intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Im s = 0) by lra. rewrite H, Rabs_R0 in Ht. lra. }
  (* the cut point N, from the archimedean property *)
  set (z := up (Rabs (Im s))).
  destruct (archimed (Rabs (Im s))) as [Hup1 Hup2]. fold z in Hup1, Hup2.
  assert (Hz0 : (0 <= z)%Z) by (apply le_IZR; simpl; lra).
  set (N := Z.to_nat z).
  assert (HNz : INR N = IZR z)
    by (unfold N; rewrite INR_IZR_INZ, Z2Nat.id by exact Hz0; reflexivity).
  assert (HN1 : (1 <= N)%nat).
  { apply INR_le. rewrite HNz, INR_1. lra. }
  assert (Nlo : Rabs (Im s) <= INR N) by (rewrite HNz; lra).
  assert (Nhi : INR N <= Rabs (Im s) + 1) by (rewrite HNz; lra).
  (* the Euler-Maclaurin sum is bounded by ln T + 9 *)
  assert (HZ : Cmod (proj1_sig (gtermC_cv s H0 Hne)) <= ln (Rabs (Im s)) + 9).
  { pose proof (proj2_sig (gtermC_cv s H0 Hne)) as HC.
    eapply Rle_cv_lim.
    - intro M. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
      exact (psum_bound_N s N M Hs1 Hs2 Ht Hne HN1 Nlo Nhi).
    - apply CUn_cv_Cmod. exact HC.
    - apply Un_cv_const. }
  (* the pole term contributes at most 1/2 *)
  assert (Hpole : / Cmod (Cminus s C1) <= / 2).
  { assert (Hlow : Rabs (Im s) <= Cmod (Cminus s C1)).
    { apply HIm. unfold Cminus, C1; cbn [Re Im]; ring. }
    apply Rinv_le_contravar; lra. }
  rewrite (zF_eq s H0 Hne). unfold zetaC.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite (Cmod_Cinv _ Hne1).
  lra.
Qed.

Print Assumptions head_term.
Print Assumptions tail_term.
Print Assumptions psum_bound_N.
Print Assumptions zeta_log_bound.
