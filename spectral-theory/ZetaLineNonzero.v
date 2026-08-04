(* ================================================================= *)
(*  ZetaLineNonzero.v  —  the PNT zero-free line: zeta(1+it) != 0.     *)
(*                                                                    *)
(*  If zeta(1+i t0) = 0 (t0 != 0), take sigma_n = 1 + 1/(n+1) -> 1+.   *)
(*  The Mertens 3-4-1 inequality (ThreeFourOne.tfo_zeta) gives          *)
(*     1 <= |zeta(sigma)|^3 |zeta(sigma+i t0)|^4 |zeta(sigma+2 i t0)|.  *)
(*  But near sigma = 1:                                                *)
(*   - |zeta(sigma)|      <= 2/(sigma-1)      (the simple pole),        *)
(*   - |zeta(sigma+i t0)| <= C (sigma-1)      (holomorphy AT the zero), *)
(*   - |zeta(sigma+2i t0)|<= M                (holomorphy, bounded),    *)
(*  so 1 <= 8 C^4 M (sigma-1) -> 0, a contradiction.  Hence            *)
(*     zetaC (mkC 1 t) != 0   for every t != 0.  Axiom-clean.          *)
(*                                                                    *)
(*  This is the boundary (Re s = 1) nonvanishing, equivalent to the    *)
(*  Prime Number Theorem, extending zetaC_nonzero from Re s > 1.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CZetaTerm CZeta CZetaHolo
        ZetaContinuation Ell2ZetaCont ThreeFourOne.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  zetaC is proof-irrelevant / a congruence in its point         *)
(* ================================================================= *)

Lemma zetaC_congr : forall s s' H0 H1 H0' H1',
  s = s' -> zetaC s H0 H1 = zetaC s' H0' H1'.
Proof.
  intros s s' H0 H1 H0' H1' E; unfold zetaC.
  assert (Es : Cminus s C1 = Cminus s' C1) by (rewrite E; reflexivity).
  assert (Ef : gtermC s = gtermC s') by (rewrite E; reflexivity).
  assert (Eg : proj1_sig (gtermC_cv s H0 H1) = proj1_sig (gtermC_cv s' H0' H1')).
  { apply (CUn_cv_unique (Cpsum (gtermC s))).
    - exact (proj2_sig (gtermC_cv s H0 H1)).
    - rewrite Ef; exact (proj2_sig (gtermC_cv s' H0' H1')). }
  rewrite Es, Eg; reflexivity.
Qed.

(* ================================================================= *)
(*  1.  the regular part of zeta_cont is bounded by 1                  *)
(* ================================================================= *)

Lemma gterm_partial_bound : forall s N, 0 < s -> s <> 1 ->
  0 <= sum_f_R0 (gterm s) N <= 1.
Proof.
  intros s N Hs0 Hs1; split.
  - apply cond_pos_sum; intro k; destruct (g_bound s k Hs0 Hs1) as [Hge _]; exact Hge.
  - apply Rle_trans with
      (sum_f_R0 (fun n => Rpower (INR (S n)) (- s) - Rpower (INR (S (S n))) (- s)) N).
    + apply sum_Rle; intros k Hk; destruct (g_bound s k Hs0 Hs1) as [_ Hle]; exact Hle.
    + rewrite (sum_telescope_dec (fun n => Rpower (INR (S n)) (- s))).
      rewrite INR_1, Rpower_base1.
      assert (0 <= Rpower (INR (S (S N))) (- s)) by (left; unfold Rpower; apply exp_pos); lra.
Qed.

Lemma reg_bound : forall s (Hs0 : 0 < s) (Hs1 : s <> 1),
  0 <= proj1_sig (gterm_cv s Hs0 Hs1) <= 1.
Proof.
  intros s Hs0 Hs1; pose proof (proj2_sig (gterm_cv s Hs0 Hs1)) as Hcv; split.
  - apply Rle_cv_lim with (Un := fun _ : nat => 0) (Vn := sum_f_R0 (gterm s)).
    + intro N; apply (proj1 (gterm_partial_bound s N Hs0 Hs1)).
    + apply Un_cv_const.
    + exact Hcv.
  - apply Rle_cv_lim with (Un := sum_f_R0 (gterm s)) (Vn := fun _ : nat => 1).
    + intro N; apply (proj2 (gterm_partial_bound s N Hs0 Hs1)).
    + exact Hcv.
    + apply Un_cv_const.
Qed.

(* the simple-pole bound: zeta_cont s <= 2/(s-1) on (1,2] *)
Lemma zeta_cont_pole : forall s (Hs0 : 0 < s) (Hs1 : s <> 1),
  1 < s -> s <= 2 -> zeta_cont s Hs0 Hs1 <= 2 / (s - 1).
Proof.
  intros s Hs0 Hs1 Hlt Hle; unfold zeta_cont.
  pose proof (reg_bound s Hs0 Hs1) as [Hr0 Hr1].
  set (r := proj1_sig (gterm_cv s Hs0 Hs1)) in *.
  assert (Hpos : 0 < s - 1) by lra.
  assert (Hinv1 : 1 <= / (s - 1))
    by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  replace (2 / (s - 1)) with (/ (s - 1) + / (s - 1)) by (field; lra).
  lra.
Qed.

(* zeta on the real axis: |zetaC (mkC s 0)| = zeta_cont s *)
Lemma real_zeta_mod : forall s (Hs0 : 0 < s) (Hs1 : s <> 1)
  (H0 : 0 < Re (mkC s 0)) (H1 : Cminus C1 (mkC s 0) <> C0),
  1 < s -> Cmod (zetaC (mkC s 0) H0 H1) = zeta_cont s Hs0 Hs1.
Proof.
  intros s Hs0 Hs1 H0 H1 Hs.
  assert (Es : mkC s 0 = RtoC s) by (unfold RtoC; reflexivity).
  rewrite (zetaC_congr (mkC s 0) (RtoC s) H0 H1 H0 H1 Es).
  rewrite (zetaC_agree s Hs0 Hs1 H0 H1), Cmod_RtoC, Rabs_right; [ reflexivity | ].
  unfold zeta_cont; pose proof (reg_bound s Hs0 Hs1) as [Hr0 _].
  set (r := proj1_sig (gterm_cv s Hs0 Hs1)) in *.
  assert (0 < / (s - 1)) by (apply Rinv_0_lt_compat; lra); lra.
Qed.

(* ================================================================= *)
(*  2.  THE PNT ZERO-FREE LINE                                         *)
(* ================================================================= *)

Theorem zetaC_line_nonzero : forall t, t <> 0 ->
  forall (H0 : 0 < Re (mkC 1 t)) (H1 : Cminus C1 (mkC 1 t) <> C0),
    zetaC (mkC 1 t) H0 H1 <> C0.
Proof.
  intros t Ht H0 H1 Hz.
  (* holomorphy at the zero z1 = 1 + i t *)
  destruct (zetaC_holo (mkC 1 t) H0 H1) as [D1 HD1].
  destruct (HD1 1 Rlt_0_1) as [del1 [Hdel1 Hb1]].
  (* holomorphy at z2 = 1 + 2 i t *)
  assert (Hz20 : 0 < Re (mkC 1 (2 * t))) by (cbn [Re]; lra).
  assert (Hz21 : Cminus C1 (mkC 1 (2 * t)) <> C0).
  { intro He; apply Ht.
    assert (Im (Cminus C1 (mkC 1 (2 * t))) = Im C0) by (rewrite He; reflexivity).
    unfold Cminus, C1, C0 in H; cbn [Im] in H; lra. }
  destruct (zetaC_holo (mkC 1 (2 * t)) Hz20 Hz21) as [D2 HD2].
  destruct (HD2 1 Rlt_0_1) as [del2 [Hdel2 Hb2]].
  (* the target constant K, and a large index N *)
  set (M2 := Cmod (zetaC (mkC 1 (2 * t)) Hz20 Hz21) + (Cmod D2 + 1)).
  assert (HM2 : 0 <= M2)
    by (unfold M2; pose proof (Cmod_nonneg (zetaC (mkC 1 (2 * t)) Hz20 Hz21));
        pose proof (Cmod_nonneg D2); lra).
  set (K := 8 * (Cmod D1 + 1) ^ 4 * M2).
  destruct (INR_unbounded (Rmax (Rmax (/ del1) (/ del2)) K)) as [N HN].
  set (n0 := INR (S N)).
  assert (Hn0 : 1 <= n0) by (unfold n0; rewrite S_INR; pose proof (pos_INR N); lra).
  assert (Hn0p : 0 < n0) by lra.
  assert (HNn : Rmax (Rmax (/ del1) (/ del2)) K < n0)
    by (unfold n0; rewrite S_INR; pose proof (pos_INR N); lra).
  assert (Hd1n : / del1 < n0)
    by (eapply Rle_lt_trans; [ eapply Rle_trans; [ apply Rmax_l | apply Rmax_l ] | exact HNn ]).
  assert (Hd2n : / del2 < n0)
    by (eapply Rle_lt_trans; [ eapply Rle_trans; [ apply Rmax_r | apply Rmax_l ] | exact HNn ]).
  assert (HKn : K < n0)
    by (eapply Rle_lt_trans; [ apply Rmax_r | exact HNn ]).
  (* sigma = 1 + 1/n0 in (1,2] *)
  set (sg := 1 + / n0).
  assert (Hinv0 : 0 < / n0) by (apply Rinv_0_lt_compat; lra).
  assert (Hinv1 : / n0 <= 1)
    by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  assert (Hsg1 : 1 < sg) by (unfold sg; lra).
  assert (Hsg2 : sg <= 2) by (unfold sg; lra).
  assert (Hsgm1 : sg - 1 = / n0) by (unfold sg; ring).
  (* proof obligations for zetaC at the three points *)
  assert (Ha0 : 0 < sg) by lra.
  assert (Ha1 : sg <> 1) by lra.
  assert (HR00 : 0 < Re (mkC sg 0)) by (cbn [Re]; lra).
  assert (Hne_re : forall im, Cminus C1 (mkC sg im) <> C0).
  { intros im He.
    assert (Re (Cminus C1 (mkC sg im)) = Re C0) by (rewrite He; reflexivity).
    unfold Cminus, C1, C0 in H; cbn [Re] in H; lra. }
  assert (HR01 : Cminus C1 (mkC sg 0) <> C0) by apply Hne_re.
  assert (HR10 : 0 < Re (mkC sg t)) by (cbn [Re]; lra).
  assert (HR11 : Cminus C1 (mkC sg t) <> C0) by apply Hne_re.
  assert (HR20 : 0 < Re (mkC sg (2 * t))) by (cbn [Re]; lra).
  assert (HR21 : Cminus C1 (mkC sg (2 * t)) <> C0) by apply Hne_re.
  (* the 3-4-1 inequality at sigma *)
  pose proof (tfo_zeta sg t Hsg1 HR00 HR01 HR10 HR11 HR20 HR21) as Htfo.
  set (A := Cmod (zetaC (mkC sg 0) HR00 HR01)) in *.
  set (Bz := Cmod (zetaC (mkC sg t) HR10 HR11)) in *.
  set (Cz := Cmod (zetaC (mkC sg (2 * t)) HR20 HR21)) in *.
  (* --- pole bound: A <= 2 n0 --- *)
  assert (HA : A <= 2 * n0).
  { unfold A; rewrite (real_zeta_mod sg Ha0 Ha1 HR00 HR01 Hsg1).
    eapply Rle_trans; [ apply (zeta_cont_pole sg Ha0 Ha1 Hsg1 Hsg2) | ].
    unfold Rdiv; rewrite Hsgm1, Rinv_inv; apply Rle_refl. }
  (* --- the shift h = (sigma-1) on the real axis --- *)
  set (h := mkC (/ n0) 0).
  assert (Hhmod : Cmod h = / n0).
  { unfold h; change (mkC (/ n0) 0) with (RtoC (/ n0)).
    rewrite Cmod_RtoC, Rabs_right; [ reflexivity | apply Rle_ge; lra ]. }
  assert (Hhd1 : Cmod h < del1).
  { rewrite Hhmod, <- (Rinv_inv del1).
    apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat;
      [ apply Rinv_0_lt_compat; lra | lra ] | exact Hd1n ]. }
  assert (Hhd2 : Cmod h < del2).
  { rewrite Hhmod, <- (Rinv_inv del2).
    apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat;
      [ apply Rinv_0_lt_compat; lra | lra ] | exact Hd2n ]. }
  (* --- zero bound: Bz <= (|D1|+1)/n0 --- *)
  assert (Kz0 : 0 < Re (Cadd (mkC 1 t) h)) by (unfold h, Cadd; cbn [Re]; lra).
  assert (Kz1 : Cminus C1 (Cadd (mkC 1 t) h) <> C0).
  { intro He.
    assert (Re (Cminus C1 (Cadd (mkC 1 t) h)) = Re C0) by (rewrite He; reflexivity).
    unfold h, Cminus, Cadd, C1, C0 in H; cbn [Re] in H; lra. }
  pose proof (Hb1 h Kz0 Kz1 Hhd1) as Hbb1.
  assert (Heq1 : mkC sg t = Cadd (mkC 1 t) h)
    by (unfold sg, h, Cadd; apply Ceq; cbn [Re Im]; ring).
  assert (HB : Bz <= (Cmod D1 + 1) * / n0).
  { unfold Bz; rewrite (zetaC_congr (mkC sg t) (Cadd (mkC 1 t) h) HR10 HR11 Kz0 Kz1 Heq1).
    rewrite <- Hhmod.
    assert (Hstep : Cmod (Cminus (zetaC (Cadd (mkC 1 t) h) Kz0 Kz1) (Cmul D1 h)) <= Cmod h).
    { replace (Cminus (zetaC (Cadd (mkC 1 t) h) Kz0 Kz1) (Cmul D1 h))
        with (Cminus (Cminus (zetaC (Cadd (mkC 1 t) h) Kz0 Kz1) (zetaC (mkC 1 t) H0 H1))
                     (Cmul D1 h)) by (rewrite Hz; ring).
      eapply Rle_trans; [ apply Hbb1 | rewrite Rmult_1_l; apply Rle_refl ]. }
    replace (zetaC (Cadd (mkC 1 t) h) Kz0 Kz1)
      with (Cadd (Cminus (zetaC (Cadd (mkC 1 t) h) Kz0 Kz1) (Cmul D1 h)) (Cmul D1 h)) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_mul; pose proof (Cmod_nonneg h); nra. }
  (* --- boundedness: Cz <= M2 --- *)
  assert (Kw0 : 0 < Re (Cadd (mkC 1 (2 * t)) h)) by (unfold h, Cadd; cbn [Re]; lra).
  assert (Kw1 : Cminus C1 (Cadd (mkC 1 (2 * t)) h) <> C0).
  { intro He.
    assert (Re (Cminus C1 (Cadd (mkC 1 (2 * t)) h)) = Re C0) by (rewrite He; reflexivity).
    unfold h, Cminus, Cadd, C1, C0 in H; cbn [Re] in H; lra. }
  pose proof (Hb2 h Kw0 Kw1 Hhd2) as Hbb2.
  assert (Heq2 : mkC sg (2 * t) = Cadd (mkC 1 (2 * t)) h)
    by (unfold sg, h, Cadd; apply Ceq; cbn [Re Im]; ring).
  assert (HC : Cz <= M2).
  { unfold Cz; rewrite (zetaC_congr (mkC sg (2 * t)) (Cadd (mkC 1 (2 * t)) h) HR20 HR21 Kw0 Kw1 Heq2).
    replace (zetaC (Cadd (mkC 1 (2 * t)) h) Kw0 Kw1)
      with (Cadd (Cadd (Cminus (Cminus (zetaC (Cadd (mkC 1 (2 * t)) h) Kw0 Kw1)
                                       (zetaC (mkC 1 (2 * t)) Hz20 Hz21)) (Cmul D2 h))
                       (zetaC (mkC 1 (2 * t)) Hz20 Hz21)) (Cmul D2 h)) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    eapply Rle_trans; [ apply Rplus_le_compat_r, Cmod_triangle | ].
    rewrite Cmod_mul.
    rewrite Rmult_1_l in Hbb2.
    rewrite Hhmod in Hbb2 |- *.
    unfold M2.
    set (Y := Cmod (Cminus (Cminus (zetaC (Cadd (mkC 1 (2 * t)) h) Kw0 Kw1)
                                   (zetaC (mkC 1 (2 * t)) Hz20 Hz21)) (Cmul D2 h))) in *.
    set (Z2 := Cmod (zetaC (mkC 1 (2 * t)) Hz20 Hz21)) in *.
    pose proof (Cmod_nonneg D2); nra. }
  (* --- assemble and contradict --- *)
  assert (HA0 : 0 <= A) by (unfold A; apply Cmod_nonneg).
  assert (HB0 : 0 <= Bz) by (unfold Bz; apply Cmod_nonneg).
  assert (HC0 : 0 <= Cz) by (unfold Cz; apply Cmod_nonneg).
  assert (H2n0 : 0 <= 2 * n0) by lra.
  assert (HD1p : 0 <= (Cmod D1 + 1) * / n0)
    by (apply Rmult_le_pos; [ pose proof (Cmod_nonneg D1); lra | lra ]).
  assert (Hprod : A ^ 3 * Bz ^ 4 * Cz
                  <= (2 * n0) ^ 3 * ((Cmod D1 + 1) * / n0) ^ 4 * M2).
  { apply Rmult_le_compat.
    - apply Rmult_le_pos; apply pow_le; assumption.
    - exact HC0.
    - apply Rmult_le_compat;
        [ apply pow_le; exact HA0 | apply pow_le; exact HB0
        | apply pow_incr; split; assumption | apply pow_incr; split; assumption ].
    - exact HC. }
  assert (Hfin : 1 <= (2 * n0) ^ 3 * ((Cmod D1 + 1) * / n0) ^ 4 * M2)
    by (eapply Rle_trans; [ exact Htfo | exact Hprod ]).
  assert (Heqf : (2 * n0) ^ 3 * ((Cmod D1 + 1) * / n0) ^ 4 * M2
                 = 8 * (Cmod D1 + 1) ^ 4 * M2 / n0) by (field; lra).
  rewrite Heqf in Hfin.
  (* 1 <= K/n0 with K < n0 and K >= 0 : contradiction *)
  assert (HK0 : 0 <= K)
    by (unfold K; apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | apply pow_le; pose proof (Cmod_nonneg D1); lra ] | exact HM2 ]).
  assert (Hinv_r : / n0 * n0 = 1) by (apply Rinv_l; lra).
  unfold K in HKn, HK0.
  unfold Rdiv in Hfin; nra.
Qed.

Print Assumptions zetaC_line_nonzero.

(* ================================================================= *)
(*  END ZetaLineNonzero.v                                             *)
(*  zetaC (1 + i t) != 0 for t != 0 — the PNT zero-free line.          *)
(* ================================================================= *)
