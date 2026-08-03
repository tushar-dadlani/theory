(* ================================================================= *)
(*  CZetaTerm2.v  —  item 3b: the (ln)^2 double-MVT bound on the        *)
(*  second s-derivative of gtermC.                                     *)
(*                                                                    *)
(*  d2gtermC s n = d2s gC(n+1) - (d2s GC(n+2) - d2s GC(n+1))            *)
(*  has the SAME double-MVT shape as gtermC (CZetaTerm.v), now driven   *)
(*  by the knot (base_deriv_d2sGC : d/dt d2s GC = d2s gC) and the       *)
(*  base derivative of the kernel (Re/Im_d2k_deriv : d/dt d2s gC = dd2k)*)
(*  with modulus Cmod_dd2k.  Two MVT_cor2 passes give                  *)
(*  |d2gtermC s n| <= 2·(2 ln(n+2) + (ln(n+2))^2|s|)·(n+1)^{-Re s-1},    *)
(*  which is summable for Re s > 0 (the (ln)^2-weighted p-series).       *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CSeries CBaseDeriv CBaseDeriv2 CZetaTerm.
Open Scope R_scope.

Lemma ln_le' : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy; destruct (Rle_lt_or_eq_dec x y Hxy) as [H|H];
    [ left; apply ln_increasing; lra | rewrite H; apply Rle_refl ].
Qed.

Definition d2gtermC (s : C) (n : nat) : C :=
  Cminus (d2k (Copp s) (INR (S n)))
         (Cminus (d2sGC s (INR (S (S n)))) (d2sGC s (INR (S n)))).

(* the per-term n-bound produced by the double MVT *)
Definition d2bound (s : C) (n : nat) : R :=
  (2 * ln (INR (S (S n))) + ln (INR (S (S n))) * ln (INR (S (S n))) * Cmod s)
  * Rpower (INR (S n)) (- Re s - 1).

Section Bound.
Variables (s : C) (n : nat).
Hypotheses (Hs0 : 0 <= Re s) (Hs1 : Cminus C1 s <> C0).

Let a := INR (S n).
Let b := INR (S (S n)).

Lemma d2_Ha : 0 < a. Proof. unfold a; apply lt_0_INR; lia. Qed.
Lemma d2_Ha1 : 1 <= a. Proof. unfold a; rewrite <- INR_1; apply le_INR; lia. Qed.
Lemma d2_Hab : a < b. Proof. unfold a, b; apply lt_INR; lia. Qed.
Lemma d2_Hba1 : b - a = 1. Proof. unfold a, b; rewrite (S_INR (S n)); ring. Qed.

(* the tail bound: |dd2k(-s) zeta| <= d2bound, for a < zeta < b *)
Lemma dd2k_tail_bound : forall zeta, a < zeta -> zeta < b ->
  Cmod (dd2k (Copp s) zeta) <= d2bound s n.
Proof.
  intros zeta Hza Hzb.
  pose proof d2_Ha as Ha. pose proof d2_Ha1 as Ha1.
  assert (Hzpos : 0 < zeta) by lra.
  assert (Hz1 : 1 <= zeta) by lra.
  assert (Hlz0 : 0 <= ln zeta) by (rewrite <- ln_1; apply ln_le'; lra).
  assert (Hlzb : ln zeta <= ln b) by (apply ln_le'; lra).
  eapply Rle_trans; [ apply Cmod_dd2k; exact Hz1 | ].
  rewrite Cmod_opp.
  replace (Re (Copp s) - 1) with (- Re s - 1) by (unfold Copp; cbn [Re]; ring).
  unfold d2bound; fold b.
  apply Rmult_le_compat.
  - apply Rplus_le_le_0_compat.
    + apply Rmult_le_pos; lra.
    + apply Rmult_le_pos; [ apply Rmult_le_pos; exact Hlz0 | apply Cmod_nonneg ].
  - apply Rlt_le; unfold Rpower; apply exp_pos.
  - apply Rplus_le_compat.
    + apply Rmult_le_compat_l; lra.
    + apply Rmult_le_compat_r; [ apply Cmod_nonneg | apply Rmult_le_compat; assumption ].
  - replace (- Re s - 1) with (- (Re s + 1)) by ring.
    apply Rpow_negexp_anti; [ exact Ha | apply Rlt_le; exact Hza | lra ].
Qed.

Lemma Re_d2gtermC_bound : Rabs (Re (d2gtermC s n)) <= d2bound s n.
Proof.
  pose proof d2_Ha as Ha. pose proof d2_Hab as Hab. pose proof d2_Hba1 as Hba1.
  destruct (MVT_cor2 (fun t => Re (d2sGC s t)) (fun t => Re (d2k (Copp s) t)) a b Hab
             (fun c Hc => base_deriv_d2sGC_Re s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Re (d2k (Copp s) t)) (fun t => Re (dd2k (Copp s) t)) a xi Hxia
             (fun c Hc => Re_d2k_deriv (Copp s) c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hval : Re (d2gtermC s n) = - (Re (dd2k (Copp s) zeta) * (xi - a))).
  { unfold d2gtermC; fold a b; rewrite !Re_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (dd2k (Copp s) zeta) * 1).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Cmod_Re_le.
    + rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r; apply dd2k_tail_bound; lra.
Qed.

Lemma Im_d2gtermC_bound : Rabs (Im (d2gtermC s n)) <= d2bound s n.
Proof.
  pose proof d2_Ha as Ha. pose proof d2_Hab as Hab. pose proof d2_Hba1 as Hba1.
  destruct (MVT_cor2 (fun t => Im (d2sGC s t)) (fun t => Im (d2k (Copp s) t)) a b Hab
             (fun c Hc => base_deriv_d2sGC_Im s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Im (d2k (Copp s) t)) (fun t => Im (dd2k (Copp s) t)) a xi Hxia
             (fun c Hc => Im_d2k_deriv (Copp s) c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hval : Im (d2gtermC s n) = - (Im (dd2k (Copp s) zeta) * (xi - a))).
  { unfold d2gtermC; fold a b; rewrite !Im_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (dd2k (Copp s) zeta) * 1).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Cmod_Im_le.
    + rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r; apply dd2k_tail_bound; lra.
Qed.

End Bound.

Lemma Cmod_d2gtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (d2gtermC s n) <= 2 * d2bound s n.
Proof.
  intros s n Hs0 Hs1.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  pose proof (Re_d2gtermC_bound s n Hs0 Hs1) as HR.
  pose proof (Im_d2gtermC_bound s n Hs0 Hs1) as HI.
  lra.
Qed.

(* ================================================================= *)
(*  Part B: summability of d2bound (the (ln)^2-weighted p-series).     *)
(* ================================================================= *)

(* ln x <= (1/d) x^d  for x>=1, d>0   (via 1+u <= exp u) *)
Lemma ln_le_rpow : forall d x, 0 < d -> 1 <= x -> ln x <= / d * Rpower x d.
Proof.
  intros d x Hd Hx.
  assert (H1 : 1 + d * ln x <= Rpower x d) by (unfold Rpower; apply exp_ineq1_le).
  apply Rle_trans with (/ d * (1 + d * ln x)).
  - replace (/ d * (1 + d * ln x)) with (/ d + ln x) by (field; lra).
    assert (0 < / d) by (apply Rinv_0_lt_compat; exact Hd); lra.
  - apply Rmult_le_compat_l; [ apply Rlt_le; apply Rinv_0_lt_compat; exact Hd | exact H1 ].
Qed.

Lemma Rpower_base_le : forall c x y, 0 <= c -> 0 < x -> x <= y -> Rpower x c <= Rpower y c.
Proof.
  intros c x y Hc Hx Hxy; unfold Rpower; apply exp_le.
  apply Rmult_le_compat_l; [ exact Hc | apply ln_le'; assumption ].
Qed.

Lemma Rpower_mult_distr : forall x y z, 0 < x -> 0 < y ->
  Rpower (x * y) z = Rpower x z * Rpower y z.
Proof.
  intros x y z Hx Hy; unfold Rpower.
  rewrite ln_mult by assumption; rewrite Rmult_plus_distr_l, exp_plus; reflexivity.
Qed.

(* the weighted p-series:  sum  (n+2)^c (n+1)^{-p}  converges for c+1 < p *)
Lemma lnpow_pseries_cv : forall c p, 0 <= c -> c + 1 < p ->
  { T | Un_cv (sum_f_R0 (fun n => Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- p))) T }.
Proof.
  intros c p Hc Hcp.
  destruct (pseries_cv (p - c) ltac:(lra)) as [T' HT'].
  set (conv := fun n => Rpower (INR (S n)) (- (p - c))).
  assert (Hp2 : 0 <= Rpower 2 c) by (apply Rlt_le; unfold Rpower; apply exp_pos).
  assert (Hbound : forall n, Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- p)
                            <= Rpower 2 c * conv n).
  { intro n; unfold conv.
    assert (Hsn : 0 < INR (S n)) by (apply lt_0_INR; lia).
    assert (Hle : INR (S (S n)) <= 2 * INR (S n)).
    { rewrite (S_INR (S n)); assert (1 <= INR (S n)) by (rewrite <- INR_1; apply le_INR; lia); lra. }
    apply Rle_trans with (Rpower (2 * INR (S n)) c * Rpower (INR (S n)) (- p)).
    - apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
      apply Rpower_base_le; [ exact Hc | apply lt_0_INR; lia | exact Hle ].
    - rewrite (Rpower_mult_distr 2 (INR (S n)) c ltac:(lra) Hsn), Rmult_assoc.
      apply Rmult_le_compat_l; [ exact Hp2 | ].
      rewrite <- Rpower_plus; replace (c + - p) with (- (p - c)) by ring; apply Rle_refl. }
  assert (Hterm0 : forall n, 0 <= Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- p))
    by (intro n; apply Rmult_le_pos; apply Rlt_le; unfold Rpower; apply exp_pos).
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hterm0 (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (Rpower 2 c * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun n => Rpower 2 c * conv n) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun n => Rpower 2 c * conv n) with (fun n => conv n * Rpower 2 c)
        by (apply functional_extensionality; intro n; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact Hp2 | ].
      apply (growing_ineq (sum_f_R0 conv) T'); [ | exact HT' ].
      intro M; rewrite tech5.
      assert (0 <= conv (S M)) by (unfold conv; apply Rlt_le; unfold Rpower; apply exp_pos); lra.
Qed.

(* the defining bound of d2gtermC is summable on Re s > 0 *)
Lemma d2bound_sum_cv : forall s, 0 < Re s -> { T | Un_cv (sum_f_R0 (d2bound s)) T }.
Proof.
  intros s Hs.
  set (c := Re s / 2).
  assert (Hc : 0 <= c) by (unfold c; lra).
  destruct (lnpow_pseries_cv c (Re s + 1) Hc ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- (Re s + 1))).
  set (K := 4 / Re s + Cmod s * (4 / Re s) * (4 / Re s)).
  assert (HK : 0 <= K) by (unfold K; pose proof (Cmod_nonneg s);
    apply Rplus_le_le_0_compat; [ | apply Rmult_le_pos; [ apply Rmult_le_pos | ] ];
    try assumption; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  assert (Hd0 : forall n, 0 <= d2bound s n).
  { intro n; unfold d2bound.
    assert (Hb1 : 1 <= INR (S (S n))) by (rewrite <- INR_1; apply le_INR; lia).
    assert (0 <= ln (INR (S (S n)))) by (rewrite <- ln_1; apply ln_le'; lra).
    apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
    apply Rplus_le_le_0_compat; [ apply Rmult_le_pos; lra
      | apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | apply Cmod_nonneg ] ]. }
  assert (Hbound : forall n, d2bound s n <= K * term n).
  { intro n; unfold d2bound, term.
    set (b := INR (S (S n))).
    assert (Hb1 : 1 <= b) by (unfold b; rewrite <- INR_1; apply le_INR; lia).
    assert (Hlnb0 : 0 <= ln b) by (rewrite <- ln_1; apply ln_le'; lra).
    assert (Hlin : ln b <= 2 / Re s * Rpower b c).
    { replace (2 / Re s) with (/ c) by (unfold c; field; lra).
      apply ln_le_rpow; [ unfold c; lra | exact Hb1 ]. }
    assert (Hsq : ln b * ln b <= (4 / Re s) * (4 / Re s) * Rpower b c).
    { assert (Hq : ln b <= 4 / Re s * Rpower b (Re s / 4)).
      { replace (4 / Re s) with (/ (Re s / 4)) by (field; lra).
        apply ln_le_rpow; [ lra | exact Hb1 ]. }
      apply Rle_trans with ((4 / Re s * Rpower b (Re s / 4)) * (4 / Re s * Rpower b (Re s / 4))).
      - apply Rmult_le_compat; assumption.
      - replace ((4 / Re s * Rpower b (Re s / 4)) * (4 / Re s * Rpower b (Re s / 4)))
          with ((4 / Re s) * (4 / Re s) * (Rpower b (Re s / 4) * Rpower b (Re s / 4))) by ring.
        rewrite <- Rpower_plus; replace (Re s / 4 + Re s / 4) with c by (unfold c; field).
        apply Rle_refl. }
    replace (- Re s - 1) with (- (Re s + 1)) by ring.
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
    unfold K.
    replace ((4 / Re s + Cmod s * (4 / Re s) * (4 / Re s)) * Rpower b c)
      with ((4 / Re s * Rpower b c) + Cmod s * ((4 / Re s) * (4 / Re s) * Rpower b c)) by ring.
    apply Rplus_le_compat.
    - apply Rle_trans with (2 * (2 / Re s * Rpower b c));
        [ apply Rmult_le_compat_l; lra | apply Req_le; field; lra ].
    - rewrite (Rmult_comm (ln b * ln b) (Cmod s)).
      apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hsq ]. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hd0 (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (K * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun n => K * term n) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun n => K * term n) with (fun n => term n * K)
        by (apply functional_extensionality; intro n; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact HK | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M; rewrite tech5.
      assert (0 <= term (S M)) by (unfold term; apply Rmult_le_pos; apply Rlt_le;
        unfold Rpower; apply exp_pos); lra.
Qed.

Print Assumptions Cmod_d2gtermC_bound.
Print Assumptions d2bound_sum_cv.

(* ================================================================= *)
(*  END CZetaTerm2.v (item 3b: (ln)^2 double-MVT bound + summability). *)
(* ================================================================= *)
