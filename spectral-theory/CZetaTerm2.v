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

Print Assumptions Cmod_d2gtermC_bound.

(* ================================================================= *)
(*  END CZetaTerm2.v (part A: the (ln)^2 double-MVT bound).           *)
(* ================================================================= *)
