(* ================================================================= *)
(*  CZetaTerm.v  —  the complex Euler–Maclaurin term and its bound.    *)
(*                                                                    *)
(*  Part 1: derivatives of Re/Im of (c^w · K) for a complex constant   *)
(*  K (needed for the antiderivative G(x)=x^{1-s}/(1-s), whose         *)
(*  derivative is x^{-s}), and the modulus of the base derivative      *)
(*  |w·x^{w-1}| = |w|·x^{Re w-1}.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CSeries.
Open Scope R_scope.

(* modulus of the base derivative  w·x^{w-1} *)
Lemma Cmod_wCpw : forall w x,
  Cmod (Cmul w (Cpw x (Cminus w C1))) = Cmod w * Rpower x (Re w - 1).
Proof.
  intros w x; rewrite Cmod_mul, Cpw_mod.
  replace (Re (Cminus w C1)) with (Re w - 1)
    by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
  reflexivity.
Qed.

(* derivative of Re/Im of (c^w · K) in the base *)
Lemma Re_Cmul_deriv : forall w K x, 0 < x ->
  derivable_pt_lim (fun t => Re (Cmul (Cpw t w) K)) x
    (Re (Cmul (Cmul w (Cpw x (Cminus w C1))) K)).
Proof.
  intros w K x Hx.
  assert (Heq : (fun t => Re (Cmul (Cpw t w) K))
              = (fun t => Re K * Re (Cpw t w) - Im K * Im (Cpw t w)))
    by (apply functional_extensionality; intro t; unfold Cmul; cbn [Re]; ring).
  rewrite Heq.
  replace (Re (Cmul (Cmul w (Cpw x (Cminus w C1))) K))
    with (Re K * Re (Cmul w (Cpw x (Cminus w C1)))
          - Im K * Im (Cmul w (Cpw x (Cminus w C1))))
    by (unfold Cmul; cbn [Re Im]; ring).
  apply (derivable_pt_lim_minus
           (fun t => Re K * Re (Cpw t w)) (fun t => Im K * Im (Cpw t w)) x
           (Re K * Re (Cmul w (Cpw x (Cminus w C1))))
           (Im K * Im (Cmul w (Cpw x (Cminus w C1))))).
  - apply (derivable_pt_lim_scal (fun t => Re (Cpw t w)) (Re K) x
             (Re (Cmul w (Cpw x (Cminus w C1))))); apply Re_Cpw_deriv; exact Hx.
  - apply (derivable_pt_lim_scal (fun t => Im (Cpw t w)) (Im K) x
             (Im (Cmul w (Cpw x (Cminus w C1))))); apply Im_Cpw_deriv; exact Hx.
Qed.

Lemma Im_Cmul_deriv : forall w K x, 0 < x ->
  derivable_pt_lim (fun t => Im (Cmul (Cpw t w) K)) x
    (Im (Cmul (Cmul w (Cpw x (Cminus w C1))) K)).
Proof.
  intros w K x Hx.
  assert (Heq : (fun t => Im (Cmul (Cpw t w) K))
              = (fun t => Re K * Im (Cpw t w) + Im K * Re (Cpw t w)))
    by (apply functional_extensionality; intro t; unfold Cmul; cbn [Im]; ring).
  rewrite Heq.
  replace (Im (Cmul (Cmul w (Cpw x (Cminus w C1))) K))
    with (Re K * Im (Cmul w (Cpw x (Cminus w C1)))
          + Im K * Re (Cmul w (Cpw x (Cminus w C1))))
    by (unfold Cmul; cbn [Re Im]; ring).
  apply (derivable_pt_lim_plus
           (fun t => Re K * Im (Cpw t w)) (fun t => Im K * Re (Cpw t w)) x
           (Re K * Im (Cmul w (Cpw x (Cminus w C1))))
           (Im K * Re (Cmul w (Cpw x (Cminus w C1))))).
  - apply (derivable_pt_lim_scal (fun t => Im (Cpw t w)) (Re K) x
             (Im (Cmul w (Cpw x (Cminus w C1))))); apply Im_Cpw_deriv; exact Hx.
  - apply (derivable_pt_lim_scal (fun t => Re (Cpw t w)) (Im K) x
             (Re (Cmul w (Cpw x (Cminus w C1))))); apply Re_Cpw_deriv; exact Hx.
Qed.

(* ================================================================= *)
(*  Part 2: the complex EM term, its antiderivative relations, and     *)
(*  real-analysis helpers for the double-MVT bound.                    *)
(* ================================================================= *)

Definition gC (s : C) (x : R) : C := Cpw x (Copp s).
Definition GC (s : C) (x : R) : C := Cmul (Cpw x (Cminus C1 s)) (Cinv (Cminus C1 s)).
Definition gderivC (s : C) (x : R) : C := Cmul (Copp s) (Cpw x (Cminus (Copp s) C1)).
Definition gtermC (s : C) (n : nat) : C :=
  Cminus (gC s (INR (S n))) (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))).

Lemma Re_Cminus : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros a b; unfold Cminus, Cadd, Copp; cbn [Re]; ring. Qed.

Lemma Im_Cminus : forall a b, Im (Cminus a b) = Im a - Im b.
Proof. intros a b; unfold Cminus, Cadd, Copp; cbn [Im]; ring. Qed.

Lemma exp_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H; destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

(* x^{-e} is antitone in the base for e>=0 *)
Lemma Rpow_negexp_anti : forall x y e, 0 < x -> x <= y -> 0 <= e ->
  Rpower y (- e) <= Rpower x (- e).
Proof.
  intros x y e Hx Hxy He; unfold Rpower; apply exp_le.
  assert (Hln : ln x <= ln y).
  { destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq];
      [ left; apply ln_increasing; [ exact Hx | exact Hlt ] | rewrite Heq; apply Rle_refl ]. }
  apply Rmult_le_compat_neg_l; [ lra | exact Hln ].
Qed.

(* the antiderivative relation  Re/Im (G)' = Re/Im (g), where the Cinv
   factor cancels the (1-s) from the base derivative of x^{1-s} *)
Lemma ReGC_deriv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun t => Re (GC s t)) x (Re (gC s x)).
Proof.
  intros s x Hx Hs; unfold GC, gC.
  replace (Re (Cpw x (Copp s)))
    with (Re (Cmul (Cmul (Cminus C1 s) (Cpw x (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    by (f_equal; replace (Cminus (Cminus C1 s) C1) with (Copp s) by ring; field; exact Hs).
  apply Re_Cmul_deriv; exact Hx.
Qed.

Lemma ImGC_deriv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun t => Im (GC s t)) x (Im (gC s x)).
Proof.
  intros s x Hx Hs; unfold GC, gC.
  replace (Im (Cpw x (Copp s)))
    with (Im (Cmul (Cmul (Cminus C1 s) (Cpw x (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    by (f_equal; replace (Cminus (Cminus C1 s) C1) with (Copp s) by ring; field; exact Hs).
  apply Im_Cmul_deriv; exact Hx.
Qed.

Lemma RegC_deriv : forall s x, 0 < x ->
  derivable_pt_lim (fun t => Re (gC s t)) x (Re (gderivC s x)).
Proof. intros s x Hx; unfold gC, gderivC; apply Re_Cpw_deriv; exact Hx. Qed.

Lemma ImgC_deriv : forall s x, 0 < x ->
  derivable_pt_lim (fun t => Im (gC s t)) x (Im (gderivC s x)).
Proof. intros s x Hx; unfold gC, gderivC; apply Im_Cpw_deriv; exact Hx. Qed.

Lemma Cmod_gderivC : forall s x, Cmod (gderivC s x) = Cmod s * Rpower x (- Re s - 1).
Proof.
  intros s x; unfold gderivC; rewrite Cmod_wCpw, Cmod_opp.
  replace (Re (Copp s) - 1) with (- Re s - 1) by (unfold Copp; cbn [Re]; ring).
  reflexivity.
Qed.

(* ================================================================= *)
(*  Part 3: the double-MVT bound  |gtermC s n| <= 2|s|·(n+1)^{-Re s-1}. *)
(* ================================================================= *)

Lemma Re_gtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Rabs (Re (gtermC s n)) <= Cmod s * Rpower (INR (S n)) (- Re s - 1).
Proof.
  intros s n Hs0 Hs1.
  set (a := INR (S n)); set (b := INR (S (S n))).
  assert (Ha : 0 < a) by (unfold a; apply lt_0_INR; lia).
  assert (Hab : a < b) by (unfold a, b; apply lt_INR; lia).
  assert (Hba1 : b - a = 1) by (unfold a, b; rewrite (S_INR (S n)); ring).
  destruct (MVT_cor2 (fun t => Re (GC s t)) (fun t => Re (gC s t)) a b Hab
             (fun c Hc => ReGC_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Re (gC s t)) (fun t => Re (gderivC s t)) a xi Hxia
             (fun c Hc => RegC_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hval : Re (gtermC s n) = - (Re (gderivC s zeta) * (xi - a))).
  { unfold gtermC; fold a b; rewrite !Re_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (gderivC s zeta) * 1).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Cmod_Re_le.
    + rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r, Cmod_gderivC.
    apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
    replace (- Re s - 1) with (- (Re s + 1)) by ring.
    apply Rpow_negexp_anti; [ exact Ha | lra | lra ].
Qed.

Lemma Im_gtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Rabs (Im (gtermC s n)) <= Cmod s * Rpower (INR (S n)) (- Re s - 1).
Proof.
  intros s n Hs0 Hs1.
  set (a := INR (S n)); set (b := INR (S (S n))).
  assert (Ha : 0 < a) by (unfold a; apply lt_0_INR; lia).
  assert (Hab : a < b) by (unfold a, b; apply lt_INR; lia).
  assert (Hba1 : b - a = 1) by (unfold a, b; rewrite (S_INR (S n)); ring).
  destruct (MVT_cor2 (fun t => Im (GC s t)) (fun t => Im (gC s t)) a b Hab
             (fun c Hc => ImGC_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Im (gC s t)) (fun t => Im (gderivC s t)) a xi Hxia
             (fun c Hc => ImgC_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hval : Im (gtermC s n) = - (Im (gderivC s zeta) * (xi - a))).
  { unfold gtermC; fold a b; rewrite !Im_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (gderivC s zeta) * 1).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Cmod_Im_le.
    + rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r, Cmod_gderivC.
    apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
    replace (- Re s - 1) with (- (Re s + 1)) by ring.
    apply Rpow_negexp_anti; [ exact Ha | lra | lra ].
Qed.

Lemma Cmod_gtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (gtermC s n) <= 2 * (Cmod s * Rpower (INR (S n)) (- Re s - 1)).
Proof.
  intros s n Hs0 Hs1.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  pose proof (Re_gtermC_bound s n Hs0 Hs1) as HR.
  pose proof (Im_gtermC_bound s n Hs0 Hs1) as HI.
  lra.
Qed.

(* ================================================================= *)
(*  Part 4: convergence — the p-series and hence zeta on the strip.    *)
(* ================================================================= *)

Lemma Rpow1 : forall y, Rpower 1 y = 1.
Proof. intro y; unfold Rpower; rewrite ln_1, Rmult_0_r, exp_0; reflexivity. Qed.

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists 0%nat; intros n _; unfold R_dist.
  replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

Lemma sum_tele : forall (u : nat -> R) N,
  sum_f_R0 (fun n => u n - u (S n)) N = u 0%nat - u (S N).
Proof.
  intros u N; induction N as [| N IH]; [ cbn [sum_f_R0]; reflexivity | ].
  rewrite tech5, IH; ring.
Qed.

Lemma pseries_cv : forall p, 1 < p ->
  { T | Un_cv (sum_f_R0 (fun n => Rpower (INR (S n)) (- p))) T }.
Proof.
  intros p Hp.
  set (q := p - 1); assert (Hq : 0 < q) by (unfold q; lra).
  assert (Hqi : 0 < / q) by (apply Rinv_0_lt_compat; exact Hq).
  assert (Ha0 : forall n, 0 <= Rpower (INR (S n)) (- p))
    by (intro n; apply Rlt_le; unfold Rpower; apply exp_pos).
  set (t := fun n => Rpower (INR (S n)) (- q)).
  assert (Ht0 : forall n, 0 <= t n)
    by (intro n; unfold t; apply Rlt_le; unfold Rpower; apply exp_pos).
  assert (Ht00 : t 0%nat = 1) by (unfold t; rewrite INR_1, Rpow1; reflexivity).
  assert (Habound : forall n, Rpower (INR (S (S n))) (- p) <= (t n - t (S n)) / q).
  { intro n.
    assert (Hu : 0 < INR (S n)) by (apply lt_0_INR; lia).
    assert (Huv : INR (S n) < INR (S (S n))) by (apply lt_INR; lia).
    assert (Hvu1 : INR (S (S n)) - INR (S n) = 1) by (rewrite (S_INR (S n)); ring).
    assert (Hd : forall c, INR (S n) <= c <= INR (S (S n)) ->
                 derivable_pt_lim (fun y => Rpower y (- q)) c (- q * Rpower c (- p))).
    { intros c Hc; replace (- p) with (- q - 1) by (unfold q; ring).
      apply Rpow_deriv; apply Rlt_le_trans with (INR (S n)); [ exact Hu | apply (proj1 Hc) ]. }
    destruct (MVT_cor2 (fun y => Rpower y (- q)) (fun y => - q * Rpower y (- p))
               (INR (S n)) (INR (S (S n))) Huv Hd) as [xi [Hxi [Hxu Hxv]]].
    rewrite Hvu1, Rmult_1_r in Hxi.
    assert (Hxipos : 0 < xi) by (apply Rlt_trans with (INR (S n)); [ exact Hu | exact Hxu ]).
    assert (Htt : t n - t (S n) = q * Rpower xi (- p)) by (unfold t; nra).
    rewrite Htt; replace (q * Rpower xi (- p) / q) with (Rpower xi (- p)) by (field; lra).
    apply Rpow_negexp_anti; [ exact Hxipos | lra | lra ]. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Ha0 (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (1 + / q); intros y [N Hy]; rewrite Hy; clear Hy y.
    destruct N as [| N].
    + cbn [sum_f_R0]; rewrite INR_1, Rpow1; lra.
    + rewrite decomp_sum by lia; rewrite INR_1, Rpow1; apply Rplus_le_compat_l.
      apply Rle_trans with (sum_f_R0 (fun i => (t i - t (S i)) / q) N).
      * apply sum_Rle; intros i _; apply Habound.
      * replace (fun i => (t i - t (S i)) / q) with (fun i => (t i - t (S i)) * / q)
          by (apply functional_extensionality; intro i; unfold Rdiv; reflexivity).
        rewrite <- scal_sum, sum_tele, Ht00.
        pose proof (Ht0 (S N)); nra.
Qed.

(* zeta's defining series converges on the strip *)
Lemma gtermC_cv : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  { Z | Cseries_cv (gtermC s) Z }.
Proof.
  intros s Hs0 Hs1.
  apply (Cseries_abs_cv (gtermC s)
           (fun n => 2 * (Cmod s * Rpower (INR (S n)) (- Re s - 1)))).
  - intro n; apply Cmod_gtermC_bound; [ lra | exact Hs1 ].
  - destruct (pseries_cv (Re s + 1) ltac:(lra)) as [T HT].
    exists (2 * Cmod s * T).
    replace (sum_f_R0 (fun n => 2 * (Cmod s * Rpower (INR (S n)) (- Re s - 1))))
      with (fun N => 2 * Cmod s * sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 1))) N).
    + apply (CV_mult (fun _ => 2 * Cmod s)
               (sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 1)))) (2 * Cmod s) T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun n => Rpower (INR (S n)) (- (Re s + 1))) N (2 * Cmod s)).
      apply sum_eq; intros i _.
      replace (- (Re s + 1)) with (- Re s - 1) by ring; ring.
Qed.

Print Assumptions gtermC_cv.

(* ================================================================= *)
(*  END CZetaTerm.v (part 4).                                          *)
(* ================================================================= *)
