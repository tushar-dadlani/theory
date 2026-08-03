(* ================================================================= *)
(*  CZetaDeriv3.v  —  the FIRST-order knot and the convergence of the   *)
(*  derivative series D = sum dgtermC(z,n), needed for zetaC_holo.      *)
(*                                                                    *)
(*  Part 1: the first-order knot  d/dt (dsGC s t) = dsk s t             *)
(*  (dsGC = d_s GC = -ln t A B + A B^2, dsk = d_s gC = -ln t t^{-s}),   *)
(*  the exact analogue of base_deriv_d2sGC, reusing base_deriv_term,    *)
(*  Cpw_onems, combine_real.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CSeries CBaseDeriv CBaseDeriv2
               CZetaTerm CZetaTerm2 CZetaDeriv2.
Open Scope R_scope.

(* the algebraic heart of the first-order knot: the four terms of
   d/dt(dsGC) collapse (via onems·B = 1) to -a·Q = dsk.  *)
Lemma dsGC_cancel : forall (Q onems : C) (a : R), onems <> C0 ->
  Cadd (Cadd
    (Cmul (RtoC (-1)) (Cmul Q (Cinv onems)))
    (Cmul (RtoC (- a)) (Cmul (Cmul onems Q) (Cinv onems))))
    (Cadd
    (Cmul (RtoC 0) (Cmul Q (Cmul (Cinv onems) (Cinv onems))))
    (Cmul (RtoC 1) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cinv onems)))))
  = Cmul (Copp C1) (Cmul (RtoC a) Q).
Proof.
  intros Q onems a H.
  replace (RtoC (- a)) with (Cmul (Copp C1) (RtoC a))
    by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (-1)) with (Copp C1)
    by (unfold RtoC, Copp, C1; apply Ceq; cbn; ring).
  replace (RtoC 1) with C1 by (unfold RtoC, C1; apply Ceq; cbn; ring).
  replace (RtoC 0) with C0 by (unfold RtoC, C0; apply Ceq; cbn; ring).
  field; exact H.
Qed.

(* the raw base derivative of dsGC (as produced by base_deriv_term) *)
Definition ddsGC (s : C) (t : R) : C :=
  Cadd (Cadd
    (Cmul (RtoC (- / t)) (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s))))
    (Cmul (RtoC (- ln t))
          (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s)))))
    (Cadd
    (Cmul (RtoC 0)
          (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
    (Cmul (RtoC 1)
          (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1)))
                (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))).

Lemma dd_eq_1 : forall s t, 0 < t -> Cminus C1 s <> C0 -> ddsGC s t = dsk s t.
Proof.
  intros s t Ht Hs; assert (Ht0 : t <> 0) by lra; unfold ddsGC, dsk.
  assert (HP1 : Cpw t (Cminus (Cminus C1 s) C1) = Cpw t (Copp s)) by (f_equal; ring).
  rewrite !HP1, !(Cpw_onems s t Ht).
  replace (- / t) with ((-1) * / t) by ring.
  rewrite (combine_real (-1) t (Cpw t (Copp s)) (Cinv (Cminus C1 s)) Ht0).
  replace (Cmul (RtoC 0)
             (Cmul (Cmul (RtoC t) (Cpw t (Copp s)))
                   (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
    with (Cmul (RtoC 0)
             (Cmul (Cpw t (Copp s))
                   (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
    by (rewrite !RtoC0_mul; reflexivity).
  apply (dsGC_cancel (Cpw t (Copp s)) (Cminus C1 s) (ln t) Hs).
Qed.

(* THE FIRST-ORDER KNOT: d/dt (d_s GC) = d_s gC, componentwise. *)
Lemma base_deriv_dsGC_Re : forall s t, 0 < t -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun u => Re (dsGC s u)) t (Re (dsk s t)).
Proof.
  intros s t Ht Hs.
  rewrite <- (dd_eq_1 s t Ht Hs).
  assert (Hfun : (fun u => Re (dsGC s u))
    = (fun u =>
        Re (Cmul (RtoC (- ln u)) (Cmul (Cpw u (Cminus C1 s)) (Cinv (Cminus C1 s))))
      + Re (Cmul (RtoC 1)
              (Cmul (Cpw u (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))).
  { apply functional_extensionality; intro u; unfold dsGC; rewrite Re_Cadd.
    f_equal; rewrite Re_RtoC_mul; ring. }
  rewrite Hfun.
  replace (Re (ddsGC s t)) with (
    ((- / t) * Re (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s)))
     + (- ln t) * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    + (0 * Re (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))
     + 1 * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
    by (unfold ddsGC; rewrite !Re_Cadd, !Re_RtoC_mul; ring).
  apply derivable_pt_lim_plus.
  - apply (base_deriv_term_Re (fun u => - ln u) (- / t)
             (Cinv (Cminus C1 s)) s t Ht).
    apply derivable_pt_lim_opp; apply derivable_pt_lim_ln; exact Ht.
  - apply (base_deriv_term_Re (fun u => 1) 0
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) s t Ht).
    apply (derivable_pt_lim_const 1 t).
Qed.

Lemma base_deriv_dsGC_Im : forall s t, 0 < t -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun u => Im (dsGC s u)) t (Im (dsk s t)).
Proof.
  intros s t Ht Hs.
  rewrite <- (dd_eq_1 s t Ht Hs).
  assert (Hfun : (fun u => Im (dsGC s u))
    = (fun u =>
        Im (Cmul (RtoC (- ln u)) (Cmul (Cpw u (Cminus C1 s)) (Cinv (Cminus C1 s))))
      + Im (Cmul (RtoC 1)
              (Cmul (Cpw u (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))).
  { apply functional_extensionality; intro u; unfold dsGC; rewrite Im_Cadd.
    f_equal; rewrite Im_RtoC_mul; ring. }
  rewrite Hfun.
  replace (Im (ddsGC s t)) with (
    ((- / t) * Im (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s)))
     + (- ln t) * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    + (0 * Im (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))
     + 1 * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
    by (unfold ddsGC; rewrite !Im_Cadd, !Im_RtoC_mul; ring).
  apply derivable_pt_lim_plus.
  - apply (base_deriv_term_Im (fun u => - ln u) (- / t)
             (Cinv (Cminus C1 s)) s t Ht).
    apply derivable_pt_lim_opp; apply derivable_pt_lim_ln; exact Ht.
  - apply (base_deriv_term_Im (fun u => 1) 0
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) s t Ht).
    apply (derivable_pt_lim_const 1 t).
Qed.

(* ------------------------------------------------------------------ *)
(*  Part 2: the base derivative of dsk and its modulus bound.          *)
(* ------------------------------------------------------------------ *)

Lemma Re_Copp : forall c, Re (Copp c) = - Re c.
Proof. intro c; unfold Copp; cbn [Re]; ring. Qed.
Lemma Im_Copp : forall c, Im (Copp c) = - Im c.
Proof. intro c; unfold Copp; cbn [Im]; ring. Qed.

Definition ddsk (s : C) (t : R) : C :=
  Copp (Cadd (Cmul (RtoC (/ t)) (Cpw t (Copp s)))
             (Cmul (RtoC (ln t)) (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1))))).

Lemma Re_dsk_deriv : forall s t, 0 < t ->
  derivable_pt_lim (fun u => Re (dsk s u)) t (Re (ddsk s t)).
Proof.
  intros s t Ht.
  assert (Heq : (fun u => Re (dsk s u)) = (fun u => - (ln u * Re (Cpw u (Copp s)))))
    by (apply functional_extensionality; intro u; unfold dsk, Cmul, RtoC, Copp, C1; cbn; ring).
  rewrite Heq.
  replace (Re (ddsk s t))
    with (- (/ t * Re (Cpw t (Copp s)) + ln t * Re (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1)))))
    by (unfold ddsk; rewrite Re_Copp, Re_Cadd, !Re_RtoC_mul; ring).
  apply derivable_pt_lim_opp.
  apply (derivable_pt_lim_mult ln (fun u => Re (Cpw u (Copp s))) t (/ t)
           (Re (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1))))).
  - apply derivable_pt_lim_ln; exact Ht.
  - apply Re_Cpw_deriv; exact Ht.
Qed.

Lemma Im_dsk_deriv : forall s t, 0 < t ->
  derivable_pt_lim (fun u => Im (dsk s u)) t (Im (ddsk s t)).
Proof.
  intros s t Ht.
  assert (Heq : (fun u => Im (dsk s u)) = (fun u => - (ln u * Im (Cpw u (Copp s)))))
    by (apply functional_extensionality; intro u; unfold dsk, Cmul, RtoC, Copp, C1; cbn; ring).
  rewrite Heq.
  replace (Im (ddsk s t))
    with (- (/ t * Im (Cpw t (Copp s)) + ln t * Im (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1)))))
    by (unfold ddsk; rewrite Im_Copp, Im_Cadd, !Im_RtoC_mul; ring).
  apply derivable_pt_lim_opp.
  apply (derivable_pt_lim_mult ln (fun u => Im (Cpw u (Copp s))) t (/ t)
           (Im (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1))))).
  - apply derivable_pt_lim_ln; exact Ht.
  - apply Im_Cpw_deriv; exact Ht.
Qed.

Lemma Cmod_ddsk : forall s t, 1 <= t ->
  Cmod (ddsk s t) <= (1 + ln t * Cmod s) * Rpower t (- Re s - 1).
Proof.
  intros s t Ht.
  assert (Htp : 0 < t) by lra.
  assert (Hln : 0 <= ln t) by (rewrite <- ln_1; destruct (Rle_lt_or_eq_dec 1 t Ht) as [H|H];
    [ left; apply ln_increasing; lra | rewrite <- H; apply Rle_refl ]).
  assert (Hpred : Rpower t (- Re s) * / t = Rpower t (- Re s - 1)) by (apply Rpower_pred; exact Htp).
  unfold ddsk; rewrite Cmod_opp.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC, Cmod_opp, !Cpw_mod.
  replace (Re (Copp s)) with (- Re s) by (rewrite Re_Copp; ring).
  replace (Re (Cminus (Copp s) C1)) with (- Re s - 1)
    by (unfold Cminus, Copp, C1; cbn [Re]; ring).
  rewrite (Rabs_right (/ t)) by (apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; exact Htp).
  rewrite (Rabs_right (ln t)) by (apply Rle_ge; exact Hln).
  replace (/ t * Rpower t (- Re s)) with (Rpower t (- Re s) * / t) by ring.
  rewrite Hpred.
  apply Req_le; ring.
Qed.

Print Assumptions Re_dsk_deriv.
Print Assumptions Cmod_ddsk.

(* ------------------------------------------------------------------ *)
(*  Part 3: the first-order double-MVT bound on dgtermC.               *)
(* ------------------------------------------------------------------ *)

Definition dbound1 (s : C) (n : nat) : R :=
  (1 + ln (INR (S (S n))) * Cmod s) * Rpower (INR (S n)) (- Re s - 1).

Lemma Re_dgtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Rabs (Re (dgtermC s n)) <= dbound1 s n.
Proof.
  intros s n Hs0 Hs1.
  set (a := INR (S n)); set (b := INR (S (S n))).
  assert (Ha : 0 < a) by (unfold a; apply lt_0_INR; lia).
  assert (Hab : a < b) by (unfold a, b; apply lt_INR; lia).
  assert (Hba1 : b - a = 1) by (unfold a, b; rewrite (S_INR (S n)); ring).
  destruct (MVT_cor2 (fun t => Re (dsGC s t)) (fun t => Re (dsk s t)) a b Hab
             (fun c Hc => base_deriv_dsGC_Re s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Re (dsk s t)) (fun t => Re (ddsk s t)) a xi Hxia
             (fun c Hc => Re_dsk_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hzpos : 0 < zeta) by lra.
  assert (Hz1 : 1 <= zeta) by (apply Rle_trans with a;
    [ unfold a; rewrite <- INR_1; apply le_INR; lia | lra ]).
  assert (Hlzb : ln zeta <= ln b) by (apply ln_le'; lra).
  assert (Hval : Re (dgtermC s n) = - (Re (ddsk s zeta) * (xi - a))).
  { unfold dgtermC; fold a b; rewrite !Re_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (ddsk s zeta) * 1).
  - apply Rmult_le_compat; [ apply Rabs_pos | apply Rabs_pos | apply Cmod_Re_le | ].
    rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r.
    eapply Rle_trans; [ apply Cmod_ddsk; exact Hz1 | ].
    unfold dbound1.
    apply Rmult_le_compat.
    + apply Rplus_le_le_0_compat;
        [ lra | apply Rmult_le_pos; [ rewrite <- ln_1; apply ln_le'; lra | apply Cmod_nonneg ] ].
    + apply Rlt_le; unfold Rpower; apply exp_pos.
    + apply Rplus_le_compat_l; apply Rmult_le_compat_r; [ apply Cmod_nonneg | exact Hlzb ].
    + replace (- Re s - 1) with (- (Re s + 1)) by ring.
      apply Rpow_negexp_anti; [ exact Ha | apply Rlt_le; exact Hza | lra ].
Qed.

Lemma Im_dgtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Rabs (Im (dgtermC s n)) <= dbound1 s n.
Proof.
  intros s n Hs0 Hs1.
  set (a := INR (S n)); set (b := INR (S (S n))).
  assert (Ha : 0 < a) by (unfold a; apply lt_0_INR; lia).
  assert (Hab : a < b) by (unfold a, b; apply lt_INR; lia).
  assert (Hba1 : b - a = 1) by (unfold a, b; rewrite (S_INR (S n)); ring).
  destruct (MVT_cor2 (fun t => Im (dsGC s t)) (fun t => Im (dsk s t)) a b Hab
             (fun c Hc => base_deriv_dsGC_Im s c (Rlt_le_trans 0 a c Ha (proj1 Hc)) Hs1))
    as [xi [Hxi [Hxia Hxib]]].
  rewrite Hba1, Rmult_1_r in Hxi.
  destruct (MVT_cor2 (fun t => Im (dsk s t)) (fun t => Im (ddsk s t)) a xi Hxia
             (fun c Hc => Im_dsk_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzx]]].
  assert (Hzpos : 0 < zeta) by lra.
  assert (Hz1 : 1 <= zeta) by (apply Rle_trans with a;
    [ unfold a; rewrite <- INR_1; apply le_INR; lia | lra ]).
  assert (Hlzb : ln zeta <= ln b) by (apply ln_le'; lra).
  assert (Hval : Im (dgtermC s n) = - (Im (ddsk s zeta) * (xi - a))).
  { unfold dgtermC; fold a b; rewrite !Im_Cminus, Hxi; lra. }
  rewrite Hval, Rabs_Ropp, Rabs_mult.
  apply Rle_trans with (Cmod (ddsk s zeta) * 1).
  - apply Rmult_le_compat; [ apply Rabs_pos | apply Rabs_pos | apply Cmod_Im_le | ].
    rewrite (Rabs_right (xi - a)) by (apply Rle_ge; lra); lra.
  - rewrite Rmult_1_r.
    eapply Rle_trans; [ apply Cmod_ddsk; exact Hz1 | ].
    unfold dbound1.
    apply Rmult_le_compat.
    + apply Rplus_le_le_0_compat;
        [ lra | apply Rmult_le_pos; [ rewrite <- ln_1; apply ln_le'; lra | apply Cmod_nonneg ] ].
    + apply Rlt_le; unfold Rpower; apply exp_pos.
    + apply Rplus_le_compat_l; apply Rmult_le_compat_r; [ apply Cmod_nonneg | exact Hlzb ].
    + replace (- Re s - 1) with (- (Re s + 1)) by ring.
      apply Rpow_negexp_anti; [ exact Ha | apply Rlt_le; exact Hza | lra ].
Qed.

Lemma Cmod_dgtermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (dgtermC s n) <= 2 * dbound1 s n.
Proof.
  intros s n Hs0 Hs1.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  pose proof (Re_dgtermC_bound s n Hs0 Hs1).
  pose proof (Im_dgtermC_bound s n Hs0 Hs1); lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  Part 4: summability of dbound1, hence dgtermC_cv.                  *)
(* ------------------------------------------------------------------ *)

Lemma Rpower_ge_1 : forall x a, 1 <= x -> 0 <= a -> 1 <= Rpower x a.
Proof.
  intros x a Hx Ha; unfold Rpower; rewrite <- exp_0; apply exp_le.
  apply Rmult_le_pos; [ exact Ha | rewrite <- ln_1; apply ln_le'; lra ].
Qed.

Lemma dbound1_sum_cv : forall s, 0 < Re s -> { T | Un_cv (sum_f_R0 (dbound1 s)) T }.
Proof.
  intros s Hs.
  set (c := Re s / 2).
  destruct (lnpow_pseries_cv c (Re s + 1) ltac:(unfold c; lra) ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- (Re s + 1))).
  set (K := 1 + Cmod s * (2 / Re s)).
  assert (HK : 0 <= K) by (unfold K; pose proof (Cmod_nonneg s);
    apply Rplus_le_le_0_compat; [ lra | apply Rmult_le_pos;
      [ assumption | apply Rlt_le; apply Rdiv_lt_0_compat; lra ] ]).
  assert (Hd0 : forall n, 0 <= dbound1 s n).
  { intro n; unfold dbound1.
    apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
    apply Rplus_le_le_0_compat; [ lra | apply Rmult_le_pos;
      [ rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]
      | apply Cmod_nonneg ] ]. }
  assert (Hbound : forall n, dbound1 s n <= K * term n).
  { intro n; unfold dbound1, term; set (b := INR (S (S n))).
    assert (Hb1 : 1 <= b) by (unfold b; rewrite <- INR_1; apply le_INR; lia).
    assert (H1 : 1 <= Rpower b c) by (apply Rpower_ge_1; [ exact Hb1 | unfold c; lra ]).
    assert (Hln : ln b <= 2 / Re s * Rpower b c)
      by (replace (2 / Re s) with (/ c) by (unfold c; field; lra);
          apply ln_le_rpow; [ unfold c; lra | exact Hb1 ]).
    replace (- Re s - 1) with (- (Re s + 1)) by ring.
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
    unfold K.
    replace ((1 + Cmod s * (2 / Re s)) * Rpower b c)
      with (Rpower b c + Cmod s * (2 / Re s * Rpower b c)) by ring.
    apply Rplus_le_compat.
    - exact H1.
    - rewrite (Rmult_comm (ln b) (Cmod s)); apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hln ]. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hd0 (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (K * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun m => K * term m) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun m => K * term m) with (fun m => term m * K)
        by (apply functional_extensionality; intro m; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact HK | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M; rewrite tech5.
      assert (0 <= term (S M)) by (unfold term; apply Rmult_le_pos; apply Rlt_le;
        unfold Rpower; apply exp_pos); lra.
Qed.

(* the derivative series D = sum dgtermC(s,n) converges on Re s > 0 *)
Lemma dgtermC_cv : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  { D | Cseries_cv (dgtermC s) D }.
Proof.
  intros s Hs0 Hs1.
  apply (Cseries_abs_cv (dgtermC s) (fun n => 2 * dbound1 s n)).
  - intro n; apply Cmod_dgtermC_bound; [ lra | exact Hs1 ].
  - destruct (dbound1_sum_cv s Hs0) as [T HT].
    exists (2 * T).
    replace (sum_f_R0 (fun n => 2 * dbound1 s n))
      with (fun N => 2 * sum_f_R0 (dbound1 s) N).
    + apply (CV_mult (fun _ => 2) (sum_f_R0 (dbound1 s)) 2 T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (dbound1 s) N 2); apply sum_eq; intros i _; ring.
Qed.

Print Assumptions Cmod_dgtermC_bound.
Print Assumptions dgtermC_cv.

(* ================================================================= *)
(*  END CZetaDeriv3.v (dgtermC_cv: the derivative series converges).  *)
(* ================================================================= *)
