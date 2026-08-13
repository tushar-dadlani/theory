(* ================================================================= *)
(*  CCauchyAnalytic.v  (identity-theorem plan, analyticity master key) *)
(*                                                                    *)
(*  The complex differentiation-under-the-integral for the Cauchy      *)
(*  kernel (n = 1): w |-> oint_{|z|=R} g(z)/(z-w) dz is holomorphic in  *)
(*  w (|w| < R) with derivative oint g(z)/(z-w)^2 dz.                   *)
(*                                                                    *)
(*  This file: the reusable ALGEBRAIC + MODULUS core of the first-order *)
(*  remainder estimate,                                                *)
(*    1/(zeta-h) - 1/zeta - h/zeta^2 = h^2 / ((zeta-h) zeta^2),         *)
(*  and its modulus, plus the pointwise integrand bound feeding the ML  *)
(*  estimate.  (The is_Cderiv packaging, with a clamp to totalise the   *)
(*  parametrised integral, is the next installment.)                   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CGoursatLin
        CLeibniz CDeriv Holomorphic RootsOfUnity CTaylor CWindingOffCenter.
Open Scope R_scope.

(* ---- the first-order Cauchy-kernel remainder, as pure C-field algebra ---- *)
Lemma cauchy_bracket : forall (zeta h : C),
  zeta <> C0 -> Cminus zeta h <> C0 ->
  Cminus (Cminus (Cinv (Cminus zeta h)) (Cinv zeta)) (Cmul h (Cinv (Cmul zeta zeta)))
  = Cmul (Cmul h h) (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))).
Proof.
  intros zeta h Hz Hzh. field. split; assumption.
Qed.

(* ---- its modulus ---- *)
Lemma cauchy_bracket_mod : forall (zeta h : C),
  zeta <> C0 -> Cminus zeta h <> C0 ->
  Cmod (Cmul (Cmul h h) (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))))
  = Cmod h * Cmod h * / (Cmod (Cminus zeta h) * (Cmod zeta * Cmod zeta)).
Proof.
  intros zeta h Hz Hzh.
  assert (HY : Cmul (Cminus zeta h) (Cmul zeta zeta) <> C0)
    by (apply Cmul_ne0; [ exact Hzh | apply Cmul_ne0; exact Hz ]).
  rewrite Cmod_mul, Cmod_mul, (Cmod_inv _ HY), Cmod_mul, Cmod_mul.
  reflexivity.
Qed.

(* ---- the remainder modulus is bounded by  |h|^2 / (m' * m^2) ---- *)
Lemma cauchy_bracket_bound : forall (zeta h : C) (m mp : R),
  zeta <> C0 -> Cminus zeta h <> C0 ->
  0 < mp -> mp <= Cmod (Cminus zeta h) ->
  0 < m -> m <= Cmod zeta ->
  Cmod (Cmul (Cmul h h) (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))))
  <= Cmod h * Cmod h * / (mp * (m * m)).
Proof.
  intros zeta h m mp Hz Hzh Hmp Hmpb Hm Hmb.
  rewrite cauchy_bracket_mod by assumption.
  assert (Hhh : 0 <= Cmod h * Cmod h)
    by (apply Rmult_le_pos; apply Cmod_nonneg).
  apply Rmult_le_compat_l; [ exact Hhh | ].
  apply Rinv_le_contravar.
  - apply Rmult_lt_0_compat; [ exact Hmp | apply Rmult_lt_0_compat; exact Hm ].
  - apply Rmult_le_compat; try lra.
    + apply Rmult_le_pos; lra.
    + apply Rmult_le_compat; lra.
Qed.

(* ================================================================= *)
(*  General-n first-order Cauchy-kernel remainder, by recurrence       *)
(* ================================================================= *)

(* B_n(zeta,h) = 1/(zeta-h)^n - 1/zeta^n - n h / zeta^{n+1} *)
Definition Bn (zeta h : C) (n : nat) : C :=
  Cminus (Cminus (Cinv (Cpow (Cminus zeta h) n)) (Cinv (Cpow zeta n)))
         (Cmul (RtoC (INR n)) (Cmul h (Cinv (Cpow zeta (S n))))).

(* the key recurrence:  B_{n+1} = A B_n + (n+1) h^2 A b^{n+2}  *)
(*   with A = 1/(zeta-h),  b^{n+2} = 1/zeta^{n+2}.                *)
Lemma bracket_recur : forall zeta h n, zeta <> C0 -> Cminus zeta h <> C0 ->
  Bn zeta h (S n)
  = Cadd (Cmul (Cinv (Cminus zeta h)) (Bn zeta h n))
         (Cmul (RtoC (INR (S n)))
               (Cmul (Cmul h h)
                     (Cmul (Cinv (Cminus zeta h)) (Cinv (Cpow zeta (S (S n))))))).
Proof.
  intros zeta h n Hz Hzh. unfold Bn. cbn [Cpow].
  set (P := Cpow (Cminus zeta h) n). set (Q := Cpow zeta n).
  assert (HP : P <> C0) by (apply Cpow_ne0; exact Hzh).
  assert (HQ : Q <> C0) by (apply Cpow_ne0; exact Hz).
  rewrite S_INR.
  replace (RtoC (INR n + 1)) with (Cadd (RtoC (INR n)) C1)
    by (apply Ceq; unfold RtoC, Cadd, C1; cbn [Re Im]; ring).
  set (cn := RtoC (INR n)).
  field. repeat split; assumption.
Qed.

(* Cmod of a power (local, to avoid a heavy import) *)
Lemma Cmod_Cpow : forall a k, Cmod (Cpow a k) = (Cmod a) ^ k.
Proof.
  intros a k; induction k as [|k IH]; cbn [Cpow pow];
    [ apply Cmod_C1 | rewrite Cmod_mul, IH; reflexivity ].
Qed.

(* the inductive modulus bound  Cmod(B_n) <= |h|^2 . Wn *)
Fixpoint Wn (mp m : R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => / mp * Wn mp m k + INR (S k) * / (mp * m ^ (S (S k)))
  end.

Lemma Wn_nonneg : forall mp m n, 0 < mp -> 0 < m -> 0 <= Wn mp m n.
Proof.
  intros mp m n Hmp Hm; induction n as [|n IH]; cbn [Wn].
  - lra.
  - apply Rplus_le_le_0_compat.
    + apply Rmult_le_pos; [ left; apply Rinv_0_lt_compat; exact Hmp | exact IH ].
    + apply Rmult_le_pos; [ apply pos_INR | left; apply Rinv_0_lt_compat;
        apply Rmult_lt_0_compat; [ exact Hmp | apply pow_lt; exact Hm ] ].
Qed.

Lemma bracket_gen_bound : forall n zeta h mp m,
  zeta <> C0 -> Cminus zeta h <> C0 ->
  0 < mp -> mp <= Cmod (Cminus zeta h) ->
  0 < m -> m <= Cmod zeta ->
  Cmod (Bn zeta h n) <= Cmod h * Cmod h * Wn mp m n.
Proof.
  intros n; induction n as [|n IH]; intros zeta h mp m Hz Hzh Hmp Hmpb Hm Hmb.
  - assert (HB0 : Bn zeta h 0 = C0)
      by (unfold Bn; cbn [Cpow INR]; change (RtoC 0) with C0; ring).
    rewrite HB0, (proj2 (Cmod0 C0) eq_refl). cbn [Wn]. rewrite Rmult_0_r. lra.
  - rewrite (bracket_recur zeta h n Hz Hzh).
    eapply Rle_trans; [ apply Cmod_triangle | ].
    assert (Hmpp : 0 < Cmod (Cminus zeta h)) by lra.
    assert (Hzp : 0 < Cmod zeta) by lra.
    assert (Hhh : 0 <= Cmod h * Cmod h) by (apply Rmult_le_pos; apply Cmod_nonneg).
    assert (Hpowpos : 0 < m ^ S (S n)) by (apply pow_lt; exact Hm).
    assert (Hpowle : m ^ S (S n) <= (Cmod zeta) ^ S (S n))
      by (apply pow_incr; split; [ lra | exact Hmb ]).
    (* term 1:  |A.B_n| <= /mp . (|h|^2 Wn n) *)
    assert (Ht1 : Cmod (Cmul (Cinv (Cminus zeta h)) (Bn zeta h n))
                  <= / mp * (Cmod h * Cmod h * Wn mp m n)).
    { rewrite Cmod_mul, (Cmod_inv _ Hzh).
      apply Rle_trans with (/ Cmod (Cminus zeta h) * (Cmod h * Cmod h * Wn mp m n)).
      - apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; exact Hmpp
                                 | apply IH; assumption ].
      - apply Rmult_le_compat_r;
          [ apply Rmult_le_pos; [ exact Hhh | apply Wn_nonneg; assumption ]
          | apply Rinv_le_contravar; [ exact Hmp | exact Hmpb ] ]. }
    (* term 2:  <= |h|^2 . INR(S n) / (mp . m^{S(S n)}) *)
    assert (Ha : / Cmod (Cminus zeta h) <= / mp)
      by (apply Rinv_le_contravar; [ exact Hmp | exact Hmpb ]).
    assert (Hb : / (Cmod zeta) ^ S (S n) <= / m ^ S (S n))
      by (apply Rinv_le_contravar; [ exact Hpowpos | exact Hpowle ]).
    assert (Ht2 : Cmod (Cmul (RtoC (INR (S n)))
                    (Cmul (Cmul h h)
                          (Cmul (Cinv (Cminus zeta h)) (Cinv (Cpow zeta (S (S n)))))))
                  <= Cmod h * Cmod h * (INR (S n) * / (mp * m ^ S (S n)))).
    { rewrite !Cmod_mul, Cmod_RtoC, (Rabs_right (INR (S n))) by (apply Rle_ge, pos_INR).
      rewrite (Cmod_inv _ Hzh), (Cmod_inv _ (Cpow_ne0 _ _ Hz)), Cmod_Cpow.
      apply Rle_trans with (INR (S n) * (Cmod h * Cmod h * (/ mp * / m ^ S (S n)))).
      - apply Rmult_le_compat_l; [ apply pos_INR | ].
        apply Rmult_le_compat_l; [ exact Hhh | ].
        apply Rmult_le_compat;
          [ left; apply Rinv_0_lt_compat; exact Hmpp
          | left; apply Rinv_0_lt_compat, pow_lt; exact Hzp
          | exact Ha | exact Hb ].
      - apply Req_le. rewrite Rinv_mult. ring. }
    eapply Rle_trans; [ apply Rplus_le_compat; [ exact Ht1 | exact Ht2 ] | ].
    cbn [Wn]. apply Req_le. ring.
Qed.

(* ================================================================= *)
(*  The ML integral estimate for the difference quotient              *)
(* ================================================================= *)

Section CauchyEst.
Variable g : C -> C.
Variable Rr : R.
Variable w0 : C.
Hypothesis HR : 0 < Rr.
Hypothesis Hw0 : Cmod w0 < Rr.
Hypothesis Hg : CcontC g.

(* the half-distance to the circle *)
Definition dd := Rr - Cmod w0.
Lemma dd_pos : 0 < dd. Proof. unfold dd; lra. Qed.

(* lower bounds for the two denominators on the circle *)
Lemma arc_w0_lb : forall u, dd <= Cmod (Cminus (arc Rr u) w0).
Proof.
  intro u. unfold dd. eapply Rle_trans; [ | apply Cmod_rev_triangle ].
  rewrite (Cmod_arc Rr u) by lra. lra.
Qed.

Lemma arc_w0_ne : forall u, Cminus (arc Rr u) w0 <> C0.
Proof.
  intros u Hc. pose proof (arc_w0_lb u) as H. pose proof dd_pos.
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

Lemma arc_w0h_lb : forall u h, dd - Cmod h <= Cmod (Cminus (arc Rr u) (Cadd w0 h)).
Proof.
  intros u h. unfold dd. eapply Rle_trans; [ | apply Cmod_rev_triangle ].
  rewrite (Cmod_arc Rr u) by lra.
  pose proof (Cmod_triangle w0 h). lra.
Qed.

Lemma arc_w0h_ne : forall u h, Cmod h < dd -> Cminus (arc Rr u) (Cadd w0 h) <> C0.
Proof.
  intros u h Hh Hc. pose proof (arc_w0h_lb u h) as H.
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

(* the three integrands (in the path parameter u) *)
Definition Kw (w : C) (u : R) : C :=
  Cmul (Cmul (g (arc Rr u)) (Cinv (Cminus (arc Rr u) w))) (arc' Rr u).
Definition K2 (u : R) : C :=
  Cmul (Cmul (g (arc Rr u))
             (Cinv (Cmul (Cminus (arc Rr u) w0) (Cminus (arc Rr u) w0)))) (arc' Rr u).
Definition Brem (h : C) (u : R) : C :=
  Cmul (Cmul (g (arc Rr u))
             (Cmul (Cmul h h)
                   (Cinv (Cmul (Cminus (Cminus (arc Rr u) w0) h)
                               (Cmul (Cminus (arc Rr u) w0) (Cminus (arc Rr u) w0))))))
       (arc' Rr u).

(* continuity of the integrands *)
Lemma Kw_cont : forall w, (forall u, Cminus (arc Rr u) w <> C0) -> Ccont (Kw w).
Proof.
  intros w Hne; unfold Kw. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hg (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ] | exact Hne ].
Qed.

Lemma K2_cont : Ccont K2.
Proof.
  unfold K2. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hg (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv;
    [ apply Ccont_mul; apply Ccont_minus; solve [ exact (Ccont_arc Rr) | apply Ccont_const ]
    | intro u; apply Cmul_ne0; apply arc_w0_ne ].
Qed.

Lemma Brem_cont : forall h, Cmod h < dd -> Ccont (Brem h).
Proof.
  intros h Hh; unfold Brem. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hg (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  apply Ccont_inv.
  - apply Ccont_mul.
    + apply Ccont_minus; [ apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ]
                         | apply Ccont_const ].
    + apply Ccont_mul; apply Ccont_minus; solve [ exact (Ccont_arc Rr) | apply Ccont_const ].
  - intro u. apply Cmul_ne0;
      [ (* arc - w0 - h <> 0 *)
        replace (Cminus (Cminus (arc Rr u) w0) h) with (Cminus (arc Rr u) (Cadd w0 h)) by ring;
        apply arc_w0h_ne; exact Hh
      | apply Cmul_ne0; apply arc_w0_ne ].
Qed.

(* the pointwise identity:  Kw(w0+h) - Kw(w0) - h.K2 = Brem h *)
Lemma Brem_eq : forall h u, Cmod h < dd ->
  Cminus (Cminus (Kw (Cadd w0 h) u) (Kw w0 u)) (Cmul h (K2 u)) = Brem h u.
Proof.
  intros h u Hh. unfold Kw, K2, Brem.
  replace (Cminus (arc Rr u) (Cadd w0 h)) with (Cminus (Cminus (arc Rr u) w0) h) by ring.
  rewrite <- (cauchy_bracket (Cminus (arc Rr u) w0) h (arc_w0_ne u)).
  - ring.
  - replace (Cminus (Cminus (arc Rr u) w0) h) with (Cminus (arc Rr u) (Cadd w0 h)) by ring.
    apply arc_w0h_ne; exact Hh.
Qed.

(* the difference-quotient remainder is a single integral of Brem *)
Lemma cauchy_diff_int : forall h
  (HA : Ccont (Kw (Cadd w0 h))) (HB : Ccont (Kw w0)) (HC : Ccont K2) (HD : Ccont (Brem h)),
  Cmod h < dd ->
  Cminus (Cminus (Cintf (Kw (Cadd w0 h)) HA 0 (2 * PI)) (Cintf (Kw w0) HB 0 (2 * PI)))
         (Cmul h (Cintf K2 HC 0 (2 * PI)))
  = Cintf (Brem h) HD 0 (2 * PI).
Proof.
  intros h HA HB HC HD Hh.
  assert (Hpi : 0 <= 2 * PI) by (generalize PI_RGT_0; lra).
  assert (Hsub1 : Ccont (fun u => Cminus (Kw (Cadd w0 h) u) (Kw w0 u)))
    by (apply Ccont_sub; assumption).
  assert (Hhk2 : Ccont (fun u => Cmul h (K2 u))) by (apply Ccont_scal; exact HC).
  rewrite <- (Cintf_sub (Kw (Cadd w0 h)) (Kw w0) HA HB Hsub1 0 (2 * PI) Hpi).
  rewrite <- (Cintf_cmul_l h K2 HC Hhk2 0 (2 * PI) Hpi).
  rewrite <- (Cintf_sub (fun u => Cminus (Kw (Cadd w0 h) u) (Kw w0 u))
               (fun u => Cmul h (K2 u)) Hsub1 Hhk2
               (Ccont_sub _ _ Hsub1 Hhk2) 0 (2 * PI) Hpi).
  apply (Cintf_ext _ (Brem h) (Ccont_sub _ _ Hsub1 Hhk2) HD 0 (2 * PI)).
  intro u. apply Brem_eq; exact Hh.
Qed.

(* THE ESTIMATE: the remainder integral is O(|h|^2) *)
Theorem cauchy_est : forall (Mg : R), 0 <= Mg -> (forall u, Cmod (g (arc Rr u)) <= Mg) ->
  forall h (HA : Ccont (Kw (Cadd w0 h))) (HB : Ccont (Kw w0)) (HC : Ccont K2) (HD : Ccont (Brem h)),
  Cmod h < dd / 2 ->
  Cmod (Cminus (Cminus (Cintf (Kw (Cadd w0 h)) HA 0 (2 * PI)) (Cintf (Kw w0) HB 0 (2 * PI)))
               (Cmul h (Cintf K2 HC 0 (2 * PI))))
  <= 2 * (Mg * Rr * / (dd / 2 * (dd * dd))) * (2 * PI) * (Cmod h * Cmod h).
Proof.
  intros Mg HMg Hgb h HA HB HC HD Hh.
  pose proof dd_pos as Hdd.
  assert (Hhdd : Cmod h < dd) by lra.
  rewrite (cauchy_diff_int h HA HB HC HD Hhdd).
  set (M := Mg * Rr * / (dd / 2 * (dd * dd)) * (Cmod h * Cmod h)).
  assert (HBrem : forall u, 0 <= u <= 2 * PI -> Cmod (Brem h u) <= M).
  { intros u _. unfold Brem, M.
    rewrite Cmod_mul, (Cmod_arc' Rr u ltac:(lra)), Cmod_mul.
    (* Cmod(g) * Cmod(bracket_hsq) * Rr *)
    set (zeta := Cminus (arc Rr u) w0).
    assert (Hbb : Cmod (Cmul (Cmul h h)
                   (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))))
               <= Cmod h * Cmod h * / (dd / 2 * (dd * dd))).
    { apply (cauchy_bracket_bound zeta h dd (dd / 2)).
      - unfold zeta; apply arc_w0_ne.
      - unfold zeta;
          replace (Cminus (Cminus (arc Rr u) w0) h) with (Cminus (arc Rr u) (Cadd w0 h)) by ring;
          apply arc_w0h_ne; lra.
      - lra.
      - unfold zeta;
          replace (Cminus (Cminus (arc Rr u) w0) h) with (Cminus (arc Rr u) (Cadd w0 h)) by ring;
          eapply Rle_trans; [ | apply arc_w0h_lb ]; lra.
      - exact Hdd.
      - unfold zeta; apply arc_w0_lb. }
    (* assemble: |g| |bracket| Rr <= Mg (|h|^2/(dd/2 (dd dd))) Rr *)
    apply Rle_trans with (Mg * (Cmod h * Cmod h * / (dd / 2 * (dd * dd))) * Rr).
    - apply Rmult_le_compat_r; [ lra | ].
      apply Rmult_le_compat; [ apply Cmod_nonneg | apply Cmod_nonneg | apply Hgb | exact Hbb ].
    - apply Req_le. ring. }
  eapply Rle_trans; [ apply (Cintf_ML (Brem h) HD 0 (2 * PI) M ltac:(generalize PI_RGT_0; lra) HBrem) | ].
  unfold M. apply Req_le. ring.
Qed.

(* ---- is_Cderiv packaging: the Cauchy integral is holomorphic in w ---- *)
Theorem cauchy_type_holo1 : forall (Mg : R), 0 <= Mg -> (forall u, Cmod (g (arc Rr u)) <= Mg) ->
  forall (Phi : C -> C) (HK2 : Ccont K2),
  (forall w (Hc : Ccont (Kw w)), Cmod (Cminus w w0) < dd / 2 ->
     Phi w = Cintf (Kw w) Hc 0 (2 * PI)) ->
  is_Cderiv Phi w0 (Cintf K2 HK2 0 (2 * PI)).
Proof.
  intros Mg HMg Hgb Phi HK2 Hagree eps Heps.
  pose proof dd_pos as Hdd.
  set (C := 2 * (Mg * Rr * / (dd / 2 * (dd * dd))) * (2 * PI)).
  assert (Hden : 0 < dd / 2 * (dd * dd)) by (apply Rmult_lt_0_compat; nra).
  assert (HC0 : 0 <= C).
  { unfold C. apply Rmult_le_pos; [ | generalize PI_RGT_0; lra ].
    apply Rmult_le_pos; [ lra | ].
    apply Rmult_le_pos; [ apply Rmult_le_pos; [ exact HMg | lra ] | left; apply Rinv_0_lt_compat; exact Hden ]. }
  exists (Rmin (dd / 2) (eps / (C + 1))). split.
  { apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; [ exact Heps | lra ] ]. }
  intros h Hh.
  assert (Hhalf : Cmod h < dd / 2) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hheps : Cmod h < eps / (C + 1)) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (HcW0 : Ccont (Kw w0)) by (apply Kw_cont; apply arc_w0_ne).
  assert (HcWh : Ccont (Kw (Cadd w0 h))) by (apply Kw_cont; intro u; apply arc_w0h_ne; lra).
  assert (HcBrem : Ccont (Brem h)) by (apply Brem_cont; lra).
  rewrite (Hagree (Cadd w0 h) HcWh
             ltac:(replace (Cminus (Cadd w0 h) w0) with h by ring; exact Hhalf)).
  rewrite (Hagree w0 HcW0
             ltac:(replace (Cminus w0 w0) with C0 by ring;
                   rewrite (proj2 (Cmod0 C0) eq_refl); lra)).
  replace (Cmul (Cintf K2 HK2 0 (2 * PI)) h)
     with (Cmul h (Cintf K2 HK2 0 (2 * PI))) by ring.
  eapply Rle_trans; [ apply (cauchy_est Mg HMg Hgb h HcWh HcW0 HK2 HcBrem Hhalf) | ].
  fold C.
  (* C * |h|^2 <= eps * |h| *)
  assert (Hmh : 0 <= Cmod h) by apply Cmod_nonneg.
  assert (Hlt : Cmod h * (C + 1) < eps).
  { apply (Rmult_lt_reg_r (/ (C + 1))); [ apply Rinv_0_lt_compat; lra | ].
    rewrite Rmult_assoc. rewrite Rinv_r by lra. rewrite Rmult_1_r.
    unfold Rdiv in Hheps. exact Hheps. }
  nra.
Qed.

End CauchyEst.

Print Assumptions cauchy_bracket.
Print Assumptions cauchy_est.
Print Assumptions cauchy_type_holo1.
