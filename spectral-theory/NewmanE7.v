(* ================================================================= *)
(*  NewmanE7.v  --  brick E7: the triple limit, and PNT.               *)
(*                                                                    *)
(*  NewmanE6.newman_bound gives, for every admissible (R, d, alpha, T),*)
(*                                                                    *)
(*    |g(0) - g_T(0)| * 2pi                                            *)
(*        <= (24 pi B + 4 pi M d)/R + 4 M R (1/d + 1/R) e^{-dT}.       *)
(*                                                                    *)
(*  The three parameters must be chosen in THIS order, and no other:   *)
(*                                                                    *)
(*    R first, killing 24 pi B/R -- B = Kup + 1 is absolute;           *)
(*    then d, killing 4 pi M d/R -- and M is a bound for g near the    *)
(*      imaginary axis, which depends on R but NOT on d (that is what  *)
(*      CStripBound.strip_bounded buys, and why it is stated on a      *)
(*      strip rather than on the chord itself);                        *)
(*    then T, killing the last term, whose constant depends on both.   *)
(*                                                                    *)
(*  The conclusion is that g_T(0) -> g(0), i.e. int_0^T nf converges;  *)
(*  Cauchy-ness of that is TintCoV.NfCauchy, which closes PNT.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        CIntegral2 CSegInt CPathIntegral CExpKernel CExpEntire
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV
        CIntegralD PerronRemovable PrimePowerReindex
        NewmanTransform NewmanGExt NewmanCutoff BfnUniform
        CStripBound NewmanContour NewmanE6.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  exp (-cT) eventually undercuts any positive bound.                 *)
(* ----------------------------------------------------------------- *)

Lemma exp_decay_below : forall c y, 0 < c -> 0 < y ->
  exists T0, 0 <= T0 /\ forall T, T0 <= T -> exp (- (c * T)) < y.
Proof.
  intros c y Hc Hy.
  set (T0 := Rmax 0 (ln (/ y) / c) + 1).
  assert (Hm1 := Rmax_l 0 (ln (/ y) / c)).
  assert (Hm2 := Rmax_r 0 (ln (/ y) / c)).
  exists T0; split; [ unfold T0; lra | ].
  intros T HT.
  assert (Hge : ln (/ y) / c + 1 <= T) by (unfold T0 in HT; lra).
  assert (Hlt : ln (/ y) < c * T).
  { apply Rmult_lt_reg_l with (/ c); [ apply Rinv_0_lt_compat; exact Hc | ].
    replace (/ c * (c * T)) with T by (field; lra).
    replace (/ c * ln (/ y)) with (ln (/ y) / c) by (unfold Rdiv; ring).
    lra. }
  rewrite (ln_Rinv y Hy) in Hlt.
  apply Rlt_le_trans with (exp (ln y));
    [ apply exp_increasing; lra | rewrite exp_ln by exact Hy; apply Rle_refl ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The transform at the origin is the plain integral of nf.           *)
(* ----------------------------------------------------------------- *)

Lemma lintN_at0 : forall t, lintN C0 t = RtoC (nf t).
Proof.
  intro t; unfold lintN, nfC, cexpzt.
  replace (Cmul (Copp C0) (RtoC t)) with C0 by (apply Ceq; cbn; ring).
  rewrite Cexpf_at0; ring.
Qed.

Lemma Re_LTN0 : forall a b (Ha : 0 <= a) (Hab : a <= b)
  (pr : Riemann_integrable nf a b),
  Re (LTN C0 a b Ha Hab) = RiemannInt pr.
Proof.
  intros a b Ha Hab pr; unfold LTN; rewrite Re_CintfD.
  apply RiemannInt_P18; [ exact Hab | ].
  intros x _; rewrite lintN_at0; reflexivity.
Qed.

(* ================================================================= *)
(*  The triple limit.                                                 *)
(* ================================================================= *)

Theorem gext_LTN_cv : forall eps, 0 < eps -> exists T0, 0 <= T0 /\
  forall T (HT : 0 <= T), T0 <= T ->
    Cmod (Cminus (gext C0) (LTN C0 0 T (Rle_refl 0) HT)) < eps.
Proof.
  intros eps Heps.
  pose proof PI_RGT_0 as HPI.
  pose proof Kup_pos as HKup.
  assert (HB : 0 < Kup + 1) by lra.
  (* --- (a) the radius --- *)
  set (Rc := 1 + 36 * (Kup + 1) / eps).
  assert (HRc : 0 < Rc).
  { unfold Rc; assert (0 < 36 * (Kup + 1) / eps)
      by (apply Rdiv_lt_0_compat; lra); lra. }
  assert (HRcv : eps * Rc = eps + 36 * (Kup + 1)) by (unfold Rc; field; lra).
  assert (Hstep1 : 12 * (Kup + 1) / Rc < eps / 3).
  { apply Rmult_lt_reg_r with (3 * Rc); [ lra | ].
    replace (12 * (Kup + 1) / Rc * (3 * Rc)) with (36 * (Kup + 1)) by (field; lra).
    replace (eps / 3 * (3 * Rc)) with (eps * Rc) by (field; lra).
    lra. }
  (* --- (b) the cutoff, the holomorphy width, and the strip bound --- *)
  destruct (gtrunc_ptcont (Rc + 1) ltac:(lra)) as [del [Hdel [Hptc Hagree]]].
  destruct (gext_holo_strip (Rc + 1) ltac:(lra)) as [d1 [Hd1 Hstr]].
  destruct (strip_bounded (gtrunc (Rc + 1) del) Hptc
              (ptcont_CcontC _ Hptc) Rc HRc) as [ds [Mg [Hds HMg]]].
  assert (HMg0 : 0 <= Mg).
  { assert (HR0 : Re C0 = 0) by reflexivity.
    assert (HI0 : Im C0 = 0) by reflexivity.
    eapply Rle_trans; [ apply Cmod_nonneg | apply HMg ];
      [ rewrite HR0 | rewrite HI0 ]; rewrite Rabs_R0; lra. }
  (* --- (c) the truncation depth --- *)
  set (dl := Rmin (Rmin (del / 4) (d1 / 2))
                  (Rmin (ds / 2) (Rmin (Rc / 2) (eps * Rc / (12 * (Mg + 1)))))).
  assert (Hq1 : dl <= del / 4)
    by (unfold dl; eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ]).
  assert (Hq2 : dl <= d1 / 2)
    by (unfold dl; eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ]).
  assert (Hq3 : dl <= ds / 2)
    by (unfold dl; eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ]).
  assert (Hq4 : dl <= Rc / 2)
    by (unfold dl; eapply Rle_trans; [ apply Rmin_r
        | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (Hq5 : dl <= eps * Rc / (12 * (Mg + 1)))
    by (unfold dl; eapply Rle_trans; [ apply Rmin_r
        | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
  assert (Hdl : 0 < dl).
  { unfold dl; repeat apply Rmin_glb_lt; try lra.
    apply Rdiv_lt_0_compat; lra. }
  assert (Hstep2 : 2 * Mg * dl / Rc <= eps / 6).
  { apply Rmult_le_reg_r with (6 * Rc); [ lra | ].
    replace (2 * Mg * dl / Rc * (6 * Rc)) with (12 * Mg * dl) by (field; lra).
    replace (eps / 6 * (6 * Rc)) with (eps * Rc) by (field; lra).
    assert (Hd : 12 * (Mg + 1) * dl <= eps * Rc).
    { apply Rmult_le_reg_r with (/ (12 * (Mg + 1)));
        [ apply Rinv_0_lt_compat; lra | ].
      replace (12 * (Mg + 1) * dl * / (12 * (Mg + 1))) with dl by (field; lra).
      replace (eps * Rc * / (12 * (Mg + 1))) with (eps * Rc / (12 * (Mg + 1)))
        by (unfold Rdiv; ring).
      exact Hq5. }
    nra. }
  (* --- (d) the angle --- *)
  destruct (alpha_of_delta Rc dl Hdl ltac:(lra)) as [alpha [Halpha Hchord]].
  (* --- (e) the truncation time --- *)
  assert (HK : 0 < / dl + / Rc)
    by (assert (0 < / dl) by (apply Rinv_0_lt_compat; lra);
        assert (0 < / Rc) by (apply Rinv_0_lt_compat; lra); lra).
  set (yb := eps * PI / (12 * (Mg + 1) * Rc * (/ dl + / Rc))).
  assert (Hyb : 0 < yb).
  { unfold yb; apply Rdiv_lt_0_compat.
    - apply Rmult_lt_0_compat; lra.
    - repeat apply Rmult_lt_0_compat; lra. }
  destruct (exp_decay_below dl yb Hdl Hyb) as [T0 [HT0 Hexp]].
  exists T0; split; [ exact HT0 | ].
  intros T HT HTge.
  (* --- the estimate --- *)
  assert (Hbd := newman_bound Rc dl del T alpha Mg HRc Hdl ltac:(lra) HT
                   Halpha Hchord
                   (fun z Hre Him => Hstr z ltac:(lra) Him)
                   Hagree Hptc
                   (fun z Hre Him => HMg z ltac:(lra) Him)).
  assert (HE := Hexp T HTge).
  assert (HEpos : 0 < exp (- (dl * T))) by apply exp_pos.
  (* the three summands *)
  assert (S1 : 24 * PI * (Kup + 1) / Rc < 2 * PI * (eps / 3)).
  { replace (24 * PI * (Kup + 1) / Rc) with (2 * PI * (12 * (Kup + 1) / Rc))
      by (field; lra).
    apply Rmult_lt_compat_l; lra. }
  assert (S2 : 4 * PI * Mg * dl / Rc <= 2 * PI * (eps / 6)).
  { replace (4 * PI * Mg * dl / Rc) with (2 * PI * (2 * Mg * dl / Rc))
      by (field; lra).
    apply Rmult_le_compat_l; lra. }
  assert (S3 : 4 * Mg * Rc * (/ dl + / Rc) * exp (- (dl * T)) <= PI * eps / 3).
  { assert (Hc : 0 <= 4 * Mg * Rc * (/ dl + / Rc))
      by (repeat apply Rmult_le_pos; lra).
    eapply Rle_trans.
    - apply Rmult_le_compat_l; [ exact Hc | left; exact HE ].
    - unfold yb.
      replace (4 * Mg * Rc * (/ dl + / Rc)
               * (eps * PI / (12 * (Mg + 1) * Rc * (/ dl + / Rc))))
        with (Mg / (Mg + 1) * (eps * PI / 3)) by (field; lra).
      assert (Hfr : Mg / (Mg + 1) <= 1).
      { apply Rmult_le_reg_r with (Mg + 1); [ lra | ].
        replace (Mg / (Mg + 1) * (Mg + 1)) with Mg by (field; lra); lra. }
      assert (Hpe : 0 <= eps * PI / 3) by (unfold Rdiv; nra).
      replace (PI * eps / 3) with (1 * (eps * PI / 3)) by (field; lra).
      apply Rmult_le_compat_r; assumption. }
  assert (Hsum : (24 * PI * (Kup + 1) + 4 * PI * Mg * dl) / Rc
                 + 4 * Mg * Rc * (/ dl + / Rc) * exp (- (dl * T))
                 < 2 * PI * eps).
  { replace ((24 * PI * (Kup + 1) + 4 * PI * Mg * dl) / Rc)
      with (24 * PI * (Kup + 1) / Rc + 4 * PI * Mg * dl / Rc) by (field; lra).
    nra. }
  apply Rmult_lt_reg_r with (2 * PI); [ lra | ].
  eapply Rle_lt_trans; [ exact Hbd | ].
  replace (eps * (2 * PI)) with (2 * PI * eps) by ring; exact Hsum.
Qed.

(* ================================================================= *)
(*  NfCauchy, and PNT.                                                *)
(* ================================================================= *)

Theorem newman_nf_cauchy : NfCauchy.
Proof.
  intros eps Heps.
  destruct (gext_LTN_cv (eps / 3) ltac:(lra)) as [T0 [HT0 Hcv]].
  exists T0; split; [ exact HT0 | ].
  intros a b Ha Hab pr.
  assert (Ha0 : 0 <= a) by lra.
  assert (Hb0 : 0 <= b) by lra.
  assert (Hbge : T0 <= b) by lra.
  assert (Hsplit : Cadd (LTN C0 0 a (Rle_refl 0) Ha0) (LTN C0 a b Ha0 Hab)
                 = LTN C0 0 b (Rle_refl 0) Hb0) by apply LTN_split.
  assert (Hd : LTN C0 a b Ha0 Hab
             = Cminus (Cminus (gext C0) (LTN C0 0 a (Rle_refl 0) Ha0))
                      (Cminus (gext C0) (LTN C0 0 b (Rle_refl 0) Hb0)))
    by (rewrite <- Hsplit; ring).
  assert (Hmod : Cmod (LTN C0 a b Ha0 Hab) < eps).
  { rewrite Hd.
    eapply Rle_lt_trans.
    - replace (Cminus (Cminus (gext C0) (LTN C0 0 a (Rle_refl 0) Ha0))
                      (Cminus (gext C0) (LTN C0 0 b (Rle_refl 0) Hb0)))
        with (Cadd (Cminus (gext C0) (LTN C0 0 a (Rle_refl 0) Ha0))
                   (Copp (Cminus (gext C0) (LTN C0 0 b (Rle_refl 0) Hb0))))
        by ring.
      eapply Rle_trans; [ apply Cmod_triangle | ]; rewrite Cmod_opp;
        apply Rle_refl.
    - assert (H1 := Hcv a Ha0 Ha); assert (H2 := Hcv b Hb0 Hbge); lra. }
  assert (Hre : Re (LTN C0 a b Ha0 Hab) = RiemannInt pr) by apply Re_LTN0.
  rewrite <- Hre.
  eapply Rle_lt_trans; [ apply Rabs_Re_le4 | exact Hmod ].
Qed.

Theorem PNT : Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof. apply pnt_of_nf_cauchy, newman_nf_cauchy. Qed.

Print Assumptions gext_LTN_cv.
Print Assumptions newman_nf_cauchy.
Print Assumptions PNT.

(* ================================================================= *)
(*  END NewmanE7.v -- the prime number theorem.                        *)
(* ================================================================= *)
