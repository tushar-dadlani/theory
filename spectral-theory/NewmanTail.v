(* ================================================================= *)
(*  NewmanTail.v  --  the exponential tail bound for LTN, and the      *)
(*  full transform gN.  Brick E3 of docs/pnt_endgame_plan.md.          *)
(*                                                                    *)
(*  LaplaceFull.LT_tail_bound proves the same estimate for the         *)
(*  continuous case, but via Cintf_mod_le2 (|int f| <= int |f|), which *)
(*  needs Cmod (lint z u) INTEGRABLE -- there obtained from continuity.*)
(*  Cmod (lintN z u) is discontinuous, so that route would cost        *)
(*  another cell argument.  Bounding the two COMPONENTS separately     *)
(*  against the continuous majorant B*exp(-Re z*t) avoids it entirely, *)
(*  at the cost of the same factor 2 already in CintfD_ML.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus CIntegral2 CExpKernel
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV
        CIntegralD LaplaceFull NewmanTransform.
Open Scope R_scope.

Theorem LTN_tail : forall z a b Ha Hab, 0 < Re z ->
  Cmod (LTN z a b Ha Hab)
  <= 2 * ((Kup + 1) * (exp (- (Re z * a)) - exp (- (Re z * b))) / Re z).
Proof.
  intros z a b Ha Hab Hz.
  assert (prU : Riemann_integrable (fun t => (Kup + 1) * exp (- (Re z * t))) a b)
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros u _; apply Bexp_cont ]).
  assert (prL : Riemann_integrable (fun t => (- (Kup + 1)) * exp (- (Re z * t))) a b)
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros u _; apply Bexp_cont ]).
  assert (HU : RiemannInt prU
               = (Kup + 1) * (exp (- (Re z * a)) - exp (- (Re z * b))) / Re z)
    by (apply exp_int_AB_scaled; assumption).
  assert (HL : RiemannInt prL
               = (- (Kup + 1)) * (exp (- (Re z * a)) - exp (- (Re z * b))) / Re z)
    by (apply exp_int_AB_scaled; assumption).
  (* the pointwise majorant, on the open interval *)
  assert (Hpt : forall u, a < u < b ->
            Cmod (lintN z u) <= (Kup + 1) * exp (- (Re z * u))).
  { intros u Hu.
    assert (Hu0 : 0 <= u) by lra.
    pose proof (Cmod_lintN z u) as HM.
    replace (- Re z * u) with (- (Re z * u)) in HM by ring.
    pose proof (nf_bound u Hu0) as HB.
    pose proof (exp_pos (- (Re z * u))) as Hep.
    rewrite HM. nra. }
  (* each component is squeezed between the two majorant integrals *)
  assert (HReU : RiemannInt (lintN_Re_int z a b Ha Hab) <= RiemannInt prU).
  { apply (RiemannInt_P19 _ prU Hab). intros x Hx.
    pose proof (Hpt x Hx) as H. pose proof (Rabs_Re_le4 (lintN z x)) as HR.
    pose proof (Rabs_pos (Re (lintN z x))) as Hp.
    unfold Rabs in HR; destruct (Rcase_abs (Re (lintN z x))); lra. }
  assert (HReL : RiemannInt prL <= RiemannInt (lintN_Re_int z a b Ha Hab)).
  { apply (RiemannInt_P19 prL _ Hab). intros x Hx.
    pose proof (Hpt x Hx) as H. pose proof (Rabs_Re_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Re (lintN z x))); lra. }
  assert (HImU : RiemannInt (lintN_Im_int z a b Ha Hab) <= RiemannInt prU).
  { apply (RiemannInt_P19 _ prU Hab). intros x Hx.
    pose proof (Hpt x Hx) as H. pose proof (Rabs_Im_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Im (lintN z x))); lra. }
  assert (HImL : RiemannInt prL <= RiemannInt (lintN_Im_int z a b Ha Hab)).
  { apply (RiemannInt_P19 prL _ Hab). intros x Hx.
    pose proof (Hpt x Hx) as H. pose proof (Rabs_Im_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Im (lintN z x))); lra. }
  eapply Rle_trans; [ apply Cmod_le_ReIm4 | ].
  unfold LTN. rewrite Re_CintfD, Im_CintfD.
  rewrite HU in HReU, HImU. rewrite HL in HReL, HImL.
  unfold Rabs;
    destruct (Rcase_abs (RiemannInt (lintN_Re_int z a b Ha Hab)));
    destruct (Rcase_abs (RiemannInt (lintN_Im_int z a b Ha Hab))); lra.
Qed.

(* the tail proper: a >= 0, b arbitrary above it *)
Corollary LTN_tail_le : forall z a b Ha Hab, 0 < Re z ->
  Cmod (LTN z a b Ha Hab) <= 2 * (Kup + 1) * exp (- (Re z * a)) / Re z.
Proof.
  intros z a b Ha Hab Hz.
  eapply Rle_trans; [ apply LTN_tail; exact Hz | ].
  pose proof (exp_pos (- (Re z * b))) as H1.
  pose proof (exp_pos (- (Re z * a))) as H2.
  pose proof Kup_pos as HK.
  assert (Hinv : 0 < / Re z) by (apply Rinv_0_lt_compat; exact Hz).
  assert (Hnum : (Kup + 1) * (exp (- (Re z * a)) - exp (- (Re z * b)))
                 <= (Kup + 1) * exp (- (Re z * a))) by nra.
  unfold Rdiv. nra.
Qed.

Print Assumptions LTN_tail.
Print Assumptions LTN_tail_le.

(* ================================================================= *)
(*  The full transform gN, as the T -> oo limit.                       *)
(* ================================================================= *)

Lemma Cmod_min_sym : forall a b : C, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof.
  intros a b. unfold Cmod, Cnorm2, Cminus; cbn [Re Im]. f_equal. ring.
Qed.

Section GN.
Variable z : C.
Hypothesis Hz : 0 < Re z.

Definition LTNn (n : nat) : C := LTN z 0 (INR n) (Rle_refl 0) (pos_INR n).
Definition tailN (n : nat) : R :=
  2 * (Kup + 1) * exp (- (Re z * INR n)) / Re z.

Lemma tailN_nonneg : forall n, 0 <= tailN n.
Proof.
  intro n. unfold tailN, Rdiv.
  pose proof Kup_pos as HK. pose proof (exp_pos (- (Re z * INR n))) as HE.
  assert (Hinv : 0 < / Re z) by (apply Rinv_0_lt_compat; exact Hz).
  apply Rmult_le_pos; [ apply Rmult_le_pos; lra | lra ].
Qed.

Lemma tailN_dec : forall m n, (m <= n)%nat -> tailN n <= tailN m.
Proof.
  intros m n Hmn. unfold tailN.
  assert (HI : INR m <= INR n) by (apply le_INR; exact Hmn).
  assert (Hexp : exp (- (Re z * INR n)) <= exp (- (Re z * INR m))).
  { destruct (Rle_lt_or_eq_dec (- (Re z * INR n)) (- (Re z * INR m)) ltac:(nra))
      as [H | H]; [ left; apply exp_increasing; exact H | rewrite H; apply Rle_refl ]. }
  pose proof Kup_pos as HK.
  assert (Hinv : 0 < / Re z) by (apply Rinv_0_lt_compat; exact Hz).
  unfold Rdiv.
  apply Rmult_le_compat_r; [ lra | ].
  apply Rmult_le_compat_l; [ lra | exact Hexp ].
Qed.

Lemma tailN_cv0 : Un_cv tailN 0.
Proof.
  assert (Hinf : cv_infty (fun n => Re z * INR n))
    by (apply cv_infty_scal_pos; [ exact Hz | apply cv_infty_INR_loc ]).
  pose proof (exp_neg_cv0 _ Hinf) as Hexp.
  pose proof (Un_cv_cscal_R _ _ (2 * (Kup + 1) / Re z) Hexp) as Hsc.
  intros eps Heps. destruct (Hsc eps Heps) as [N HN]. exists N; intros n Hn.
  specialize (HN n Hn). unfold R_dist in *.
  replace (tailN n - 0)
    with (2 * (Kup + 1) / Re z * exp (- (Re z * INR n)) - 2 * (Kup + 1) / Re z * 0)
    by (unfold tailN; field; lra).
  exact HN.
Qed.

Lemma LTNn_close : forall m n, (m <= n)%nat ->
  Cmod (Cminus (LTNn n) (LTNn m)) <= tailN m.
Proof.
  intros m n Hmn.
  assert (Hmn' : INR m <= INR n) by (apply le_INR; exact Hmn).
  assert (Hsplit : Cadd (LTN z 0 (INR m) (Rle_refl 0) (pos_INR m))
                        (LTN z (INR m) (INR n) (pos_INR m) Hmn')
                   = LTN z 0 (INR n) (Rle_refl 0) (pos_INR n))
    by apply LTN_split.
  assert (Heq : Cminus (LTNn n) (LTNn m)
                = LTN z (INR m) (INR n) (pos_INR m) Hmn')
    by (unfold LTNn; rewrite <- Hsplit; ring).
  rewrite Heq. unfold tailN. apply LTN_tail_le; exact Hz.
Qed.

Lemma LTNn_close_sym : forall m n,
  Cmod (Cminus (LTNn m) (LTNn n)) <= tailN (Nat.min m n).
Proof.
  intros m n. destruct (le_gt_dec m n) as [H | H].
  - rewrite Cmod_min_sym, (Nat.min_l m n H). apply LTNn_close; exact H.
  - rewrite (Nat.min_r m n ltac:(lia)). apply LTNn_close; lia.
Qed.

Lemma LTNn_Re_cauchy : Cauchy_crit (fun n => Re (LTNn n)).
Proof.
  intros eps Heps. destruct (tailN_cv0 eps Heps) as [N HN].
  exists N; intros m n Hm Hn; unfold R_dist.
  apply Rle_lt_trans with (Cmod (Cminus (LTNn m) (LTNn n))).
  - replace (Re (LTNn m) - Re (LTNn n)) with (Re (Cminus (LTNn m) (LTNn n)))
      by (unfold Cminus; cbn [Re]; ring).
    apply Rabs_Re_le4.
  - apply Rle_lt_trans with (tailN (Nat.min m n)); [ apply LTNn_close_sym | ].
    apply Rle_lt_trans with (tailN N);
      [ apply tailN_dec; apply Nat.min_glb; assumption | ].
    pose proof (HN N (Nat.le_refl N)) as H; unfold R_dist in H.
    rewrite Rminus_0_r, Rabs_pos_eq in H by apply tailN_nonneg. exact H.
Qed.

Lemma LTNn_Im_cauchy : Cauchy_crit (fun n => Im (LTNn n)).
Proof.
  intros eps Heps. destruct (tailN_cv0 eps Heps) as [N HN].
  exists N; intros m n Hm Hn; unfold R_dist.
  apply Rle_lt_trans with (Cmod (Cminus (LTNn m) (LTNn n))).
  - replace (Im (LTNn m) - Im (LTNn n)) with (Im (Cminus (LTNn m) (LTNn n)))
      by (unfold Cminus; cbn [Im]; ring).
    apply Rabs_Im_le4.
  - apply Rle_lt_trans with (tailN (Nat.min m n)); [ apply LTNn_close_sym | ].
    apply Rle_lt_trans with (tailN N);
      [ apply tailN_dec; apply Nat.min_glb; assumption | ].
    pose proof (HN N (Nat.le_refl N)) as H; unfold R_dist in H.
    rewrite Rminus_0_r, Rabs_pos_eq in H by apply tailN_nonneg. exact H.
Qed.

Definition gN : C :=
  mkC (proj1_sig (R_complete _ LTNn_Re_cauchy))
      (proj1_sig (R_complete _ LTNn_Im_cauchy)).

Lemma gN_Re_cv : Un_cv (fun n => Re (LTNn n)) (Re gN).
Proof. exact (proj2_sig (R_complete _ LTNn_Re_cauchy)). Qed.

Lemma gN_Im_cv : Un_cv (fun n => Im (LTNn n)) (Im gN).
Proof. exact (proj2_sig (R_complete _ LTNn_Im_cauchy)). Qed.

End GN.

Print Assumptions gN_Re_cv.
