(* ================================================================= *)
(*  NewmanCellSum.v  --  reconciling the honest transform LTN with     *)
(*  NewmanIdentity's cell sums.  Core of brick E4.                     *)
(*                                                                    *)
(*    LTN z 0 (ln (INR (S (S M)))) = StepSum z M - OneSum z M          *)
(*                                                                    *)
(*  On each open cell (ln(k+1), ln(k+2)) Newman's integrand is         *)
(*      nf(t) e^{-zt} = psi(k+1) e^{-(z+1)t} - e^{-zt},                *)
(*  because nf t = psiR(e^t)/e^t - 1 and psiR(e^t) is CONSTANT there.  *)
(*  Both terms on the right are continuous, so the honest CintfD       *)
(*  integral collapses to Cintf and splits by Cintf_sub/Cintf_cmul_l   *)
(*  into exactly StepSum's and OneSum's k-th summands.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus CSeries CIntegral2 CExpKernel CLeibniz
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV
        CIntegralD NewmanTransform PiecewiseTransform CellAdditivity
        CVonMangoldtSeries NewmanIdentity.
Open Scope R_scope.

(* e^{-(z+1)t} = e^{-t} * e^{-zt} *)
Lemma cexpzt_shift : forall z t,
  cexpzt (Copp (Cadd z C1)) t = Cmul (RtoC (exp (- t))) (cexpzt (Copp z) t).
Proof.
  intros z t. rewrite !cexpzt_mkC.
  unfold Cmul, RtoC, Copp, Cadd, C1; cbn [Re Im].
  assert (Hsplit : - (Re z + 1) * t = - Re z * t + - t) by ring.
  apply Ceq; cbn [Re Im]; rewrite Hsplit, exp_plus;
    replace (- (Im z + 0) * t) with (- Im z * t) by ring; ring.
Qed.

(* the pointwise cell identity *)
Lemma lintN_cell_id : forall z k t,
  ln (INR (S k)) < t < ln (INR (S (S k))) ->
  lintN z t = Cminus (Cmul (RtoC (psi (S k))) (cexpzt (Copp (Cadd z C1)) t))
                     (cexpzt (Copp z) t).
Proof.
  intros z k t Ht.
  assert (Hpsi : psiR (exp t) = psi (S k))
    by (apply (psiRexp_const_cell (S k) t ltac:(lia)); exact Ht).
  assert (Hex : 0 < exp t) by apply exp_pos.
  assert (Hinv : exp (- t) = / exp t) by (rewrite exp_Ropp; reflexivity).
  rewrite cexpzt_shift.
  unfold lintN, nfC. rewrite nf_closed_form, Hpsi.
  rewrite Hinv.
  unfold Cmul, Cminus, RtoC; apply Ceq; cbn [Re Im]; field; lra.
Qed.

(* the cell integral *)
Lemma LTN_cell : forall z k Hk Hkk,
  LTN z (ln (INR (S k))) (ln (INR (S (S k)))) Hk Hkk
  = Cminus (Cmul (RtoC (psi (S k)))
              (Cintf (fun t => cexpzt (Copp (Cadd z C1)) t)
                     (Ccont_cexpzt (Copp (Cadd z C1)))
                     (ln (INR (S k))) (ln (INR (S (S k))))))
           (Cintf (fun t => cexpzt (Copp z) t) (Ccont_cexpzt (Copp z))
                  (ln (INR (S k))) (ln (INR (S (S k))))).
Proof.
  intros z k Hk Hkk.
  assert (Hsc : Ccont (fun t => Cmul (RtoC (psi (S k)))
                                  (cexpzt (Copp (Cadd z C1)) t)))
    by (apply Ccont_scal, Ccont_cexpzt).
  assert (HG : Ccont (fun t => Cminus (Cmul (RtoC (psi (S k)))
                                        (cexpzt (Copp (Cadd z C1)) t))
                                      (cexpzt (Copp z) t)))
    by (apply Ccont_sub; [ exact Hsc | apply Ccont_cexpzt ]).
  assert (prRe : Riemann_integrable
                   (fun t => Re (Cminus (Cmul (RtoC (psi (S k)))
                                          (cexpzt (Copp (Cadd z C1)) t))
                                        (cexpzt (Copp z) t)))
                   (ln (INR (S k))) (ln (INR (S (S k)))))
    by (apply continuity_implies_RiemannInt;
        [ exact Hkk | intros x _; apply (proj1 HG) ]).
  assert (prIm : Riemann_integrable
                   (fun t => Im (Cminus (Cmul (RtoC (psi (S k)))
                                          (cexpzt (Copp (Cadd z C1)) t))
                                        (cexpzt (Copp z) t)))
                   (ln (INR (S k))) (ln (INR (S (S k)))))
    by (apply continuity_implies_RiemannInt;
        [ exact Hkk | intros x _; apply (proj2 HG) ]).
  unfold LTN.
  rewrite (CintfD_ext_open (lintN z)
             (fun t => Cminus (Cmul (RtoC (psi (S k)))
                                (cexpzt (Copp (Cadd z C1)) t))
                              (cexpzt (Copp z) t))
             _ _ _ _ prRe prIm Hkk (fun t Ht => lintN_cell_id z k t Ht)).
  rewrite (CintfD_Cintf _ HG _ _ prRe prIm).
  rewrite (Cintf_sub _ _ Hsc (Ccont_cexpzt (Copp z)) HG _ _ Hkk).
  rewrite (Cintf_cmul_l _ _ (Ccont_cexpzt (Copp (Cadd z C1))) Hsc _ _ Hkk).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Summing the cells.                                                *)
(* ----------------------------------------------------------------- *)

Lemma LTN_endpoint : forall z a a' b Ha Hab Ha' Hab', a = a' ->
  LTN z a b Ha Hab = LTN z a' b Ha' Hab'.
Proof. intros z a a' b Ha Hab Ha' Hab' Heq. subst a'. apply LTN_irrel. Qed.

Lemma ln_SS_nonneg : forall k, 0 <= ln (INR (S k)).
Proof.
  intro k. rewrite <- ln_1. apply ln_mono_le; [ lra | ].
  replace 1 with (INR 1) by (simpl; ring). apply le_INR. lia.
Qed.

Lemma ln_SS_mono : forall k, ln (INR (S k)) <= ln (INR (S (S k))).
Proof.
  intro k. apply ln_mono_le.
  - apply lt_0_INR; lia.
  - apply le_INR; lia.
Qed.

Theorem LTN_stepsum : forall z M H0 HT,
  LTN z 0 (ln (INR (S (S M)))) H0 HT = Cminus (StepSum z M) (OneSum z M).
Proof.
  intros z M. induction M as [| M IH]; intros H0 HT.
  - assert (Hln1 : (0:R) = ln (INR 1)) by (simpl; rewrite ln_1; reflexivity).
    rewrite (LTN_endpoint z 0 (ln (INR 1)) (ln (INR 2)) H0 HT
               (ln_SS_nonneg 0) (ln_SS_mono 0) Hln1).
    rewrite (LTN_cell z 0 (ln_SS_nonneg 0) (ln_SS_mono 0)).
    unfold StepSum, OneSum; cbn [Cpsum]. reflexivity.
  - assert (HTm : (0:R) <= ln (INR (S (S M)))) by apply ln_SS_nonneg.
    assert (Hkk : ln (INR (S (S M))) <= ln (INR (S (S (S M)))))
      by apply (ln_SS_mono (S M)).
    assert (Hsplit : Cadd (LTN z 0 (ln (INR (S (S M)))) H0 HTm)
                          (LTN z (ln (INR (S (S M)))) (ln (INR (S (S (S M)))))
                             HTm Hkk)
                     = LTN z 0 (ln (INR (S (S (S M))))) H0 HT)
      by apply LTN_split.
    rewrite <- Hsplit, (IH H0 HTm), (LTN_cell z (S M) HTm Hkk).
    unfold StepSum, OneSum; cbn [Cpsum]. ring.
Qed.

Print Assumptions LTN_cell.
Print Assumptions LTN_stepsum.
