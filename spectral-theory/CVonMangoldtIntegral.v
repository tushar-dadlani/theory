(* ================================================================= *)
(*  CVonMangoldtIntegral.v  —  integral rep, brick IR3: the improper    *)
(*  limit.  From the Abel identity (IR1)                                *)
(*     Cpsum(pterm s) M = psi(S M)(S M)^{-s} - Cabel_correction … M,    *)
(*  letting M→∞ with Cpsum(pterm)→Φ (Phi_spec) and psi(N)N^{-s}→0        *)
(*  (psi_upper × Rpower decay, Re s>1) gives                            *)
(*     Cabel_correction … → −Φ,                                         *)
(*  i.e. Φ(s) = −lim Σ_k ψ(k)·(c_{k+1}−c_k) = s·Σ_k ψ(k)∫_k^{k+1}x^{-s-1}*)
(*  = s ∫₁^∞ ψ(⌊x⌋) x^{-s-1} dx  (in the sum-of-cell-integrals sense;    *)
(*  each increment c_{k+1}−c_k = CgderivInt s k (k+1) is a genuine cell  *)
(*  integral by the C-FTC, CFTC.gC_FTC / IR1.cell_increment).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CSeries CAbelSummation CFTC
        CVonMangoldtSeries CVonMangoldtAbel CDirichlet CDirichletProduct
        CZetaTerm VonMangoldtGlobal Chebyshev ChebyshevBound ZetaContinuation
        GammaFunction.
Open Scope R_scope.

Section IntRep.
Variable s : C.
Hypothesis H : 1 < Re s.

Lemma psi_nonneg : forall N, 0 <= psi N.
Proof. intro N; rewrite <- psi_0; apply psi_mono; lia. Qed.

(* the boundary weight psi(N)·N^{-s} tends to 0 *)
Lemma psi_weight_cv0 :
  CUn_cv (fun M => Cmul (RtoC (psi (S M))) (gC s (INR (S M)))) C0.
Proof.
  apply CUn_cv_mod0.
  apply (Un_cv_squeeze0 _ (fun M => Kup * Rpower (INR (S M)) (1 - Re s))).
  - exists 0%nat; intros M _; split; [ apply Cmod_nonneg | ].
    rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq (psi (S M))) by apply psi_nonneg.
    unfold gC; rewrite Cpw_mod.
    replace (Re (Copp s)) with (- Re s) by (unfold Copp; cbn [Re]; ring).
    assert (Hpow : INR (S M) * Rpower (INR (S M)) (- Re s) = Rpower (INR (S M)) (1 - Re s)).
    { rewrite <- (Rpower_1 (INR (S M))) at 1 by (apply lt_0_INR; lia).
      rewrite <- Rpower_plus; f_equal; ring. }
    apply Rle_trans with (INR (S M) * Kup * Rpower (INR (S M)) (- Re s)).
    + apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | apply psi_upper ].
    + replace (INR (S M) * Kup * Rpower (INR (S M)) (- Re s))
        with (Kup * (INR (S M) * Rpower (INR (S M)) (- Re s))) by ring.
      rewrite Hpow; apply Rle_refl.
  - replace 0 with (Kup * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | apply Rpower_neg_cv0; lra ].
Qed.

(* THE integral representation (sum-of-cell-integrals form):
   the Abel correction converges to −Φ. *)
Theorem phi_correction_cv :
  CUn_cv (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)))
         (Copp (Phi s H)).
Proof.
  apply (CUn_cv_ext
    (fun M => Cminus (Cmul (RtoC (psi (S M))) (gC s (INR (S M)))) (Cpsum (pterm s) M))).
  - intro M; pose proof (phi_abel s M) as HP; rewrite HP; ring.
  - replace (Copp (Phi s H)) with (Cminus C0 (Phi s H)) by ring.
    apply CUn_cv_minus; [ apply psi_weight_cv0 | exact (Phi_spec s H) ].
Qed.

(* the positive form:  Φ = lim −(correction) = s·Σ ψ(k)∫_k^{k+1} x^{-s-1} *)
Theorem phi_integral_rep :
  CUn_cv (fun M => Copp (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M))
         (Phi s H).
Proof.
  apply CUn_cv_comp.
  pose proof phi_correction_cv as HC; rewrite CUn_cv_comp in HC; destruct HC as [HCr HCi].
  split.
  - apply (Un_cv_ext (fun M => 0 - Re (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M)));
      [ intro M; unfold Copp; cbn [Re]; ring | ].
    replace (Re (Phi s H)) with (0 - Re (Copp (Phi s H))) by (unfold Copp; cbn [Re]; ring).
    apply CV_minus; [ apply Un_cv_const | exact HCr ].
  - apply (Un_cv_ext (fun M => 0 - Im (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M)));
      [ intro M; unfold Copp; cbn [Im]; ring | ].
    replace (Im (Phi s H)) with (0 - Im (Copp (Phi s H))) by (unfold Copp; cbn [Im]; ring).
    apply CV_minus; [ apply Un_cv_const | exact HCi ].
Qed.

End IntRep.

Print Assumptions phi_correction_cv.
Print Assumptions phi_integral_rep.

(* ================================================================= *)
(*  END CVonMangoldtIntegral.v  —  Phi = s·Sum_k psi(k) Int cell (IR3).  *)
(* ================================================================= *)
