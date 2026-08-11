(* ================================================================= *)
(*  NewmanG.v  —  Newman A3: the normalized Phi term, and the g bundle.   *)
(*                                                                    *)
(*  step_transform_cv : the t-space Laplace step transform of psiR(e^t)    *)
(*  converges to Phi(s)/s (dividing newman_phi_term by s):               *)
(*                                                                    *)
(*    sum_{k<=M} psi(k+1) int_{ln(k+1)}^{ln(k+2)} e^{-st} dt -> Phi(s)/s.   *)
(*                                                                    *)
(*  With s = z+1 this is exactly the Phi(z+1)/(z+1) term of the Newman      *)
(*  identity g(z) = Phi(z+1)/(z+1) - 1/z.  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CExpKernel
        CZetaTerm CFTC CVonMangoldtSeries Chebyshev NewmanPhiTerm PhiCellRep.
Open Scope R_scope.

Lemma Cmul_Cinv_l_cancel : forall s X, s <> C0 -> Cmul (Cinv s) (Cmul s X) = X.
Proof.
  intros s X Hs; replace (Cmul (Cinv s) (Cmul s X)) with (Cmul (Cmul (Cinv s) s) X) by ring.
  rewrite (Cinv_l s Hs); ring.
Qed.

Lemma CUn_cv_scal_l : forall u l k, CUn_cv u l -> CUn_cv (fun n => Cmul k (u n)) (Cmul k l).
Proof.
  intros u l k H eps He.
  set (K := Cmod k + 1); assert (HK : 0 < K) by (unfold K; pose proof (Cmod_nonneg k); lra).
  destruct (H (eps / K) ltac:(apply Rdiv_lt_0_compat; [ exact He | exact HK ])) as [N HN].
  exists N; intros n Hn; specialize (HN n Hn).
  replace (Cminus (Cmul k (u n)) (Cmul k l)) with (Cmul k (Cminus (u n) l)) by ring.
  rewrite Cmod_mul.
  apply Rle_lt_trans with (Cmod k * (eps / K)).
  - apply Rmult_le_compat_l; [ apply Cmod_nonneg | left; exact HN ].
  - apply Rlt_le_trans with (K * (eps / K));
      [ apply Rmult_lt_compat_r; [ apply Rdiv_lt_0_compat; [ exact He | exact HK ] | unfold K; lra ]
      | right; field; unfold K; apply Rgt_not_eq; pose proof (Cmod_nonneg k); lra ].
Qed.

Theorem step_transform_cv : forall s (H : 1 < Re s),
  CUn_cv (fun M => Cpsum (fun k =>
            Cmul (RtoC (psi (S k)))
                 (Cintf (fun t => cexpzt (Copp s) t) (Ccont_cexpzt (Copp s))
                        (ln (INR (S k))) (ln (INR (S (S k)))))) M)
         (Cmul (Cinv s) (Phi s H)).
Proof.
  intros s H; assert (Hsne : s <> C0) by (intro Hs; rewrite Hs in H; cbn in H; lra).
  apply (CUn_cv_ext (fun M => Cmul (Cinv s) (Cmul s
    (Cpsum (fun k => Cmul (RtoC (psi (S k)))
              (Cintf (fun t => cexpzt (Copp s) t) (Ccont_cexpzt (Copp s))
                     (ln (INR (S k))) (ln (INR (S (S k)))))) M)))).
  - intro M; apply Cmul_Cinv_l_cancel; exact Hsne.
  - apply CUn_cv_scal_l; apply newman_phi_term.
Qed.

Print Assumptions step_transform_cv.

(* ================================================================= *)
(*  END NewmanG.v — the Phi(z+1)/(z+1) term as a clean limit.             *)
(*  The full bundle g(z) = Phi(z+1)/(z+1) - 1/z is step_transform_cv        *)
(*  (s=z+1) minus the -1 part: the cell sum sum_k int_{cell} e^{-zt} dt      *)
(*  = int_0^{ln(M+2)} e^{-zt} dt (logpart_additive) -> 1/z (Cint_cexpzt +   *)
(*  (M+2)^{-z} -> 0), joined by CV_minus.                                  *)
(* ================================================================= *)
