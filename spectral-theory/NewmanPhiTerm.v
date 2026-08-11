(* ================================================================= *)
(*  NewmanPhiTerm.v  —  Newman A3: the Phi term in Newman-Laplace form.   *)
(*                                                                    *)
(*  Fusing FusionIntegral (CgderivInt_Laplace) with PhiCellRep            *)
(*  (phi_cellint_rep): the s-scaled Newman Laplace step transform          *)
(*  converges to Phi(s):                                                 *)
(*                                                                    *)
(*    newman_phi_term :                                                  *)
(*      s * sum_{k<=M} psi(k+1) int_{ln(k+1)}^{ln(k+2)} e^{-st} dt          *)
(*        -> Phi s   (1 < Re s).                                         *)
(*                                                                    *)
(*  i.e. the t-space Laplace step transform -> Phi(s)/s.  With s = z+1     *)
(*  this is the Phi(z+1)/(z+1) term of g(z) = Phi(z+1)/(z+1) - 1/z.        *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CExpKernel
        CZetaTerm CFTC CVonMangoldtSeries Chebyshev FusionIntegral PhiCellRep.
Open Scope R_scope.

Lemma Cpsum_scal_l : forall (a : nat -> C) (k : C) N,
  Cpsum (fun n => Cmul k (a n)) N = Cmul k (Cpsum a N).
Proof. intros a k N; induction N as [|N IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Theorem newman_phi_term : forall s (H : 1 < Re s),
  CUn_cv (fun M => Cmul s (Cpsum (fun k =>
            Cmul (RtoC (psi (S k)))
                 (Cintf (fun t => cexpzt (Copp s) t) (Ccont_cexpzt (Copp s))
                        (ln (INR (S k))) (ln (INR (S (S k)))))) M))
         (Phi s H).
Proof.
  intros s H.
  apply (CUn_cv_ext (fun M => Copp (Cpsum (fun k =>
    Cmul (RtoC (psi (S k)))
         (CgderivInt s (INR (S k)) (INR (S (S k))) (cellpos k) (cellle k))) M))).
  - intro M.
    rewrite (Cpsum_ext
      (fun k => Cmul (RtoC (psi (S k)))
                  (CgderivInt s (INR (S k)) (INR (S (S k))) (cellpos k) (cellle k)))
      (fun k => Cmul (Copp s)
                  (Cmul (RtoC (psi (S k)))
                     (Cintf (fun t => cexpzt (Copp s) t) (Ccont_cexpzt (Copp s))
                            (ln (INR (S k))) (ln (INR (S (S k))))))) M)
      by (intro k; rewrite (CgderivInt_Laplace s (INR (S k)) (INR (S (S k)))
                              (cellpos k) (cellle k)); ring).
    rewrite Cpsum_scal_l; ring.
  - apply phi_cellint_rep.
Qed.

Print Assumptions newman_phi_term.

(* ================================================================= *)
(*  END NewmanPhiTerm.v — the Phi(z+1)/(z+1) term in Newman-Laplace form.  *)
(*  Together with laplace_one (the 1/z term), and modulo assembling         *)
(*  Newman's f = psiR(e^t)e^{-t} - 1 as the step cell sum (the -1 giving    *)
(*  the 1/z part, psiR(e^t)e^{-t} the step part), this is the Newman        *)
(*  identity g(z) = Phi(z+1)/(z+1) - 1/z.  Next: the Newman contour          *)
(*  estimate (Cmod_newman_kernel + gfull_tail) and the Tauberian squeeze.   *)
(* ================================================================= *)
