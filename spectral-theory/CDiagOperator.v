(* ================================================================= *)
(*  CDiagOperator.v  —  the complex von Mangoldt–Mellin operator.        *)
(*                                                                    *)
(*  The genuine COMPLEX (s in C) analogue of Ell2MellinVM's real          *)
(*  Mellin-regularized von Mangoldt operator.  Since the repo has no       *)
(*  complex Hilbert space (only the real l^2), the complex diagonal        *)
(*  operator lives on nat -> C, with coordinate matrix elements:          *)
(*                                                                    *)
(*      M_s  :=  CDmul (pterm s)  :  (nat->C) -> (nat->C),                *)
(*      (M_s f)(n) = (Lam(n+1) (n+1)^{-s}) * f(n).                        *)
(*                                                                    *)
(*  Its SPECTRUM is {Lam(n) n^{-s}} in C (complex eigenvalues), and its    *)
(*  TRACE (the complex partial sum of the diagonal matrix elements)        *)
(*  converges to the analytic Dirichlet series                            *)
(*      Ctrace s N  ->  Phi(s) = -zeta'/zeta(s)   (Re s > 1),             *)
(*  the operator-theoretic bridge from primes (via Lam, pterm) to the      *)
(*  complex field (s in C, zeta).  Axiom-clean.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CVonMangoldtSeries
        CZeta CZetaDerivDirichlet CVonMangoldtZeta VonMangoldtGlobal Ell2MellinVM.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the complex diagonal operator on  nat -> C  and its basis          *)
(* ----------------------------------------------------------------- *)

Definition CDmul (a f : nat -> C) : nat -> C := fun n => Cmul (a n) (f n).

Definition Ce (i : nat) : nat -> C := fun n => if Nat.eqb n i then C1 else C0.

Lemma Ce_diag : forall i, Ce i i = C1.
Proof. intro i; unfold Ce; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma Ce_off : forall i n, n <> i -> Ce i n = C0.
Proof. intros i n Hn; unfold Ce; rewrite (proj2 (Nat.eqb_neq n i) Hn); reflexivity. Qed.

Lemma CDmul_add : forall a f g, CDmul a (fun n => Cadd (f n) (g n))
                              = (fun n => Cadd (CDmul a f n) (CDmul a g n)).
Proof. intros a f g; apply functional_extensionality; intro n; unfold CDmul; ring. Qed.

Lemma CDmul_scal : forall a c f, CDmul a (fun n => Cmul c (f n))
                              = (fun n => Cmul c (CDmul a f n)).
Proof. intros a c f; apply functional_extensionality; intro n; unfold CDmul; ring. Qed.

(*  EIGENVECTORS:  M (Ce i) = (a i) . (Ce i)  —  complex eigenvalue a i  *)
Lemma CDmul_eigen : forall a i n, CDmul a (Ce i) n = Cmul (a i) (Ce i n).
Proof.
  intros a i n; unfold CDmul, Ce; destruct (Nat.eqb n i) eqn:E;
    [ apply Nat.eqb_eq in E; subst; reflexivity | ring ].
Qed.

(*  the diagonal matrix element  <M e_n, e_n> = a n  (coordinate n)  *)
Definition Cdiag_elt (a : nat -> C) (n : nat) : C := CDmul a (Ce n) n.

Lemma Cdiag_elt_eq : forall a n, Cdiag_elt a n = a n.
Proof. intros a n; unfold Cdiag_elt, CDmul, Ce; rewrite Nat.eqb_refl; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  the von Mangoldt–Mellin operator  M_s := CDmul (pterm s)  and trace  *)
(* ----------------------------------------------------------------- *)

Definition Ctrace (s : C) (N : nat) : C := Cpsum (fun n => Cdiag_elt (pterm s) n) N.

Lemma Ctrace_eq : forall s N, Ctrace s N = Cpsum (pterm s) N.
Proof.
  intros s N; unfold Ctrace.
  replace (fun n => Cdiag_elt (pterm s) n) with (pterm s);
    [ reflexivity
    | apply functional_extensionality; intro n; symmetry; apply Cdiag_elt_eq ].
Qed.

(*  THE TRACE CONVERGES TO Phi(s)  (Re s > 1)  *)
Theorem trace_cv_Phi : forall s (H : 1 < Re s), CUn_cv (Ctrace s) (Phi s H).
Proof.
  intros s H.
  replace (Ctrace s) with (Cpsum (pterm s));
    [ exact (Phi_spec s H)
    | apply functional_extensionality; intro N; symmetry; apply Ctrace_eq ].
Qed.

(*  ...and the trace limit IS -zeta'/zeta(s): the operator's spectral      *)
(*  trace is the analytic logarithmic derivative of zeta.                 *)
Corollary trace_cv_neg_zeta_ratio :
  forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  CUn_cv (Ctrace s) (Copp (Cmul (proj1_sig (dcterm_cv s H)) (Cinv (zetaC s H0 H1)))).
Proof.
  intros s H0 H1 H.
  rewrite <- (phi_eq_neg_zeta_ratio s H0 H1 H); apply trace_cv_Phi.
Qed.

(* ----------------------------------------------------------------- *)
(*  the real bridge:  at s = sigma (real), the eigenvalue moduli are the  *)
(*  real Mellin-von-Mangoldt weights WLam (Ell2MellinVM)                  *)
(* ----------------------------------------------------------------- *)

Lemma Cdiag_elt_Cmod_real : forall sigma n,
  Cmod (Cdiag_elt (pterm (RtoC sigma)) n) = WLam sigma (S n).
Proof.
  intros sigma n; rewrite Cdiag_elt_eq, Cmod_pterm.
  replace (Re (RtoC sigma)) with sigma by (unfold RtoC; reflexivity).
  unfold WLam; reflexivity.
Qed.

Print Assumptions trace_cv_Phi.
Print Assumptions trace_cv_neg_zeta_ratio.

(* ================================================================= *)
(*  END CDiagOperator.v — the complex von Mangoldt–Mellin operator.       *)
(*  spectrum {Lam(n) n^{-s}} in C; trace -> Phi(s) = -zeta'/zeta(s).        *)
(*  The complex (s in C) face of Ell2MellinVM's real Mellin operator, and  *)
(*  the operator whose trace is the Phi driving Perron/Newman/PNT.          *)
(* ================================================================= *)
