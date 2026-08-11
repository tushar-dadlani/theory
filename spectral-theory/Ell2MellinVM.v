(* ================================================================= *)
(*  Ell2MellinVM.v  —  the Mellin-regularized von Mangoldt operator.     *)
(*                                                                    *)
(*  The von Mangoldt diagonal operator D_Lam (Ell2VonMangoldt) is         *)
(*  UNBOUNDED (Lam(p^k)=log p).  Regularize it by the diagonal weight     *)
(*  n^{-sigma}: the "Mellin-smeared" operator                            *)
(*                                                                    *)
(*      M_sigma  :=  D_Lam . N^{-sigma}  =  Dmul (fun n => Lam n * n^{-sigma}).*)
(*                                                                    *)
(*  Its EIGENVALUES  Lam(n) n^{-sigma} >= 0 (self-adjoint, positive), and   *)
(*  its SPECTRAL TRACE over the first N basis vectors is the truncated     *)
(*  Dirichlet series                                                     *)
(*      sum_{n=1}^{N} Lam(n) n^{-sigma}   ->  Phi(sigma) = -zeta'/zeta(sigma) *)
(*  (sigma>1).  This is the operator-theoretic face of the whole Perron/    *)
(*  Newman apparatus: the SPECTRAL trace of M_sigma is the ANALYTIC Phi.    *)
(*  At sigma=0 it degenerates to D_Lam, whose trace is Chebyshev's psi.     *)
(*  Axiom-clean (the shared Ell2 + classical-Reals axioms).              *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator Ell2Basis Ell2Parseval Ell2VonMangoldt.
Require Import VonMangoldtGlobal Chebyshev.
From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Open Scope R_scope.

(*  the Mellin-weighted von Mangoldt symbol (the eigenvalue sequence)  *)
Definition WLam (sigma : R) (n : nat) : R := Lam n * Rpower (INR n) (- sigma).

(*  EIGENVECTORS:  M_sigma (e i) = (Lam(i) i^{-sigma}) (e i)  *)
Lemma mvm_eigen : forall sigma i n, Dmul (WLam sigma) (e i) n = (WLam sigma i * e i n)%R.
Proof. intros sigma i n; apply Dmul_eigen. Qed.

Lemma mvm_e_scal : forall sigma n m, Dmul (WLam sigma) (e n) m = (WLam sigma n * e n m)%R.
Proof.
  intros sigma n m; unfold Dmul; destruct (Nat.eq_dec m n) as [-> | Hmn];
    [ reflexivity | rewrite (e_off n m Hmn); ring ].
Qed.

Lemma Ell2_mvm_e : forall sigma n, Ell2 (Dmul (WLam sigma) (e n)).
Proof.
  intros sigma n; apply (Ell2_ext (fun m => WLam sigma n * e n m));
    [ intro m; symmetry; apply mvm_e_scal | apply Ell2_scal; apply Ell2_e ].
Qed.

(*  eigenvalues are nonnegative:  M_sigma is self-adjoint and POSITIVE  *)
Lemma mvm_eigen_nonneg : forall sigma n, 0 <= WLam sigma n.
Proof.
  intros sigma n; unfold WLam; apply Rmult_le_pos;
    [ apply Lam_nonneg | left; unfold Rpower; apply exp_pos ].
Qed.

(*  DIAGONAL MATRIX ELEMENT:  <M_sigma e n, e n> = Lam(n) n^{-sigma}  *)
Lemma mvm_diag : forall sigma n,
  ip (Dmul (WLam sigma) (e n)) (e n) (Ell2_mvm_e sigma n) (Ell2_e n) = WLam sigma n.
Proof.
  intros sigma n; rewrite (ip_coord (Dmul (WLam sigma) (e n)) n (Ell2_mvm_e sigma n) (Ell2_e n)).
  unfold Dmul; rewrite (e_diag n); ring.
Qed.

(*  the SPECTRAL TRACE over the first N basis vectors  *)
Definition mvm_trace (sigma : R) (N : nat) : R :=
  fold_right Rplus 0
    (map (fun n => ip (Dmul (WLam sigma) (e n)) (e n) (Ell2_mvm_e sigma n) (Ell2_e n)) (seq 1 N)).

(*  it is the truncated Dirichlet series  sum_{n=1}^N Lam(n) n^{-sigma}  *)
Lemma mvm_trace_eq : forall sigma N,
  mvm_trace sigma N = fold_right Rplus 0 (map (WLam sigma) (seq 1 N)).
Proof.
  intros sigma N; unfold mvm_trace; f_equal; apply map_ext; intro n; apply mvm_diag.
Qed.

(*  at sigma = 0 the Mellin weight is trivial and the trace is Chebyshev psi  *)
Lemma WLam_0 : forall n, (1 <= n)%nat -> WLam 0 n = Lam n.
Proof.
  intros n Hn; unfold WLam; rewrite Ropp_0, Rpower_O; [ ring | apply lt_0_INR; lia ].
Qed.

Theorem mvm_trace_0 : forall N, mvm_trace 0 N = psi N.
Proof.
  intro N; rewrite mvm_trace_eq; unfold psi; f_equal.
  apply map_ext_in; intros n Hn; apply WLam_0; apply in_seq in Hn; lia.
Qed.

Print Assumptions mvm_trace_0.

(* ================================================================= *)
(*  END Ell2MellinVM.v — the Mellin-regularized von Mangoldt operator.    *)
(*  spectrum {Lam(n) n^{-sigma}} >= 0; trace = sum Lam(n) n^{-sigma} ->     *)
(*  Phi(sigma); at sigma=0, trace = psi (Chebyshev).  The bridge from the  *)
(*  ell^2 SPECTRAL side (D_Lam, trace psi) to the ANALYTIC side (Phi = the  *)
(*  Dirichlet series driving Perron/Newman and PNT).                      *)
(* ================================================================= *)
