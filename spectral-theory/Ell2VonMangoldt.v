(* ================================================================= *)
(*  Ell2VonMangoldt.v  —  the von Mangoldt diagonal operator on ℓ²,    *)
(*  and its spectral trace = Chebyshev's ψ.                          *)
(*                                                                    *)
(*  Instantiate the diagonal operator D_a with the von Mangoldt        *)
(*  symbol a = Λ (Lam).  Λ is UNBOUNDED (Λ(pᵏ) = log p), so D_Λ is an  *)
(*  UNBOUNDED operator: the global bounded-operator lemmas             *)
(*  (Dmul_Ell2 on all of ℓ², Dmul_bound, self-adjointness) do NOT     *)
(*  apply.  But its EIGENSTRUCTURE on the standard basis is perfectly  *)
(*  well defined — each e i is a finite-support vector — and that is   *)
(*  what ties ℓ² spectral theory to the primes:                      *)
(*                                                                    *)
(*    • EIGENVECTORS:  D_Λ (e i) = Λ(i)·(e i)      (vm_eigen);         *)
(*      the point spectrum is {Λ(n)} = {0} ∪ {log p : p prime}.       *)
(*    • DIAGONAL MATRIX ELEMENTS:  ⟨D_Λ e n, e n⟩ = Λ(n)   (vm_diag);  *)
(*    • SPECTRAL TRACE:  Σ_{n=1}^{N} ⟨D_Λ e n, e n⟩ = ψ(N)             *)
(*      (vm_trace_eq_psi), Chebyshev's function — whence, by           *)
(*      ChebyshevBound,  the trace grows LINEARLY:                    *)
(*         ψ(N) ≤ (2·log2 + 2)·N   and   ψ(2M) ≥ (2M)·log2 − log(2M+1).*)
(*                                                                    *)
(*  So the average eigenvalue of D_Λ over the first N basis vectors is *)
(*  bounded between two positive constants — the operator-theoretic    *)
(*  face of the Chebyshev bound ψ(x) ≍ x.                            *)
(*                                                                    *)
(*  Axiom footprint: the standard classical-Reals + functional-        *)
(*  extensionality axioms (shared by the Ell2 and von Mangoldt trees). *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator Ell2Basis Ell2Parseval.
Require Import VonMangoldtGlobal Chebyshev ChebyshevBound.
From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Open Scope R_scope.

(* EIGENVECTORS: D_Λ (e i) = Λ(i)·(e i) — eigenvalue Λ(i) *)
Lemma vm_eigen : forall i n, Dmul Lam (e i) n = (Lam i * e i n)%R.
Proof. intros i n; apply Dmul_eigen. Qed.

(* D_Λ (e n) = Λ(n)·(e n) is a finite-support vector, so it is in ℓ² *)
Lemma vm_e_scal : forall n m, Dmul Lam (e n) m = (Lam n * e n m)%R.
Proof.
  intros n m; unfold Dmul; destruct (Nat.eq_dec m n) as [-> | Hmn];
    [ reflexivity | rewrite (e_off n m Hmn); ring ].
Qed.

Lemma Ell2_vm_e : forall n, Ell2 (Dmul Lam (e n)).
Proof.
  intro n; apply (Ell2_ext (fun m => Lam n * e n m));
    [ intro m; symmetry; apply vm_e_scal | apply Ell2_scal; apply Ell2_e ].
Qed.

(* DIAGONAL MATRIX ELEMENT: ⟨D_Λ e n, e n⟩ = Λ(n) *)
Lemma vm_diag : forall n,
  ip (Dmul Lam (e n)) (e n) (Ell2_vm_e n) (Ell2_e n) = Lam n.
Proof.
  intro n; rewrite (ip_coord (Dmul Lam (e n)) n (Ell2_vm_e n) (Ell2_e n)).
  unfold Dmul; rewrite (e_diag n); ring.
Qed.

(* the SPECTRAL TRACE of D_Λ over the first N basis vectors *)
Definition vm_trace (N : nat) : R :=
  fold_right Rplus 0
    (map (fun n => ip (Dmul Lam (e n)) (e n) (Ell2_vm_e n) (Ell2_e n)) (seq 1 N)).

(* it is exactly Chebyshev's ψ(N) = Σ_{n=1}^{N} Λ(n) *)
Lemma vm_trace_eq_psi : forall N, vm_trace N = psi N.
Proof.
  intro N; unfold vm_trace, psi; f_equal; apply map_ext; intro n; apply vm_diag.
Qed.

(* CONSEQUENCE (ChebyshevBound): the spectral trace grows linearly *)
Theorem vm_trace_upper : forall N, vm_trace N <= INR N * (2 * ln 2 + 2).
Proof.
  intro N; rewrite vm_trace_eq_psi.
  destruct chebyshev_psi_bound as (_ & Hup & _ & _); apply Hup.
Qed.

Theorem vm_trace_lower :
  forall M, INR (2 * M) * ln 2 - ln (INR (2 * M + 1)) <= vm_trace (2 * M).
Proof.
  intro M; rewrite vm_trace_eq_psi.
  destruct chebyshev_psi_bound as (_ & _ & _ & Hlo); apply Hlo.
Qed.

(* the operator has a nonnegative spectrum (Λ ≥ 0) *)
Lemma vm_eigenvalue_nonneg : forall i, 0 <= Lam i.
Proof. exact Lam_nonneg. Qed.

Print Assumptions vm_diag.
Print Assumptions vm_trace_eq_psi.
Print Assumptions vm_trace_upper.

(* ================================================================= *)
(*  END Ell2VonMangoldt.v                                            *)
(*  The (unbounded) von Mangoldt operator D_Λ on ℓ² is diagonalised   *)
(*  by the standard basis with eigenvalues Λ(n); its spectral trace   *)
(*  over the first N basis vectors is Chebyshev's ψ(N), which grows   *)
(*  linearly (ψ(x) ≍ x).  This is the bridge between the ℓ² spectral  *)
(*  apparatus and the arithmetic of the primes.                      *)
(* ================================================================= *)
