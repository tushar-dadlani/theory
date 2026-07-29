(* ================================================================= *)
(*  Ell2Spectral.v  —  the SPECTRAL THEOREM for the diagonal operator  *)
(*  D_a on ℓ².                                                        *)
(*                                                                    *)
(*  D_a is diagonalised by the eigenbasis {e i} (eigenvalue a(i)):    *)
(*      D_a f  =  Σ_i a(i)·⟨f, e i⟩·e i        (ℓ²-norm limit).        *)
(*                                                                    *)
(*  The spectral partial sum  specsum f N = Σ_{i≤N} a(i)·f(i)·e i  is  *)
(*  exactly the Fourier reconstruction of the vector D_a f (because    *)
(*  the i-th coefficient of D_a f is a(i)·⟨f,e i⟩, spec_coeff), so the *)
(*  spectral theorem is the reconstruction theorem applied to D_a f:   *)
(*      ‖D_a f − specsum f N‖² → 0        (spectral_theorem /          *)
(*                                          spectral_series).          *)
(*                                                                    *)
(*  Axiom footprint: inherited from Ell2 — the standard classical-    *)
(*  Reals + functional-extensionality axioms only.                   *)
(* ================================================================= *)

Require Import Ell2 Ell2Basis Ell2Parseval Ell2Reconstruct Ell2Operator.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

Section Spectral.

Variable a : nat -> R.
Variable M : R.
Hypothesis Ha : forall n, Rabs (a n) <= M.

(* EIGENVALUE EXTRACTION: the i-th coefficient of D_a f is a(i)·⟨f,e i⟩ *)
Lemma spec_coeff : forall f i (Hf : Ell2 f) (HDf : Ell2 (Dmul a f)) (Hei : Ell2 (e i)),
  ip (Dmul a f) (e i) HDf Hei = a i * ip f (e i) Hf Hei.
Proof.
  intros f i Hf HDf Hei.
  rewrite (ip_coord (Dmul a f) i HDf Hei), (ip_coord f i Hf Hei); unfold Dmul; reflexivity.
Qed.

(* the spectral partial sum  Σ_{i≤N} a(i)·f(i)·e i, at coordinate n *)
Definition specsum (f : nat -> R) (N : nat) : nat -> R :=
  fun n => sum_f_R0 (fun i => a i * f i * e i n) N.

(* it is the Fourier reconstruction of the vector D_a f *)
Lemma specsum_recon : forall f N n, specsum f N n = recon (Dmul a f) N n.
Proof. intros f N n; unfold specsum, recon, Dmul; reflexivity. Qed.

(* hence  D_a f − specsum f N  is the reconstruction tail of D_a f *)
Lemma spec_error : forall f N n,
  tail (Dmul a f) N n = (Dmul a f n - specsum f N n)%R.
Proof. intros f N n; unfold tail; rewrite specsum_recon; reflexivity. Qed.

(* THE SPECTRAL THEOREM (tail form = reconstruction of D_a f):        *)
(*   ‖D_a f − Σ_{i≤N} a(i)·f(i)·e i‖² → 0.                            *)
Theorem spectral_theorem : forall f (Hf : Ell2 f),
  Un_cv (fun N => ip (tail (Dmul a f) N) (tail (Dmul a f) N)
                     (Ell2_tailvec (Dmul a f) N (Dmul_Ell2 a M Ha f Hf))
                     (Ell2_tailvec (Dmul a f) N (Dmul_Ell2 a M Ha f Hf))) 0.
Proof. intros f Hf; apply (reconstruction (Dmul a f) (Dmul_Ell2 a M Ha f Hf)). Qed.

(* the same, stated on the explicit spectral partial sum specsum *)
Corollary spectral_series : forall f (Hf : Ell2 f)
  (Hd : forall N, Ell2 (fun n => Dmul a f n - specsum f N n)),
  Un_cv (fun N => ip (fun n => Dmul a f n - specsum f N n)
                     (fun n => Dmul a f n - specsum f N n) (Hd N) (Hd N)) 0.
Proof.
  intros f Hf Hd.
  apply (Un_cv_eq (fun N => ip (tail (Dmul a f) N) (tail (Dmul a f) N)
                     (Ell2_tailvec (Dmul a f) N (Dmul_Ell2 a M Ha f Hf))
                     (Ell2_tailvec (Dmul a f) N (Dmul_Ell2 a M Ha f Hf)))).
  - intro N; apply ip_ext; intro n; apply spec_error.
  - apply (spectral_theorem f Hf).
Qed.

End Spectral.

Print Assumptions spectral_theorem.
Print Assumptions spectral_series.

(* ================================================================= *)
(*  END Ell2Spectral.v                                               *)
(*  The bounded self-adjoint diagonal operator D_a is diagonalised by  *)
(*  its eigenbasis {e i}:  D_a f = Σ_i a(i)·⟨f,e i⟩·e i in ℓ².  This   *)
(*  is the spectral theorem for D_a — the concrete infinite-dim.       *)
(*  counterpart of the finite self-adjoint diagonalisations elsewhere  *)
(*  in the spectral-theory tree.                                      *)
(* ================================================================= *)
