(* ================================================================= *)
(*  Ell2Operator.v  —  operators on the Hilbert space ℓ².            *)
(*                                                                    *)
(*  The DIAGONAL / MULTIPLICATION operator  (D_a f)(n) = a(n)·f(n),    *)
(*  for a bounded real symbol  a : ℕ → ℝ  with  |a(n)| ≤ M.           *)
(*  This is the prototypical bounded self-adjoint operator on ℓ²      *)
(*  (a real "Hamiltonian"); its eigenvectors are the standard basis   *)
(*  vectors, with eigenvalues a(n).  Here we prove it:                *)
(*    • maps ℓ² → ℓ²         (Dmul_Ell2, boundedness in disguise);    *)
(*    • is LINEAR            (Dmul_add, Dmul_scal, pointwise);         *)
(*    • is SELF-ADJOINT      ⟨D f, g⟩ = ⟨f, D g⟩   (Dmul_selfadjoint); *)
(*    • is BOUNDED           ‖D f‖ ≤ M·‖f‖          (Dmul_bound).      *)
(*                                                                    *)
(*  Axiom footprint: inherited from Ell2 — the standard classical-    *)
(*  Reals + functional-extensionality axioms only.                   *)
(* ================================================================= *)

Require Import Ell2.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* |x| ≤ M  ⇒  x² ≤ M² *)
Lemma sq_le_of_abs_le : forall x M, Rabs x <= M -> x ^ 2 <= M ^ 2.
Proof.
  intros x M H; pose proof (Rabs_pos x).
  assert (x ^ 2 = Rabs x ^ 2) by (rewrite <- Rsqr_pow2, Rsqr_abs, Rsqr_pow2; reflexivity).
  nra.
Qed.

(* monotonicity of a partial sum in its summand *)
Lemma sum_f_R0_le : forall A B N,
  (forall i, A i <= B i) -> sum_f_R0 A N <= sum_f_R0 B N.
Proof.
  intros A B N H; induction N; cbn [sum_f_R0]; [ apply H | pose proof (H (S N)); lra ].
Qed.

Section Diagonal.

Variable a : nat -> R.
Variable M : R.
Hypothesis Ha : forall n, Rabs (a n) <= M.

(* the diagonal (multiplication) operator *)
Definition Dmul (f : nat -> R) : nat -> R := fun n => a n * f n.

(* LINEARITY (pointwise) *)
Lemma Dmul_add : forall f g n, Dmul (fun m => f m + g m) n = (Dmul f n + Dmul g n)%R.
Proof. intros; unfold Dmul; ring. Qed.

Lemma Dmul_scal : forall c f n, Dmul (fun m => c * f m) n = (c * Dmul f n)%R.
Proof. intros; unfold Dmul; ring. Qed.

(* D_a maps ℓ² into ℓ² : (a f)² ≤ M² f², so the squares stay summable *)
Lemma Dmul_Ell2 : forall f, Ell2 f -> Ell2 (Dmul f).
Proof.
  intros f Hf.
  apply (Rseries_CV_comp (fun n => (Dmul f n) ^ 2) (fun n => M ^ 2 * (f n) ^ 2)).
  - intro n; split.
    + apply pow2_ge_0.
    + unfold Dmul.
      pose proof (sq_le_of_abs_le (a n) M (Ha n)); pose proof (pow2_ge_0 (f n)); nra.
  - apply (Summable_scal (fun n => (f n) ^ 2) (M ^ 2)); exact Hf.
Qed.

(* SELF-ADJOINTNESS: ⟨D f, g⟩ = ⟨f, D g⟩ *)
Lemma Dmul_selfadjoint :
  forall f g (HDf : Ell2 (Dmul f)) (Hg : Ell2 g) (Hf : Ell2 f) (HDg : Ell2 (Dmul g)),
  ip (Dmul f) g HDf Hg = ip f (Dmul g) Hf HDg.
Proof.
  intros f g HDf Hg Hf HDg.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => Dmul f n * g n) N)).
  - apply ip_spec.
  - apply (Un_cv_eq (fun N => sum_f_R0 (fun n => f n * Dmul g n) N)).
    + intro N; apply sum_eq; intros n _; unfold Dmul; ring.
    + apply ip_spec.
Qed.

(* BOUNDEDNESS: ‖D f‖ ≤ M·‖f‖ *)
Lemma Dmul_bound : forall f (Hf : Ell2 f) (HDf : Ell2 (Dmul f)),
  norm (Dmul f) HDf <= M * norm f Hf.
Proof.
  intros f Hf HDf.
  assert (HM : 0 <= M) by (pose proof (Rabs_pos (a 0)); pose proof (Ha 0); lra).
  assert (Hip : ip (Dmul f) (Dmul f) HDf HDf <= M ^ 2 * ip f f Hf Hf).
  { apply (Un_cv_le (fun N => sum_f_R0 (fun n => Dmul f n * Dmul f n) N)
                    (fun N => M ^ 2 * sum_f_R0 (fun n => f n * f n) N)).
    - intro N; rewrite <- (sum_f_R0_scal (fun n => f n * f n) (M ^ 2) N).
      apply sum_f_R0_le; intro n; unfold Dmul.
      pose proof (sq_le_of_abs_le (a n) M (Ha n)); pose proof (pow2_ge_0 (f n)); nra.
    - apply ip_spec.
    - apply Un_cv_scal, ip_spec. }
  unfold norm.
  apply Rle_trans with (sqrt (M ^ 2 * ip f f Hf Hf)).
  - apply sqrt_le_1_alt; exact Hip.
  - rewrite (sqrt_mult (M ^ 2) (ip f f Hf Hf) ltac:(nra) (ip_diag_nonneg f Hf)).
    rewrite <- Rsqr_pow2, sqrt_Rsqr by exact HM.
    apply Rle_refl.
Qed.

End Diagonal.

Print Assumptions Dmul_selfadjoint.
Print Assumptions Dmul_bound.

(* ================================================================= *)
(*  END Ell2Operator.v                                               *)
(*  The diagonal operator D_a on ℓ² (|a| ≤ M): a bounded (‖D‖ ≤ M),   *)
(*  self-adjoint linear operator — the prototypical Hamiltonian on    *)
(*  the infinite-dimensional Hilbert space.  Next: its eigenvectors   *)
(*  (the standard basis, eigenvalue a(n)) and the spectrum.          *)
(* ================================================================= *)
