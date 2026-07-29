(* ================================================================= *)
(*  Ell2Parseval.v  —  Fourier coefficients, Bessel, Parseval on ℓ².  *)
(*                                                                    *)
(*  Against the standard basis {e i}, the Fourier coefficient of      *)
(*  f ∈ ℓ² is just its i-th component:                               *)
(*        ⟨f, e i⟩ = f(i)                       (ip_coord).           *)
(*  Consequently:                                                    *)
(*    • BESSEL:  Σ_{i≤N} ⟨f, e i⟩² ≤ ‖f‖²        (bessel);            *)
(*    • PARSEVAL: Σ_i ⟨f, e i⟩²  converges to  ‖f‖²  (parseval),      *)
(*      so {e i} is a COMPLETE orthonormal basis (a Hilbert basis)    *)
(*      of ℓ² — the infinite-dimensional analogue of the finite       *)
(*      Parseval identity in WalshHadamardHilbert.v.                 *)
(*                                                                    *)
(*  Axiom footprint: inherited from Ell2 — the standard classical-    *)
(*  Reals + functional-extensionality axioms only.                   *)
(* ================================================================= *)

Require Import Ell2 Ell2Basis.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* the f-weighted indicator partial sum:  Σ_{n≤N} f(n)·[n=i] = [i≤N]·f(i) *)
Lemma sum_fe_closed : forall f i N,
  sum_f_R0 (fun n => f n * e i n) N = (if Nat.leb i N then f i else 0)%R.
Proof.
  intros f i N.
  rewrite (sum_eq (fun n => f n * e i n) (fun n => f i * e i n) N).
  2:{ intros k _; destruct (Nat.eq_dec k i) as [-> | Hk];
        [ reflexivity | rewrite (e_off i k Hk); ring ]. }
  rewrite (sum_f_R0_scal (e i) (f i) N), (sum_e_closed i N).
  destruct (Nat.leb i N); ring.
Qed.

(* an eventually-constant sequence converges to that constant *)
Lemma Un_cv_stepc : forall i c, Un_cv (fun N => if Nat.leb i N then c else 0) c.
Proof.
  intros i c eps Heps; exists i; intros N HN.
  assert (Hb : Nat.leb i N = true) by (apply Nat.leb_le; exact HN).
  rewrite Hb; unfold R_dist; rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0; exact Heps.
Qed.

(* THE FOURIER COEFFICIENT IS THE COMPONENT:  ⟨f, e i⟩ = f(i) *)
Lemma ip_coord : forall f i (Hf : Ell2 f) (Hei : Ell2 (e i)),
  ip f (e i) Hf Hei = f i.
Proof.
  intros f i Hf Hei.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => f n * e i n) N)
                     (ip f (e i) Hf Hei) (f i)).
  - apply ip_spec.
  - apply (Un_cv_eq (fun N => if Nat.leb i N then f i else 0));
      [ intro N; symmetry; apply sum_fe_closed | apply Un_cv_stepc ].
Qed.

(* BESSEL'S INEQUALITY (partial-sum form): Σ_{i≤N} ⟨f,e i⟩² ≤ ‖f‖² *)
Theorem bessel : forall f (Hf : Ell2 f) N,
  sum_f_R0 (fun i => (ip f (e i) Hf (Ell2_e i)) ^ 2) N <= ip f f Hf Hf.
Proof.
  intros f Hf N.
  rewrite (sum_eq (fun i => (ip f (e i) Hf (Ell2_e i)) ^ 2) (fun i => (f i) ^ 2) N)
    by (intros i _; rewrite (ip_coord f i Hf (Ell2_e i)); reflexivity).
  apply partial_le_ip.
Qed.

(* PARSEVAL: Σ_i ⟨f, e i⟩² converges to ‖f‖² = ⟨f,f⟩ *)
Theorem parseval : forall f (Hf : Ell2 f),
  Un_cv (fun N => sum_f_R0 (fun i => (ip f (e i) Hf (Ell2_e i)) ^ 2) N)
        (ip f f Hf Hf).
Proof.
  intros f Hf.
  apply (Un_cv_eq (fun N => sum_f_R0 (fun i => f i * f i) N)); [ | apply ip_spec ].
  intro N; apply sum_eq; intros i _.
  rewrite (ip_coord f i Hf (Ell2_e i)); ring.
Qed.

Print Assumptions ip_coord.
Print Assumptions bessel.
Print Assumptions parseval.

(* ================================================================= *)
(*  END Ell2Parseval.v                                               *)
(*  {e i} is a complete orthonormal (Hilbert) basis of ℓ²:  every     *)
(*  f is determined by its coefficients ⟨f,e i⟩ = f(i), and the       *)
(*  Parseval identity Σ ⟨f,e i⟩² = ‖f‖² holds.                        *)
(* ================================================================= *)
