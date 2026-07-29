(* ================================================================= *)
(*  Ell2Zeta.v  —  the ζ-operator on ℓ², and D_Λ as its logarithmic   *)
(*  derivative.                                                       *)
(*                                                                    *)
(*  The "primon gas" picture, made concrete and elementary:          *)
(*   • H = diag(log n) is the (unbounded) Hamiltonian, energies log n; *)
(*   • Z_s = e^{-sH} = diag(n^{-s}) is the BOUNDED ζ-operator          *)
(*     (0 < n^{-s} ≤ 1 for n≥1, s≥0), self-adjoint with eigenvectors   *)
(*     Z_s e_n = n^{-s}·e_n;                                          *)
(*   • its PARTITION FUNCTION is the trace  Tr Z_s = Σ n^{-s} = ζ(s)   *)
(*     (STAGE 2, partial form zeta_partition);                        *)
(*   • the von Mangoldt observable gives the log-derivative            *)
(*     Tr(D_Λ Z_s) = Σ Λ(n) n^{-s} = −ζ'/ζ (s)                        *)
(*     (STAGE 3, vonmangoldt_zeta_trace);                            *)
(*   • the BRIDGE (−ζ'/ζ)·ζ = −ζ' is the Dirichlet convolution         *)
(*     Λ∗1 = log: per mode  log n = Σ_{d|n} Λ(d) (energy_eq_divisor_   *)
(*     sum), summatorily  Tr_N H = Σ_{d≤N} Λ(d)⌊N/d⌋ (trace_Hlog_eq_   *)
(*     chsum)  — STAGE 4, reusing vonmangoldt_identity /              *)
(*     order_swap_identity.                                          *)
(*                                                                    *)
(*  NOTE. This is the *elementary diagonal* spectral picture (energies *)
(*  log n) — NOT the conjectural Hilbert–Pólya operator, and it says   *)
(*  nothing about the zeta zeros or RH.  Convergence of the partial    *)
(*  traces to the analytic ζ(s) (Re s>1) is a separate analytic step.  *)
(*                                                                    *)
(*  Axiom footprint: the von Mangoldt / Chebyshev tree's standard set. *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator Ell2Basis Ell2Parseval.
Require Import VonMangoldtGlobal Chebyshev.
From Stdlib Require Import Reals Rpower Lra Lia List.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Diagonal operators on the standard basis (general symbol a).      *)
(* ----------------------------------------------------------------- *)

Lemma diag_e_scal : forall a n m, Dmul a (e n) m = (a n * e n m)%R.
Proof.
  intros a n m; unfold Dmul; destruct (Nat.eq_dec m n) as [-> | Hmn];
    [ reflexivity | rewrite (e_off n m Hmn); ring ].
Qed.

Lemma Ell2_diag_e : forall a n, Ell2 (Dmul a (e n)).
Proof.
  intros a n; apply (Ell2_ext (fun m => a n * e n m));
    [ intro m; symmetry; apply diag_e_scal | apply Ell2_scal; apply Ell2_e ].
Qed.

(* diagonal matrix element: ⟨D_a e n, e n⟩ = a(n) *)
Lemma diag_matrix_elt : forall a n,
  ip (Dmul a (e n)) (e n) (Ell2_diag_e a n) (Ell2_e n) = a n.
Proof.
  intros a n; rewrite (ip_coord (Dmul a (e n)) n (Ell2_diag_e a n) (Ell2_e n)).
  unfold Dmul; rewrite (e_diag n); ring.
Qed.

(* spectral trace of D_a over the first N basis vectors *)
Definition diag_trace (a : nat -> R) (N : nat) : R :=
  fold_right Rplus 0
    (map (fun n => ip (Dmul a (e n)) (e n) (Ell2_diag_e a n) (Ell2_e n)) (seq 1 N)).

Lemma diag_trace_eq : forall a N,
  diag_trace a N = fold_right Rplus 0 (map a (seq 1 N)).
Proof.
  intros a N; unfold diag_trace; f_equal; apply map_ext; intro n; apply diag_matrix_elt.
Qed.

(* ================================================================= *)
(*  STAGE 1 — the ζ-operator  Z_s = diag(n^{-s}).                     *)
(* ================================================================= *)

Definition z (s : R) (n : nat) : R := if Nat.eqb n 0 then 0 else Rpower (INR n) (- s).

Lemma z_exp : forall s n, (1 <= n)%nat -> z s n = exp ((- s) * ln (INR n)).
Proof. intros s n Hn; unfold z, Rpower; destruct n as [| m]; [ lia | reflexivity ]. Qed.

Lemma exp_le1_nonpos : forall x, x <= 0 -> exp x <= 1.
Proof.
  intros x Hx; rewrite <- exp_0; destruct (Rle_lt_or_eq_dec x 0 Hx) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

(* 0 ≤ n^{-s} ≤ 1  for s ≥ 0 : Z_s is bounded by 1 *)
Lemma z_bounds : forall s n, 0 <= s -> 0 <= z s n <= 1.
Proof.
  intros s n Hs; unfold z; destruct (Nat.eqb n 0) eqn:E; [ lra | ].
  apply Nat.eqb_neq in E.
  assert (Hln : 0 <= ln (INR n)) by (apply ln_ge0; rewrite <- INR_1; apply le_INR; lia).
  unfold Rpower; split.
  - apply Rlt_le, exp_pos.
  - apply exp_le1_nonpos; nra.
Qed.

Lemma z_abs : forall s n, 0 <= s -> Rabs (z s n) <= 1.
Proof. intros s n Hs; pose proof (z_bounds s n Hs) as [Hlo Hhi]; rewrite Rabs_pos_eq; assumption. Qed.

(* EIGENVECTORS: Z_s e n = n^{-s}·e n *)
Lemma zeta_eigen : forall s n m, Dmul (z s) (e n) m = (z s n * e n m)%R.
Proof. intros; apply diag_e_scal. Qed.

(* Z_s maps ℓ² into ℓ², is self-adjoint, and is bounded by 1 (s ≥ 0) *)
Lemma Ell2_zeta : forall s, 0 <= s -> forall f, Ell2 f -> Ell2 (Dmul (z s) f).
Proof. intros s Hs f Hf; apply (Dmul_Ell2 (z s) 1 (fun n => z_abs s n Hs) f Hf). Qed.

Lemma zeta_selfadjoint : forall s f g
  (HZf : Ell2 (Dmul (z s) f)) (Hg : Ell2 g) (Hf : Ell2 f) (HZg : Ell2 (Dmul (z s) g)),
  ip (Dmul (z s) f) g HZf Hg = ip f (Dmul (z s) g) Hf HZg.
Proof. intros; apply Dmul_selfadjoint. Qed.

Lemma zeta_bounded : forall s, 0 <= s -> forall f (Hf : Ell2 f) (HZf : Ell2 (Dmul (z s) f)),
  norm (Dmul (z s) f) HZf <= 1 * norm f Hf.
Proof. intros s Hs f Hf HZf; apply (Dmul_bound (z s) 1 (fun n => z_abs s n Hs) f Hf HZf). Qed.

(* ================================================================= *)
(*  STAGE 2 — PARTITION FUNCTION:  Tr Z_s = Σ n^{-s} = ζ(s).          *)
(* ================================================================= *)

Definition dzeta (s : R) (N : nat) : R := fold_right Rplus 0 (map (z s) (seq 1 N)).

Theorem zeta_partition : forall s N, diag_trace (z s) N = dzeta s N.
Proof. intros s N; unfold dzeta; apply diag_trace_eq. Qed.

(* ================================================================= *)
(*  STAGE 3 — von Mangoldt WEIGHTED TRACE:                           *)
(*    Tr(D_Λ Z_s) = Σ Λ(n) n^{-s} = −ζ'/ζ (s).                        *)
(* ================================================================= *)

Definition dvmzeta (s : R) (N : nat) : R :=
  fold_right Rplus 0 (map (fun n => Lam n * z s n) (seq 1 N)).

Theorem vonmangoldt_zeta_trace : forall s N,
  diag_trace (fun n => Lam n * z s n) N = dvmzeta s N.
Proof. intros s N; unfold dvmzeta; apply diag_trace_eq. Qed.

(* ================================================================= *)
(*  STAGE 4 — THE BRIDGE  (−ζ'/ζ)·ζ = −ζ'  is  Λ∗1 = log.             *)
(* ================================================================= *)

(* the log-Hamiltonian H (unbounded): energies log n *)
Definition Hlog (n : nat) : R := ln (INR n).

(* Z_s = e^{-sH}: the ζ-operator is the exponential of −sH *)
Lemma zeta_is_exp_neg_sH : forall s n, (1 <= n)%nat -> z s n = exp ((- s) * Hlog n).
Proof. intros s n Hn; unfold Hlog; apply z_exp; exact Hn. Qed.

(* per mode: the energy log n is the von Mangoldt divisor sum Σ_{d|n} Λ(d) *)
Theorem energy_eq_divisor_sum : forall n, (1 <= n)%nat -> Hlog n = dsum Lam n.
Proof. intros n Hn; unfold Hlog; symmetry; apply vonmangoldt_identity; exact Hn. Qed.

(* summatory/Perron form: the trace of H over the first N modes is the
   von Mangoldt hyperbola sum  Σ_{d≤N} Λ(d)⌊N/d⌋ (= chsum N) — the finite
   operator identity  (−ζ'/ζ)·ζ = −ζ'. *)
Theorem trace_Hlog_eq_chsum : forall N, diag_trace Hlog N = chsum N.
Proof.
  intro N; rewrite diag_trace_eq.
  change (fold_right Rplus 0 (map Hlog (seq 1 N))) with (Tlog N).
  apply order_swap_identity.
Qed.

Print Assumptions zeta_partition.
Print Assumptions vonmangoldt_zeta_trace.
Print Assumptions trace_Hlog_eq_chsum.

(* ================================================================= *)
(*  END Ell2Zeta.v                                                   *)
(*  The bounded ζ-operator Z_s = e^{-sH} on ℓ² has partition function  *)
(*  Tr Z_s = Σ n^{-s} = ζ(s); the von Mangoldt operator D_Λ is its     *)
(*  logarithmic derivative, Tr(D_Λ Z_s) = Σ Λ(n) n^{-s} = −ζ'/ζ; and   *)
(*  the two are tied by Λ∗1 = log (energy = divisor sum), whose        *)
(*  summatory form is Chebyshev's order-swap identity.  This connects  *)
(*  the ℓ² spectral apparatus to the Euler-product / ζ world.         *)
(* ================================================================= *)
