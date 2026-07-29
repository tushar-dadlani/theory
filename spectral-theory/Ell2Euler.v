(* ================================================================= *)
(*  Ell2Euler.v  —  the EULER PRODUCT at the operator level.          *)
(*                                                                    *)
(*  The primon-gas factorisation, on ℓ²:                             *)
(*                                                                    *)
(*  STAGE A — the local EULER FACTOR.  For a prime p, the "p-mode" is  *)
(*  the subspace spanned by {e_{p^k} : k≥0}, on which Z_s acts with    *)
(*  eigenvalues (p^{-s})^k.  Its sub-trace (a geometric series) sums   *)
(*  to the Euler factor:                                              *)
(*     Σ_{k=0}^{∞} ⟨Z_s e_{p^k}, e_{p^k}⟩ = Σ_k (p^{-s})^k             *)
(*                                        = 1/(1 − p^{-s})            *)
(*  (euler_factor), for p ≥ 2, s > 0.                                *)
(*                                                                    *)
(*  STAGE B — the FULL product at s = 2.  Reusing EulerProductZeta's   *)
(*  euler_product_zeta2 (Π_{p≤B}(1−p^{-2})^{-1} → ζ(2)) and BaselZeta,  *)
(*  the prime product and the operator trace Tr Z_2 converge to the    *)
(*  SAME value π²/6:  ζ(2) = Tr Z_2 = Π_p (1 − p^{-2})^{-1} = π²/6.     *)
(*                                                                    *)
(*  HONEST SCOPE: the local factor is proved for all p≥2, s>0; the     *)
(*  FULL product is proved only at s = 2 (inherited from              *)
(*  EulerProductZeta), and says nothing about analytic continuation   *)
(*  or the zeta zeros.                                                *)
(*                                                                    *)
(*  Axiom footprint: the classical-Reals set inherited via the Euler / *)
(*  Basel / von Mangoldt trees.                                      *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator Ell2Basis Ell2Parseval Ell2Zeta Ell2Basel.
Require Import ZetaConverge BaselZeta EulerProductZeta EulerProductR.
From Stdlib Require Import Reals Rpower Rseries Lra Lia List.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The geometric series (from Stdlib GP_infinite).                  *)
(* ----------------------------------------------------------------- *)

Lemma geom_cv : forall x, Rabs x < 1 ->
  Un_cv (fun N => sum_f_R0 (fun k => x ^ k) N) (/ (1 - x)).
Proof.
  intros x Hx; pose proof (GP_infinite x Hx) as H; unfold Pser, infinite_sum in H.
  apply (Un_cv_eq (fun N => sum_f_R0 (fun k => 1 * x ^ k) N)); [ | ].
  - intro N; apply sum_eq; intros k _; ring.
  - intros eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn;
      apply HN; exact Hn.
Qed.

(* ----------------------------------------------------------------- *)
(*  STAGE A — the local Euler factor as a p-mode sub-trace.           *)
(* ----------------------------------------------------------------- *)

Lemma pk_ge1 : forall p k, (1 <= p)%nat -> (1 <= p ^ k)%nat.
Proof. intros p k Hp; induction k as [| k IH]; simpl; [ lia | nia ]. Qed.

Lemma exp_INR_pow : forall x k, (exp x) ^ k = exp (INR k * x).
Proof.
  intros x k; induction k as [| k IH].
  - simpl; rewrite Rmult_0_l, exp_0; reflexivity.
  - cbn [pow]; rewrite IH, <- exp_plus, S_INR; f_equal; ring.
Qed.

(* the p-mode eigenvalues are powers: n^{-s} at n = p^k is (p^{-s})^k *)
Lemma zeta_pk : forall s p k, (1 <= p)%nat -> z s (p ^ k) = (z s p) ^ k.
Proof.
  intros s p k Hp.
  rewrite (z_exp s (p ^ k) (pk_ge1 p k Hp)), pow_INR,
          (ln_pow (INR p) ltac:(apply lt_0_INR; lia) k),
          (z_exp s p Hp), exp_INR_pow.
  f_equal; ring.
Qed.

(* the eigenvalue p^{-s} has |·| < 1  for p ≥ 2, s > 0 *)
Lemma z_abs_lt1 : forall s p, (2 <= p)%nat -> 0 < s -> Rabs (z s p) < 1.
Proof.
  intros s p Hp Hs; rewrite (z_exp s p ltac:(lia)).
  assert (Hln : 0 < ln (INR p))
    by (rewrite <- ln_1; apply ln_increasing; [ lra | rewrite <- INR_1; apply lt_INR; lia ]).
  rewrite Rabs_pos_eq by (left; apply exp_pos).
  rewrite <- exp_0; apply exp_increasing; nra.
Qed.

(* the sub-trace of Z_s over the p-mode {e_{p^k} : k ≤ K} *)
Definition euler_subtrace (s : R) (p : nat) (K : nat) : R :=
  sum_f_R0 (fun k => ip (Dmul (z s) (e (p ^ k))) (e (p ^ k))
                        (Ell2_diag_e (z s) (p ^ k)) (Ell2_e (p ^ k))) K.

Lemma euler_subtrace_eq : forall s p K, (1 <= p)%nat ->
  euler_subtrace s p K = sum_f_R0 (fun k => (z s p) ^ k) K.
Proof.
  intros s p K Hp; unfold euler_subtrace; apply sum_eq; intros k _.
  rewrite (diag_matrix_elt (z s) (p ^ k)); apply zeta_pk; exact Hp.
Qed.

(* THE LOCAL EULER FACTOR: the p-mode sub-trace → 1/(1 − p^{-s}) *)
Theorem euler_factor : forall s p, (2 <= p)%nat -> 0 < s ->
  Un_cv (fun K => euler_subtrace s p K) (/ (1 - z s p)).
Proof.
  intros s p Hp Hs.
  apply (Un_cv_eq (fun K => sum_f_R0 (fun k => (z s p) ^ k) K)).
  - intro K; symmetry; apply euler_subtrace_eq; lia.
  - apply geom_cv, z_abs_lt1; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  STAGE B — the full Euler product at s = 2 (via EulerProductZeta). *)
(* ----------------------------------------------------------------- *)

(* Π_{p≤B}(1 − p^{-2})^{-1} → π²/6, the same value as the operator     *)
(* trace Tr Z_2 (zeta2_partition_value).  So ζ(2) = Tr Z_2 = the       *)
(* Euler product over all primes = π²/6.                             *)
Theorem euler_product_operator_2 :
  Un_cv (fun N => Zfactor (map (fun p => / (IZR p) ^ 2) (primes_upto (S N)))) (PI ^ 2 / 6).
Proof. pose proof euler_product_zeta2 as H; rewrite basel in H; exact H. Qed.

Print Assumptions euler_factor.
Print Assumptions euler_product_operator_2.

(* ================================================================= *)
(*  END Ell2Euler.v                                                  *)
(*  Locally, each prime contributes the Euler factor (1−p^{-s})^{-1}   *)
(*  as the geometric sub-trace of Z_s over that prime's mode; globally *)
(*  at s = 2 the operator trace Tr Z_2 equals the full prime product   *)
(*  Π_p (1−p^{-2})^{-1} = π²/6.  The Euler product realized on ℓ².     *)
(* ================================================================= *)
