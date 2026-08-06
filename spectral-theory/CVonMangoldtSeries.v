(* ================================================================= *)
(*  CVonMangoldtSeries.v  —  the complex von Mangoldt Dirichlet series *)
(*    Phi(s) = Sum_{n>=1} Lam(n) n^{-s},  convergent for Re s > 1.      *)
(*                                                                    *)
(*  Milestone A, file B1 of the analytic PNT (Newman) route.  Defines  *)
(*  pterm s n = Lam(n+1)*(n+1)^{-s} = Lam(n+1)*cterm s n, and proves   *)
(*  absolute convergence by dominating |pterm| = Lam(n+1) (n+1)^{-Re s} *)
(*  by ln(n+1)(n+1)^{-Re s} (Lam <= ln) and that latter series by a     *)
(*  plain p-series of exponent (Re s + 1)/2 > 1 (ln x <= (1/c) x^c).    *)
(*  Mirrors CDirichlet.cdirichlet_cv / CZetaDeriv3.dbound1_sum_cv.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CSeries CZetaTerm CZetaTerm2
        CDirichlet VonMangoldtGlobal PrimePowerReindex Chebyshev.
Open Scope R_scope.

(* ---- the term and its modulus ---- *)
Definition pterm (s : C) (n : nat) : C := Cmul (RtoC (Lam (S n))) (cterm s n).

Lemma Cmod_pterm : forall s n,
  Cmod (pterm s n) = Lam (S n) * Rpower (INR (S n)) (- Re s).
Proof.
  intros s n; unfold pterm; rewrite Cmod_mul, Cmod_RtoC, Cmod_cterm.
  rewrite Rabs_pos_eq by apply Lam_nonneg; reflexivity.
Qed.

(* ---- Lam n <= ln n : Lam is ln(spf n) on prime powers (spf n <= n) ---- *)
Lemma Lam_le_ln : forall n, (1 <= n)%nat -> Lam n <= ln (INR n).
Proof.
  intros n Hn; destruct (Nat.eq_dec n 1) as [-> | Hne].
  - rewrite Lam_1, INR_1, ln_1; lra.
  - assert (Hn2 : (2 <= n)%nat) by lia.
    unfold Lam; destruct (is_pow n (spf n) n).
    + apply ln_le'; [ apply lt_0_INR; pose proof (spf_ge2 n Hn2); lia
                    | apply le_INR; apply spf_le; exact Hn2 ].
    + rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ].
Qed.

(* ---- the dominating real series ln(n+1)(n+1)^{-Re s}, summable for Re s>1 ---- *)
Definition blam (s : C) (n : nat) : R := ln (INR (S n)) * Rpower (INR (S n)) (- Re s).

Lemma blam_sum_cv : forall s, 1 < Re s -> { T | Un_cv (sum_f_R0 (blam s)) T }.
Proof.
  intros s Hs; set (c := (Re s - 1) / 2); assert (Hc : 0 < c) by (unfold c; lra).
  assert (Hci : 0 <= / c) by (apply Rlt_le, Rinv_0_lt_compat; exact Hc).
  destruct (pseries_cv (Re s - c) ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S n)) (- (Re s - c))).
  assert (Ht0 : forall n, 0 <= term n)
    by (intro n; unfold term; apply Rlt_le; unfold Rpower; apply exp_pos).
  assert (Hd0 : forall n, 0 <= blam s n).
  { intro n; unfold blam; apply Rmult_le_pos;
      [ rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]
      | apply Rlt_le; unfold Rpower; apply exp_pos ]. }
  assert (Hbound : forall n, blam s n <= / c * term n).
  { intro n; unfold blam, term.
    assert (Hb1 : 1 <= INR (S n)) by (rewrite <- INR_1; apply le_INR; lia).
    assert (Hln : ln (INR (S n)) <= / c * Rpower (INR (S n)) c)
      by (apply ln_le_rpow; [ exact Hc | exact Hb1 ]).
    apply Rle_trans with (/ c * Rpower (INR (S n)) c * Rpower (INR (S n)) (- Re s)).
    - apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | exact Hln ].
    - rewrite Rmult_assoc, <- Rpower_plus.
      replace (c + - Re s) with (- (Re s - c)) by ring; apply Req_le; reflexivity. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hd0 (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (/ c * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun m => / c * term m) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun m => / c * term m) with (fun m => term m * / c)
        by (apply functional_extensionality; intro m; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact Hci | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M; rewrite tech5; pose proof (Ht0 (S M)); lra.
Qed.

(* ---- the complex series converges for Re s > 1 ---- *)
Lemma pvm_cv : forall s, 1 < Re s -> { P | Cseries_cv (pterm s) P }.
Proof.
  intros s Hs.
  apply (Cseries_abs_cv (pterm s) (blam s)).
  - intro n; rewrite Cmod_pterm; unfold blam.
    apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
    apply Lam_le_ln; lia.
  - apply blam_sum_cv; exact Hs.
Qed.

Definition Phi (s : C) (H : 1 < Re s) : C := proj1_sig (pvm_cv s H).

Lemma Phi_spec : forall s (H : 1 < Re s), Cseries_cv (pterm s) (Phi s H).
Proof. intros s H; unfold Phi; exact (proj2_sig (pvm_cv s H)). Qed.

Print Assumptions Phi_spec.

(* ================================================================= *)
(*  END CVonMangoldtSeries.v  —  Phi(s) = Sum Lam(n) n^{-s} on Re s>1. *)
(* ================================================================= *)
