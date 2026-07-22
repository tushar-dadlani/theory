(* ================================================================= *)
(*  ZetaConverge.v                                                    *)
(*                                                                    *)
(*  AN INFINITE PROCESS: the Dirichlet series zeta(2) = sum_{n>=1} 1/n^2 *)
(*  CONVERGES -- a genuine infinite sum over ALL numbers (the total     *)
(*  primon-gas partition function at s = 2), over R.                  *)
(*                                                                    *)
(*  This is the first genuinely-infinite, over-all-primes object in the *)
(*  arc: not a per-prime factor, not a finite product, but the full     *)
(*  sum over every natural number.  Proved by monotone-bounded          *)
(*  convergence (growing_cv): the partial sums are increasing and        *)
(*  bounded above by 2, via the telescoping estimate                    *)
(*     1/(m+1)^2 <= 1/m - 1/(m+1) = 1/(m(m+1)).                         *)
(*                                                                    *)
(*  HONEST SCOPE: this proves the series CONVERGES (the limit EXISTS);  *)
(*  it does NOT compute the value (pi^2/6).  The same telescoping bound  *)
(*  gives convergence of sum 1/n^s for every real s >= 2.  The Euler     *)
(*  product identity zeta = prod_p (1-p^-s)^-1 over ALL primes, and the  *)
(*  1 < s < 2 range, remain out of scope (LEDGER.md).                   *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* term n = 1/(n+1)^2, so the partial sums are 1/1^2 + ... + 1/(N+1)^2 *)
Definition zterm (k : nat) : R := / (INR (S k)) ^ 2.
Definition zpart (N : nat) : R := sum_f_R0 zterm N.

Lemma zterm_pos : forall k, 0 < zterm k.
Proof. intro k; unfold zterm; apply Rinv_0_lt_compat, pow_lt, lt_0_INR; lia. Qed.

(* the partial sums are increasing *)
Lemma zpart_growing : Un_growing zpart.
Proof.
  intro n; unfold zpart.
  change (sum_f_R0 zterm (S n)) with (sum_f_R0 zterm n + zterm (S n)).
  pose proof (zterm_pos (S n)); lra.
Qed.

(* the telescoping bound: partial sums stay below 2 - 1/(N+1) *)
Lemma zpart_bound : forall N, zpart N <= 2 - / INR (S N).
Proof.
  induction N as [|N IH].
  - unfold zpart, zterm; simpl; rewrite ?Rinv_1; lra.
  - change (zpart (S N)) with (zpart N + zterm (S N)).
    unfold zterm; rewrite (S_INR (S N)).
    assert (Hm : 1 <= INR (S N)) by (rewrite S_INR; pose proof (pos_INR N); lra).
    set (m := INR (S N)) in *.
    assert (Hstep : / (m + 1) ^ 2 <= / m - / (m + 1)).
    { replace (/ m - / (m + 1)) with (/ (m * (m + 1))) by (field; lra).
      apply Rinv_le_contravar; nra. }
    lra.
Qed.

(* hence the partial sums are bounded above (by 2) *)
Lemma zpart_ub : has_ub zpart.
Proof.
  exists 2; intros x [n Hn]; subst x; destruct n.
  - unfold zpart, zterm; simpl; rewrite ?Rinv_1; lra.
  - pose proof (zpart_bound (S n)) as Hb.
    assert (0 < / INR (S (S n))) by (apply Rinv_0_lt_compat, lt_0_INR; lia).
    lra.
Qed.

(* THE INFINITE PROCESS: zeta(2) converges (the limit exists) *)
Theorem zeta2_converges : { l : R | Un_cv zpart l }.
Proof. apply growing_cv; [ exact zpart_growing | exact zpart_ub ]. Qed.

Print Assumptions zeta2_converges.

(* ================================================================= *)
(*  END ZetaConverge.v                                                *)
(*  zeta(2) = sum_{n>=1} 1/n^2 converges: a genuine infinite sum over   *)
(*  all numbers, via telescoping + monotone-bounded convergence.        *)
(*  Existence, not the value pi^2/6.  Uses the classical Reals axioms.  *)
(* ================================================================= *)
