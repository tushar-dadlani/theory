(* ================================================================= *)
(*  PrimorialEulerBound.v                                             *)
(*                                                                    *)
(*  "ARE THE PRIMORIAL RUNGS UNIFORMLY BOUNDED?"  -- yes, and so the    *)
(*  primorial-relativized Euler product CONVERGES.                     *)
(*                                                                    *)
(*  Under the honest hypothesis that the i-th prime satisfies           *)
(*  P i >= i + 2 (true for the actual primes: p_0=2, p_1=3, p_2=5,...),  *)
(*  we majorize each Euler factor 1/(1 - p_i^{-2}) by the consecutive-   *)
(*  integer factor 1/(1 - 1/(i+2)^2), whose product TELESCOPES:          *)
(*                                                                    *)
(*     M n = prod_{i<n} 1/(1 - 1/(i+2)^2) = 2 - 2/(n+2) < 2.            *)
(*                                                                    *)
(*  Hence EP n <= M n < 2 for ALL n: the primorial rungs are uniformly  *)
(*  bounded.  Combined with EP_monotone (PrimorialEuler), monotone-      *)
(*  bounded convergence (growing_cv) gives EP_converges: the Euler       *)
(*  product over all primes, relativized to the primorial tower,         *)
(*  EXISTS as a limit.                                                 *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

Require Import PrimorialEuler EulerFactorR EulerProductR.
From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Open Scope R_scope.

Section Bound.

Variable P : nat -> R.
Hypothesis HP : forall i, INR i + 2 <= P i.

Lemma HP2 : forall i, 2 <= P i.
Proof. intro i; pose proof (HP i); pose proof (pos_INR i); lra. Qed.

(* the consecutive-integer majorant factor 1/(1 - 1/(i+2)^2) *)
Definition mfac (i : nat) : R := / (1 - / (INR i + 2) ^ 2).
Definition M (n : nat) : R := fold_right Rmult 1 (map mfac (seq 0 n)).

Lemma M_rec : forall n, M (S n) = M n * mfac n.
Proof.
  intro n; unfold M; rewrite seq_S, map_app; cbn [map];
    rewrite Nat.add_0_l; apply fold_mult_app.
Qed.

(* the telescoping closed form *)
Lemma M_closed : forall n, M n = 2 - 2 / (INR n + 2).
Proof.
  induction n as [|n IH].
  - unfold M; simpl; lra.
  - rewrite M_rec, IH; unfold mfac; rewrite S_INR.
    assert (Ha : 2 <= INR n + 2) by (pose proof (pos_INR n); lra).
    field; repeat split; apply Rgt_not_eq; nra.
Qed.

Lemma M_le_2 : forall n, M n <= 2.
Proof.
  intro n; rewrite M_closed.
  assert (0 < 2 / (INR n + 2))
    by (apply Rdiv_lt_0_compat; [ lra | pose proof (pos_INR n); lra ]); lra.
Qed.

(* each Euler factor is majorized by the consecutive-integer factor *)
Lemma factor_le : forall n, / (1 - fug P n) <= mfac n.
Proof.
  intro n; unfold mfac.
  assert (Ha : 2 <= INR n + 2) by (pose proof (pos_INR n); lra).
  assert (Hpn : INR n + 2 <= P n) by apply HP.
  assert (Hpos2 : 0 < (INR n + 2) ^ 2) by nra.
  assert (Hsq : (INR n + 2) ^ 2 <= (P n) ^ 2) by (apply pow_incr; split; lra).
  assert (Hf : fug P n <= / (INR n + 2) ^ 2).
  { change (fug P n) with (/ (P n) ^ 2);
      apply Rinv_le_contravar; [ exact Hpos2 | exact Hsq ]. }
  assert (Hc : 0 < 1 - / (INR n + 2) ^ 2).
  { assert (/ (INR n + 2) ^ 2 <= / 4) by (apply Rinv_le_contravar; nra); lra. }
  apply Rinv_le_contravar; lra.
Qed.

(* the primorial rungs are majorized by the telescoping product *)
Lemma EP_le_M : forall n, EP P n <= M n.
Proof.
  induction n as [|n IH].
  - unfold EP, pfugs, Zfactor, M; simpl; lra.
  - rewrite (EP_rec P n), M_rec.
    apply Rmult_le_compat.
    + apply Rlt_le, (EP_pos P HP2).
    + apply Rlt_le, Rinv_0_lt_compat; pose proof (fug_lt1 P HP2 n); lra.
    + exact IH.
    + apply factor_le.
Qed.

(* UNIFORM BOUND: every primorial rung is below 2 *)
Theorem EP_bounded : forall n, EP P n <= 2.
Proof. intro n; apply Rle_trans with (M n); [ apply EP_le_M | apply M_le_2 ]. Qed.

Lemma EP_has_ub : has_ub (EP P).
Proof. exists 2; intros x [n Hn]; subst x; apply EP_bounded. Qed.

(* CONVERGENCE: the primorial-relativized Euler product exists as a limit *)
Theorem EP_converges : { l : R | Un_cv (EP P) l }.
Proof.
  apply growing_cv; [ exact (EP_monotone P HP2) | exact EP_has_ub ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the rungs are uniformly bounded, tower converges *)
(* ----------------------------------------------------------------- *)

Theorem primorial_euler_converges :
  (forall n, M n = 2 - 2 / (INR n + 2))          (* telescoping majorant *)
  /\ (forall n, EP P n <= M n)                   (* rungs majorized *)
  /\ (forall n, EP P n <= 2)                     (* uniformly bounded *)
  /\ (exists l : R, Un_cv (EP P) l).             (* hence converges *)
Proof.
  split; [ exact M_closed | ].
  split; [ exact EP_le_M | ].
  split; [ exact EP_bounded | ].
  destruct EP_converges as [l Hl]; exists l; exact Hl.
Qed.

End Bound.

Print Assumptions primorial_euler_converges.

(* ================================================================= *)
(*  END PrimorialEulerBound.v                                         *)
(*  The primorial rungs EP n are uniformly bounded (EP n <= 2 < oo) via *)
(*  the telescoping majorant M n = 2 - 2/(n+2); with EP_monotone the     *)
(*  primorial-relativized Euler product converges.  Reals axioms.       *)
(* ================================================================= *)
