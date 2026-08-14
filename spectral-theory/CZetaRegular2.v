(* ================================================================= *)
(*  CZetaRegular2.v   (Phase B2, part 1: the limit sequence ell_n)     *)
(*                                                                    *)
(*  As z -> 1, each gtermC z n tends to the REAL value                  *)
(*    ell n = 1/(n+1) - ln((n+2)/(n+1)).                                *)
(*  Here we build ell and prove sum_n ell n converges (it is the        *)
(*  constant term of zeta's Laurent expansion at 1, ~ Euler-Mascheroni).*)
(*  Bounds: 0 <= ell n <= 1/(n+1) - 1/(n+2)  (telescoping), from the     *)
(*  elementary  ln x <= x - 1.                                          *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField.
Open Scope R_scope.

(* elementary:  ln x <= x - 1  (from 1 + y <= exp y) *)
Lemma ln_le_x1 : forall x, 0 < x -> ln x <= x - 1.
Proof.
  intros x Hx. pose proof (exp_ineq1_le (ln x)) as H.
  rewrite exp_ln in H by exact Hx. lra.
Qed.

Lemma Snpos : forall n, 0 < INR (S n).
Proof. intro n; apply lt_0_INR; lia. Qed.

Definition ell (n : nat) : R := / INR (S n) - ln (INR (S (S n)) / INR (S n)).

Lemma ell_nonneg : forall n, 0 <= ell n.
Proof.
  intro n. unfold ell.
  set (a := INR (S n)). set (b := INR (S (S n))).
  assert (Ha : 0 < a) by apply Snpos.
  assert (Hb : 0 < b) by apply Snpos.
  assert (Hab : b = a + 1) by (unfold a, b; rewrite (S_INR (S n)); ring).
  assert (Hr : 0 < b / a) by (apply Rdiv_lt_0_compat; assumption).
  pose proof (ln_le_x1 _ Hr) as Hln.
  assert (Hval : b / a - 1 = / a) by (rewrite Hab; field; lra).
  lra.
Qed.

Lemma ell_upper : forall n, ell n <= / INR (S n) - / INR (S (S n)).
Proof.
  intro n. unfold ell.
  set (a := INR (S n)). set (b := INR (S (S n))).
  assert (Ha : 0 < a) by apply Snpos.
  assert (Hb : 0 < b) by apply Snpos.
  assert (Hab : b = a + 1) by (unfold a, b; rewrite (S_INR (S n)); ring).
  assert (Hrec : ln (a / b) <= a / b - 1)
    by (apply ln_le_x1; apply Rdiv_lt_0_compat; assumption).
  assert (Hlninv : ln (b / a) = - ln (a / b)).
  { rewrite <- ln_Rinv by (apply Rdiv_lt_0_compat; assumption).
    f_equal. field; split; lra. }
  assert (Habm : a / b - 1 = - / b) by (rewrite Hab; field; lra).
  rewrite Hlninv. lra.
Qed.

(* the telescoping majorant  sum (1/(n+1) - 1/(n+2)) = 1 - 1/(N+2) <= 1 *)
Lemma tele_sum : forall N,
  sum_f_R0 (fun n => / INR (S n) - / INR (S (S n))) N = / INR 1 - / INR (S (S N)).
Proof.
  induction N as [| N IH]; [ cbn [sum_f_R0]; reflexivity | ].
  rewrite tech5, IH. cbv beta. lra.
Qed.

Lemma ell_cv : { L | Un_cv (sum_f_R0 ell) L }.
Proof.
  apply growing_cv.
  - intro N. rewrite tech5. pose proof (ell_nonneg (S N)). lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists 1. intros x [N Hx]. rewrite Hx.
    apply Rle_trans with (sum_f_R0 (fun n => / INR (S n) - / INR (S (S n))) N).
    + apply sum_Rle. intros k Hk. apply ell_upper.
    + rewrite tele_sum.
      assert (H1 : / INR 1 = 1) by (rewrite INR_1; apply Rinv_1).
      assert (0 < / INR (S (S N))) by (apply Rinv_0_lt_compat; apply Snpos).
      rewrite H1. lra.
Qed.

Definition ellsum : R := proj1_sig ell_cv.
Definition ellsum_cv : Un_cv (sum_f_R0 ell) ellsum := proj2_sig ell_cv.

Print Assumptions ell_cv.
