(* ================================================================= *)
(*  SumLogSqRatio.v  —  the cancellation  Sum ln^2(N/d) = O(N)          *)
(*                      (Step 2d, ii).                                  *)
(*                                                                    *)
(*  The exact algebraic identity                                        *)
(*      Sum_{d<=N} (ln N - ln d)^2                                       *)
(*         = N ln^2 N - 2 ln N * Tlog N + Slog2 N                        *)
(*  (pure Rls linearity), combined with the sharp Stirling bracket       *)
(*  (Tlog N = N ln N - N + O(ln N), StirlingSharp) and the Slog2 bracket *)
(*  (Slog2 N = N ln^2 N - 2N ln N + 2N + O(ln^2 N)), collapses the        *)
(*  leading terms and yields                                            *)
(*      Sum_{d<=N} (ln N - ln d)^2 = 2N + O(ln^2 N) <= 6N.               *)
(*  This is the Mobius-weighted error control for the summed Selberg     *)
(*  formula (each |mu(d)| <= 1, and ln^2(floor(N/d)) <= (ln N - ln d)^2). *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound ChebyshevPrime RealMobius
        SelbergSymmetry SelbergSum SumLogSq StirlingSharp.
Import ListNotations.
Open Scope R_scope.

(* the exact identity, from Rls linearity *)
Lemma sumlogsq_ratio_eq : forall N,
  Rls (seq 1 N) (fun d => (ln (INR N) - ln (INR d)) ^ 2)
  = INR N * (ln (INR N)) ^ 2 - 2 * ln (INR N) * Tlog N + Slog2 N.
Proof.
  intro N.
  rewrite (Rls_ext _ (fun d => (ln (INR N) - ln (INR d)) ^ 2)
             (fun d => ((ln (INR N)) ^ 2 + (-2 * ln (INR N)) * ln (INR d))
                       + (ln (INR d)) ^ 2) (seq 1 N)) by (intros d _; ring).
  rewrite (Rls_add _ (fun d => (ln (INR N)) ^ 2 + (-2 * ln (INR N)) * ln (INR d))
                     (fun d => (ln (INR d)) ^ 2) (seq 1 N)).
  rewrite (Rls_add _ (fun d => (ln (INR N)) ^ 2)
                     (fun d => (-2 * ln (INR N)) * ln (INR d)) (seq 1 N)).
  rewrite (Rls_seq_const ((ln (INR N)) ^ 2) 1 N).
  rewrite <- (Rls_scal _ (-2 * ln (INR N)) (fun d => ln (INR d)) (seq 1 N)).
  change (Rls (seq 1 N) (fun d => (ln (INR d)) ^ 2)) with (Slog2 N).
  change (Rls (seq 1 N) (fun d => ln (INR d))) with (Tlog N).
  ring.
Qed.

(* ln^2 N <= 4 N, from ln N <= 2 sqrt N *)
Lemma lnsq_le_4N : forall N, (1 <= N)%nat -> ln (INR N) * ln (INR N) <= 4 * INR N.
Proof.
  intros N HN.
  assert (H1 : 1 <= INR N) by (apply (le_INR 1); lia).
  pose proof (ln_le_2sqrt (INR N) ltac:(lra)) as Hls.
  assert (Hln0 : 0 <= ln (INR N)) by (rewrite <- ln_1; apply ln_le; lra).
  pose proof (sqrt_pos (INR N)) as Hsp.
  assert (Hsq : sqrt (INR N) * sqrt (INR N) = INR N) by (apply sqrt_sqrt; lra).
  nra.
Qed.

(* the O(N) cancellation bound *)
Theorem sumlogsq_ratio_bound : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => (ln (INR N) - ln (INR d)) ^ 2) <= 6 * INR N.
Proof.
  intros N HN.
  rewrite sumlogsq_ratio_eq.
  pose proof (Tlog_sharp N HN) as [Tlo Thi].
  pose proof (Slog2_bracket N HN) as [Slo Shi].
  pose proof (lnsq_le_4N N HN) as Hlnsq.
  assert (Hln0 : 0 <= ln (INR N)).
  { assert (1 <= INR N) by (apply (le_INR 1); lia).
    rewrite <- ln_1; apply ln_le; lra. }
  replace ((ln (INR N)) ^ 2) with (ln (INR N) * ln (INR N)) by ring.
  unfold Alsq in *.
  nra.
Qed.

Print Assumptions sumlogsq_ratio_bound.

(* ================================================================= *)
(*  END SumLogSqRatio.v                                               *)
(*  Sum_{d<=N} (ln N - ln d)^2 <= 6 N   (main term 2N, error O(ln^2 N)). *)
(* ================================================================= *)
