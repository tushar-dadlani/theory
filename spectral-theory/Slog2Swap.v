(* ================================================================= *)
(*  Slog2Swap.v  —  the degree-2 order-swap (toward the log^2 Selberg). *)
(*                                                                    *)
(*  The Lam_2 analog of Chebyshev.order_swap_identity (Tlog = Sum       *)
(*  Lam(d) floor(N/d)).  From  Sum_{d|n} Lam_2(d) = ln^2 n              *)
(*  (SelbergSymmetry.logsq_dsum) summed over n<=N and swapped:          *)
(*                                                                    *)
(*    Slog2_swap : Slog2 N = Sum_{d<=N} Lam_2(d) * floor(N/d)           *)
(*                                                                    *)
(*  where Slog2 N = Sum_{m<=N} ln^2 m.  This is the degree-2 symmetry   *)
(*  skeleton the log^2 Selberg inequality (star) is built on.           *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        SelbergSymmetry SelbergSum.
Import ListNotations.
Open Scope R_scope.

Theorem Slog2_swap : forall N,
  Slog2 N = Rls (seq 1 N) (fun d => Lam2 d * INR (N / d)%nat).
Proof.
  intro N.
  transitivity (Rls (seq 1 N) (fun n => Rls (divisors n) (fun d => Lam2 d))).
  { unfold Slog2; apply Rls_ext; intros n Hn; apply in_seq in Hn;
      symmetry; apply logsq_dsum; lia. }
  transitivity (Rls (seq 1 N) (fun d => Rls (seq 1 (N / d)%nat) (fun m => Lam2 d))).
  { apply (hyperbola_swap (fun d m => Lam2 d) N). }
  apply Rls_ext; intros d _; rewrite Rls_seq_const; reflexivity.
Qed.

Print Assumptions Slog2_swap.

(* ================================================================= *)
(*  END Slog2Swap.v                                                   *)
(* ================================================================= *)
