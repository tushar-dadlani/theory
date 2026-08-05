(* ================================================================= *)
(*  MertensTail.v  —  RUNG 3c-B input: the tiny-scale Mertens bound.    *)
(*                                                                    *)
(*  The Lam/d-weight of a tail range [M+1, N] is O(1) in log-terms:     *)
(*                                                                    *)
(*    mertens_tail : msum N - msum M <= ln N - ln M + 2*Kup.            *)
(*                                                                    *)
(*  This bounds the contribution of the "tiny scales" (N/d < N0, i.e.   *)
(*  d > N/N0) to the averaged Selberg sum: their total weight is        *)
(*  msum N - msum(N/N0) <= ln N0 + 2 Kup = O(1).  Two applications of    *)
(*  mertens_lam.  Axiom-clean.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ChebyshevBound MertensVonMangoldt.
Open Scope R_scope.

Theorem mertens_tail : forall M N, (1 <= M)%nat -> (1 <= N)%nat ->
  msum N - msum M <= ln (INR N) - ln (INR M) + 2 * Kup.
Proof.
  intros M N HM HN.
  pose proof (mertens_lam N HN) as HN'.
  pose proof (mertens_lam M HM) as HM'.
  assert (H1 : msum N - ln (INR N) <= Kup)
    by (eapply Rle_trans; [ apply Rle_abs | exact HN' ]).
  assert (H2 : ln (INR M) - msum M <= Kup)
    by (eapply Rle_trans; [ apply Rle_abs | rewrite Rabs_minus_sym; exact HM' ]).
  lra.
Qed.

Print Assumptions mertens_tail.

(* ================================================================= *)
(*  END MertensTail.v                                                 *)
(* ================================================================= *)
