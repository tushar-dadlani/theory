(* ================================================================= *)
(*  AbelSummation.v                                                  *)
(*                                                                    *)
(*  SUMMATION BY PARTS (Abel summation) -- the discrete integration-   *)
(*  by-parts.                                                         *)
(*                                                                    *)
(*  In the analytic theory the bridge from zeta to primes runs through *)
(*  a CONTOUR INTEGRAL (Perron's formula + the residue theorem, whose  *)
(*  invariant is the winding number).  Our system has no complex        *)
(*  analysis and no such invariant, so we use its ELEMENTARY shadow:    *)
(*  summation by parts, whose "invariant" is the telescoping boundary   *)
(*  term.  Together with the convolution identity Lambda = mu * log     *)
(*  (VonMangoldt) this is exactly the pre-Riemann, contour-free toolkit *)
(*  behind Chebyshev's psi(x) ~ x.                                     *)
(*                                                                    *)
(*  MAIN THEOREM (abel_summation): with partial sums A_n = sum_{j<=n}   *)
(*  a_j,                                                               *)
(*                                                                    *)
(*     sum_{k=0}^{S M} a_k b_k                                         *)
(*        = A_{S M} b_{S M}                                            *)
(*          - sum_{k=0}^{M} A_k (b_{k+1} - b_k).                       *)
(*                                                                    *)
(*  Proved by induction; ring on the peeled top terms.  Uses the        *)
(*  classical Reals axioms (quarantined).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* one-step peel of a finite sum (definitional) *)
Lemma sum_f_R0_peel : forall (f : nat -> R) n,
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  SUMMATION BY PARTS                                               *)
(* ----------------------------------------------------------------- *)

Theorem abel_summation : forall (a b : nat -> R) (M : nat),
  sum_f_R0 (fun k => a k * b k) (S M)
  = sum_f_R0 a (S M) * b (S M)
    - sum_f_R0 (fun k => sum_f_R0 a k * (b (S k) - b k)) M.
Proof.
  intros a b M; induction M as [|M IH].
  - simpl; ring.
  - change (sum_f_R0 (fun k => a k * b k) (S (S M)))
      with (sum_f_R0 (fun k => a k * b k) (S M) + a (S (S M)) * b (S (S M))).
    change (sum_f_R0 a (S (S M)))
      with (sum_f_R0 a (S M) + a (S (S M))).
    change (sum_f_R0 (fun k => sum_f_R0 a k * (b (S k) - b k)) (S M))
      with (sum_f_R0 (fun k => sum_f_R0 a k * (b (S k) - b k)) M
            + sum_f_R0 a (S M) * (b (S (S M)) - b (S M))).
    rewrite IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  A useful repackaging: the "boundary minus correction" form for a   *)
(*  bounding argument -- if 0 <= A_k and the increments b_{k+1}-b_k     *)
(*  have a fixed sign, the correction sum is controlled.               *)
(* ----------------------------------------------------------------- *)

(* the correction sum in terms of partial sums *)
Definition abel_correction (a b : nat -> R) (M : nat) : R :=
  sum_f_R0 (fun k => sum_f_R0 a k * (b (S k) - b k)) M.

Corollary abel_summation' : forall (a b : nat -> R) (M : nat),
  sum_f_R0 (fun k => a k * b k) (S M)
  = sum_f_R0 a (S M) * b (S M) - abel_correction a b M.
Proof. intros a b M; unfold abel_correction; apply abel_summation. Qed.

Print Assumptions abel_summation.

(* ================================================================= *)
(*  END AbelSummation.v                                              *)
(*  Summation by parts: the discrete integration-by-parts that        *)
(*  replaces the contour-integral step in the elementary (contour-     *)
(*  free) prime bridge.  Uses the classical Reals axioms (quarantined).*)
(* ================================================================= *)
