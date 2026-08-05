(* ================================================================= *)
(*  RemSpike.v  —  RUNG 2 of the Erdos-Selberg limsup layer.           *)
(*                                                                    *)
(*  "R = psi - id cannot move fast."  Since psi is nondecreasing       *)
(*  (psi_mono), for N <= M we have psi M - psi N >= 0, hence           *)
(*                                                                    *)
(*      Rem M  >=  Rem N - (INR M - INR N)          (Rem_mono_lb)      *)
(*                                                                    *)
(*  i.e. Rem can fall by at most the length of the step.  Two          *)
(*  persistence corollaries follow immediately:                        *)
(*                                                                    *)
(*    Rem_spike_forward  : a large POSITIVE value of Rem at N persists  *)
(*                         forward on [N, M]  (drops by <= M - N);      *)
(*    Rem_spike_backward : a large NEGATIVE value of Rem at N persists  *)
(*                         backward on [m, N] (rises by <= N - m).      *)
(*                                                                    *)
(*  This is the elementary geometric input to the averaging argument   *)
(*  (Rung 3): the sup/inf of Rem/id cannot be attained on a single      *)
(*  point -- it is carried across a whole multiplicative interval.      *)
(*  Axiom-clean (reuses psi_mono only).                                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import Chebyshev ChebyshevBound SelbergEndgame.
Open Scope R_scope.

(* R cannot drop faster than the step length. *)
Lemma Rem_mono_lb : forall N M, (N <= M)%nat -> Rem N - (INR M - INR N) <= Rem M.
Proof.
  intros N M H; unfold Rem; pose proof (psi_mono N M H); lra.
Qed.

(* Symmetric reading: R cannot rise faster than the step length either
   (going backward). *)
Lemma Rem_mono_ub_back : forall m N, (m <= N)%nat -> Rem m <= Rem N + (INR N - INR m).
Proof.
  intros m N H; pose proof (Rem_mono_lb m N H); lra.
Qed.

(* A large positive spike at N persists forward across [N, M]. *)
Lemma Rem_spike_forward : forall N M c,
  (N <= M)%nat -> c <= Rem N -> c - (INR M - INR N) <= Rem M.
Proof.
  intros N M c H Hc.
  apply Rle_trans with (Rem N - (INR M - INR N)); [ lra | apply Rem_mono_lb; exact H ].
Qed.

(* A large negative spike at N persists backward across [m, N]. *)
Lemma Rem_spike_backward : forall m N c,
  (m <= N)%nat -> Rem N <= c -> Rem m <= c + (INR N - INR m).
Proof.
  intros m N c H Hc.
  apply Rle_trans with (Rem N + (INR N - INR m)); [ apply Rem_mono_ub_back; exact H | lra ].
Qed.

Print Assumptions Rem_mono_lb.

(* ================================================================= *)
(*  END RemSpike.v  —  RUNG 2: the spike lemma (R moves slowly).       *)
(* ================================================================= *)
