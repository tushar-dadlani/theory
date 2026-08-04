(* ================================================================= *)
(*  SelbergEndgame.v  —  the Erdos-Selberg endgame, setup (Selberg 3). *)
(*                                                                    *)
(*  The remainder  R(N) := psi(N) - N,  whose asymptotic  R(N) = o(N)   *)
(*  (i.e. psi(N) ~ N) is the Prime Number Theorem.  The Erdos-Selberg   *)
(*  limit argument bootstraps from the UNCONDITIONAL Chebyshev bound     *)
(*      | R(N) |  <=  (Kup - 1) N        (Kup = 2 ln2 + 2),              *)
(*  established here from psi_upper and psi >= 0.  Axiom-clean.         *)
(*                                                                    *)
(*  (The full limit argument -- Selberg's inequality in R-form and the   *)
(*  averaging/limsup contradiction giving R(N)=o(N) -- is a large        *)
(*  further development gated on the summatory Selberg inequality.)      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal.
Open Scope R_scope.

Definition Rem (N : nat) : R := psi N - INR N.

Lemma psi_nonneg : forall N, 0 <= psi N.
Proof.
  intro N; rewrite psi_Rsum; apply Rsum_nonneg; intros i _; apply Lam_nonneg.
Qed.

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1; apply ln_increasing; lra. Qed.

(* the unconditional Chebyshev bound on the remainder *)
Theorem Rem_bound : forall N, Rabs (Rem N) <= (Kup - 1) * INR N.
Proof.
  intro N; unfold Rem.
  assert (HN : 0 <= INR N) by apply pos_INR.
  assert (Hup : psi N <= INR N * Kup) by apply psi_upper.
  assert (Hlo : 0 <= psi N) by apply psi_nonneg.
  assert (HK : 1 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  apply Rabs_le; split; nra.
Qed.

Print Assumptions Rem_bound.

(* ================================================================= *)
(*  END SelbergEndgame.v (setup: the remainder and its Chebyshev bound)*)
(* ================================================================= *)
