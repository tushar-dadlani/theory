(* ================================================================= *)
(*  LandauerBoundL.v                                                  *)
(*                                                                    *)
(*  The Landauer bound with the one-bit ENTROPY ABSTRACTED to a       *)
(*  parameter L -- the axiom-free version of LandauerBound.v.         *)
(*                                                                    *)
(*  LandauerBound.v proved the one genuinely transcendental fact,     *)
(*  Hb(1/2) = ln 2, which forces the classical Reals axioms.  Here we  *)
(*  do NOT compute the entropy: we take the entropy of one fair bit    *)
(*  as a positive PARAMETER L (= ln 2 in the R interpretation, but we  *)
(*  never commit to that value).  Everything else -- the k T L bound,  *)
(*  positivity, additivity over bits, monotonicity, the second-law     *)
(*  inequality -- is then pure Q arithmetic, axiom-free.              *)
(*                                                                    *)
(*  So the transcendental `ln 2` is quarantined to a labelled          *)
(*  parameter, and the WHOLE spectral chain becomes axiom-free.        *)
(* ================================================================= *)

From Stdlib Require Import QArith Lqa.
Open Scope Q_scope.

Section LandauerL.

Variables k T L : Q.       (* Boltzmann constant, temperature, one-bit entropy *)
Hypothesis Hk : 0 < k.
Hypothesis HT : 0 < T.
Hypothesis HL : 0 < L.     (* L = ln 2 > 0 in the R interpretation *)

(* the model's minimum dissipated heat for an entropy drop dS at T *)
Definition landauer_min (dS : Q) : Q := k * T * dS.

(* erasing one fair bit drops entropy by L, and so dissipates k T L *)
Theorem erase_bit_heat : landauer_min L == k * T * L.
Proof. unfold landauer_min; reflexivity. Qed.

(* erasing n bits (entropy drop n*L) costs n times as much *)
Theorem landauer_additive : forall a b,
  landauer_min (a + b) == landauer_min a + landauer_min b.
Proof. intros a b; unfold landauer_min; ring. Qed.

Lemma HkT : 0 < k * T.
Proof. nra. Qed.

(* the heat is monotone in the entropy erased *)
Theorem landauer_monotone : forall a b, a <= b -> landauer_min a <= landauer_min b.
Proof. intros a b Hab; unfold landauer_min; pose proof HkT; nra. Qed.

(* the erasure cost is strictly positive *)
Theorem landauer_cost_positive : 0 < k * T * L.
Proof. pose proof HkT; nra. Qed.

(* the second-law inequality: dissipated heat is at least the floor *)
Theorem landauer_inequality :
  forall Qh, Qh >= landauer_min L -> Qh >= k * T * L.
Proof. intros Qh H; unfold landauer_min in H; exact H. Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — axiom-free over Q                                *)
(* ----------------------------------------------------------------- *)

Theorem landauer_L :
  landauer_min L == k * T * L
  /\ (forall a b, landauer_min (a + b) == landauer_min a + landauer_min b)
  /\ (forall a b, a <= b -> landauer_min a <= landauer_min b)
  /\ 0 < k * T * L
  /\ (forall Qh, Qh >= landauer_min L -> Qh >= k * T * L).
Proof.
  split; [ exact erase_bit_heat | ].
  split; [ exact landauer_additive | ].
  split; [ exact landauer_monotone | ].
  split; [ exact landauer_cost_positive | exact landauer_inequality ].
Qed.

End LandauerL.

Print Assumptions landauer_L.

(* ================================================================= *)
(*  END LandauerBoundL.v                                              *)
(*  The Landauer floor k T L with L the abstract one-bit entropy       *)
(*  (= ln 2 over R).  ZERO Admitted; Closed under the global context.  *)
(* ================================================================= *)
