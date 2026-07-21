(* ================================================================= *)
(*  LandauerBound.v                                                   *)
(*                                                                    *)
(*  THE GENUINE k T ln 2 -- the information/thermodynamics layer.     *)
(*                                                                    *)
(*  Landauer.v charged the residue erasure a lost L^2 energy (3/4     *)
(*  ||res||^2).  Here we account the SAME erasure in information +    *)
(*  temperature units and recover the textbook bound k T ln 2.        *)
(*                                                                    *)
(*  What is a genuine THEOREM (pure math, only the Reals axioms):     *)
(*    - the Shannon entropy of a fair bit is ln 2  (Hb (1/2) = ln 2), *)
(*    - the entropy of a deterministic bit is 0    (Hb 0 = Hb 1 = 0), *)
(*    - so erasing (resetting a fair bit to a definite value) drops   *)
(*      entropy by exactly ln 2.                                      *)
(*                                                                    *)
(*  What is PHYSICS, kept explicit and NOT smuggled as an axiom:      *)
(*    - the entropy->heat conversion at temperature T is the second   *)
(*      law, `heat >= k T (dS)`.  We model the minimum dissipated     *)
(*      heat as `landauer_min dH = k T dH` (a DEFINITION), and give   *)
(*      the inequality form with the second law as an explicit        *)
(*      HYPOTHESIS.  k and T are section variables (0<k, 0<T), so no  *)
(*      physical constant is added to the trusted base.               *)
(*                                                                    *)
(*  Result: erasing a fair bit costs exactly k T ln 2, strictly       *)
(*  positive.  The "ln 2" is proved; the "k T" is the carried         *)
(*  conversion.  This is the one bit of information in the involution *)
(*  residue (the sign bit distinguishing f from Rop f); its           *)
(*  thermodynamic floor is k T ln 2.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — Shannon entropy of a Bernoulli bit (pure math)        *)
(* ----------------------------------------------------------------- *)

(* p log p with the standard 0 log 0 = 0 convention *)
Definition plogp (x : R) : R := if Rle_dec x 0 then 0 else x * ln x.

(* binary (Bernoulli) entropy, in nats *)
Definition Hb (p : R) : R := - (plogp p + plogp (1 - p)).

Lemma plogp_pos : forall x, 0 < x -> plogp x = x * ln x.
Proof. intros x Hx; unfold plogp; destruct (Rle_dec x 0); [ lra | reflexivity ]. Qed.

Lemma plogp_zero : plogp 0 = 0.
Proof. unfold plogp; destruct (Rle_dec 0 0); [ reflexivity | lra ]. Qed.

Lemma ln_half : ln (1 / 2) = - ln 2.
Proof.
  replace (1 / 2) with (/ 2) by lra.
  rewrite ln_Rinv; [ reflexivity | lra ].
Qed.

Lemma ln2_pos : 0 < ln 2.
Proof.
  rewrite <- ln_1; apply ln_increasing; lra.
Qed.

(* the fair bit has entropy ln 2 *)
Theorem Hb_half : Hb (1 / 2) = ln 2.
Proof.
  unfold Hb; replace (1 - 1 / 2) with (1 / 2) by lra.
  rewrite !(plogp_pos (1 / 2)) by lra.
  rewrite ln_half; lra.
Qed.

(* a deterministic bit has entropy 0 *)
Theorem Hb_zero : Hb 0 = 0.
Proof.
  unfold Hb; replace (1 - 0) with 1 by lra.
  rewrite plogp_zero, (plogp_pos 1) by lra.
  rewrite ln_1; lra.
Qed.

Theorem Hb_one : Hb 1 = 0.
Proof.
  unfold Hb; replace (1 - 1) with 0 by lra.
  rewrite plogp_zero, (plogp_pos 1) by lra.
  rewrite ln_1; lra.
Qed.

(* erasing a fair bit drops the entropy by exactly ln 2 *)
Theorem bit_entropy_drop : Hb (1 / 2) - Hb 0 = ln 2.
Proof. rewrite Hb_half, Hb_zero; ring. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — the Landauer bound k T ln 2 (physics: k, T explicit)  *)
(* ----------------------------------------------------------------- *)

Section Landauer_kT.

Variables k T : R.            (* Boltzmann constant and temperature *)
Hypothesis kpos : 0 < k.
Hypothesis Tpos : 0 < T.

(* the model's minimum dissipated heat for an entropy drop dH at      *)
(* temperature T (the entropy->heat conversion of the second law).    *)
Definition landauer_min (dH : R) : R := k * T * dH.

(* erasing a fair bit costs exactly k T ln 2 *)
Theorem erase_fair_bit_heat :
  landauer_min (Hb (1 / 2) - Hb 0) = k * T * ln 2.
Proof. unfold landauer_min; rewrite bit_entropy_drop; ring. Qed.

(* and that cost is strictly positive *)
Theorem landauer_cost_positive : 0 < k * T * ln 2.
Proof.
  apply Rmult_lt_0_compat;
    [ apply Rmult_lt_0_compat; [ exact kpos | exact Tpos ] | exact ln2_pos ].
Qed.

(* the inequality form: the SECOND LAW is an explicit premise         *)
(* (dissipated heat is at least k T times the entropy drop), and it   *)
(* yields the textbook floor k T ln 2. *)
Theorem landauer_inequality :
  forall Q, Q >= k * T * (Hb (1 / 2) - Hb 0) -> Q >= k * T * ln 2.
Proof.
  intros Q H; rewrite bit_entropy_drop in H; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the genuine k T ln 2                             *)
(* ----------------------------------------------------------------- *)

Theorem landauer_kT_ln2 :
  Hb (1 / 2) = ln 2                                     (* fair-bit entropy *)
  /\ Hb 0 = 0                                            (* erased-bit entropy *)
  /\ landauer_min (Hb (1 / 2) - Hb 0) = k * T * ln 2     (* erasure heat *)
  /\ 0 < k * T * ln 2                                    (* strictly positive *)
  /\ (forall Q, Q >= k * T * (Hb (1 / 2) - Hb 0) -> Q >= k * T * ln 2). (* second law *)
Proof.
  split; [ exact Hb_half | ].
  split; [ exact Hb_zero | ].
  split; [ exact erase_fair_bit_heat | ].
  split; [ exact landauer_cost_positive | exact landauer_inequality ].
Qed.

End Landauer_kT.

Print Assumptions landauer_kT_ln2.

(* ================================================================= *)
(*  END LandauerBound.v                                               *)
(*  Erasing one bit of information (the involution's residue-bit)      *)
(*  drops Shannon entropy by ln 2, so its thermodynamic floor is       *)
(*  k T ln 2 -- the "ln 2" proved, the "k T" the physical conversion.  *)
(*  ZERO Admitted.                                                    *)
(* ================================================================= *)
