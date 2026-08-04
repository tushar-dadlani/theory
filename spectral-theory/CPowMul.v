(* ================================================================= *)
(*  CPowMul.v  —  base laws for the real-base complex power Cpw.       *)
(*                                                                    *)
(*  CexpFull gives the exponent-additive law Cpw_split                *)
(*  (Cpw c (w1+w2) = Cpw c w1 · Cpw c w2).  Here we add the           *)
(*  BASE-multiplicative laws needed to reindex the complex Euler       *)
(*  product along the integer coding map:                             *)
(*                                                                    *)
(*    Cpw_one     : Cpw 1 w = 1                                       *)
(*    Cpw_base_mul: 0<c → 0<d → Cpw (c·d) w = Cpw c w · Cpw d w       *)
(*    Cpw_base_pow: 0<c → Cpw (c^k) w = (Cpw c w)^k                   *)
(*                                                                    *)
(*  (the complex analogue of qpow_mul / qpow_mult_exp).  Axiom-clean.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull RootsOfUnity.
Open Scope R_scope.

Lemma Cpw_one : forall w, Cpw 1 w = C1.
Proof.
  intro w; unfold Cpw.
  replace (RtoC (ln 1)) with C0 by (rewrite ln_1; reflexivity).
  replace (Cmul w C0) with C0 by ring.
  change C0 with (RtoC 0); rewrite Cexpf_RtoC, exp_0; reflexivity.
Qed.

Lemma Cpw_base_mul : forall c d w, 0 < c -> 0 < d ->
  Cpw (c * d) w = Cmul (Cpw c w) (Cpw d w).
Proof.
  intros c d w Hc Hd; unfold Cpw.
  rewrite ln_mult by assumption.
  rewrite RtoC_add.
  replace (Cmul w (Cadd (RtoC (ln c)) (RtoC (ln d))))
    with (Cadd (Cmul w (RtoC (ln c))) (Cmul w (RtoC (ln d)))) by ring.
  apply Cexpf_add.
Qed.

Lemma Cpw_base_pow : forall c w k, 0 < c ->
  Cpw (c ^ k) w = Cpow (Cpw c w) k.
Proof.
  intros c w k Hc; induction k as [| k IH]; cbn [pow Cpow].
  - apply Cpw_one.
  - rewrite (Cpw_base_mul c (pow c k) w Hc (pow_lt c k Hc)), IH; reflexivity.
Qed.

Print Assumptions Cpw_base_pow.

(* ================================================================= *)
(*  END CPowMul.v                                                     *)
(* ================================================================= *)
