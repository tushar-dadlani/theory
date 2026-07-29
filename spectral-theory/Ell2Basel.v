(* ================================================================= *)
(*  Ell2Basel.v  —  the value of the partition function at s = 2:      *)
(*      ζ(2) = Tr Z_2 = π²/6.                                         *)
(*                                                                    *)
(*  Ell2ZetaConverge proved the ζ-operator trace Tr_N Z_2 = Σ_{n≤N}    *)
(*  1/n² converges; BaselZeta (the Cauchy/Vieta cotangent squeeze)     *)
(*  proves that limit is π²/6.  Composing, the spectral trace of the   *)
(*  ζ-operator at s = 2 — the primon-gas partition function — equals   *)
(*  π²/6:                                                             *)
(*      zeta2_partition_value : Un_cv (Tr_N Z_2) (π²/6).               *)
(*                                                                    *)
(*  Axiom footprint: the classical-Reals set inherited via BaselZeta   *)
(*  and the Ell2/ von Mangoldt trees.                                *)
(* ================================================================= *)

Require Import Ell2 Ell2Zeta Ell2ZetaConverge.
Require Import ZetaConverge BaselZeta.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* ζ(2) = π²/6 : the s = 2 partition-function trace converges to π²/6 *)
Theorem zeta2_value : Un_cv (fun N => dzeta 2 N) (PI ^ 2 / 6).
Proof.
  pose proof (proj2_sig zeta2_converges) as Hz.
  rewrite basel in Hz.
  apply Un_cv_unshift.
  apply (Un_cv_eq zpart); [ intro M; symmetry; apply dzeta2_eq_zpart | exact Hz ].
Qed.

(* the operator statement: the spectral trace of Z_2 converges to π²/6 *)
Theorem zeta2_partition_value : Un_cv (fun N => diag_trace (z 2) N) (PI ^ 2 / 6).
Proof.
  apply (Un_cv_eq (fun N => dzeta 2 N));
    [ intro N; symmetry; apply zeta_partition | apply zeta2_value ].
Qed.

Print Assumptions zeta2_partition_value.

(* ================================================================= *)
(*  END Ell2Basel.v                                                  *)
(*  The primon-gas partition function at s = 2 — the spectral trace    *)
(*  of the ζ-operator Z_2 on ℓ² — is exactly π²/6.                    *)
(* ================================================================= *)
