(* ================================================================= *)
(*  Ell2ZetaCont.v  —  the operator's ζ as a real function past s = 2  *)
(*  (pole and all), via the Euler–Maclaurin continuation.             *)
(*                                                                    *)
(*  Ell2ZetaConverge showed the ζ-operator trace Tr_N Z_s = Σ_{n≤N}    *)
(*  n^{-s} converges for s ≥ 2.  ZetaContinuation continues ζ to the   *)
(*  whole real half-line (0,∞)∖{1} (axiom-free, Euler–Maclaurin):     *)
(*      ζ̃(s) = 1/(s−1) + Σ_{n≥0} gterm s n,                          *)
(*  the 1/(s−1) being the pole at s=1 and the series converging for    *)
(*  every s>0.  Here we HOOK THE OPERATOR TRACE INTO IT:              *)
(*                                                                    *)
(*    • dzeta_eq_Zpart : the operator trace is ZetaContinuation's      *)
(*      Dirichlet partial sum  (dzeta s (S M) = Zpart s M);           *)
(*    • operator_zeta_cont / operator_zeta_eq_cont : for s>1 the       *)
(*      operator trace Tr_N Z_s converges to the continued value       *)
(*      zeta_cont s = 1/(s−1) + Σ gterm s.                            *)
(*                                                                    *)
(*  So the operator's partition function ζ(s) = Tr Z_s, previously a   *)
(*  limit only for s≥2, is now a genuine real function on (0,∞)∖{1}    *)
(*  (its continuation zeta_cont), agreeing with the trace for all s>1  *)
(*  and exhibiting the pole 1/(s−1) at s=1.  (For 0<s<1 the continued  *)
(*  value zeta_cont s still exists, though the naive trace diverges.)  *)
(*                                                                    *)
(*  Axiom footprint: the classical-Reals set inherited via Ell2Zeta    *)
(*  and ZetaContinuation.                                            *)
(* ================================================================= *)

Require Import Ell2 Ell2Zeta Ell2ZetaConverge.
Require Import HagedornTransition ZetaContinuation.
From Stdlib Require Import Reals Rpower Lra Lia List.
Import ListNotations.
Open Scope R_scope.

(* the operator symbol on a successor index is the plain power *)
Lemma z_S : forall s k, z s (S k) = Rpower (INR (S k)) (- s).
Proof. intros s k; unfold z; reflexivity. Qed.

(* THE BRIDGE: the operator trace is ZetaContinuation's Dirichlet sum *)
Lemma dzeta_eq_Zpart : forall s M, dzeta s (S M) = Zpart s M.
Proof.
  intros s M; induction M as [| M IH].
  - rewrite dzeta_succ, (z_S s 0); unfold dzeta, Zpart; simpl; ring.
  - rewrite dzeta_succ, IH, Zpart_tech5, (z_S s (S M)); reflexivity.
Qed.

(* for s>1, the operator trace and the EM continuation series share a
   common limit *)
Theorem operator_zeta_cont : forall s, 1 < s ->
  exists Z : R,
    Un_cv (fun N => diag_trace (z s) N) Z /\
    Un_cv (fun N => / (s - 1) + sum_f_R0 (gterm s) N) Z.
Proof.
  intros s Hs.
  destruct (zeta_analytic_continuation s ltac:(lra) ltac:(lra)) as [Z [Hem Hzp]].
  exists Z; split; [ | exact Hem ].
  apply (Un_cv_eq (fun N => dzeta s N)); [ intro N; symmetry; apply zeta_partition | ].
  apply Un_cv_unshift.
  apply (Un_cv_eq (Zpart s)); [ intro M; symmetry; apply dzeta_eq_Zpart | apply Hzp; exact Hs ].
Qed.

(* the continued ζ as a real function on (0,∞)∖{1} : 1/(s−1) + regular *)
Definition zeta_cont (s : R) (Hs0 : 0 < s) (Hs1 : s <> 1) : R :=
  / (s - 1) + proj1_sig (gterm_cv s Hs0 Hs1).

Lemma zeta_cont_series : forall s (Hs0 : 0 < s) (Hs1 : s <> 1),
  Un_cv (fun N => / (s - 1) + sum_f_R0 (gterm s) N) (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1; unfold zeta_cont.
  apply CV_plus; [ apply Un_cv_const | apply (proj2_sig (gterm_cv s Hs0 Hs1)) ].
Qed.

(* THE OPERATOR ζ IS ITS CONTINUATION: for s>1, Tr Z_s → zeta_cont s *)
Theorem operator_zeta_eq_cont : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  Un_cv (fun N => diag_trace (z s) N) (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hs.
  destruct (operator_zeta_cont s Hs) as [Z [Htr Hem]].
  assert (HZ : Z = zeta_cont s Hs0 Hs1)
    by (apply (UL_sequence (fun N => / (s - 1) + sum_f_R0 (gterm s) N));
        [ exact Hem | apply zeta_cont_series ]).
  rewrite <- HZ; exact Htr.
Qed.

Print Assumptions dzeta_eq_Zpart.
Print Assumptions operator_zeta_eq_cont.

(* ================================================================= *)
(*  END Ell2ZetaCont.v                                               *)
(*  The ζ-operator's partition function is now a real function        *)
(*  zeta_cont on (0,∞)∖{1} — the Euler–Maclaurin continuation of      *)
(*  Σ n^{-s} — equal to the spectral trace Tr Z_s for every s>1 and    *)
(*  carrying the pole 1/(s−1) at s=1.                                 *)
(* ================================================================= *)
