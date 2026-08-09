(* ================================================================= *)
(*  PNTUnconditional.v  —  the by-contradiction capstone.              *)
(*                                                                    *)
(*  The whole elementary chain reaches PNT once  limsup Vrem = 0.  The  *)
(*  clean way to feed the Erdos-Selberg SELF-IMPROVEMENT into it is by   *)
(*  contradiction: with L0 := limsup Vrem >= 0, if L0 > 0 the            *)
(*  self-improvement gives a contradiction, so L0 = 0, whence psi ~ x    *)
(*  and PNT.  (The older pnt_of_avg_below cannot be reused: it           *)
(*  instantiates its hypothesis at the true limsup L0 = 0, which the     *)
(*  self-improvement/dip route cannot reach.)                           *)
(*                                                                    *)
(*    pnt_of_self_improve :                                            *)
(*      (forall L, is_limsup Vrem L -> 0 < L -> False)                  *)
(*      -> Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.        *)
(*                                                                    *)
(*  This isolates PNT to the SINGLE research lemma `self_improve`        *)
(*  (SelbergSelfImprove.v), everything else being axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound ChebyshevPrime PrimePowerReindex
        VonMangoldtGlobal RealMobius SelbergEndgame SelbergAverage
        LimSup PsiAsymp PNTConditional.
Open Scope R_scope.

Theorem pnt_of_self_improve :
  (forall L, is_limsup Vrem L -> 0 < L -> False) ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof.
  intro Hself.
  assert (Hlb : exists m, forall n, m <= Vrem n) by (exists 0; apply Vrem_nonneg).
  assert (Hub : exists M, forall n, Vrem n <= M) by (exists (Kup - 1); apply Vrem_bound_all).
  destruct (limsup_exists Vrem Hlb Hub) as [L HL].
  assert (HL0 : 0 <= L) by (apply (is_limsup_nonneg Vrem L HL); apply Vrem_nonneg).
  assert (Heq : L = 0).
  { destruct (Rle_lt_or_eq_dec 0 L HL0) as [Hpos | Heq0].
    - exfalso; exact (Hself L HL Hpos).
    - symmetry; exact Heq0. }
  rewrite Heq in HL.
  apply pi_asymp_of_psi, psi_asymp_cv, Vrem_cv0; exact HL.
Qed.

Print Assumptions pnt_of_self_improve.

(* ================================================================= *)
(*  END PNTUnconditional.v  —  PNT modulo the single self-improvement   *)
(*  lemma  `forall L, is_limsup Vrem L -> 0 < L -> False`.              *)
(* ================================================================= *)
