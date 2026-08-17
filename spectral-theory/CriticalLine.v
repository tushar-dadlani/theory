(* ================================================================= *)
(*  CriticalLine.v  —  moving the collapse argument onto the critical line. *)
(*                                                                    *)
(*  The critical line is Re s = 1/2.  Our collapse argument                 *)
(*  (EtaZetaStrip.eta_zeta_cont_strip: eta(s) = (1-2^{1-s})zeta(s) on the    *)
(*  real segment 0<s<1) meets the critical line at exactly one REAL point,  *)
(*  s = 1/2.  There we get the value of the collapse on the line:           *)
(*                                                                    *)
(*    eta_at_half : Un_cv (eta_partial (1/2)) ((1 - sqrt 2) * zeta_cont(1/2)).*)
(*                                                                    *)
(*  i.e. the (-2)^inf-oscillating alternating sum sum (-1)^{n-1} n^{-1/2}    *)
(*  converges to (1 - sqrt 2) . zeta(1/2).  Since zeta(1/2) <> 0 (the first  *)
(*  nontrivial zero is at 1/2 + i.14.13..., NOT on the real axis), this is   *)
(*  a NON-zero -- the real point of the line carries no zero, exactly as     *)
(*  expected.                                                              *)
(*                                                                    *)
(*  HONEST HORIZON.  The NONTRIVIAL zeros live at 1/2 + it (t <> 0), off     *)
(*  the real axis -- our real argument cannot reach them.  Moving the whole  *)
(*  line requires the COMPLEX eta identity  eta_C(s) = (1 - 2^{1-s}) zetaC(s)*)
(*  on Re s > 0; this is obtainable by MIRRORING EtaZetaStrip with the       *)
(*  complex Euler-Maclaurin machinery already in the repo                    *)
(*  (CDirichlet.czeta_EM_identity, CZetaTerm.gtermC/gC/GC, CPowMul.          *)
(*  Cpw_base_mul/Cpw_one) -- NO identity theorem / analytic continuation is  *)
(*  needed, just the same telescoping cancellation over C.  Then a zeta zero *)
(*  at 1/2 + it would be exactly the complex alternating sum collapsing to 0 *)
(*  at infinity.  RH -- that EVERY nontrivial zero sits on this line -- stays *)
(*  open and is not claimed here.                                          *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import Ell2ZetaCont ZeroAsLimit EtaZetaStrip.
Open Scope R_scope.

Lemma half_pos : 0 < / 2. Proof. lra. Qed.
Lemma half_ne1 : / 2 <> 1. Proof. lra. Qed.

(* our argument AT the real point of the critical line, s = 1/2:
   the alternating sum converges to (1 - sqrt 2) * zeta(1/2). *)
Theorem eta_at_half :
  Un_cv (eta_partial (/ 2)) ((1 - sqrt 2) * zeta_cont (/ 2) half_pos half_ne1).
Proof.
  pose proof (eta_zeta_cont_strip (/ 2) half_pos half_ne1) as H.
  replace (1 - Rpower 2 (1 - / 2)) with (1 - sqrt 2) in H; [ exact H | ].
  replace (1 - / 2) with (/ 2) by lra.
  rewrite (Rpower_sqrt 2) by lra. reflexivity.
Qed.

Print Assumptions eta_at_half.
