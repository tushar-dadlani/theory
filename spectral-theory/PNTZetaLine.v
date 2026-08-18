(* ================================================================= *)
(*  PNTZetaLine.v  —  PNT and the zero-free line Re(s)=1: the honest    *)
(*  reduction, with the zeta-non-vanishing input DISCHARGED.            *)
(*                                                                    *)
(*  Classically PNT is equivalent to zeta(1+it) <> 0 for all t <> 0.    *)
(*  In THIS repo the zero-free line is ALREADY A THEOREM, proved        *)
(*  unconditionally via the 3-4-1 inequality (ZetaLineNonzero.          *)
(*  zetaC_line_nonzero), NOT via PNT.  So the equivalence is not        *)
(*  symmetric here: the reverse direction PNT -> (zeta<>0) is vacuous   *)
(*  (the conclusion already holds), and the ENTIRE remaining content    *)
(*  is the forward analytic-Tauberian direction                        *)
(*                                                                    *)
(*     NewmanTransfer :  ZeroFreeLine -> pnt_theta                      *)
(*                                                                    *)
(*  i.e. Newman's Tauberian theorem.  This file:                       *)
(*                                                                    *)
(*   * PROVES  zero_free_line_holds : ZeroFreeLine  (reusing the        *)
(*     3-4-1 result zetaC_line_nonzero);                               *)
(*   * reduces PNT to the single implication NewmanTransfer, with its   *)
(*     zeta<>0 hypothesis discharged                                    *)
(*     (pnt_of_newman_transfer : NewmanTransfer -> pnt_theta);          *)
(*   * gives the honest equivalence GIVEN Newman                        *)
(*     (pnt_iff_zfl_given_newman);                                      *)
(*   * ties it back to the primorial: NewmanTransfer -> x# ~ e^x        *)
(*     (primorial_of_newman_transfer).                                  *)
(*                                                                    *)
(*  This is the ANALYTIC-route sibling of PNTUnconditional.             *)
(*  pnt_of_self_improve (the elementary Selberg route): both isolate    *)
(*  sharp PNT to a single named lemma.  The difference is that here the *)
(*  zeta<>0 input Newman consumes is already proved, so PNT reduces to  *)
(*  exactly the analytic Tauberian transfer.                           *)
(*                                                                    *)
(*  HONESTY: NewmanTransfer is NOT proved (it is Newman's Tauberian     *)
(*  theorem, still to be assembled from the repo's Newman* pieces).     *)
(*  Nothing here proves sharp PNT.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals.
Require Import ComplexField CZeta ZetaLineNonzero PrimorialChebyshev.
Open Scope R_scope.

(* the zero-free line: zeta(1+it) <> 0 for every t <> 0 *)
Definition ZeroFreeLine : Prop :=
  forall t, t <> 0 ->
    forall (H0 : 0 < Re (mkC 1 t)) (H1 : Cminus C1 (mkC 1 t) <> C0),
      zetaC (mkC 1 t) H0 H1 <> C0.

(* PROVEN unconditionally in the repo (3-4-1 inequality), not via PNT *)
Theorem zero_free_line_holds : ZeroFreeLine.
Proof. unfold ZeroFreeLine. exact zetaC_line_nonzero. Qed.

(* Newman's Tauberian theorem: the zero-free line yields PNT.           *)
(* This is the ONE remaining implication; NOT proved here.              *)
Definition NewmanTransfer : Prop := ZeroFreeLine -> pnt_theta.

(* PNT reduces to the Newman transfer, with the zeta<>0 input discharged *)
Theorem pnt_of_newman_transfer : NewmanTransfer -> pnt_theta.
Proof. intro Hnt. exact (Hnt zero_free_line_holds). Qed.

(* the reverse direction is vacuous: the zero-free line holds anyway *)
Theorem zfl_of_pnt : pnt_theta -> ZeroFreeLine.
Proof. intros _. exact zero_free_line_holds. Qed.

(* the honest equivalence: GIVEN Newman's transfer, PNT <-> zero-free line *)
Theorem pnt_iff_zfl_given_newman :
  NewmanTransfer -> (pnt_theta <-> ZeroFreeLine).
Proof.
  intro Hnt. split.
  - intros _; exact zero_free_line_holds.
  - intros _; exact (pnt_of_newman_transfer Hnt).
Qed.

(* tie back to the primorial tower: Newman's transfer -> x# ~ e^x *)
Corollary primorial_of_newman_transfer :
  NewmanTransfer -> Un_cv (fun N => ln (INR (Nprimorial N)) / INR N) 1.
Proof.
  intro Hnt. apply (proj1 pnt_iff_primorial_rate).
  exact (pnt_of_newman_transfer Hnt).
Qed.

(* ===== the reduction, bundled ===== *)
Theorem pnt_zeta_line_reduction :
  (* the zero-free line Re(s)=1 is a THEOREM here (via 3-4-1) *)
  ZeroFreeLine
  (* PNT reduces to the single analytic Tauberian implication (Newman) *)
  /\ (NewmanTransfer -> pnt_theta)
  (* honest equivalence PNT <-> zero-free line, given Newman *)
  /\ (NewmanTransfer -> (pnt_theta <-> ZeroFreeLine))
  (* and Newman's transfer would deliver the primorial rate x# ~ e^x *)
  /\ (NewmanTransfer -> Un_cv (fun N => ln (INR (Nprimorial N)) / INR N) 1).
Proof.
  split; [ exact zero_free_line_holds | ].
  split; [ exact pnt_of_newman_transfer | ].
  split; [ exact pnt_iff_zfl_given_newman | exact primorial_of_newman_transfer ].
Qed.

Print Assumptions zero_free_line_holds.
Print Assumptions pnt_zeta_line_reduction.
