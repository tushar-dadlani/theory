(* ================================================================= *)
(*  ZetaSBounds.v  --  turning one vm_compute into explicit real       *)
(*  bounds on zeta at a rational point off the critical line.          *)
(*                                                                    *)
(*  The analogue of CheapSign.xir_neg_cheap for the sigma-general      *)
(*  evaluator: the whole numeric computation is a BOOLEAN hypothesis   *)
(*  the caller discharges by vm_compute, and everything else is        *)
(*  discharged here once.  Two side conditions remain per call, both   *)
(*  cheap: 0 < Dts (i.e. s <> 1) and the rational tail bound, the       *)
(*  latter supplied by ZetaEncloseS.tail_le_S.                         *)
(*                                                                    *)
(*  As always in this development the computation must be INLINED in   *)
(*  the boolean hypothesis at the call site; routing it through a      *)
(*  named Definition makes Qed re-run it (documented at               *)
(*  ThirdZeroCheap.v:24 as having cost an hour).                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith Bool.
Require Import ComplexField Cmodulus CZeta CZetaTerm
        IntervalArith IntervalGint ZetaEM ZetaLineS ZetaEncloseS.
Open Scope R_scope.

Lemma Re_lineC : forall sg t, Re (lineC sg t) = sg.
Proof. reflexivity. Qed.

Lemma Im_lineC : forall sg t, Im (lineC sg t) = t.
Proof. reflexivity. Qed.

(* s <> 1 is exactly the non-vanishing of the denominator *)
Lemma lineC_ne1 : forall sg t, 0 < Dts sg t -> Cminus C1 (lineC sg t) <> C0.
Proof.
  intros sg t HD Hc.
  assert (Hr : 1 - sg = 0) by (apply (f_equal Re) in Hc; cbn in Hc; lra).
  assert (Hi : 0 - t = 0) by (apply (f_equal Im) in Hc; cbn in Hc; lra).
  unfold Dts in HD; nra.
Qed.

(* ================================================================= *)
(*  The certificate wrapper.                                          *)
(* ================================================================= *)

Theorem zetaS_bounds :
  forall (p m pl pr pc mc nc K : nat) (sq tq : Q) (M : nat)
         (Bq lr hr li hi : Q)
         (H0 : 0 < Re (lineC (Q2R sq) (Q2R tq)))
         (H1 : Cminus C1 (lineC (Q2R sq) (Q2R tq)) <> C0),
  0 < Dts (Q2R sq) (Q2R tq) ->
  Kh (lineC (Q2R sq) (Q2R tq))
    * Rpower (INR (S M)) (- Re (lineC (Q2R sq) (Q2R tq))) / INR (S M)
    <= Q2R Bq ->
  (match IzetaS p m pl pr pc mc nc K sq tq M Bq with
   | Some (zr, zi) =>
       andb (andb (Qle_bool lr (ilo zr)) (Qle_bool (ihi zr) hr))
            (andb (Qle_bool li (ilo zi)) (Qle_bool (ihi zi) hi))
   | None => false
   end) = true ->
  (Q2R lr <= Re (zetaC (lineC (Q2R sq) (Q2R tq)) H0 H1) <= Q2R hr)
  /\ (Q2R li <= Im (zetaC (lineC (Q2R sq) (Q2R tq)) H0 H1) <= Q2R hi).
Proof.
  intros p m pl pr pc mc nc K sq tq M Bq lr hr li hi H0 H1 HD HB Hc.
  destruct (IzetaS p m pl pr pc mc nc K sq tq M Bq) as [[zr zi] |] eqn:HZ;
    [ | discriminate ].
  apply andb_true_iff in Hc as [Hc1 Hc2].
  apply andb_true_iff in Hc1 as [A1 A2].
  apply andb_true_iff in Hc2 as [B1 B2].
  destruct (IzetaS_sound p m pl pr pc mc nc K sq tq M Bq zr zi H0 H1 HD HB HZ)
    as [Zr Zi].
  unfold Icontains in Zr, Zi.
  pose proof (Qle_R _ _ A1) as QA1. pose proof (Qle_R _ _ A2) as QA2.
  pose proof (Qle_R _ _ B1) as QB1. pose proof (Qle_R _ _ B2) as QB2.
  split; split; lra.
Qed.

Print Assumptions zetaS_bounds.

(* ================================================================= *)
(*  END ZetaSBounds.v -- one vm_compute in, explicit real bounds out.  *)
(* ================================================================= *)
