(* ================================================================= *)
(*  WeilPositivityReduction.v  —  Weil's positivity criterion as an     *)
(*  honest logical skeleton (the cost>=0 forcing operator).             *)
(*                                                                    *)
(*  The prime-zero duality (explicit formula), written as a quadratic   *)
(*  form on test functions, gives Weil's criterion:                     *)
(*                                                                    *)
(*     RH  <->  W(f conv f-star) >= 0  for all test functions f.       *)
(*                                                                    *)
(*  Positivity FORCES the zeros onto Re=1/2: an on-line zero makes W a  *)
(*  genuine sum of squares (>=0); an off-line zero (which drags a full  *)
(*  Klein 4-group {z,1-z,conj z,1-conj z} straddling the line) can be   *)
(*  made to contribute a NEGATIVE test value.  So W>=0 leaves the zeros *)
(*  nowhere to go but the critical line.                                *)
(*                                                                    *)
(*  This file builds the LOGICAL SKELETON of that criterion.  The       *)
(*  irreducibly-analytic content is isolated as explicit Section        *)
(*  hypotheses:                                                         *)
(*    - rho_onto      : the zeros are enumerable (the HADAMARD keystone,*)
(*                      missing in the repo: needs Jensen/zero-count);  *)
(*    - W_sos_of_RH   : on-line zeros => W is a sum of squares (the     *)
(*                      explicit formula's archimedean-side positivity);*)
(*    - W_neg_of_offline : an off-line zero yields a negative test      *)
(*                      value (the explicit formula's off-line term).   *)
(*  From these the criterion equivalence is proved, and wired to the    *)
(*  PROVEN one-sided reduction (SpectralReflectionBridge.RH_iff_no_left).*)
(*                                                                    *)
(*  HONESTY: WeilPositive is the framework-native cost>=0 forcing       *)
(*  operator -- an EQUIVALENT REFORMULATION of RH, not a proof.  The    *)
(*  hypotheses are Section Variables/Hypotheses (discharged at End),    *)
(*  never Axiom/admit.  Nothing here proves RH.  Axiom-clean.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire ZetaZeroPairing ZetaZeroQuadruple
        SpectralReflectionBridge.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A. the per-zero forcing scalar: vanishes exactly on the line       *)
(* ----------------------------------------------------------------- *)

Definition line_defect (z : C) : R := (2 * Re z - 1) ^ 2.

Lemma line_defect_nonneg : forall z, 0 <= line_defect z.
Proof. intro z. unfold line_defect. apply pow2_ge_0. Qed.

Lemma line_defect_zero_iff : forall z, line_defect z = 0 <-> Re z = / 2.
Proof.
  intro z. unfold line_defect. split.
  - intro H. assert (H0 : 2 * Re z - 1 = 0).
    { apply Rsqr_0_uniq. unfold Rsqr. rewrite <- H. ring. }
    lra.
  - intro H. rewrite H. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B. an off-line zero drags a full Klein 4-group (reflection makes   *)
(*     off-line configurations detectable by the Weil pairing)         *)
(* ----------------------------------------------------------------- *)

Lemma offline_zero_quadruple : forall z, XiC z = C0 -> Re z <> / 2 ->
  XiC z = C0 /\ XiC (Cminus C1 z) = C0 /\ XiC (Cconj z) = C0
  /\ XiC (Cminus C1 (Cconj z)) = C0 /\ 0 < line_defect z.
Proof.
  intros z Hz Hne.
  pose proof (XiC_zero_quadruple z Hz) as [H1 [H2 [H3 H4]]].
  repeat split; try assumption.
  destruct (line_defect_nonneg z) as [Hpos | Hzero]; [ exact Hpos | ].
  exfalso; apply Hne; apply line_defect_zero_iff; symmetry; exact Hzero.
Qed.

(* ----------------------------------------------------------------- *)
(*  C. the Weil criterion skeleton (hypothesis-gated reduction)        *)
(* ----------------------------------------------------------------- *)

Section Weil.

(* the HADAMARD keystone, abstracted: the zeros are enumerable *)
Variable rho : nat -> C.
Hypothesis rho_zero : forall n, XiC (rho n) = C0.
Hypothesis rho_onto : forall z, XiC z = C0 -> exists n, z = rho n.

(* the Weil quadratic form on test functions, and its two explicit-    *)
(* formula properties (the archimedean-side positivity analysis)       *)
Variable Wform : (nat -> R) -> R.
Hypothesis W_sos_of_RH :
  (forall n, Re (rho n) = / 2) -> forall f, 0 <= Wform f.
Hypothesis W_neg_of_offline :
  (exists n, Re (rho n) <> / 2) -> exists f, Wform f < 0.

Definition WeilPositive : Prop := forall f, 0 <= Wform f.

(* Weil's criterion: RH <-> the cost functional is nonnegative *)
Theorem RH_iff_WeilPositive :
  (forall z, XiC z = C0 -> Re z = / 2) <-> WeilPositive.
Proof.
  split.
  - (* RH -> W >= 0 : on-line zeros make W a sum of squares *)
    intro HRH. unfold WeilPositive. apply W_sos_of_RH.
    intro n. exact (HRH (rho n) (rho_zero n)).
  - (* W >= 0 -> RH : an off-line zero would give a negative test value *)
    intros HW z Hz. destruct (Req_dec (Re z) (/ 2)) as [Heq | Hne]; [ exact Heq | ].
    exfalso.
    destruct (rho_onto z Hz) as [n Hn].
    assert (Hne' : Re (rho n) <> / 2) by (rewrite <- Hn; exact Hne).
    destruct (W_neg_of_offline (ex_intro _ n Hne')) as [f Hf].
    pose proof (HW f) as Hpos. lra.
Qed.

(* bridge to the PROVEN one-sided reduction: the cost functional sits   *)
(* in the established RH-reduction family                               *)
Theorem weil_positive_iff_no_left :
  WeilPositive <-> (forall z, XiC z = C0 -> / 2 <= Re z).
Proof.
  split; intro H.
  - exact (proj1 RH_iff_no_left (proj2 RH_iff_WeilPositive H)).
  - exact (proj1 RH_iff_WeilPositive (proj2 RH_iff_no_left H)).
Qed.

(* ===== the reduction, bundled ===== *)
Theorem weil_positivity_reduction :
  (* A. the per-zero forcing scalar *)
  (forall z, 0 <= line_defect z)
  /\ (forall z, line_defect z = 0 <-> Re z = / 2)
  (* B. off-line zeros come as a straddling Klein 4-group with positive defect *)
  /\ (forall z, XiC z = C0 -> Re z <> / 2 ->
        XiC (Cminus C1 z) = C0 /\ XiC (Cconj z) = C0 /\ 0 < line_defect z)
  (* C. Weil's criterion and its bridge to the proven one-sided reduction *)
  /\ ((forall z, XiC z = C0 -> Re z = / 2) <-> WeilPositive)
  /\ (WeilPositive <-> (forall z, XiC z = C0 -> / 2 <= Re z)).
Proof.
  split; [ exact line_defect_nonneg | ].
  split; [ exact line_defect_zero_iff | ].
  split.
  - intros z Hz Hne. pose proof (offline_zero_quadruple z Hz Hne) as [_ [H2 [H3 [_ H5]]]].
    repeat split; assumption.
  - split; [ exact RH_iff_WeilPositive | exact weil_positive_iff_no_left ].
Qed.

End Weil.

Print Assumptions weil_positivity_reduction.
