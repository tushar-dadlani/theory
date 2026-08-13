(* ================================================================= *)
(*  GammaCFE.v  (toward Block B / the complex functional equation)     *)
(*                                                                    *)
(*  The complex Gamma functional equation                             *)
(*     GammaC (z + 1) = z * GammaC z   on Re z > 0.                     *)
(*                                                                    *)
(*  Status: reduced, machine-checked, to the IDENTITY THEOREM.  Both   *)
(*  sides are holomorphic on Re z > 0 and they AGREE on the positive   *)
(*  real axis, so the FE follows from analytic continuation.           *)
(*                                                                    *)
(*  PROVED here (axiom-clean, standard classical-Reals only):          *)
(*   - GammaC_FE_real: the FE holds on the positive real axis          *)
(*     (from GammaC_agree + the real recurrence Gam_recur);            *)
(*   - FE_diff_vanishes_real: FE_diff := LHS - RHS vanishes on R+;      *)
(*   - FE_diff_holo: FE_diff is holomorphic on Re z > 0                 *)
(*     (product rule for z*GammaC z, chain rule for GammaC(z+1));       *)
(*   - GammaC_FE_from_identity: IF FE_diff vanishes on all of Re z > 0  *)
(*     (the conclusion the identity theorem delivers from the two      *)
(*     facts above), THEN the full complex FE holds.                   *)
(*                                                                    *)
(*  REMAINING GAP: the identity theorem for holomorphic functions on   *)
(*  Re z > 0 (a function holomorphic there and vanishing on R+ vanishes *)
(*  identically).  The repo has the Cauchy integral formula            *)
(*  (CCauchyFormula.cauchy_integral_formula) but not the power-series / *)
(*  uniqueness machinery the identity theorem needs.  The alternative  *)
(*  route -- complex integration by parts on the GammaC integral --     *)
(*  would need a u-derivative of the Gamma kernel (only the            *)
(*  z-derivative dgnkC exists) plus improper-limit boundary analysis.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField GammaReal GammaRecur GammaC Holomorphic CDeriv.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  The FE on the positive real axis                             *)
(* ----------------------------------------------------------------- *)

Theorem GammaC_FE_real : forall s (Hs : 0 < s),
  GammaC (Cadd (RtoC s) C1) = Cmul (RtoC s) (GammaC (RtoC s)).
Proof.
  intros s Hs.
  assert (Hs1 : 0 < s + 1) by lra.
  assert (Heq : Cadd (RtoC s) C1 = RtoC (s + 1))
    by (unfold RtoC, Cadd, C1; apply Ceq; simpl; ring).
  rewrite Heq, (GammaC_agree (s + 1) Hs1), (Gam_recur s Hs Hs1), RtoC_mul.
  rewrite <- (GammaC_agree s Hs). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  The difference LHS - RHS: vanishes on R+, holomorphic on Re>0 *)
(* ----------------------------------------------------------------- *)

Definition FE_diff (z : C) : C := Cminus (GammaC (Cadd z C1)) (Cmul z (GammaC z)).

Lemma FE_diff_vanishes_real : forall s (Hs : 0 < s), FE_diff (RtoC s) = C0.
Proof.
  intros s Hs. unfold FE_diff. rewrite (GammaC_FE_real s Hs).
  unfold Cminus, C0; apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma FE_diff_holo : forall z (Hz : 0 < Re z), exists d, is_Cderiv FE_diff z d.
Proof.
  intros z Hz.
  assert (Hz1 : 0 < Re (Cadd z C1)) by (unfold Cadd, C1; cbn [Re Im]; lra).
  unfold FE_diff. eexists.
  apply Cderiv_minus.
  - apply (Cderiv_comp GammaC (fun w => Cadd w C1) z).
    + apply (GammaC_entire (Cadd z C1) Hz1).
    + apply (Cderiv_add (fun w => w) (fun _ => C1) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ].
  - apply (Cderiv_mul (fun w => w) GammaC z);
      [ apply Cderiv_id | apply (GammaC_entire z Hz) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Reduction of the complex FE to the identity theorem          *)
(* ----------------------------------------------------------------- *)

Definition GammaC_FE : Prop :=
  forall z, 0 < Re z -> GammaC (Cadd z C1) = Cmul z (GammaC z).

(* The full FE follows once the identity theorem furnishes FE_diff = 0 *)
(* everywhere on Re z > 0 (its premises FE_diff_holo and                *)
(* FE_diff_vanishes_real are proved above).                             *)
Theorem GammaC_FE_from_identity :
  (forall z, 0 < Re z -> FE_diff z = C0) -> GammaC_FE.
Proof.
  intros Hid z Hz. pose proof (Hid z Hz) as H. unfold FE_diff in H.
  apply Ceq;
    [ apply (f_equal Re) in H | apply (f_equal Im) in H ];
    unfold Cminus, C0 in H; cbn [Re Im] in H; lra.
Qed.

Print Assumptions GammaC_FE_real.
Print Assumptions FE_diff_holo.
Print Assumptions GammaC_FE_from_identity.
