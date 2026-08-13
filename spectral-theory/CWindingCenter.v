(* ================================================================= *)
(*  CWindingCenter.v  (identity-theorem plan, brick B1 ingredient)     *)
(*                                                                    *)
(*  The winding integral around a circle centred at an ARBITRARY       *)
(*  point c (radius r), of the pole AT that centre:                    *)
(*     oint_{|z-c|=r} dz/(z-c) = 2 pi i.                                *)
(*                                                                    *)
(*  This generalises CWinding.winding_dz_z (the centre-0 case) to any  *)
(*  centre by the change of variables z = c + r e^{i u}, under which    *)
(*  the integrand collapses to the constant Ci exactly as in the       *)
(*  centre case (carc_over_id).  It is the value of the small-circle-   *)
(*  around-w integral needed to assemble the interior-point Cauchy      *)
(*  integral formula.                                                  *)
(*                                                                    *)
(*  NOT proved here: the genuinely off-centre-POLE winding             *)
(*     oint_{|z-a|=R} dz/(z-w) = 2 pi i   for  w <> a,  |w-a| < R,      *)
(*  the crux of B1.  Every route to it is gated by a large missing      *)
(*  capability: (i) an annulus deformation onto this small circle,     *)
(*  blocked by the repo's convex-only Cauchy theorem                   *)
(*  (CPrimConv.pathint_loop_conv); (ii) parameter differentiation,      *)
(*  requiring a full port of the CCauchyFormula M_const machine incl.   *)
(*  a new 2D uniform-continuity input (Harc_uc-analogue); (iii) the     *)
(*  geometric expansion 1/(z-w)=sum w^n/z^{n+1}, needing term-by-term   *)
(*  contour integration of a uniformly convergent series.  See          *)
(*  docs/identity_theorem_plan.md.                                     *)
(*                                                                    *)
(*  Axiom-clean (standard classical-Reals + functional_extensionality).*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CWinding.
Open Scope R_scope.

(* the circle of radius r centred at c (derivative is arc', c constant) *)
Definition carc (c : C) (r : R) (u : R) : C := Cadd c (arc r u).

(* on this circle the integrand of dz/(z-c) collapses to Ci *)
Lemma carc_over_id : forall c r u, 0 < r ->
  Cmul (Cinv (Cminus (carc c r u) c)) (arc' r u) = Ci.
Proof.
  intros c r u Hr. unfold carc.
  replace (Cminus (Cadd c (arc r u)) c) with (arc r u)
    by (apply Ceq; simpl; ring).
  apply arc_over_id; exact Hr.
Qed.

Lemma carc_int_cont : forall c r, 0 < r ->
  Ccont (fun u => Cmul (Cinv (Cminus (carc c r u) c)) (arc' r u)).
Proof.
  intros c r Hr.
  replace (fun u => Cmul (Cinv (Cminus (carc c r u) c)) (arc' r u))
    with (fun _ : R => Ci)
    by (apply functional_extensionality; intro u; symmetry; apply carc_over_id; exact Hr).
  apply Ccont_const.
Qed.

(* the winding integral around any centre c equals 2 pi i *)
Theorem winding_center : forall (c : C) (r : R) (Hr : 0 < r)
  (Hf : Ccont (fun u => Cmul (Cinv (Cminus (carc c r u) c)) (arc' r u))),
  pathint (carc c r) (arc' r) (fun z => Cinv (Cminus z c)) Hf 0 (2 * PI)
  = mkC 0 (2 * PI).
Proof.
  intros c r Hr Hf; unfold pathint.
  transitivity (Cintf (fun _ => Ci) (Ccont_const Ci) 0 (2 * PI)).
  - apply Cintf_ext; intro u; apply carc_over_id; exact Hr.
  - rewrite Cintf_const_ab; unfold Cmul, RtoC, Ci; apply Ceq; cbn; ring.
Qed.

Print Assumptions winding_center.
