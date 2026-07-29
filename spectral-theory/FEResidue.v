(* ================================================================= *)
(*  FEResidue.v  —  the self-dual value √π = Γ(½), NOW DISCHARGED.     *)
(*                                                                    *)
(*  This file once ISOLATED the functional equation's one archimedean  *)
(*  residue as a single axiom `Γ(½)² = π`.  That axiom is now a        *)
(*  THEOREM: over the constructive reals `CReal`, with                *)
(*                                                                    *)
(*    piR       := ConstructivePi.constructive_pi        (Wallis π)   *)
(*    GammaHalf := ConstructiveSqrtPi.constructive_sqrt_pi (its root)  *)
(*                                                                    *)
(*  we PROVE  `GammaHalf² == piR`  (`Gamma_half_selfdual`, from        *)
(*  `ConstructiveSqrtPi.gamma_half_sq_eq_pi`) and `GammaHalf > 0`      *)
(*  (`GammaHalf_pos`).  `Print Assumptions` = Closed under the global  *)
(*  context — the repo's LAST axiom is gone.                          *)
(*                                                                    *)
(*  HONEST BOUNDARY (unchanged, and the point of the whole arc): `π`   *)
(*  and `√π` here are the WALLIS / central-binomial constructions,     *)
(*  taken as the constructive definitions of these constants.  Their   *)
(*  identification with the CIRCLE π and with the GAUSSIAN INTEGRAL     *)
(*  `∫e^{−πx²}=√π` — i.e. that this `√π` is the value the analytic     *)
(*  functional equation `ξ(s)=ξ(1−s)` carries at its fixed point       *)
(*  `s=1/2` — is Wallis's / the Gaussian's theorem, classical and NOT  *)
(*  formalized.  The value now EXISTS axiom-free; the analytic bridge  *)
(*  to θ / the Gaussian remains the archimedean content behind the     *)
(*  wall.                                                             *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
  Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import QArith.
Require Import CRealCv ConstructivePi ConstructiveSqrtPi FEInvolution.
Open Scope Q_scope.

(* the concrete self-dual value and its square (π), axiom-free *)
Definition piR : CReal := constructive_pi.
Definition GammaHalf : CReal := constructive_sqrt_pi.

(* ================================================================= *)
(*  THE RESIDUE, as a THEOREM:  Γ(½)² = π  and  Γ(½) > 0.             *)
(* ================================================================= *)
Theorem Gamma_half_selfdual : (GammaHalf * GammaHalf == piR)%CReal.
Proof. unfold GammaHalf, piR; exact gamma_half_sq_eq_pi. Qed.

(* positivity as a Prop fact: √π ≥ 1 > 0 (CReal's strict < is Set-valued) *)
Theorem GammaHalf_pos : (inject_Q 1 <= GammaHalf)%CReal.
Proof. unfold GammaHalf; exact gamma_half_pos. Qed.

(* Γ(½) is THE positive square root of π: Γ(½) = √π, the self-dual     *)
(* value at the functional equation's fixed point s = 1/2.            *)
Definition positive_sqrt (r x : CReal) : Prop := (r * r == x)%CReal /\ (inject_Q 1 <= r)%CReal.

Theorem Gamma_half_is_sqrt_pi : positive_sqrt GammaHalf piR.
Proof. split; [ exact Gamma_half_selfdual | exact GammaHalf_pos ]. Qed.

(* the residue sits at the FE involution's fixed point — s = 1/2 = the *)
(* critical line (FEInvolution.critical), the unique self-dual point.  *)
Definition fe_fixed_point : Q := critical.

Remark residue_at_the_critical_line :
  fe_fixed_point == 1 # 2 /\ refl fe_fixed_point == fe_fixed_point.
Proof. unfold fe_fixed_point; split; [ reflexivity | apply refl_fixed ]. Qed.

Print Assumptions Gamma_half_is_sqrt_pi.

(* ================================================================= *)
(*  END FEResidue.v                                                  *)
(*  The functional equation's one archimedean value, `√π = Γ(½)`, is  *)
(*  now a THEOREM over axiom-free constructive reals — the repo's     *)
(*  last axiom discharged.  What stays classical is only the          *)
(*  IDENTIFICATION of this Wallis √π with the Gaussian integral (the   *)
(*  analytic θ-bridge), not the existence of the value.  Closed under *)
(*  the global context.                                              *)
(* ================================================================= *)
