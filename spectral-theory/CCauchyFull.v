(* ================================================================= *)
(*  CCauchyFull.v  (identity-theorem plan, brick B1 COMPLETE)          *)
(*                                                                    *)
(*  The UNCONDITIONAL Cauchy integral formula at an interior point:    *)
(*     oint_{|z|=R} F(z)/(z-w) dz = 2 pi i . F(w)                       *)
(*  for F holomorphic (is_Cderiv everywhere) and |w| < R.  Obtained by  *)
(*  feeding the removable extension rphi (CRemovableExt) -- whose       *)
(*  properties are all derived from F's differentiability -- into the   *)
(*  conditional formula CCauchyInterior.cauchy_interior_cond.           *)
(*                                                                    *)
(*  This closes brick B1 of the identity-theorem plan.                 *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral Holomorphic
        CWinding CWindingOffCenter CCauchyInterior CRemovableExt.
Open Scope R_scope.

Theorem cauchy_interior : forall (F : C -> C) (Rr : R) (w dw : C)
  (HFhol : forall z, exists d, is_Cderiv F z d)
  (Hdw : is_Cderiv F w dw)
  (HR : 0 < Rr) (HwR : Cmod w < Rr)
  (Hf : Ccont (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (Cminus (arc Rr u) w)))
                             (arc' Rr u))),
  pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv (Cminus z w))) Hf 0 (2 * PI)
  = Cmul (mkC 0 (2 * PI)) (F w).
Proof.
  intros F Rr w dw HFhol Hdw HR HwR Hf.
  assert (Harc_ne : forall u, arc Rr u <> w).
  { intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
    rewrite Hc in HM. lra. }
  apply (cauchy_interior_cond (Rr + 1) Rr w F (rphi F w dw)).
  - exact HR.
  - lra.
  - exact HwR.
  - exact (rphi_cc F HFhol w dw Hdw).
  - intro u. exact (rphi_off F w dw (arc Rr u) (Harc_ne u)).
  - intros z _ Hz. exact (rphi_holo_off F HFhol w dw z Hz).
  - exact (rphi_bd F w dw Hdw).
  - intros z _ eps He. exact (rphi_ptcont F HFhol w dw Hdw z eps He).
Qed.

Print Assumptions cauchy_interior.
