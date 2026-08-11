(* ================================================================= *)
(*  FusionKernel.v  —  Newman A3: the change-of-variables kernel identity *)
(*  that fuses the Newman Laplace side with the Phi u-power side.        *)
(*                                                                    *)
(*  Under u = e^t, the u-power kernel u^{-s-1} times the Jacobian e^t     *)
(*  IS the Laplace kernel e^{-st}:                                       *)
(*                                                                    *)
(*    Fpow_exp : Fpow s (e^t) * e^t = cexpzt (-s) t   (= e^{-st}),        *)
(*                                                                    *)
(*  where Fpow s u = u^{-s-1}, and gderivC s = -s * Fpow s (gderivC_Fpow).*)
(*  Hence, cell by cell,                                                 *)
(*    int_{ln N}^{ln(N+1)} e^{-st} dt = int_N^{N+1} u^{-s-1} du,          *)
(*  and int_N^{N+1} gderivC s = -s * int_N^{N+1} u^{-s-1}, tying          *)
(*  phi_cellint_rep (u-space, gderivC) to the Newman Laplace kernel       *)
(*  (t-space, cexpzt).  This is the pointwise heart of the identity        *)
(*  g(z) = Phi(z+1)/(z+1) - 1/z.  Axiom-clean.                           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CExpKernel EulerFormula CZetaTerm.
Open Scope R_scope.

(*  the u-power kernel  u^{-s-1}  *)
Definition Fpow (s : C) (u : R) : C := Cpw u (Cminus (Copp s) C1).

(*  gderivC = d/du u^{-s} = -s * u^{-s-1}  (definitional)  *)
Lemma gderivC_Fpow : forall s u, gderivC s u = Cmul (Copp s) (Fpow s u).
Proof. intros s u; unfold gderivC, Fpow; reflexivity. Qed.

(*  the real exponential, as a complex exponential  *)
Lemma RtoC_exp_Cexpf : forall t, RtoC (exp t) = Cexpf (RtoC t).
Proof.
  intro t; unfold Cexpf, Cexp, RtoC; cbn [Re Im];
    rewrite sin_0, cos_0; apply Ceq; cbn; ring.
Qed.

(*  the change-of-variables kernel identity:  u^{-s-1} * (du/dt) = e^{-st}  *)
Lemma Fpow_exp : forall s t, Cmul (Fpow s (exp t)) (RtoC (exp t)) = cexpzt (Copp s) t.
Proof.
  intros s t; unfold Fpow, cexpzt, Cpw.
  rewrite ln_exp, RtoC_exp_Cexpf, <- Cexpf_add.
  f_equal; ring.
Qed.

Print Assumptions Fpow_exp.
Print Assumptions gderivC_Fpow.

(* ================================================================= *)
(*  END FusionKernel.v — the CoV kernel identity u^{-s-1} e^t = e^{-st}.   *)
(*                                                                    *)
(*  Remaining integral-level assembly (the wall):  turning this into      *)
(*  int_N^{N+1} u^{-s-1} du = int_{ln N}^{ln(N+1)} e^{-st} dt at the        *)
(*  integral level needs a complex integral that does NOT require GLOBAL   *)
(*  continuity -- Cintf's Ccont hypothesis is global, but Fpow s / gderivC *)
(*  s are continuous only on (0,oo).  So CgderivInt (interval-specific     *)
(*  Riemann_integrable) cannot be a Cintf, and the CoV must be run at the  *)
(*  RiemannInt component level with a dependent-endpoint rewrite           *)
(*  (exp(ln N) = N).  That interval-local complex-integral layer is the    *)
(*  next infrastructure brick before the identity can be stated.          *)
(* ================================================================= *)
