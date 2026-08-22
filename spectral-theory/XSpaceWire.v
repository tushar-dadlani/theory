(* ================================================================= *)
(*  XSpaceWire.v  --  Re TC's integrand, wired to gint.                *)
(*                                                                    *)
(*    ReTC_xspace : 0 <= L ->                                          *)
(*      int_1^{e^L} Re (wkerC (crit t) u) du  =  int_0^L gint t x dx   *)
(*                                                                    *)
(*  Stage 4c join.  XSpaceIntegral.xspace_substitution has existed     *)
(*  since the substitution brick, but only in its abstract C1_fun      *)
(*  shape -- for an arbitrary continuous f, phrased in terms of        *)
(*  exp_C1 and derive exp_C1 (diff0 exp_C1).  This file instantiates   *)
(*  it at the one integrand the sign change needs and identifies the   *)
(*  result with IntegrandLip.gint, closing the gap between the u-space *)
(*  object ReTCTailBound bounds and the x-space object the quadrature  *)
(*  evaluates.                                                        *)
(*                                                                    *)
(*  Three transports are involved and each needs its own tool:         *)
(*   - the ENDPOINTS (exp_C1 0 vs 1, exp_C1 L vs e^L) are equal as     *)
(*     reals but sit inside the TYPE Riemann_integrable f a b, so      *)
(*     they move by subst-then-RiemannInt_P5 (RI_ends);                *)
(*   - the INTEGRAND of the substituted side differs from gint only    *)
(*     for x < 0 (where clamp bites and Psi(e^x) is not the same       *)
(*     function), so it cannot move by functional extensionality; it   *)
(*     moves by RiemannInt_P18, which asks only for agreement on the   *)
(*     OPEN interval;                                                  *)
(*   - exp_C1 and its derive, on the other hand, agree with exp        *)
(*     everywhere, so THAT rewrite is a genuine function equality and  *)
(*     functional extensionality is the right tool.                    *)
(*                                                                    *)
(*  The arithmetic core is one line: u^{-3/4} . du = e^{-3x/4} e^x dx  *)
(*  = e^{x/4} dx.  Axiom-clean (the four standard axioms).             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull MellinElem CPowBase
        RiemannPsi ThetaTailEntire CoherenceSingularity
        XSpaceIntegral PsiXDeriv IntegrandLip.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the exponent of the Mellin kernel on the critical line        *)
(* ----------------------------------------------------------------- *)
Lemma crit_w_re : forall t, Re (Cminus (Cmul (crit t) (RtoC (/ 2))) C1) = - (3 / 4).
Proof. intro t. unfold Cminus, Cmul, RtoC, C1, crit; cbn [Re Im]; lra. Qed.

Lemma crit_w_im : forall t, Im (Cminus (Cmul (crit t) (RtoC (/ 2))) C1) = t / 2.
Proof. intro t. unfold Cminus, Cmul, RtoC, C1, crit; cbn [Re Im]; lra. Qed.

Lemma Re_wkerC_crit : forall t u, 1 <= u ->
  Re (wkerC (crit t) u) = Psi u * (Rpower u (- (3 / 4)) * cos (t / 2 * ln u)).
Proof.
  intros t u Hu. unfold wkerC. rewrite (clamp_id u Hu).
  unfold Cmul at 1; cbn [Re Im]. unfold RtoC; cbn [Re Im].
  rewrite Re_Cpw, crit_w_re, crit_w_im. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the substituted integrand IS gint                             *)
(* ----------------------------------------------------------------- *)
Theorem gint_from_wker : forall t x, 0 <= x ->
  Re (wkerC (crit t) (exp x)) * exp x = gint t x.
Proof.
  intros t x Hx.
  assert (Hu : 1 <= exp x) by (apply exp_ge_1; exact Hx).
  rewrite (Re_wkerC_crit t (exp x) Hu).
  unfold Rpower. rewrite ln_exp.
  unfold gint, GPsi, Qe, Ct.
  replace (Psi (exp x) * (exp (- (3 / 4) * x) * cos (t / 2 * x)) * exp x)
    with (Psi (exp x) * (exp (- (3 / 4) * x) * exp x) * cos (t / 2 * x)) by ring.
  rewrite <- exp_plus.
  replace (- (3 / 4) * x + x) with (/ 4 * x) by lra.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  transports                                                    *)
(* ----------------------------------------------------------------- *)
Lemma RI_ends : forall f a b a' b'
  (pr : Riemann_integrable f a b) (pr' : Riemann_integrable f a' b'),
  a = a' -> b = b' -> RiemannInt pr = RiemannInt pr'.
Proof. intros f a b a' b' pr pr' E1 E2. subst a' b'. apply RiemannInt_P5. Qed.

(* exp_C1 agrees with exp EVERYWHERE, so this one is a function equality *)
Lemma subst_fun_eq : forall t,
  (fun x => Re (wkerC (crit t) (exp_C1 x)) * derive exp_C1 (diff0 exp_C1) x)
  = (fun x => Re (wkerC (crit t) (exp x)) * exp x).
Proof.
  intro t. apply functional_extensionality; intro x.
  rewrite exp_C1_val, exp_C1_deriv. reflexivity.
Qed.

Lemma subst_RI : forall t L, 0 <= L ->
  Riemann_integrable
    (fun x => Re (wkerC (crit t) (exp_C1 x)) * derive exp_C1 (diff0 exp_C1) x) 0 L.
Proof.
  intros t L HL. rewrite (subst_fun_eq t).
  apply continuity_implies_RiemannInt; [ exact HL | ].
  intros x _. apply continuity_pt_mult.
  - apply (continuity_pt_comp exp (fun u => Re (wkerC (crit t) u)) x).
    + apply derivable_continuous_pt. exists (exp x). apply derivable_pt_lim_exp.
    + apply cont_wkerC_re.
  - apply derivable_continuous_pt. exists (exp x). apply derivable_pt_lim_exp.
Qed.

Lemma outer_RI : forall t L, 0 <= L ->
  Riemann_integrable (fun u => Re (wkerC (crit t) u)) (exp_C1 0) (exp_C1 L).
Proof.
  intros t L HL.
  apply continuity_implies_RiemannInt.
  - rewrite !exp_C1_val, exp_0. apply exp_ge_1; exact HL.
  - intros u _. apply cont_wkerC_re.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE WIRING                                                    *)
(* ----------------------------------------------------------------- *)
Theorem ReTC_xspace : forall t L
  (prX : Riemann_integrable (fun u => Re (wkerC (crit t) u)) 1 (exp L))
  (prx : Riemann_integrable (gint t) 0 L),
  0 <= L -> RiemannInt prX = RiemannInt prx.
Proof.
  intros t L prX prx HL.
  pose proof (subst_RI t L HL) as prL.
  pose proof (outer_RI t L HL) as prR.
  (* outer integral: move the endpoints onto exp_C1 *)
  assert (E1 : (1 : R) = exp_C1 0) by (rewrite exp_C1_val, exp_0; reflexivity).
  assert (E2 : exp L = exp_C1 L) by (symmetry; apply exp_C1_val).
  rewrite (RI_ends (fun u => Re (wkerC (crit t) u)) 1 (exp L)
             (exp_C1 0) (exp_C1 L) prX prR E1 E2).
  (* change of variables *)
  rewrite <- (xspace_substitution (fun u => Re (wkerC (crit t) u)) L HL
                (fun u _ => cont_wkerC_re (crit t) u) prL prR).
  (* the substituted integrand agrees with gint on (0, L) *)
  apply (RiemannInt_P18 prL prx HL).
  intros x Hx. rewrite exp_C1_deriv; rewrite ?exp_C1_val.
  apply gint_from_wker. lra.
Qed.

Print Assumptions Re_wkerC_crit.
Print Assumptions gint_from_wker.
Print Assumptions ReTC_xspace.
