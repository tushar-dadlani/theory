(* ================================================================= *)
(*  ReTCQuad.v  --  Re TC, to a computable finite sum with error.      *)
(*                                                                    *)
(*    ReTC_quadrature : 0 < n -> 0 <= L ->                             *)
(*      |Re (TC (crit t)) - msum (gint t) 0 (L/n) n|                   *)
(*        <=  Mfin t L . L^3 / (24 n^2)        (quadrature)            *)
(*          + Cc . e^{-pi e^L} / pi            (truncation)            *)
(*                                                                    *)
(*  Stage 4 capstone.  This is the object XirIntegralReduction.        *)
(*  xir_reduction' consumes: it replaces the improper integral         *)
(*  Re TC(1/2+it) -- the only non-elementary content of xir -- by a    *)
(*  FINITE sum of point evaluations of an interval-arithmetic-         *)
(*  evaluable integrand, with a fully proved two-part error.           *)
(*                                                                    *)
(*  Everything it needs was built separately and meets here:           *)
(*    ReTCTailBound.ReTC_tail_bound   truncation at X = e^L            *)
(*    XSpaceWire.ReTC_xspace          u-space -> x-space               *)
(*    CompositeQuad.composite_midpoint_ab   panels glued               *)
(*    IntegrandLip.dgint_lip          the Lipschitz constant           *)
(*  and the last of those rests, in turn, on Psi being differentiable  *)
(*  at all (ThetaDeriv, via CVU).                                      *)
(*                                                                    *)
(*  Note the two error terms scale oppositely in L: the truncation     *)
(*  falls like e^{-pi e^L} (doubly exponentially -- L = ln 5 already   *)
(*  gives 5e-8) while the quadrature grows like L^3 and Mfin grows     *)
(*  like e^{L/4}.  L is therefore chosen once, as small as the         *)
(*  truncation allows, and only n is tuned.  Axiom-clean.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField ThetaTailEntire CoherenceSingularity
        ImproperCv1 CImproperIntegral ReTCTailBound RiemannPsi PsiXDeriv
        IntegrandLip CompositeQuad XSpaceWire.
Open Scope R_scope.

Theorem ReTC_quadrature : forall t L n, (0 < n)%nat -> 0 <= L ->
  Rabs (Re (TC (crit t)) - msum (gint t) 0 (L / INR n) n)
  <= Mfin t L * L ^ 3 / (24 * INR n ^ 2)
     + Cc * exp (- (PI * exp L)) / PI.
Proof.
  intros t L n Hn HL.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (HeL : 1 <= exp L) by (apply exp_ge_1; exact HL).
  assert (prx : Riemann_integrable (gint t) 0 L) by (apply gint_RI; lra).
  pose (prX := cont_RI _ (cont_wkerC_re (crit t)) 1 (exp L)).
  (* --- truncation, moved onto the x-space finite integral --- *)
  pose proof (ReTC_tail_bound t (exp L) HeL) as HT.
  assert (Epint : pint1 (fun u => Re (wkerC (crit t) u))
                    (cont_RI _ (cont_wkerC_re (crit t))) (exp L) = RiemannInt prX)
    by (unfold pint1, prX; apply RiemannInt_P5).
  rewrite Epint, (ReTC_xspace t L prX prx HL) in HT.
  (* --- quadrature --- *)
  pose proof (composite_midpoint_ab (gint t) (dgint t) 0 L (Mfin t L) n prx
                Hn HL (Mfin_nonneg t L)
                (fun y Hy => gint_deriv t y (proj1 Hy))
                (fun y z Hy Hz => dgint_lip t L y z Hy Hz)) as HQ.
  assert (E0 : L - 0 = L) by ring. rewrite E0 in HQ.
  (* --- triangle --- *)
  replace (Re (TC (crit t)) - msum (gint t) 0 (L / INR n) n)
    with ((Re (TC (crit t)) - RiemannInt prx)
          + (RiemannInt prx - msum (gint t) 0 (L / INR n) n)) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ]. lra.
Qed.

Print Assumptions ReTC_quadrature.
