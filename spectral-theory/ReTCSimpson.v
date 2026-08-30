(* ================================================================= *)
(*  ReTCSimpson.v  --  Re TC as a Simpson sum, with a proved error.    *)
(*                                                                    *)
(*    ReTC_simpson : 0 < n -> 0 <= L ->                                *)
(*      |Re (TC (crit t)) - ssum (gint t) 0 (L/n) n|                   *)
(*        <=  M4fin t . L^5 / (720 n^4)      (quadrature)              *)
(*          + Cc . e^{-pi e^L} / pi          (truncation)              *)
(*                                                                    *)
(*  The O(h^4) counterpart of ReTCQuad, and structurally identical to  *)
(*  it: the same truncation bound (ReTC_tail_bound, uniform in t), the *)
(*  same u-space to x-space transport (ReTC_xspace), the same triangle *)
(*  inequality -- only composite_simpson_ab in place of                *)
(*  composite_midpoint_ab, and M4fin in place of Mfin.                 *)
(*                                                                    *)
(*  Note M4fin carries no L: the joint bounds of PsiXDeriv3 already    *)
(*  absorbed the e^{x/4} weight, so unlike Mfin there is no e^{L/4}    *)
(*  factor to track.  Axiom-clean.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField ThetaTailEntire CoherenceSingularity
        ImproperCv1 CImproperIntegral ReTCTailBound RiemannPsi PsiXDeriv
        IntegrandLip IntegrandLip4 SimpsonQuad XSpaceWire.
Open Scope R_scope.

Theorem ReTC_simpson : forall t L n, (0 < n)%nat -> 0 <= L ->
  Rabs (Re (TC (crit t)) - ssum (gint t) 0 (L / INR n) n)
  <= M4fin t * L ^ 5 / (720 * INR n ^ 4)
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
  pose proof (composite_simpson_ab (gint t) (G1 t) (G2 t) (G3 t)
                0 L (M4fin t) n prx Hn HL (M4fin_nonneg t)
                (fun y Hy => gint_deriv_1 t y (proj1 Hy))
                (fun y Hy => gint_deriv_2 t y (proj1 Hy))
                (fun y Hy => gint_deriv_3 t y (proj1 Hy))
                (fun y z Hy Hz => d3gint_lip t L y z Hy Hz)) as HQ.
  assert (E0 : L - 0 = L) by ring. rewrite E0 in HQ.
  (* --- triangle --- *)
  replace (Re (TC (crit t)) - ssum (gint t) 0 (L / INR n) n)
    with ((Re (TC (crit t)) - RiemannInt prx)
          + (RiemannInt prx - ssum (gint t) 0 (L / INR n) n)) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ]. lra.
Qed.

Print Assumptions ReTC_simpson.
