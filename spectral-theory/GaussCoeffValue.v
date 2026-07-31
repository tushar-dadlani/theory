(* ================================================================= *)
(*  GaussCoeffValue.v  —  Poisson→θ, Phase P2 complete: the value of   *)
(*  the periodization's Fourier coefficient.                          *)
(*                                                                    *)
(*    coeff_value : ∫_0^1 (gTheta_partial t x M)·cos(2πxm) dx           *)
(*                  ⟶  (1/√t)·e^{−πm²/t}   as M → ∞.                   *)
(*                                                                    *)
(*  The k-th Fourier coefficient of the periodization is the M→∞ limit  *)
(*  of the partial-sum integrals, and it equals f̂_t(m).  Proof: the      *)
(*  bounded identity period_integral rewrites each partial integral as   *)
(*  ∫_{−(S M)}^{S M} of the scaled Gaussian, whose limit is the P1        *)
(*  value (scaled_transform, restricted to the subsequence N = S M).    *)
(*                                                                    *)
(*  This sidesteps building ∫_0^1 Θ_t·cos as a plain integral (Θ_t =    *)
(*  gauss_theta carries proof arguments); the VALUE (1/√t)e^{−πm²/t} is  *)
(*  what P3/P4 need.  No new axioms (classical Reals only).            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussPeriodization GaussPeriodCoeff GaussScaledTransform GaussSqrtStep GaussPeriodInt.
Open Scope R_scope.

Theorem coeff_value : forall t m, 0 < t ->
  forall (prT : forall M, Riemann_integrable
                  (fun x => gTheta_partial t x M * cos (2 * PI * x * INR m)) 0 1),
  Un_cv (fun M => RiemannInt (prT M)) (/ sqrt t * exp (- (PI * INR m ^ 2 / t))).
Proof.
  intros t m Ht prT.
  pose (pr := fun N => sg_int t (INR m) (- INR N) (INR N)).
  pose proof (scaled_transform t (INR m) Ht pr) as Hst.
  pose proof (CV_shift' (fun N => RiemannInt (pr N)) 1 _ Hst) as Hsub.
  apply (Un_cv_ext (fun M => RiemannInt (pr (S M))) (fun M => RiemannInt (prT M))
           (/ sqrt t * exp (- (PI * INR m ^ 2 / t)))).
  - intro M; exact (period_integral t m M (pr (S M)) (prT M)).
  - apply (Un_cv_ext (fun n => RiemannInt (pr (n + 1)%nat)) (fun M => RiemannInt (pr (S M)))
             (/ sqrt t * exp (- (PI * INR m ^ 2 / t)))).
    + intro k; rewrite Nat.add_1_r; reflexivity.
    + exact Hsub.
Qed.

Print Assumptions coeff_value.

(* ================================================================= *)
(*  END GaussCoeffValue.v (P2 complete)                             *)
(*  c_k = (1/√t)·e^{−πk²/t}.  Phase P2 is done.  Next: P3 (the crux) —  *)
(*  the Fourier series of Θ_t converges to Θ_t(0) = Σ_k c_k, needing    *)
(*  Θ_t ∈ C¹ and the rescaled Fourier tower.  Then P4 assembles         *)
(*  θ(1/t) = √t·θ(t).                                                  *)
(* ================================================================= *)
