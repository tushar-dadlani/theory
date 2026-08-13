/-
  TDLean.Zeta.Identity -- the identity theorem, and transfer off the half-plane.

  ## Why this matters beyond C9

  This is the tool the Rocq repo does not have, and its absence is **finding #1** in
  LEDGER.md: `ZetaFunctionalEq.v:25 LambdaC_FE` proves `Λ(z) = Λ(1−z)` on all of `ℂ`, but
  the tie to ζ (`ZetaXiLink.XiC_is_completed_zeta`) holds only on the **real ray `s > 1`**.
  Bridging a ray to a region needs an identity theorem, and the repo has only *polynomial*
  ones (`QPolyPIT.v`, `IntPolyDerivResp.v`) — no complex-analytic one.

  `eqOn_halfplane_of_eqOn_subhalfplane` below is the region-to-region form; it is what
  cluster A's A13 cross-check will use.

  ## A precision note

  Transferring the *derivative* from `zetaSeries` to `zetaCont` on `Re s > 1` does **not**
  need the identity theorem: the two functions agree on an open set, so their derivatives
  agree there by locality (`Filter.EventuallyEq.deriv_eq`). The identity theorem is for the
  genuinely global statement — uniqueness of the continuation.
-/
import TDLean.Zeta.Telescope
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

namespace TDLean.Zeta

open Complex Filter Topology Set

/-! ### Half-planes are open, convex, preconnected -/

theorem isOpen_halfplane (σ : ℝ) : IsOpen {s : ℂ | σ < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_halfplane (σ : ℝ) : Convex ℝ {s : ℂ | σ < s.re} :=
  convex_halfSpace_re_gt σ

theorem isPreconnected_halfplane (σ : ℝ) : IsPreconnected {s : ℂ | σ < s.re} :=
  (convex_halfplane σ).isPreconnected

/-! ### The identity theorem -/

/-- **Identity theorem, region form.** Two functions holomorphic on a preconnected open set
    that agree near one point agree everywhere on it. -/
theorem eqOn_of_eventuallyEq {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h : f =ᶠ[nhds z₀] g) : EqOn f g U :=
  (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hU) hUc hz₀ h

/-- **Ray-to-region, in the form cluster A needs.** Two functions holomorphic on the
    half-plane `Re s > σ₀` that agree on the smaller half-plane `Re s > σ₁` agree on all of
    `Re s > σ₀`. -/
theorem eqOn_halfplane_of_eqOn_subhalfplane {σ₀ σ₁ : ℝ} (h01 : σ₀ < σ₁)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f {s : ℂ | σ₀ < s.re})
    (hg : DifferentiableOn ℂ g {s : ℂ | σ₀ < s.re})
    (hfg : EqOn f g {s : ℂ | σ₁ < s.re}) : EqOn f g {s : ℂ | σ₀ < s.re} := by
  set z₀ : ℂ := ((σ₁ + 1 : ℝ) : ℂ) with hz₀def
  have hre : z₀.re = σ₁ + 1 := by simp [hz₀def]
  have hz₀ : z₀ ∈ {s : ℂ | σ₀ < s.re} := by
    simp only [mem_setOf_eq, hre]; linarith
  have hnbhd : {s : ℂ | σ₁ < s.re} ∈ nhds z₀ :=
    (isOpen_halfplane σ₁).mem_nhds (by simp only [mem_setOf_eq, hre]; linarith)
  exact eqOn_of_eventuallyEq (isOpen_halfplane σ₀) (isPreconnected_halfplane σ₀) hf hg hz₀
    (Filter.eventually_of_mem hnbhd fun z hz => hfg hz)

/-! ### Uniqueness of the continuation -/

/-- **The continuation is unique.** Any function holomorphic on `Re s > 0` agreeing with
    `zetaDiffSum` on `Re s > 1` *is* `zetaDiffSum`. Equivalently: `zetaCont` is the only
    holomorphic extension of `ζ` to `Re s > 0` with the pole isolated in `1/(s−1)`.

    OVERTAKE: no Coq counterpart -- the repo has no complex-analytic identity theorem. -/
theorem zetaDiffSum_unique {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {s : ℂ | 0 < s.re})
    (hagree : EqOn g zetaDiffSum {s : ℂ | 1 < s.re}) :
    EqOn g zetaDiffSum {s : ℂ | 0 < s.re} :=
  eqOn_halfplane_of_eqOn_subhalfplane one_pos hg differentiableOn_zetaDiffSum hagree

/-! ### Derivative transfer (locality, not the identity theorem) -/

/-- On `Re s > 1` the continuation and the series have the same derivative. This is pure
    locality: they agree on an open set. -/
theorem deriv_zetaCont_eq {s : ℂ} (hs : 1 < s.re) :
    deriv zetaCont s = deriv zetaSeries s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(isOpen_halfplane 1).mem_nhds hs] with w hw
  exact zetaCont_eq_zetaSeries hw

/-- Non-vacuity: the identity-theorem hypotheses are satisfiable (take `f = g`). -/
theorem eqOn_halfplane_nonvacuous :
    ∃ (σ₀ σ₁ : ℝ) (f g : ℂ → ℂ), σ₀ < σ₁ ∧ EqOn f g {s : ℂ | σ₁ < s.re} :=
  ⟨0, 1, id, id, one_pos, fun _ _ => rfl⟩

end TDLean.Zeta
