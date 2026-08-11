/-
  TDLean.Zeta.RayIdentity -- the identity theorem in REAL-RAY form.

  This is the tool that LEDGER finding #1 actually needs, and it is *not* the half-plane
  lemma already in `Identity.lean`.

  ## The distinction, which I previously got wrong

  `eqOn_halfplane_of_eqOn_subhalfplane` transfers agreement from one **open** half-plane to a
  larger one. But the Rocq gap is not of that shape. There,
  `ZetaXiLink.v:18 XiC_is_completed_zeta` gives `XiC (RtoC s) = …ζ(s)` only for **real** `s > 1`
  — a ray inside `ℝ ⊂ ℂ`, which has **empty interior**. No open-set-to-open-set lemma can
  bridge that. What is required is the accumulation-point form of the identity principle:
  agreement on a set merely *clustering* at a point of the region.

  mathlib has the engine (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`,
  `Analysis/Analytic/IsolatedZeros.lean:243`, one-dimensional). What is packaged here is the
  usable corollary: agreement along a real ray.

  ## Scope, honestly

  This closes the *tool* gap only. Applying it to `Λ(s) = Λ(1−s)` still needs a Lean-side `Ξ`,
  i.e. cluster A (theta transformation → Mellin → `Ξ`), which is unbuilt — and whose easy route
  through `Gaussian.PoissonSummation` / `ModularForms.JacobiTheta` is closed by the gate.
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TDLean.Zeta

open Filter Topology

/-- **Identity theorem, sequential form.** Analytic functions on a preconnected open set that
    agree along any sequence converging to an interior point (from off that point) agree. -/
theorem eqOn_of_eqOn_seq {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) {z₀ : ℂ} (h₀ : z₀ ∈ U)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝[≠] z₀)) (hfg : ∀ n, f (u n) = g (u n)) :
    Set.EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀
    (hu.frequently (Frequently.of_forall hfg))

/-- The approach sequence along the real axis: `x₀ + 1/(n+1)`, which stays in `(a, ∞)`. -/
theorem tendsto_realApproach (x₀ : ℝ) :
    Tendsto (fun n : ℕ => ((x₀ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] ((x₀ : ℝ) : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀) := tendsto_const_nhds
    have hsum : Tendsto (fun n : ℕ => x₀ + (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (x₀ + 0)) :=
      hconst.add h0
    rw [add_zero] at hsum
    exact (Complex.continuous_ofReal.tendsto x₀).comp hsum
  · filter_upwards with n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hre : x₀ + 1 / ((n : ℝ) + 1) = x₀ := by exact_mod_cast congrArg Complex.re h
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **The tool LEDGER finding #1 needs.** If `f` and `g` are analytic on a preconnected open
    `U ⊆ ℂ` and agree at every *real* point of a ray `(a, ∞)`, and `U` contains one point of
    that ray, then they agree on all of `U`.

    This is exactly the shape of the Rocq gap: symmetry known on all of `ℂ`, identification
    with `ζ` known only on the real ray `s > 1`. -/
theorem eqOn_of_eqOn_realRay {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) {a x₀ : ℝ} (hax : a < x₀)
    (h₀ : ((x₀ : ℝ) : ℂ) ∈ U) (hfg : ∀ x : ℝ, a < x → f ((x : ℝ) : ℂ) = g ((x : ℝ) : ℂ)) :
    Set.EqOn f g U := by
  refine eqOn_of_eqOn_seq hf hg hU h₀ (tendsto_realApproach x₀) fun n => ?_
  refine hfg _ ?_
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! ### Non-vacuity -/

/-- The hypotheses are satisfiable, and the conclusion genuinely extends off the ray:
    `(z+1)²` and `z² + 2z + 1` are shown equal *on all of `ℂ`* from real agreement alone. -/
theorem eqOn_realRay_nonvacuous :
    Set.EqOn (fun z : ℂ => (z + 1) ^ 2) (fun z : ℂ => z ^ 2 + 2 * z + 1) Set.univ := by
  have hd1 : DifferentiableOn ℂ (fun z : ℂ => (z + 1) ^ 2) Set.univ := by
    intro z _
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (z + 1) ^ 2) z).differentiableWithinAt
  have hd2 : DifferentiableOn ℂ (fun z : ℂ => z ^ 2 + 2 * z + 1) Set.univ := by
    intro z _
    exact (by fun_prop :
      DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + 2 * z + 1) z).differentiableWithinAt
  have h1 : AnalyticOnNhd ℂ (fun z : ℂ => (z + 1) ^ 2) Set.univ :=
    DifferentiableOn.analyticOnNhd hd1 isOpen_univ
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2 + 2 * z + 1) Set.univ :=
    DifferentiableOn.analyticOnNhd hd2 isOpen_univ
  refine eqOn_of_eqOn_realRay (a := 0) (x₀ := 1) h1 h2 isPreconnected_univ (by norm_num)
    (Set.mem_univ _) ?_
  intro x _
  ring

end TDLean.Zeta
