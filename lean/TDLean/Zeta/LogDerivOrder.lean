/-
  TDLean.Zeta.LogDerivOrder -- C9 item 3, phase 2: the logarithmic derivative at a zero.

  NO COQ ORACLE. From-scratch rule in force.

  **This is the part mathlib does not have.** `Mathlib/Analysis/Calculus/LogDeriv.lean`
  supplies the algebra (`logDeriv_mul/div/pow/comp/prod`) but says nothing about behaviour
  at a zero or a pole; grep finds no occurrence of `logDeriv` anywhere under
  `Analysis/Meromorphic/`. The statement needed for the Hadamard--de la Vallee Poussin
  argument is:

      f analytic at z₀ with finite order n  ⟹  (z − z₀)·(f′/f)(z) → n  as z → z₀, z ≠ z₀.

  It is proved from the factorisation `f =ᶠ (z − z₀)^n • g` with `g z₀ ≠ 0`
  (`AnalyticAt.analyticOrderAt_ne_top`), on which `logDeriv` splits as
  `n/(z − z₀) + logDeriv g`, and the second summand stays bounded.

  Nothing here is zeta-specific: it is a general fact about analytic functions.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace TDLean.Zeta

open Complex Filter Topology

/-- `logDeriv` of a power of `(· − z₀)`: it is `n/(z − z₀)`, the model pole. -/
theorem logDeriv_sub_pow (z₀ : ℂ) (n : ℕ) (z : ℂ) :
    logDeriv (fun w : ℂ => (w - z₀) ^ n) z = n / (z - z₀) := by
  have h : (fun w : ℂ => (w - z₀) ^ n) = (fun u : ℂ => u ^ n) ∘ (fun w : ℂ => w - z₀) := rfl
  rw [h, logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
  simp

/-- `logDeriv` is local: functions agreeing near `z₀` have the same logarithmic derivative
    near `z₀`. -/
theorem logDeriv_eventuallyEq {f h : ℂ → ℂ} {z₀ : ℂ} (hfh : f =ᶠ[𝓝 z₀] h) :
    logDeriv f =ᶠ[𝓝 z₀] logDeriv h := by
  filter_upwards [hfh.eventuallyEq_nhds, hfh] with z hz hz'
  rw [logDeriv_apply, logDeriv_apply, hz.deriv_eq, hz']

/-- **The splitting.** Near a finite-order zero, `logDeriv f z = n/(z − z₀) + logDeriv g z`
    with `g` the analytic non-vanishing cofactor. -/
theorem logDeriv_eq_order_div_add {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hne : analyticOrderAt f z₀ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀,
        logDeriv f z = (analyticOrderNatAt f z₀ : ℂ) / (z - z₀) + logDeriv g z := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hne
  refine ⟨g, hg, hg0, ?_⟩
  set n := analyticOrderNatAt f z₀ with hn
  have hfg' : f =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ n * g z := by
    filter_upwards [hfg] with z hz; simpa [smul_eq_mul] using hz
  have hld := logDeriv_eventuallyEq hfg'
  have hgnz : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hld, nhdsWithin_le_nhds hgnz,
    nhdsWithin_le_nhds hg.eventually_analyticAt] with z hz hld' hgz hga
  have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [hld']
  have hmul : logDeriv (fun w : ℂ => (w - z₀) ^ n * g w) z
      = logDeriv (fun w : ℂ => (w - z₀) ^ n) z + logDeriv g z :=
    logDeriv_mul (f := fun w : ℂ => (w - z₀) ^ n) (g := g) z
      (pow_ne_zero _ hz0) hgz (by fun_prop) hga.differentiableAt
  rw [hmul, logDeriv_sub_pow]

/-- **The limit.** `(z − z₀)·logDeriv f z → n` as `z → z₀` off `z₀`, where `n` is the order
    of the zero. For a non-zero (`n = 0`) this says the product tends to `0`. -/
theorem tendsto_sub_mul_logDeriv {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hne : analyticOrderAt f z₀ ≠ ⊤) :
    Tendsto (fun z => (z - z₀) * logDeriv f z) (𝓝[≠] z₀)
      (𝓝 ((analyticOrderNatAt f z₀ : ℕ) : ℂ)) := by
  obtain ⟨g, hg, hg0, hsplit⟩ := logDeriv_eq_order_div_add hf hne
  set n := analyticOrderNatAt f z₀ with hn
  have key : ∀ᶠ z in 𝓝[≠] z₀,
      (z - z₀) * logDeriv f z = (n : ℂ) + (z - z₀) * logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hsplit] with z hz hz'
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    rw [hz']
    field_simp
  rw [tendsto_congr' key]
  have hcont : ContinuousAt (logDeriv g) z₀ := by
    have : logDeriv g = fun z => deriv g z / g z := rfl
    rw [this]
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have h1 : Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
    have hca : ContinuousAt (fun z : ℂ => z - z₀) z₀ := by fun_prop
    simpa using hca.tendsto
  have h2 : Tendsto (fun z : ℂ => (n : ℂ) + (z - z₀) * logDeriv g z) (𝓝 z₀)
      (𝓝 ((n : ℂ) + 0 * logDeriv g z₀)) :=
    tendsto_const_nhds.add (h1.mul hcont.tendsto)
  simpa using h2.mono_left nhdsWithin_le_nhds

/-! ### Non-vacuity -/

/-- The model computation is not vacuous: `logDeriv ((·−1)^3)` at `2` is `3/(2−1) = 3`. -/
theorem logDeriv_sub_pow_nonvacuous : logDeriv (fun w : ℂ => (w - 1) ^ 3) 2 = 3 := by
  rw [logDeriv_sub_pow]; norm_num

end TDLean.Zeta
