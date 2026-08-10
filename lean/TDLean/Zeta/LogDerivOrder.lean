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

/-! ### Punctured versions, for a pole as well as a zero

    The Hadamard--de la Vallee Poussin argument needs the same limit at the *pole* `s = 1`
    of zeta, where the local model is `(z − z₀)^(−1)·g`. Allowing an integer exponent covers
    zero and pole uniformly. The factorisation is then only available on a *punctured*
    neighbourhood, so locality of `logDeriv` has to be re-proved there -- which works
    because `{z₀}ᶜ` is open, so `𝓝[{z₀}ᶜ] z = 𝓝 z` at every `z ≠ z₀`. -/

theorem logDeriv_eventuallyEq_punctured {f h : ℂ → ℂ} {z₀ : ℂ}
    (hfh : ∀ᶠ z in 𝓝[≠] z₀, f z = h z) :
    ∀ᶠ z in 𝓝[≠] z₀, logDeriv f z = logDeriv h z := by
  filter_upwards [eventually_eventually_nhdsWithin.mpr hfh, hfh, self_mem_nhdsWithin]
    with z hz hz' hzne
  rw [(isOpen_compl_singleton (x := z₀)).nhdsWithin_eq hzne] at hz
  rw [logDeriv_apply, logDeriv_apply, Filter.EventuallyEq.deriv_eq hz, hz']

/-- `logDeriv` of an integer power of `(· − z₀)`. -/
theorem logDeriv_sub_zpow (z₀ : ℂ) (m : ℤ) {z : ℂ} (hz : z - z₀ ≠ 0) :
    logDeriv (fun w : ℂ => (w - z₀) ^ m) z = m / (z - z₀) := by
  have h : (fun w : ℂ => (w - z₀) ^ m) = (fun u : ℂ => u ^ m) ∘ (fun w : ℂ => w - z₀) := rfl
  rw [h, logDeriv_comp (f := fun u : ℂ => u ^ m) (g := fun w : ℂ => w - z₀) (x := z)
    (differentiableAt_zpow.mpr (Or.inl hz)) (by fun_prop), logDeriv_zpow]
  simp

/-- **The limit, uniformly for zeros and poles.** If `f z = (z − z₀)^m · g z` on a punctured
    neighbourhood with `g` analytic and `g z₀ ≠ 0`, then `(z − z₀)·logDeriv f z → m`.
    `m > 0` is a zero of order `m`, `m < 0` a pole of order `−m`. -/
theorem tendsto_sub_mul_logDeriv_of_factor {f g : ℂ → ℂ} {z₀ : ℂ} {m : ℤ}
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ m * g z) :
    Tendsto (fun z => (z - z₀) * logDeriv f z) (𝓝[≠] z₀) (𝓝 ((m : ℤ) : ℂ)) := by
  have hld := logDeriv_eventuallyEq_punctured hfac
  have hgnz : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have key : ∀ᶠ z in 𝓝[≠] z₀,
      (z - z₀) * logDeriv f z = (m : ℂ) + (z - z₀) * logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hld, nhdsWithin_le_nhds hgnz,
      nhdsWithin_le_nhds hg.eventually_analyticAt] with z hz hld' hgz hga
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hd : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ m) z :=
      (differentiableAt_zpow.mpr (Or.inl hz0)).comp z (differentiableAt_id.sub_const z₀)
    have hmul : logDeriv (fun w : ℂ => (w - z₀) ^ m * g w) z
        = logDeriv (fun w : ℂ => (w - z₀) ^ m) z + logDeriv g z :=
      logDeriv_mul z (zpow_ne_zero _ hz0) hgz hd hga.differentiableAt
    rw [hld', hmul, logDeriv_sub_zpow z₀ m hz0]
    field_simp
  rw [tendsto_congr' key]
  have hcont : ContinuousAt (logDeriv g) z₀ := by
    have hlg : logDeriv g = fun z => deriv g z / g z := rfl
    rw [hlg]
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have h1 : Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
    have hca : ContinuousAt (fun z : ℂ => z - z₀) z₀ := by fun_prop
    simpa using hca.tendsto
  have h2 : Tendsto (fun z : ℂ => (m : ℂ) + (z - z₀) * logDeriv g z) (𝓝 z₀)
      (𝓝 ((m : ℂ) + 0 * logDeriv g z₀)) :=
    tendsto_const_nhds.add (h1.mul hcont.tendsto)
  simpa using h2.mono_left nhdsWithin_le_nhds

/-! ### Non-vacuity -/

/-- The model computation is not vacuous: `logDeriv ((·−1)^3)` at `2` is `3/(2−1) = 3`. -/
theorem logDeriv_sub_pow_nonvacuous : logDeriv (fun w : ℂ => (w - 1) ^ 3) 2 = 3 := by
  rw [logDeriv_sub_pow]; norm_num

end TDLean.Zeta
