/-
  TDLean.FE.Theta.Transform -- cluster A1: the Jacobi theta transformation.

  `∑_{n∈ℤ} e^{−πan²} = a^{−1/2} ∑_{n∈ℤ} e^{−πn²/a}`  for `a > 0`.

  ORACLE: `spectral-theory/GaussThetaTransform.v:98 theta_transform`
  (`θ(1/t) = √t·θ(t)`), which is axiom-free and proved by a *different* route — pointwise
  Fourier-series convergence for a periodised Gaussian, not Poisson summation.
  **Note for the ledger:** repo A's own `spectral-theory/LEDGER.md:239` and the footer of
  `JacobiTheta.v` both still call this "the open next milestone". They are stale; the
  transformation landed in Coq on 2026-07-31.

  ## Ban boundary

  `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation` is gate-banned — it contains
  this very theorem (`Real.tsum_exp_neg_mul_int_sq`). What is *not* banned, and is used here:
  `Analysis.Fourier.PoissonSummation` (the general formula) and
  `Gaussian.FourierTransform` (`fourier_gaussian_pi`, the Gaussian's self-duality).
  So the reproduction is honest: general Poisson plus Gaussian self-duality, with the decay
  estimates — which live only in the banned file — rebuilt below.
-/
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace TDLean.FE

open Complex Filter Asymptotics Real
open scoped FourierTransform

/-! ### Decay of the Gaussian -/

/-- The Gaussian beats every power at `+∞`. Reproduces
    `Gaussian/PoissonSummation.lean:37 rexp_neg_quadratic_isLittleO_rpow_atTop` (banned). -/
theorem gaussian_isLittleO_atTop {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)) =o[atTop]
      fun x : ℝ => x ^ s := by
  have hcast : ∀ x : ℝ, -(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2 = (((-(π * a) * x ^ 2 : ℝ)) : ℂ) := by
    intro x; push_cast; ring
  have hnorm : ∀ x : ℝ, ‖Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)‖
      = Real.exp (-(π * a) * x ^ 2) := by
    intro x
    rw [hcast x, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hreal : (fun x : ℝ => Real.exp (-(π * a) * x ^ 2)) =o[atTop] fun x : ℝ => x ^ s := by
    have hpa : 0 < π * a := by positivity
    have hkey : (fun x : ℝ => Real.exp (-(π * a) * x ^ 2)) =o[atTop]
        fun x : ℝ => Real.exp (-x) := by
      rw [isLittleO_exp_comp_exp_comp]
      have hrw : (fun x : ℝ => -x - (-(π * a) * x ^ 2)) = fun x : ℝ => x * (π * a * x - 1) := by
        ext1 x; ring
      rw [hrw]
      exact tendsto_id.atTop_mul_atTop₀
        (tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hpa))
    refine hkey.trans ?_
    simpa only [neg_one_mul] using isLittleO_exp_neg_mul_rpow_atTop zero_lt_one s
  rw [isLittleO_iff] at hreal ⊢
  intro c hc
  filter_upwards [hreal hc] with x hx
  rw [hnorm x]
  calc Real.exp (-(π * a) * x ^ 2) = ‖Real.exp (-(π * a) * x ^ 2)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ c * ‖x ^ s‖ := hx

/-- Same at `−∞`, by evenness. -/
theorem gaussian_isLittleO_cocompact {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)) =o[cocompact ℝ]
      fun x : ℝ => |x| ^ s := by
  have heven : ∀ x : ℝ, Complex.exp (-(π : ℂ) * (a : ℂ) * ((-x : ℝ) : ℂ) ^ 2)
      = Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2) := by
    intro x; push_cast; ring_nf
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · -- at `atBot`, compose with `x ↦ -x`
    have hcomp := (gaussian_isLittleO_atTop ha s).comp_tendsto tendsto_neg_atBot_atTop
    refine hcomp.congr' ?_ ?_
    · filter_upwards with x
      simp only [Function.comp_apply]
      exact heven x
    · filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
      simp only [Function.comp_apply]
      rw [abs_of_nonpos hx]
  · refine (gaussian_isLittleO_atTop ha s).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [abs_of_nonneg hx]


/-! ### The transformation -/

/-- **Jacobi's theta transformation.** `∑_{n∈ℤ} e^{−πan²} = a^{−1/2} ∑_{n∈ℤ} e^{−πn²/a}`.

    ORACLE: `GaussThetaTransform.v:98 theta_transform` (`θ(1/t) = √t·θ(t)`), proved there by
    pointwise Fourier-series convergence for a periodised Gaussian; here by general Poisson
    summation plus the Gaussian's Fourier self-duality. -/
theorem tsum_gaussian_transform {a : ℝ} (ha : 0 < a) :
    ∑' n : ℤ, Complex.exp (-(π : ℂ) * (a : ℂ) * (n : ℂ) ^ 2)
      = 1 / (a : ℂ) ^ (1 / 2 : ℂ)
        * ∑' n : ℤ, Complex.exp (-(π : ℂ) * ((1 / a : ℝ) : ℂ) * (n : ℂ) ^ 2) := by
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hare : (0 : ℝ) < ((a : ℂ)).re := by simpa using ha
  have hainv : (0 : ℝ) < 1 / a := by positivity
  set f : ℝ → ℂ := fun x => Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2) with hfdef
  have hcont : Continuous f := by rw [hfdef]; fun_prop
  -- the Fourier transform, rewritten with a real parameter `1/a`
  have hrecip : -(π : ℂ) / (a : ℂ) = -(π : ℂ) * ((1 / a : ℝ) : ℂ) := by
    push_cast; ring
  have hFf : 𝓕 f = fun t : ℝ =>
      1 / (a : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(π : ℂ) * ((1 / a : ℝ) : ℂ) * (t : ℂ) ^ 2) := by
    rw [hfdef, fourier_gaussian_pi hare]
    funext t
    rw [hrecip]
  -- decay on both sides
  have hdecay : f =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) :=
    (gaussian_isLittleO_cocompact ha (-2)).isBigO
  have hdecayF : (𝓕 f) =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    rw [hFf]
    exact ((gaussian_isLittleO_cocompact hainv (-2)).isBigO).const_mul_left _
  -- Poisson summation at `x = 0`
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay hcont (b := 2) (by norm_num)
    hdecay hdecayF 0
  have hzero : ((0 : ℝ) : UnitAddCircle) = 0 := by
    simp
  rw [hzero] at hpois
  simp only [fourier_eval_zero, mul_one, zero_add] at hpois
  have hLHS : ∑' n : ℤ, f ((n : ℤ) : ℝ)
      = ∑' n : ℤ, Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℤ) : ℂ) ^ 2) := by
    refine tsum_congr fun n => ?_
    change Complex.exp (-(π : ℂ) * (a : ℂ) * ((((n : ℤ) : ℝ)) : ℂ) ^ 2)
      = Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℤ) : ℂ) ^ 2)
    norm_cast
  have hRHS : ∑' n : ℤ, 𝓕 f ((n : ℤ) : ℝ)
      = 1 / (a : ℂ) ^ (1 / 2 : ℂ)
        * ∑' n : ℤ, Complex.exp (-(π : ℂ) * ((1 / a : ℝ) : ℂ) * ((n : ℤ) : ℂ) ^ 2) := by
    rw [hFf, tsum_mul_left]
    congr 1
  rw [← hLHS, ← hRHS]
  exact hpois


/-! ### Summability

    Poisson summation gave the identity without ever exposing summability as a standalone
    fact, but the `ℤ`-to-`ℕ` decomposition (`tsum_of_add_one_of_neg_add_one`) needs it as a
    hypothesis. Like the decay estimates, it lives only in the gate-banned
    `Gaussian.PoissonSummation`, so it is rebuilt here — by comparison with a geometric
    series, using `n ≤ n²`. -/

theorem norm_gaussian {a : ℝ} (x : ℝ) :
    ‖Complex.exp (-(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)‖ = Real.exp (-(π * a) * x ^ 2) := by
  have hcast : -(π : ℂ) * (a : ℂ) * (x : ℂ) ^ 2 = (((-(π * a) * x ^ 2 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hcast, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem summable_gaussian_nat {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.exp (-(π * a) * (n : ℝ) ^ 2)) := by
  have hpa : 0 < π * a := by positivity
  have hr : Real.exp (-(π * a)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hr0 : 0 ≤ Real.exp (-(π * a)) := (Real.exp_pos _).le
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hr)
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
      nlinarith
  nlinarith

/-- The `ℤ`-indexed Gaussian series is summable. -/
theorem summable_gaussian_int {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Complex.exp (-(π : ℂ) * (a : ℂ) * (n : ℂ) ^ 2)) := by
  refine Summable.of_norm (Summable.of_nat_of_neg ?_ ?_)
  · refine (summable_gaussian_nat ha).congr fun n => ?_
    have hc : ((((n : ℕ) : ℤ)) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_gaussian]
  · refine (summable_gaussian_nat ha).congr fun n => ?_
    have hc : (((-((n : ℕ) : ℤ)) : ℤ) : ℂ) = ((-((n : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_gaussian]
    congr 1
    ring


/-! ### From the `ℤ`-sum to `ψ`

    `θ(a) = ∑_{n∈ℤ} e^{−πan²} = 1 + 2ψ(a)` with `ψ(a) = ∑_{n≥1} e^{−πan²}`. The Gaussian is
    even, so the `n < 0` half duplicates the `n > 0` half. -/

/-- `ψ(a) = ∑_{n≥1} e^{−πan²}`, indexed over `ℕ` by `n ↦ n+1`. -/
noncomputable def psiNat (a : ℝ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2)

theorem summable_psiNat {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2)) := by
  refine Summable.of_norm ?_
  have hshift : Summable (fun n : ℕ => Real.exp (-(π * a) * ((n : ℝ) + 1) ^ 2)) := by
    refine ((summable_nat_add_iff 1).mpr (summable_gaussian_nat ha)).congr fun n => ?_
    congr 2
    push_cast
    ring
  refine hshift.congr fun n => ?_
  have hc : ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hc, norm_gaussian]

set_option maxHeartbeats 1000000 in
-- The `ℤ`-to-`ℕ` decomposition unifies against a named `f`, but the cast-heavy Gaussian
-- argument still makes elaboration expensive; the default budget is not quite enough.
/-- **`θ(a) = 1 + 2ψ(a)`.** -/
theorem tsum_gaussian_eq {a : ℝ} (ha : 0 < a) :
    ∑' n : ℤ, Complex.exp (-(π : ℂ) * (a : ℂ) * (n : ℂ) ^ 2) = 1 + 2 * psiNat a := by
  set f : ℤ → ℂ := fun n => Complex.exp (-(π : ℂ) * (a : ℂ) * (n : ℂ) ^ 2) with hfdef
  have hp : ∀ n : ℕ, f ((n : ℤ) + 1)
      = Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2) := by
    intro n
    simp only [hfdef]
    congr 1
    push_cast
    ring
  have hm : ∀ n : ℕ, f (-((n : ℤ) + 1))
      = Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2) := by
    intro n
    simp only [hfdef]
    congr 1
    push_cast
    ring
  have hsp : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    (summable_psiNat ha).congr fun n => (hp n).symm
  have hsm : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    (summable_psiNat ha).congr fun n => (hm n).symm
  have hzero : f 0 = 1 := by simp [hfdef]
  rw [tsum_of_add_one_of_neg_add_one hsp hsm, tsum_congr hp, tsum_congr hm, hzero, ← psiNat]
  ring


/-! ### The transformation law for `ψ` -/

theorem cpow_half_eq_sqrt {a : ℝ} (ha : 0 ≤ a) :
    ((a : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
  rw [show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_cpow ha,
    ← Real.sqrt_eq_rpow]

/-- **`ψ(1/a) = (√a − 1)/2 + √a·ψ(a)`.** The form the Mellin split needs: the `√a·ψ(a)` term
    is what turns the `(0,1)` piece into a `(1,∞)` piece with `s` replaced by `1−s`, and the
    `(√a−1)/2` is what produces the two elementary pole terms. -/
theorem psiNat_transform {a : ℝ} (ha : 0 < a) :
    psiNat (1 / a) = (((Real.sqrt a : ℝ) : ℂ) - 1) / 2
      + ((Real.sqrt a : ℝ) : ℂ) * psiNat a := by
  have hainv : (0 : ℝ) < 1 / a := by positivity
  have hsqpos : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqpos.ne'
  have h1 := tsum_gaussian_transform ha
  rw [tsum_gaussian_eq ha, tsum_gaussian_eq hainv, cpow_half_eq_sqrt ha.le] at h1
  have h2 : ((Real.sqrt a : ℝ) : ℂ) * (1 + 2 * psiNat a) = 1 + 2 * psiNat (1 / a) := by
    rw [h1]
    field_simp
  linear_combination -h2 / 2

end TDLean.FE
