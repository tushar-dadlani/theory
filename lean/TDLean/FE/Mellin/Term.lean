/-
  TDLean.FE.Mellin.Term -- cluster A3: the single-term Mellin integral.

      ∫₀^∞ t^{s/2−1} e^{−πn²t} dt  =  π^{−s/2} · n^{−s} · Γ(s/2)

  Summing this over `n ≥ 1` is what turns `ψ(t) = ∑_{n≥1} e^{−πn²t}` into
  `π^{−s/2}Γ(s/2)ζ(s)` — the completed zeta. This file does the single term; the interchange
  of sum and integral is the next brick.

  ORACLE: `MellinTail.v:143 T_exists` / `:183 T_spec` define `T(s) = ∫₁^∞ t^{s/2−1}ψ(t)dt`
  as a convergent improper integral, and `MellinTailSeries.v:214 tail_series` gives its
  term-by-term expansion. The Coq side works with the *tail* `∫₁^∞`; this is the full
  `∫₀^∞` of a single term, which is where the `Γ` comes from.

  `Gamma.Basic` is not gate-banned (only `Gamma.Deligne` is), so `Complex.Gamma` and
  `integral_cpow_mul_exp_neg_mul_Ioi` are available.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.PSeriesComplex

namespace TDLean.FE

open Complex Real MeasureTheory Set

/-- For a positive real base, `x^w = exp(log x · w)`. -/
theorem cpow_pos_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  have hne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log, Complex.arg_ofReal_of_nonneg hx.le]
  simp

/-- `(1/(πn²))^{s/2} = π^{−s/2}·n^{−s}`. -/
theorem scale_factor {s : ℂ} (n : ℕ+) :
    (1 / ((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) ^ (s / 2)
      = ((π : ℝ) : ℂ) ^ (-s / 2) * (((n : ℕ) : ℝ) : ℂ) ^ (-s) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hprod : (0 : ℝ) < π * ((n : ℕ) : ℝ) ^ 2 := by positivity
  have hinv : (0 : ℝ) < 1 / (π * ((n : ℕ) : ℝ) ^ 2) := by positivity
  have hcast : (1 / ((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      = ((1 / (π * ((n : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, cpow_pos_eq_exp hinv, cpow_pos_eq_exp hpi, cpow_pos_eq_exp hn, ← Complex.exp_add]
  congr 1
  have hlog : Real.log (1 / (π * ((n : ℕ) : ℝ) ^ 2))
      = -(Real.log π) - 2 * Real.log ((n : ℕ) : ℝ) := by
    rw [one_div, Real.log_inv, Real.log_mul hpi.ne' (by positivity), Real.log_pow]
    push_cast; ring
  rw [hlog]
  push_cast
  ring

/-- **The single-term Mellin integral.** -/
theorem mellin_gaussian_term {s : ℂ} (hs : 0 < s.re) (n : ℕ+) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1)
        * Complex.exp (-(((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * ((t : ℝ) : ℂ))))
      = ((π : ℝ) : ℂ) ^ (-s / 2) * (((n : ℕ) : ℝ) : ℂ) ^ (-s) * Complex.Gamma (s / 2) := by
  have hhalf : s / 2 = ((1 / 2 : ℝ) : ℂ) * s := by push_cast; ring
  have hs2 : 0 < (s / 2).re := by
    rw [hhalf, Complex.re_ofReal_mul]; linarith
  have hr : (0 : ℝ) < π * ((n : ℕ) : ℝ) ^ 2 := by
    have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    positivity
  have hmain := integral_cpow_mul_exp_neg_mul_Ioi (a := s / 2)
    (r := π * ((n : ℕ) : ℝ) ^ 2) hs2 hr
  rw [hmain, scale_factor n]


/-! ### Integrability, and the norm — the two inputs `integral_tsum` needs -/

/-- The scaled Gamma integrand is integrable on `(0,∞)`. mathlib has the *value* of this
    integral (`integral_cpow_mul_exp_neg_mul_Ioi`) but not its integrability, so it is derived
    here from the unscaled `Complex.GammaIntegral_convergent` by `t ↦ rt`. -/
theorem integrableOn_gaussian_term {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (t : ℂ))))
      (Ioi 0) := by
  have hbase := Complex.GammaIntegral_convergent hs
  have hscaled : IntegrableOn
      (fun t : ℝ => (((r * t : ℝ)) : ℂ) ^ (s - 1) * Complex.exp (-(((r * t : ℝ)) : ℂ)))
      (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))) 0 hr).mpr
    simpa using h (by simpa [mul_comm] using hbase)
  have hconst := hscaled.const_mul (((r : ℝ) : ℂ) ^ (-(s - 1)))
  refine MeasureTheory.IntegrableOn.congr_fun hconst ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (0 : ℝ) < t := ht
  have hsplit : (((r * t : ℝ)) : ℂ) ^ (s - 1)
      = ((r : ℝ) : ℂ) ^ (s - 1) * ((t : ℝ) : ℂ) ^ (s - 1) := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hr.le ht0.le _
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcancel : ((r : ℝ) : ℂ) ^ (1 - s) * ((r : ℝ) : ℂ) ^ (-1 + s) = 1 := by
    rw [← Complex.cpow_add _ _ hrne]
    norm_num
  have hexp : (((r * t : ℝ)) : ℂ) = (r : ℂ) * (t : ℂ) := by push_cast; ring
  rw [hsplit, hexp]
  ring_nf
  rw [hcancel, one_mul]

/-- `‖t^{s−1}e^{−rt}‖ = t^{Re s−1}e^{−rt}` for `t > 0`. -/
theorem norm_gaussian_term {s : ℂ} {r t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))‖
      = t ^ (s.re - 1) * Real.exp (-(r * t)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp [Complex.mul_re]


/-! ### The lintegral bound -/

/-- The real integrand `t^{σ−1}e^{−rt}` is integrable on `(0,∞)`. -/
theorem integrableOn_real_term {σ : ℝ} (hσ : 0 < σ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_gaussian_term (s := (σ : ℂ)) (by simpa using hσ) hr
  refine MeasureTheory.IntegrableOn.congr_fun h.norm ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_gaussian_term (s := (σ : ℂ)) (r := r) ht]
  simp

/-- `∫₀^∞ ‖t^{s/2−1}e^{−rt}‖ dt = (1/r)^{Re s/2}·Γ(Re s/2)`. -/
theorem integral_norm_term {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s / 2 - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))‖)
      = (1 / r) ^ (s.re / 2) * Real.Gamma (s.re / 2) := by
  have hs2 : 0 < s.re / 2 := by linarith
  have hcongr : (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s / 2 - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))‖)
      = ∫ t in Ioi (0 : ℝ), t ^ (s.re / 2 - 1) * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [norm_gaussian_term ht]
    congr 2
    rw [Complex.div_ofNat_re]
  rw [hcongr, integral_rpow_mul_exp_neg_mul_Ioi hs2 hr]

/-- **The bound `integral_tsum` needs:** the total mass is finite for `Re s > 1`. -/
theorem lintegral_norm_summable {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ+, ∫⁻ t in Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s / 2 - 1)
          * Complex.exp (-(((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * (t : ℂ)))‖ₑ ≠ ⊤ := by
  have hs0 : 0 < s.re := by linarith
  have hs2 : 0 < s.re / 2 := by linarith
  have hpi : (0 : ℝ) < π := Real.pi_pos
  -- each term is `ENNReal.ofReal` of the real integral
  have hterm : ∀ n : ℕ+, (∫⁻ t in Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s / 2 - 1)
        * Complex.exp (-(((π * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * (t : ℂ)))‖ₑ)
      = ENNReal.ofReal ((1 / (π * ((n : ℕ) : ℝ) ^ 2)) ^ (s.re / 2) * Real.Gamma (s.re / 2)) := by
    intro n
    have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have hr : (0 : ℝ) < π * ((n : ℕ) : ℝ) ^ 2 := by positivity
    have hint := integrableOn_gaussian_term (s := s / 2)
      (by rw [Complex.div_ofNat_re]; linarith) hr
    rw [← integral_norm_term hs0 hr,
      ofReal_integral_eq_lintegral_ofReal hint.norm
        (Filter.Eventually.of_forall fun t => norm_nonneg _)]
    exact lintegral_congr fun t => by rw [ofReal_norm_eq_enorm]
  rw [tsum_congr hterm]
  -- the resulting real series converges
  have hsummable : Summable (fun n : ℕ+ =>
      (1 / (π * ((n : ℕ) : ℝ) ^ 2)) ^ (s.re / 2) * Real.Gamma (s.re / 2)) := by
    have hbase : ∀ n : ℕ+,
        (1 / (π * ((n : ℕ) : ℝ) ^ 2)) ^ (s.re / 2) * Real.Gamma (s.re / 2)
          = ((1 / π) ^ (s.re / 2) * Real.Gamma (s.re / 2)) * (1 / ((n : ℕ) : ℝ) ^ s.re) := by
      intro n
      have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
      have hsplit : (1 : ℝ) / (π * ((n : ℕ) : ℝ) ^ 2) = (1 / π) * (((n : ℕ) : ℝ) ^ 2)⁻¹ := by
        field_simp
      have hpow : ((((n : ℕ) : ℝ) ^ 2)⁻¹) ^ (s.re / 2) = 1 / ((n : ℕ) : ℝ) ^ s.re := by
        rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast ((n : ℕ) : ℝ) 2,
          ← Real.rpow_mul hn.le, one_div]
        congr 2
        push_cast
        ring
      rw [hsplit, Real.mul_rpow (by positivity) (by positivity), hpow]
      ring
    rw [funext hbase]
    exact ((Real.summable_one_div_nat_rpow.mpr hs).comp_injective
      PNat.coe_injective).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
  exact ENNReal.ofReal_ne_top

end TDLean.FE
