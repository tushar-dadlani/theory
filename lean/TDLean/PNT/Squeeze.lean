/-
  TDLean.PNT.Squeeze -- C10, part 10: from `∫₀^∞ f` convergent to `ψ(x) ~ x`.

  Zagier's final argument. `tendsto_integral_fNewman'` gives convergence of
  `∫₀^T f`, `f t = ψ(eᵗ)e^{−t} − 1`. Convergence forces the tail `∫_a^b f` to be small; but if
  `ψ` overshoots — `ψ(eᵗ) ≥ λeᵗ` for some `λ > 1` and arbitrarily large `t` — then
  **monotonicity of `ψ`** makes `∫_t^{t+log λ} f` at least the *fixed* positive constant
  `λ − 1 − log λ`. Contradiction.

  Working in `t`-coordinates throughout (rather than substituting back to `x = eᵗ`) keeps the
  estimate elementary: on `[t, t+c]`, monotonicity gives `f(s) ≥ λe^{t−s} − 1` directly, and
  that integrates in closed form to `λ(1 − e^{−c}) − c`.
-/
import TDLean.PNT.Tauberian

namespace TDLean.PNT

open MeasureTheory TDLean.Zeta Filter Topology

/-! ### Convergence forces small tails -/

theorem intervalIntegrable_fNewmanC' (a b : ℝ) :
    IntervalIntegrable fNewmanC MeasureTheory.volume a b :=
  (intervalIntegrable_fNewmanC a).symm.trans (intervalIntegrable_fNewmanC b)

theorem integral_split (a b : ℝ) :
    (∫ t in (0 : ℝ)..b, fNewmanC t) - (∫ t in (0 : ℝ)..a, fNewmanC t)
      = ∫ t in a..b, fNewmanC t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_fNewmanC a) (intervalIntegrable_fNewmanC' a b)]
  ring

/-- **The Cauchy criterion.** Beyond some point every tail integral is small. -/
theorem cauchy_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ a b : ℝ, M ≤ a → M ≤ b → ‖∫ t in a..b, fNewmanC t‖ < ε := by
  have h := tendsto_integral_fNewman'
  rw [Metric.tendsto_atTop] at h
  obtain ⟨M, hM⟩ := h (ε / 2) (by linarith)
  refine ⟨M, fun a b ha hb => ?_⟩
  have hA := hM a ha
  have hB := hM b hb
  rw [Complex.dist_eq] at hA hB
  have hsplit : (∫ t in a..b, fNewmanC t)
      = ((∫ t in (0 : ℝ)..b, fNewmanC t) - gNewman 0)
        - ((∫ t in (0 : ℝ)..a, fNewmanC t) - gNewman 0) := by
    rw [← integral_split]; ring
  rw [hsplit]
  calc ‖((∫ t in (0 : ℝ)..b, fNewmanC t) - gNewman 0)
        - ((∫ t in (0 : ℝ)..a, fNewmanC t) - gNewman 0)‖
      ≤ ‖(∫ t in (0 : ℝ)..b, fNewmanC t) - gNewman 0‖
        + ‖(∫ t in (0 : ℝ)..a, fNewmanC t) - gNewman 0‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by exact add_lt_add hB hA
    _ = ε := by ring

/-! ### The fixed positive constant -/

/-- `λ − 1 − log λ > 0` for `λ > 1`: the overshoot gap. -/
theorem overshoot_pos {lam : ℝ} (h : 1 < lam) : 0 < lam - 1 - Real.log lam := by
  have := Real.log_lt_sub_one_of_pos (by linarith : (0:ℝ) < lam) (by linarith : lam ≠ 1)
  linarith

/-- `1 − λ + log λ < 0` for `0 < λ < 1`: the undershoot gap. -/
theorem undershoot_neg {lam : ℝ} (h0 : 0 < lam) (h : lam < 1) : 1 - lam + Real.log lam < 0 := by
  have := Real.log_lt_sub_one_of_pos h0 (by linarith : lam ≠ 1)
  linarith

/-! ### The model integral -/

/-- `∫_t^{t+c} (λ·e^{t−s} − 1) ds = λ(1 − e^{−c}) − c`, in closed form. -/
theorem integral_model (lam t c : ℝ) :
    (∫ s in t..(t + c), lam * Real.exp (t - s) - 1)
      = lam * (1 - Real.exp (-c)) - c := by
  have hderiv : ∀ s ∈ Set.uIcc t (t + c),
      HasDerivAt (fun u : ℝ => -lam * Real.exp (t - u) - u)
        (lam * Real.exp (t - s) - 1) s := by
    intro s _
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (t - u)) (-Real.exp (t - s)) s := by
      have hin : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
        simpa using (hasDerivAt_const s t).sub (hasDerivAt_id s)
      simpa using (Real.hasDerivAt_exp (t - s)).comp s hin
    have h2 := (h1.const_mul (-lam)).sub (hasDerivAt_id s)
    convert h2 using 1
    ring
  have hcont : ContinuousOn (fun s : ℝ => lam * Real.exp (t - s) - 1) (Set.uIcc t (t + c)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hc : Real.exp (t - (t + c)) = Real.exp (-c) := by congr 1; ring
  rw [hc]
  simp only [sub_self, Real.exp_zero]
  ring

/-! ### Monotonicity gives the pointwise bound -/

/-- If `ψ` overshoots at `t`, then on `[t, t+c]` the integrand is at least the model. -/
theorem fNewman_ge_model {lam t : ℝ} (h : lam * Real.exp t ≤ psi (Real.exp t)) {s : ℝ}
    (hs : t ≤ s) : lam * Real.exp (t - s) - 1 ≤ fNewman s := by
  have hmono : psi (Real.exp t) ≤ psi (Real.exp s) :=
    psi_mono (Real.exp_le_exp.mpr hs)
  have hpos : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hkey : lam * Real.exp t * Real.exp (-s) ≤ psi (Real.exp s) * Real.exp (-s) :=
    mul_le_mul_of_nonneg_right (le_trans h hmono) hpos.le
  have hexp : Real.exp t * Real.exp (-s) = Real.exp (t - s) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  rw [fNewman, ← hexp, ← mul_assoc]
  linarith [hkey]

/-- **The overshoot bound.** If `ψ(eᵗ) ≥ λeᵗ` with `λ > 1`, the tail integral over
    `[t, t + log λ]` is at least the fixed constant `λ − 1 − log λ > 0`. -/
theorem integral_ge_overshoot {lam t : ℝ} (hlam : 1 < lam)
    (h : lam * Real.exp t ≤ psi (Real.exp t)) :
    lam - 1 - Real.log lam ≤ ∫ s in t..(t + Real.log lam), fNewman s := by
  have hlogpos : 0 < Real.log lam := Real.log_pos hlam
  have hle : t ≤ t + Real.log lam := by linarith
  have hint1 : IntervalIntegrable (fun s : ℝ => lam * Real.exp (t - s) - 1)
      MeasureTheory.volume t (t + Real.log lam) := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hint2 : IntervalIntegrable fNewman MeasureTheory.volume t (t + Real.log lam) := by
    have h1 : IntervalIntegrable (fun s : ℝ => psi (Real.exp s)) MeasureTheory.volume
        t (t + Real.log lam) := (monotone_psi_exp.monotoneOn _).intervalIntegrable
    exact (h1.mul_continuousOn (by fun_prop)).sub intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hle hint1 hint2
    (fun s hs => fNewman_ge_model h hs.1)
  rw [integral_model] at hmono
  have hexp : Real.exp (-Real.log lam) = 1 / lam := by
    rw [Real.exp_neg, Real.exp_log (by linarith)]
    ring
  rw [hexp] at hmono
  have hval : lam * (1 - 1 / lam) - Real.log lam = lam - 1 - Real.log lam := by
    field_simp
  linarith [hmono, hval]


/-! ### The mirror bound, and the contradiction -/

theorem fNewman_le_model {lam t : ℝ} (h : psi (Real.exp t) ≤ lam * Real.exp t) {s : ℝ}
    (hs : s ≤ t) : fNewman s ≤ lam * Real.exp (t - s) - 1 := by
  have hmono : psi (Real.exp s) ≤ psi (Real.exp t) := psi_mono (Real.exp_le_exp.mpr hs)
  have hpos : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hkey : psi (Real.exp s) * Real.exp (-s) ≤ lam * Real.exp t * Real.exp (-s) :=
    mul_le_mul_of_nonneg_right (le_trans hmono h) hpos.le
  have hexp : Real.exp t * Real.exp (-s) = Real.exp (t - s) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  rw [fNewman, ← hexp, ← mul_assoc]
  linarith [hkey]

theorem intervalIntegrable_fNewman' (a b : ℝ) :
    IntervalIntegrable fNewman MeasureTheory.volume a b := by
  have h1 : IntervalIntegrable (fun s : ℝ => psi (Real.exp s)) MeasureTheory.volume a b :=
    (monotone_psi_exp.monotoneOn _).intervalIntegrable
  exact (h1.mul_continuousOn (by fun_prop)).sub intervalIntegrable_const

/-- **The undershoot bound.** -/
theorem integral_le_undershoot {lam t : ℝ} (h0 : 0 < lam) (hlam : lam < 1)
    (h : psi (Real.exp t) ≤ lam * Real.exp t) :
    (∫ s in (t + Real.log lam)..t, fNewman s) ≤ -(lam - 1 - Real.log lam) := by
  have hlogneg : Real.log lam < 0 := Real.log_neg h0 hlam
  have hle : t + Real.log lam ≤ t := by linarith
  have hint1 : IntervalIntegrable (fun s : ℝ => lam * Real.exp (t - s))
      MeasureTheory.volume (t + Real.log lam) t := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hmono := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_fNewman' _ _)
    ((hint1.sub intervalIntegrable_const))
    (fun s hs => fNewman_le_model h hs.2)
  have hmodel : (∫ s in (t + Real.log lam)..t, lam * Real.exp (t - s) - 1)
      = -(lam - 1 - Real.log lam) := by
    have h1 := integral_model lam t (Real.log lam)
    rw [Real.exp_neg, Real.exp_log h0] at h1
    rw [intervalIntegral.integral_symm, h1]
    field_simp
  rw [hmodel] at hmono
  exact hmono

theorem integral_ofReal_fNewman (a b : ℝ) :
    (∫ t in a..b, fNewmanC t) = (((∫ t in a..b, fNewman t : ℝ)) : ℂ) :=
  intervalIntegral.integral_ofReal

/-- **No overshoot.** For `λ > 1`, eventually `ψ(eᵗ) < λeᵗ`. -/
theorem no_overshoot {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ t in atTop, psi (Real.exp t) < lam * Real.exp t := by
  have hδ : 0 < lam - 1 - Real.log lam := overshoot_pos hlam
  have hlogpos : 0 < Real.log lam := Real.log_pos hlam
  obtain ⟨M, hM⟩ := cauchy_tail hδ
  filter_upwards [eventually_ge_atTop M] with t ht
  by_contra hcon
  push_neg at hcon
  have h1 := integral_ge_overshoot hlam hcon
  have h2 := hM t (t + Real.log lam) ht (by linarith)
  rw [integral_ofReal_fNewman, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : |∫ s in t..(t + Real.log lam), fNewman s| < lam - 1 - Real.log lam := h2
  rw [abs_lt] at h3
  linarith [h3.2, h1]

/-- **No undershoot.** For `0 < λ < 1`, eventually `λeᵗ < ψ(eᵗ)`. -/
theorem no_undershoot {lam : ℝ} (h0 : 0 < lam) (hlam : lam < 1) :
    ∀ᶠ t in atTop, lam * Real.exp t < psi (Real.exp t) := by
  have hδ : 0 < lam - 1 - Real.log lam := by
    have := Real.log_lt_sub_one_of_pos h0 (by linarith : lam ≠ 1)
    linarith
  have hlogneg : Real.log lam < 0 := Real.log_neg h0 hlam
  obtain ⟨M, hM⟩ := cauchy_tail hδ
  filter_upwards [eventually_ge_atTop (M - Real.log lam)] with t ht
  by_contra hcon
  push_neg at hcon
  have h1 := integral_le_undershoot h0 hlam hcon
  have h2 := hM (t + Real.log lam) t (by linarith) (by linarith)
  rw [integral_ofReal_fNewman, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : |∫ s in (t + Real.log lam)..t, fNewman s| < lam - 1 - Real.log lam := h2
  rw [abs_lt] at h3
  linarith [h3.1, h1]


/-! ### `ψ(x) ~ x` -/

theorem tendsto_psi_exp :
    Tendsto (fun t : ℝ => psi (Real.exp t) / Real.exp t) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := min ε (1 / 2) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hee : e ≤ ε := min_le_left _ _
  obtain ⟨M1, hM1⟩ := eventually_atTop.mp (no_overshoot (lam := 1 + e) (by linarith))
  obtain ⟨M2, hM2⟩ :=
    eventually_atTop.mp (no_undershoot (lam := 1 - e) (by linarith) (by linarith))
  refine ⟨max M1 M2, fun t ht => ?_⟩
  have h1 := hM1 t (le_trans (le_max_left _ _) ht)
  have h2 := hM2 t (le_trans (le_max_right _ _) ht)
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hd1 : psi (Real.exp t) / Real.exp t < 1 + e := by
    rw [div_lt_iff₀ hexp]; linarith
  have hd2 : 1 - e < psi (Real.exp t) / Real.exp t := by
    rw [lt_div_iff₀ hexp]; linarith
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **`ψ(x)/x → 1`** — the Chebyshev form of the Prime Number Theorem. -/
theorem tendsto_psi : Tendsto (fun x : ℝ => psi x / x) atTop (nhds 1) := by
  have h := tendsto_psi_exp.comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply, Real.exp_log hx]

end TDLean.PNT
