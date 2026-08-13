/-
  TDLean.PNT.PrimeCountingAsymp -- C10, part 13: `π(x) ~ x/log x`.

  The two bounds of `PiCount.lean` sandwich `π(x)·log x / x`:

      θ(x)/x  ≤  π(x)·log x / x  ≤  (x^α+1)·log x/x  +  (1/α)·θ(x)/x

  Both outer terms tend to `1` and `1/α`, and `α < 1` is arbitrary, so letting `α → 1` pins
  the limit at `1`.

  ORACLE: `PNTConditional.v:52 pi_asymp_of_psi`
  (`ψ(N)/N → 1 → π(N)/(N/log N) → 1`). **Statement-fidelity note:** the Coq version is a
  `Un_cv` over a **ℕ-sequence**; this is a **real** `atTop` limit. The two agree at integers
  and the real form is strictly stronger, so this is a *strengthening*, not a plain
  confirmation.
-/
import TDLean.PNT.PiCount

namespace TDLean.PNT

open Filter Topology TDLean.Zeta

/-- `(x^α + 1)·log x / x → 0` for `0 < α < 1`. -/
theorem tendsto_rpow_mul_log_div {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun x : ℝ => (x ^ α + 1) * Real.log x / x) atTop (nhds 0) := by
  set e : ℝ := (1 - α) / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hlim : Tendsto (fun x : ℝ => (2 / e) * x ^ (-e)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop he0).const_mul (2 / e)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h1 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
    have h2 : (0 : ℝ) ≤ x ^ α := Real.rpow_nonneg (by linarith) α
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hxa : (1 : ℝ) ≤ x ^ α := Real.one_le_rpow hx hα0.le
    have hlogb : Real.log x ≤ (2 / (1 - α)) * x ^ e := by
      have := log_le_rpow_div hx0 he0
      calc Real.log x ≤ x ^ e / e := this
        _ = (2 / (1 - α)) * x ^ e := by rw [he]; field_simp
    have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
    have hnum : (x ^ α + 1) * Real.log x
        ≤ (2 * x ^ α) * ((2 / (1 - α)) * x ^ e) := by
      refine mul_le_mul (by linarith) hlogb hL0 (by positivity)
    have hsum : x ^ α * x ^ e = x ^ (-e) * x := by
      rw [← Real.rpow_add hx0,
        show x ^ (-e) * x = x ^ (-e + 1) by rw [Real.rpow_add hx0, Real.rpow_one]]
      congr 1
      rw [he]; ring
    have hconst : (2 : ℝ) * (2 / (1 - α)) = 2 / e := by
      rw [he]; field_simp
    have hcollapse : (2 * x ^ α) * ((2 / (1 - α)) * x ^ e) = (2 / e) * x ^ (-e) * x := by
      calc (2 * x ^ α) * ((2 / (1 - α)) * x ^ e)
          = (2 * (2 / (1 - α))) * (x ^ α * x ^ e) := by ring
        _ = (2 / e) * (x ^ (-e) * x) := by rw [hconst, hsum]
        _ = (2 / e) * x ^ (-e) * x := by ring
    rw [div_le_iff₀ hx0, ← hcollapse]
    exact hnum

/-- **`π(x)·log x / x → 1`** — the Prime Number Theorem. -/
theorem tendsto_piCount :
    Tendsto (fun x : ℝ => piCount x * Real.log x / x) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set d : ℝ := min ε (1 / 2) / 4 with hd
  have hd0 : 0 < d := by
    rw [hd]; have : 0 < min ε (1 / 2) := lt_min hε (by norm_num); linarith
  have hdε : 4 * d ≤ ε := by
    rw [hd]; have : min ε (1 / 2) ≤ ε := min_le_left _ _; linarith
  have hdhalf : 4 * d ≤ 1 / 2 := by
    rw [hd]; have : min ε (1 / 2) ≤ 1 / 2 := min_le_right _ _; linarith
  set α : ℝ := 1 / (1 + d) with hα
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : α < 1 := by
    rw [hα, div_lt_one (by linarith)]; linarith
  have hinv : 1 / α = 1 + d := by rw [hα]; field_simp
  obtain ⟨M1, hM1⟩ := Metric.tendsto_atTop.mp tendsto_theta d hd0
  obtain ⟨M2, hM2⟩ := Metric.tendsto_atTop.mp (tendsto_rpow_mul_log_div hα0 hα1) d hd0
  refine ⟨max (max M1 M2) 2, fun x hx => ?_⟩
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have h1 := hM1 x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  have h2 := hM2 x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  have hθ : |theta x / x - 1| < d := abs_lt.mpr h1
  have hrp : |(x ^ α + 1) * Real.log x / x - 0| < d := abs_lt.mpr h2
  rw [sub_zero] at hrp
  have hθlt : theta x / x < 1 + d := by linarith [h1.2]
  have hθgt : 1 - d < theta x / x := by linarith [h1.1]
  have hrplt : (x ^ α + 1) * Real.log x / x < d := by
    have := abs_lt.mp hrp; linarith [this.2]
  -- lower: `θ(x)/x ≤ π(x)·log x/x`
  have hlow : theta x / x ≤ piCount x * Real.log x / x :=
    div_le_div_of_nonneg_right (theta_le_piCount_mul_log hx1.le) hx0.le
  -- upper: multiply `piCount_le` by `log x / x`
  have hup : piCount x * Real.log x / x
      ≤ (x ^ α + 1) * Real.log x / x + (1 / α) * (theta x / x) := by
    have hb := piCount_le hx1 hα0
    have hmul : piCount x * Real.log x / x
        ≤ (x ^ α + 1 + theta x / (α * Real.log x)) * Real.log x / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      exact mul_le_mul_of_nonneg_right hb hlog.le
    have hexp : (x ^ α + 1 + theta x / (α * Real.log x)) * Real.log x / x
        = (x ^ α + 1) * Real.log x / x + (1 / α) * (theta x / x) := by
      field_simp
    linarith [hmul, hexp.le, hexp.ge]
  constructor
  · linarith [hlow, hθgt, hdε]
  · have hinvd : (1 / α) * (theta x / x) < (1 + d) * (1 + d) := by
      rw [hinv]
      have hpos : (0 : ℝ) < 1 + d := by linarith
      exact mul_lt_mul_of_pos_left hθlt hpos
    nlinarith [hup, hrplt, hinvd, hdε, hdhalf, hd0]

end TDLean.PNT
