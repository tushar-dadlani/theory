/-
  TDLean.PNT.Transfer -- C10, part 11: `ψ ~ x  ⟹  θ ~ x`.

  The prime-power correction `ψ − θ` is `O(√x·log²x)`, which is `o(x)` — so the two Chebyshev
  functions have the same asymptotics. The `O(x)` bound proved for Chebyshev's theorem is too
  weak here (it throws the `√x` away), which is why `psiErr_mul_log2_le'` was kept separate.

  The sharpening that makes it work is `log x ≤ x^ε/ε` at `ε = 1/8` (`Zeta.log_le_rpow_div`),
  giving `ψ_err(x) = O(x^{3/4})`. At the cruder `ε = 1/4` used for Chebyshev the bound is only
  `O(x)` and the limit fails.
-/
import TDLean.PNT.Squeeze
import TDLean.Zeta.VonMangoldt

namespace TDLean.PNT

open Filter Topology TDLean.Zeta

/-- `ψ_err(x) = O(x^{3/4})` — enough to be `o(x)`. -/
theorem psiErr_le_rpow {x : ℝ} (hx : 1 ≤ x) :
    psiErr x * Real.log 2 ≤ 144 * x ^ (3 / 4 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h8 : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    have := log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 8)
    calc Real.log x ≤ x ^ (1 / 8 : ℝ) / (1 / 8 : ℝ) := this
      _ = 8 * x ^ (1 / 8 : ℝ) := by ring
  have he1 : (1 : ℝ) ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  -- `(√x+1)(L+1)L ≤ 2·x^{1/2} · 9·x^{1/8} · 8·x^{1/8} = 144·x^{3/4}`
  have hstep : (Real.sqrt x + 1) * (Real.log x + 1) * Real.log x
      ≤ (2 * x ^ (1 / 2 : ℝ)) * (9 * x ^ (1 / 8 : ℝ)) * (8 * x ^ (1 / 8 : ℝ)) := by
    have hb1 : Real.sqrt x + 1 ≤ 2 * x ^ (1 / 2 : ℝ) := by rw [← hsq]; linarith
    have hb2 : Real.log x + 1 ≤ 9 * x ^ (1 / 8 : ℝ) := by linarith
    have hb3 : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := h8
    have hp1 : (0 : ℝ) ≤ Real.log x + 1 := by linarith
    have hp2 : (0 : ℝ) ≤ 2 * x ^ (1 / 2 : ℝ) := by positivity
    exact mul_le_mul (mul_le_mul hb1 hb2 hp1 hp2) hb3 hL0 (by positivity)
  have hcollapse : (2 * x ^ (1 / 2 : ℝ)) * (9 * x ^ (1 / 8 : ℝ)) * (8 * x ^ (1 / 8 : ℝ))
      = 144 * x ^ (3 / 4 : ℝ) := by
    rw [show (144 : ℝ) * x ^ (3 / 4 : ℝ)
        = 144 * (x ^ (1 / 2 : ℝ) * (x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ))) by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num]
    ring
  rw [← hcollapse]
  exact le_trans (psiErr_mul_log2_le' hx) hstep

/-- **`ψ_err(x)/x → 0`.** -/
theorem psiErr_div_tendsto_zero : Tendsto (fun x : ℝ => psiErr x / x) atTop (nhds 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun x : ℝ => (144 / Real.log 2) * x ^ (-(1 / 4) : ℝ)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (144 / Real.log 2)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have : 0 ≤ psiErr x := by
      rw [psiErr_eq_sum_ppSet]
      exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hb := psiErr_le_rpow hx
    rw [div_le_iff₀ hx0]
    have hrpow : x ^ (3 / 4 : ℝ) = x ^ (-(1 / 4) : ℝ) * x := by
      rw [show ((3 : ℝ) / 4) = (-(1 / 4) : ℝ) + 1 by norm_num, Real.rpow_add hx0,
        Real.rpow_one]
    calc psiErr x ≤ 144 * x ^ (3 / 4 : ℝ) / Real.log 2 := by
          rw [le_div_iff₀ hlog2]; linarith
      _ = 144 / Real.log 2 * x ^ (3 / 4 : ℝ) := by ring
      _ = 144 / Real.log 2 * (x ^ (-(1 / 4) : ℝ) * x) := by rw [← hrpow]
      _ = 144 / Real.log 2 * x ^ (-(1 / 4) : ℝ) * x := by ring

/-- **`θ(x)/x → 1`** — the Chebyshev theta form of PNT. -/
theorem tendsto_theta : Tendsto (fun x : ℝ => theta x / x) atTop (nhds 1) := by
  have h := tendsto_psi.sub psiErr_div_tendsto_zero
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [psi_eq_theta_add, add_div]
  ring

end TDLean.PNT
