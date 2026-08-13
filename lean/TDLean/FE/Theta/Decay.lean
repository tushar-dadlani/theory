/-
  TDLean.FE.Theta.Decay -- cluster A10: exponential decay of `ψ` on `[1,∞)`.

      ‖ψ(a)‖ ≤ C · e^{−πa}      for `a ≥ 1`,  `C = (1 − e^{−π})⁻¹`

  This is what makes `∫₁^∞ ψ(t)·t^{σ−1} dt` converge for **every** real `σ`, positive or
  negative — and that is exactly what the functional equation needs, because after the fold
  the surviving integral carries the exponent `(1−s)/2 − 1`, whose real part is *negative*
  precisely when `Re s > 1`. None of the `Re s > 1` machinery in `Mellin/Term.lean` reaches it.

  The estimate itself is elementary: `(n+1)² ≥ n+1`, so the theta series is dominated
  termwise by the geometric series `∑ (e^{−πa})^{n+1}`.

  NO COQ ORACLE for the bound as stated; Coq's `MellinTail.v` obtains convergence of `T`
  from `Psi_bound` in the same spirit but never isolates a decay constant.
-/
import TDLean.FE.Theta.Transform
import TDLean.FE.Mellin.Completed

namespace TDLean.FE

open Complex Real MeasureTheory Set Filter Topology

/-- Each theta term has norm `e^{−πa(n+1)²}`. -/
theorem norm_psiNat_term (a : ℝ) (n : ℕ) :
    ‖Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2)‖
      = Real.exp (-(π * a * ((n : ℝ) + 1) ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  have : (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2)
      = (((-(π * a * ((n : ℝ) + 1) ^ 2) : ℝ)) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- The decay constant `C = (1 − e^{−π})⁻¹`. -/
noncomputable def psiBound : ℝ := (1 - Real.exp (-π))⁻¹

theorem exp_neg_pi_lt_one : Real.exp (-π) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])

theorem psiBound_pos : 0 < psiBound := by
  rw [psiBound]
  exact inv_pos.mpr (by linarith [exp_neg_pi_lt_one])

/-- **Exponential decay of `ψ` on `[1,∞)`.** -/
theorem norm_psiNat_le {a : ℝ} (ha : 1 ≤ a) :
    ‖psiNat a‖ ≤ psiBound * Real.exp (-(π * a)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have ha0 : (0 : ℝ) < a := by linarith
  set r : ℝ := Real.exp (-(π * a)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  -- `r ≤ e^{−π}`, because `a ≥ 1`
  have hrle : r ≤ Real.exp (-π) := Real.exp_le_exp.mpr (by nlinarith)
  -- the geometric majorant, summing to `r/(1−r)`
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r * (1 - r)⁻¹) := by
    have h := (hasSum_geometric_of_lt_one hr0.le hr1).mul_left r
    simpa [pow_succ, mul_comm] using h
  -- termwise domination: `(n+1)² ≥ n+1`
  have hterm : ∀ n : ℕ,
      ‖Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2)‖ ≤ r ^ (n + 1) := by
    intro n
    rw [norm_psiNat_term, hrdef, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have hpa : (0 : ℝ) < π * a := by positivity
    rw [show ((((n + 1 : ℕ)) : ℝ)) * -(π * a) = -(π * a * ((n : ℝ) + 1)) by
      push_cast; ring]
    nlinarith [mul_le_mul_of_nonneg_left hsq hpa.le]
  have hle : ‖psiNat a‖ ≤ r * (1 - r)⁻¹ := by
    rw [psiNat]
    exact tsum_of_norm_bounded hgeom hterm
  refine hle.trans ?_
  rw [mul_comm psiBound r]
  refine mul_le_mul_of_nonneg_left ?_ hr0.le
  rw [psiBound]
  have h1 : 0 < 1 - Real.exp (-π) := by linarith [exp_neg_pi_lt_one]
  have h2 : 1 - Real.exp (-π) ≤ 1 - r := by linarith [hrle]
  gcongr

/-- The same bound for `psiTheta`, which is the object the Mellin side uses. -/
theorem norm_psiTheta_le {a : ℝ} (ha : 1 ≤ a) :
    ‖psiTheta a‖ ≤ psiBound * Real.exp (-(π * a)) := by
  rw [psiTheta_eq_psiNat]
  exact norm_psiNat_le ha

/-! ### Measurability

    `ψ` is a pointwise limit of the (continuous) partial sums wherever the series converges,
    which is all of `(0,∞)`. That is enough for every integrability argument below; proving
    `ψ` *continuous* would need locally uniform convergence and is not required. -/

theorem aestronglyMeasurable_psiNat :
    AEStronglyMeasurable psiNat (volume.restrict (Ioi (0 : ℝ))) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N : ℕ => fun a : ℝ => ∑ n ∈ Finset.range N,
      Complex.exp (-(π : ℂ) * (a : ℂ) * ((n : ℂ) + 1) ^ 2))
    (fun N => Continuous.aestronglyMeasurable ?_) ?_
  · refine continuous_finset_sum _ fun n _ => Complex.continuous_exp.comp ?_
    exact (continuous_const.mul Complex.continuous_ofReal).mul continuous_const
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact ((summable_psiNat (mem_Ioi.mp ha)).hasSum).tendsto_sum_nat

theorem aestronglyMeasurable_psiTheta :
    AEStronglyMeasurable psiTheta (volume.restrict (Ioi (0 : ℝ))) := by
  refine aestronglyMeasurable_psiNat.congr ?_
  filter_upwards with a
  exact (psiTheta_eq_psiNat a).symm

end TDLean.FE
