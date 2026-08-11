/-
  TDLean.PNT.NewmanInput -- C10, part 5: the function `f` Newman is applied to.

  `f t = ψ(eᵗ)e^{−t} − 1`. This is exactly the step function that made Phase 0 necessary:
  it is bounded and interval-integrable but **not continuous**, so the original
  `newman_tauberian` (which required `Continuous f`) could not have consumed it.
-/
import TDLean.PNT.Substitution

namespace TDLean.PNT

open MeasureTheory TDLean.Zeta

/-- Newman's integrand: `ψ(eᵗ)e^{−t} − 1`. -/
noncomputable def fNewman (t : ℝ) : ℝ := psi (Real.exp t) * Real.exp (-t) - 1

/-- Its complex form, as `newman_tauberian` expects. -/
noncomputable def fNewmanC (t : ℝ) : ℂ := ((fNewman t : ℝ) : ℂ)

/-! ### Boundedness -/

theorem fNewman_lower (t : ℝ) : -1 ≤ fNewman t := by
  have h : 0 ≤ psi (Real.exp t) * Real.exp (-t) :=
    mul_nonneg (psi_nonneg _) (Real.exp_pos _).le
  rw [fNewman]; linarith

theorem fNewman_upper {t : ℝ} (ht : 0 ≤ t) : fNewman t ≤ Ccheb - 1 := by
  have hexp : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  have hpsi : psi (Real.exp t) ≤ Ccheb * Real.exp t := psi_le_Ccheb hexp
  have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hmul : psi (Real.exp t) * Real.exp (-t) ≤ Ccheb * Real.exp t * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right hpsi hpos.le
  have hcancel : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Ccheb * Real.exp t * Real.exp (-t) = Ccheb := by
    rw [mul_assoc, hcancel, mul_one]
  rw [fNewman]
  linarith [hmul, h3]

/-- **The bound Newman needs.** -/
theorem norm_fNewmanC_le {t : ℝ} (ht : 0 ≤ t) : ‖fNewmanC t‖ ≤ Ccheb + 1 := by
  have hC : 0 ≤ Ccheb := Ccheb_nonneg
  rw [fNewmanC, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor
  · linarith [fNewman_lower t]
  · linarith [fNewman_upper ht]

/-! ### Interval integrability -- `f` is a step function times a continuous one -/

theorem monotone_psi_exp : Monotone (fun t : ℝ => psi (Real.exp t)) :=
  psi_mono.comp Real.exp_monotone

theorem intervalIntegrable_fNewman (T : ℝ) :
    IntervalIntegrable fNewman volume 0 T := by
  have h1 : IntervalIntegrable (fun t : ℝ => psi (Real.exp t)) volume 0 T :=
    (monotone_psi_exp.monotoneOn _).intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ => psi (Real.exp t) * Real.exp (-t)) volume 0 T :=
    h1.mul_continuousOn (by fun_prop)
  exact h2.sub intervalIntegrable_const

/-- **The regularity hypothesis of the weakened `newman_tauberian`.** -/
theorem intervalIntegrable_fNewmanC (T : ℝ) :
    IntervalIntegrable fNewmanC volume 0 T := by
  have h := intervalIntegrable_fNewman T
  rw [intervalIntegrable_iff] at h ⊢
  exact h.ofReal

/-- `ψ(eᵗ) = (f t + 1)·eᵗ`, the identity that converts the Mellin integral into a Laplace
    transform of `f`. -/
theorem psi_exp_eq {t : ℝ} : ((psi (Real.exp t) : ℝ) : ℂ)
    = (fNewmanC t + 1) * Complex.exp (t : ℂ) := by
  have hcancel : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hreal : (psi (Real.exp t) * Real.exp (-t) - 1 + 1) * Real.exp t = psi (Real.exp t) := by
    have hassoc : psi (Real.exp t) * Real.exp (-t) * Real.exp t
        = psi (Real.exp t) * (Real.exp (-t) * Real.exp t) := by ring
    rw [show (psi (Real.exp t) * Real.exp (-t) - 1 + 1)
        = psi (Real.exp t) * Real.exp (-t) by ring, hassoc, hcancel, mul_one]
  rw [fNewmanC, fNewman, ← Complex.ofReal_exp,
    show ((1 : ℂ)) = ((1 : ℝ) : ℂ) from by norm_num,
    ← Complex.ofReal_add, ← Complex.ofReal_mul, hreal]

end TDLean.PNT
