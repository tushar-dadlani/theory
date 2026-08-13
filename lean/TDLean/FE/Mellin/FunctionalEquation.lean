/-
  TDLean.FE.Mellin.FunctionalEquation -- cluster A12: the assembly.

      Λ(s) := 1/(s−1) − 1/s + ∫₁^∞ ψ(u)·(u^{s/2−1} + u^{(1−s)/2−1}) du

  Two theorems:

  * `completedZeta_symm`  —  `Λ(1−s) = Λ(s)` for **every** `s`, no hypothesis.
  * `completedZeta_eq`    —  `Λ(s) = π^{−s/2}·Γ(s/2)·ζ(s)` for `Re s > 1`.

  Together these are the functional equation of the completed zeta. The symmetry is
  *manifest* in `Λ`'s definition — the pole pair swaps and the two powers exchange — and all
  the mathematical work sits in the second theorem, which says this manifestly symmetric
  object is the completed zeta.

  That is exactly the shape Riemann's own argument takes, and it is also how the Coq side
  organises it: `RiemannThetaFE.v` *defines* `J s := T s + T (1−s) − 1/s + 1/(s−1)` and gets
  `J_symmetric` by `ring`, with the content in `xi_eq_J`/`Hu_spec`. The difference is that
  Coq's `J` is a function of a **real** `s` built on Riemann integrals; this is complex `s`
  with Bochner integrals, and Coq never performs the `(0,1) → (1,∞)` change of variable
  (its head kernel `hker` is *defined* already folded on `[1,∞)`).
-/
import TDLean.FE.Mellin.Integrable

namespace TDLean.FE

open Complex Real MeasureTheory Set TDLean.Zeta

/-- **The completed zeta**, defined by the manifestly symmetric integral formula. -/
noncomputable def completedZeta (s : ℂ) : ℂ :=
  1 / (s - 1) - 1 / s
    + ∫ u in Ioi (1 : ℝ), ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * psiTheta u

/-- **`Λ(1−s) = Λ(s)`, unconditionally.** The pole pair `1/(s−1) − 1/s` maps to
    `1/(−s) − 1/(1−s)`, which is the same pair with the roles swapped; and the two powers in
    the integrand simply exchange. No hypothesis on `s`: at `s = 0` and `s = 1` both sides
    use Lean's `x/0 = 0` convention and still agree. -/
theorem completedZeta_symm (s : ℂ) : completedZeta (1 - s) = completedZeta s := by
  rw [completedZeta, completedZeta]
  congr 1
  · have e1 : (1 : ℂ) - s - 1 = -s := by ring
    have e2 : (1 : ℂ) - s = -(s - 1) := by ring
    rw [e1, e2, div_neg, div_neg]
    ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show (1 : ℂ) - (1 - s) = s by ring]
    ring

/-! ### That `Λ` is the completed zeta -/

/-- The split of `(0,∞)` at `t = 1`, with the `(0,1)` half folded and expanded. -/
theorem mellin_eq_completedZeta {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s / 2 - 1) * psiTheta t) = completedZeta s := by
  have hsplit : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hIoc : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * psiTheta t) (Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * psiTheta t)
      (b := (1:ℝ)) (by finiteness)).mpr (integrableOn_mellin_Ioo hs)
  have hIoi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * psiTheta t) (Ioi (1 : ℝ)) :=
    integrableOn_cpow_mul_psiTheta (s / 2 - 1)
  -- split at `t = 1`
  rw [← hsplit, MeasureTheory.setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi hIoc hIoi,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- fold the `(0,1)` half
  rw [integral_Ioo_eq_integral_Ioi_inv s]
  -- expand it by the theta transformation
  have hexp : (∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-s / 2 - 1) * psiTheta (1 / u))
      = (∫ u in Ioi (1 : ℝ), ((((Real.sqrt u : ℝ)) : ℂ) - 1) / 2 * (u : ℂ) ^ (-s / 2 - 1))
        + ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ ((1 - s) / 2 - 1) * psiTheta u := by
    rw [← MeasureTheory.integral_add (integrableOn_pole hs)
      (integrableOn_cpow_mul_psiTheta ((1 - s) / 2 - 1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact folded_integrand_eq (s := s) (mem_Ioi.mp hu).le
  -- recombine the two surviving integrals: the `Λ` integrand is their sum
  have hcomb : (∫ u in Ioi (1 : ℝ),
      ((u : ℂ) ^ (s / 2 - 1) + (u : ℂ) ^ ((1 - s) / 2 - 1)) * psiTheta u)
      = (∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (s / 2 - 1) * psiTheta u)
        + ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ ((1 - s) / 2 - 1) * psiTheta u := by
    rw [← MeasureTheory.integral_add (integrableOn_cpow_mul_psiTheta (s / 2 - 1))
      (integrableOn_cpow_mul_psiTheta ((1 - s) / 2 - 1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [hexp, integral_pole_terms hs, completedZeta, hcomb]
  ring

/-- **`Λ(s) = π^{−s/2}·Γ(s/2)·ζ(s)` for `Re s > 1`.** -/
theorem completedZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedZeta s = ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * zetaSeries s :=
  (mellin_eq_completedZeta hs).symm.trans (mellin_psiTheta hs)

end TDLean.FE
