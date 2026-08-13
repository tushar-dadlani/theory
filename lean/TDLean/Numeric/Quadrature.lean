/-
  TDLean.Numeric.Quadrature -- rigorous quadrature with explicit error bounds.

  Infrastructure for the numerical route to existence of a nontrivial zero (`FE/CriticalFormula`
  reduced that to the sign of one real oscillatory integral). Nothing here is specific to zeta.

  Three pieces:

  * `norm_integral_sub_smul_le` — one panel: `‖∫ₐᵇ f − (b−a)·f(c)‖ ≤ M·(b−a)` when `f` stays
    within `M` of `f(c)` on the panel. This is just `norm_integral_le_of_norm_le_const` applied
    to `f − f(c)`, but it is the primitive everything else is built from.
  * `norm_integral_sub_midpointSum_le` — the composite midpoint rule on a uniform partition:
    error `≤ L·(b−a)²/n` for an `L`-Lipschitz integrand. `O(1/n)`, not the optimal `O(1/n²)`;
    the second-order bound needs a `C²` hypothesis and is not built.
  * `norm_integral_Ioi_tail_le` — the truncation error, from an exponential majorant.

  Together these turn `∫₁^∞ f` into a finite sum plus two explicit error terms. Supplying the
  Lipschitz constant `L` for the zeta integrand is a separate matter and is **not** done here.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace TDLean.Numeric

open MeasureTheory Set intervalIntegral

/-! ### One panel -/

/-- **The primitive.** If `f` stays within `M` of the sample value `f c` across the panel, the
    rectangle rule commits at most `M·(b−a)`. -/
theorem norm_integral_sub_smul_le {f : ℝ → ℂ} {a b c M : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable f volume a b)
    (hM : ∀ x ∈ Set.uIoc a b, ‖f x - f c‖ ≤ M) :
    ‖(∫ x in a..b, f x) - ((b - a : ℝ) : ℂ) * f c‖ ≤ M * (b - a) := by
  -- stated with `*` rather than `•`: the `SMul ℝ ℂ` instance produced by `integral_const`
  -- does not match the one `Finset.smul_sum` is stated with, which blocks the composite rule
  have hsub : (∫ x in a..b, (f x - f c))
      = (∫ x in a..b, f x) - ((b - a : ℝ) : ℂ) * f c := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    congr 1
  rw [← hsub]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (C := M) hM
  refine this.trans_eq ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]

/-- Lipschitz form of the one-panel bound. -/
theorem norm_integral_sub_smul_le_of_lipschitz {f : ℝ → ℂ} {a b c L : ℝ} (hab : a ≤ b)
    (hL : 0 ≤ L) (hc : c ∈ Icc a b)
    (hint : IntervalIntegrable f volume a b)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f x - f y‖ ≤ L * |x - y|) :
    ‖(∫ x in a..b, f x) - ((b - a : ℝ) : ℂ) * f c‖ ≤ L * (b - a) * (b - a) := by
  refine norm_integral_sub_smul_le hab hint fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  have hxI : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
  refine (hlip x hxI c hc).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hL
  rw [abs_sub_le_iff]
  constructor <;> [linarith [hx.2, hc.1]; linarith [hx.1, hc.2]]

/-! ### The composite midpoint rule -/

/-- The `k`-th sample point of the uniform `n`-panel midpoint rule on `[a,b]`. -/
noncomputable def midpt (a b : ℝ) (n : ℕ) (k : ℕ) : ℝ := a + ((k : ℝ) + 1 / 2) * ((b - a) / n)

/-- The midpoint Riemann sum. -/
noncomputable def midpointSum (f : ℝ → ℂ) (a b : ℝ) (n : ℕ) : ℂ :=
  (((b - a) / n : ℝ) : ℂ) * ∑ k ∈ Finset.range n, f (midpt a b n k)

/-- **The composite midpoint rule, with error bound.** For an `L`-Lipschitz integrand the
    uniform `n`-panel rule commits at most `L·(b−a)²/n`. -/
theorem norm_integral_sub_midpointSum_le {f : ℝ → ℂ} {a b L : ℝ} {n : ℕ}
    (hab : a ≤ b) (hn : 0 < n) (hL : 0 ≤ L)
    (hint : IntervalIntegrable f volume a b)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f x - f y‖ ≤ L * |x - y|) :
    ‖(∫ x in a..b, f x) - midpointSum f a b n‖ ≤ L * (b - a) ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ := (b - a) / n with hh
  have hh0 : 0 ≤ h := by
    rw [hh]
    exact div_nonneg (by linarith) hn0.le
  -- the partition
  set p : ℕ → ℝ := fun k => a + (k : ℝ) * h with hp
  have hp0 : p 0 = a := by simp [hp]
  have hne : (n : ℝ) ≠ 0 := hn0.ne'
  have hnh : (n : ℝ) * h = b - a := by
    rw [hh]; field_simp
  have hpn : p n = b := by
    simp only [hp]
    linarith [hnh]
  have hpmono : ∀ k : ℕ, p k ≤ p (k + 1) := by
    intro k
    simp only [hp]
    push_cast
    nlinarith
  have hpmem : ∀ k, k ≤ n → p k ∈ Icc a b := by
    intro k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    constructor
    · simp only [hp]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · have hkh : (k : ℝ) * h ≤ (n : ℝ) * h := mul_le_mul_of_nonneg_right hkn hh0
      simp only [hp]
      linarith [hnh]
  have hsubint : ∀ k, k < n → IntervalIntegrable f volume (p k) (p (k + 1)) := by
    intro k hk
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (hpmono k)]
    exact Icc_subset_Icc (hpmem k hk.le).1 (hpmem (k + 1) hk).2
  -- split the integral
  have hsplit : ∑ k ∈ Finset.range n, ∫ x in (p k)..(p (k + 1)), f x = ∫ x in a..b, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hsubint, hp0, hpn]
  -- the sample points are the panel midpoints
  have hmid : ∀ k, midpt a b n k = (p k + p (k + 1)) / 2 := by
    intro k
    simp only [midpt, hp, hh]
    push_cast
    ring
  have hwidth : ∀ k : ℕ, p (k + 1) - p k = h := by
    intro k
    simp only [hp]
    push_cast
    ring
  -- per-panel bound
  have hpanel : ∀ k ∈ Finset.range n,
      ‖(∫ x in (p k)..(p (k + 1)), f x) - ((h : ℝ) : ℂ) * f (midpt a b n k)‖
        ≤ L * h * h := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hcmem : midpt a b n k ∈ Icc (p k) (p (k + 1)) := by
      rw [hmid k]
      constructor <;> linarith [hpmono k]
    have hlip' : ∀ x ∈ Icc (p k) (p (k + 1)), ∀ y ∈ Icc (p k) (p (k + 1)),
        ‖f x - f y‖ ≤ L * |x - y| := by
      intro x hx y hy
      refine hlip x ⟨le_trans (hpmem k hk.le).1 hx.1, le_trans hx.2 (hpmem (k + 1) hk).2⟩
        y ⟨le_trans (hpmem k hk.le).1 hy.1, le_trans hy.2 (hpmem (k + 1) hk).2⟩
    have := norm_integral_sub_smul_le_of_lipschitz (hpmono k) hL hcmem (hsubint k hk) hlip'
    rwa [hwidth k] at this
  -- sum up
  rw [← hsplit, midpointSum, ← hh, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hpanel).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
  field_simp
  linarith

/-! ### The truncation error -/

/-- **Truncation.** If `‖f‖` is dominated by `K·e^{−u}` past `A`, the discarded tail is at most
    `K·e^{−A}`. -/
theorem norm_integral_Ioi_tail_le {f : ℝ → ℂ} {A K : ℝ}
    (hdom : ∀ᵐ u ∂(volume.restrict (Ioi A)), ‖f u‖ ≤ K * Real.exp (-u)) :
    ‖∫ u in Ioi A, f u‖ ≤ K * Real.exp (-A) := by
  have hgint : IntegrableOn (fun u : ℝ => K * Real.exp (-u)) (Ioi A) volume :=
    (integrableOn_exp_neg_Ioi A).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hgint hdom).trans_eq ?_
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]

end TDLean.Numeric
