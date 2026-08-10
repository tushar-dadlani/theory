/-
  TDLean.Zeta.VonMangoldt -- Brick C9 item 2, part 3: assembly.

  Targets, all on `Re s > 1`:
    * `zetaSeries s ≠ 0`, via `μ ∗ 1 = δ` -- note this needs NO Euler product, so it does
      not drag item 3's work forward;
    * `L(Λ, s) · ζ(s) = −ζ′(s)`, from `Λ ∗ 1 = log`;
    * hence `L(Λ, s) = −ζ′(s)/ζ(s)`.

  ORACLE (arithmetic half only): `Ell2Zeta.v:149 energy_eq_divisor_sum` (`log n = ∑_{d∣n} Λ(d)`).
  The analytic half is an overtake -- see `TDLean/Zeta/LogDeriv.lean`'s header for why
  `vonmangoldt_zeta_trace` does *not* cover it.

  Ban boundary: `ArithmeticFunction.{VonMangoldt, Moebius}` are FOUNDATIONS (elementary
  arithmetic, no analysis). `NumberTheory.LSeries.*` stays banned.
-/
import TDLean.Zeta.DirichletMul
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace TDLean.Zeta

open Complex Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ### Bridging `ℕ`-indexed and `ℕ⁺`-indexed series -/

/-- For `s ≠ 0` the `n = 0` term vanishes (`(0:ℂ)^s = 0`), so the two indexings agree. -/
theorem LS_eq_tsum_nat (f : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) :
    LS f s = ∑' n : ℕ, f n / (n : ℂ) ^ s := by
  refine Function.Injective.tsum_eq (f := fun n : ℕ => f n / (n : ℂ) ^ s)
    (PNat.coe_injective) ?_
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (by rw [Nat.cast_zero, Complex.zero_cpow hs]; simp) hn
  · exact ⟨⟨n, hpos⟩, rfl⟩

/-- The constant-one Dirichlet series is `ζ`. -/
theorem LS_one_eq_zetaSeries {s : ℂ} (hs : s ≠ 0) :
    LS (fun _ => (1 : ℂ)) s = zetaSeries s := by
  rw [LS_eq_tsum_nat _ hs, zetaSeries]

/-! ### `ζ ≠ 0` on `Re s > 1`, from `μ ∗ 1 = δ` -/

/-- The Möbius function, complex-valued. -/
noncomputable def muC (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)

/-- The arithmetic-function `ζ` (i.e. `1` for `n ≥ 1`, `0` at `0`), complex-valued. -/
noncomputable def zetaC (n : ℕ) : ℂ := (ArithmeticFunction.zeta n : ℂ)

theorem norm_muC_le (n : ℕ) : ‖muC n‖ ≤ 1 := by
  rw [muC, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `μ ∗ 1 = δ`, transported to `ℂ`-valued functions and `dconv`. -/
theorem dconv_muC_zetaC (n : ℕ) : dconv muC zetaC n = if n = 1 then 1 else 0 := by
  have h : (((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℤ) n : ℤ) : ℂ)
      = (((1 : ArithmeticFunction ℤ) n : ℤ) : ℂ) := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply] at h
  simp only [ArithmeticFunction.natCoe_apply] at h
  push_cast at h
  simp only [dconv, muC, zetaC]
  rw [h, ArithmeticFunction.one_apply]
  split <;> simp

/-- `L(δ, s) = 1`. -/
theorem LS_delta (s : ℂ) : LS (fun n => if n = 1 then (1 : ℂ) else 0) s = 1 := by
  rw [LS]
  rw [tsum_eq_single 1 (fun n hn => by
    have : (n : ℕ) ≠ 1 := fun h => hn (PNat.coe_injective (by simpa using h))
    simp [this])]
  norm_num

end TDLean.Zeta
