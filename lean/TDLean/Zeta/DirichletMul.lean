/-
  TDLean.Zeta.DirichletMul -- Brick C9 item 2, part 2: the Dirichlet-series product formula.

  `L(f,s) · L(g,s) = L(f ∗ g, s)` for absolutely convergent Dirichlet series.

  NO COQ ORACLE. mathlib's version is `LSeries_convolution` in
  `Mathlib.NumberTheory.LSeries.Convolution`, which is BANNED (the whole `LSeries` tree is
  the target side). Rebuilt here from:
    * `tsum_mul_tsum_of_summable_norm` (product of absolutely convergent sums),
    * `sigmaAntidiagonalEquivProd` from `Mathlib.NumberTheory.TsumDivisorsAntidiagonal`
      -- the reindex `(Σ n : ℕ+, divisorsAntidiagonal n) ≃ ℕ+ × ℕ+`, which is general
      combinatorics and not part of the banned tree,
    * `Complex.natCast_mul_natCast_cpow` (`(mn)^s = m^s n^s`).

  Indexing over `ℕ+` rather than `ℕ` sidesteps the `n = 0` term entirely.
-/
import TDLean.Zeta.LogDeriv
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

namespace TDLean.Zeta

open Complex Filter Topology

/-- The Dirichlet series of `f`, indexed over positive naturals. -/
noncomputable def LS (f : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n : ℕ+, f n / ((n : ℕ) : ℂ) ^ s

/-- Dirichlet convolution. -/
noncomputable def dconv (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2

/-- The term of a product, rewritten at the shared index. -/
theorem term_mul {f g : ℕ → ℂ} {s : ℂ} (a b : ℕ+) :
    (f a / ((a : ℕ) : ℂ) ^ s) * (g b / ((b : ℕ) : ℂ) ^ s)
      = f a * g b / (((a : ℕ) * (b : ℕ) : ℕ) : ℂ) ^ s := by
  have hc : (((a : ℕ) * (b : ℕ) : ℕ) : ℂ) = ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) := by
    push_cast; ring
  rw [div_mul_div_comm, hc, Complex.natCast_mul_natCast_cpow]

/-- **The Dirichlet-series product formula.** -/
theorem LS_mul {f g : ℕ → ℂ} {s : ℂ}
    (hf : Summable fun n : ℕ+ => ‖f n / ((n : ℕ) : ℂ) ^ s‖)
    (hg : Summable fun n : ℕ+ => ‖g n / ((n : ℕ) : ℂ) ^ s‖) :
    LS f s * LS g s = LS (dconv f g) s := by
  classical
  set F : ℕ+ → ℂ := fun n => f n / ((n : ℕ) : ℂ) ^ s with hF
  set G : ℕ+ → ℂ := fun n => g n / ((n : ℕ) : ℂ) ^ s with hG
  -- the product as a sum over pairs
  have hprod : LS f s * LS g s = ∑' z : ℕ+ × ℕ+, F z.1 * G z.2 :=
    tsum_mul_tsum_of_summable_norm hf hg
  -- summability of the pair family
  have hpair : Summable (fun z : ℕ+ × ℕ+ => F z.1 * G z.2) :=
    summable_mul_of_summable_norm hf hg
  -- reindex the pairs as a sigma over the antidiagonal
  have hre : ∑' z : ℕ+ × ℕ+, F z.1 * G z.2
      = ∑' x : (Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ)),
          F (sigmaAntidiagonalEquivProd x).1 * G (sigmaAntidiagonalEquivProd x).2 :=
    (sigmaAntidiagonalEquivProd.tsum_eq (fun z : ℕ+ × ℕ+ => F z.1 * G z.2)).symm
  have hsig : Summable (fun x : (Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ)) =>
      F (sigmaAntidiagonalEquivProd x).1 * G (sigmaAntidiagonalEquivProd x).2) :=
    (sigmaAntidiagonalEquivProd.summable_iff).mpr hpair
  rw [hprod, hre, hsig.tsum_sigma, LS]
  -- each fibre is the finite antidiagonal sum, all with the same denominator
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  have hterm : ∀ x : Nat.divisorsAntidiagonal (n : ℕ),
      F (sigmaAntidiagonalEquivProd ⟨n, x⟩).1 * G (sigmaAntidiagonalEquivProd ⟨n, x⟩).2
        = f x.1.1 * g x.1.2 / ((n : ℕ) : ℂ) ^ s := by
    intro x
    have hmul : (x : ℕ × ℕ).1 * (x : ℕ × ℕ).2 = (n : ℕ) :=
      (Nat.mem_divisorsAntidiagonal.mp x.2).1
    have := term_mul (f := f) (g := g) (s := s)
      (sigmaAntidiagonalEquivProd ⟨n, x⟩).1 (sigmaAntidiagonalEquivProd ⟨n, x⟩).2
    rw [hF, hG]
    simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, Equiv.coe_fn_mk] at this ⊢
    rw [this]
    simp only [PNat.mk_coe]
    rw [hmul]
  simp only [hterm]
  rw [dconv, ← Finset.sum_div]
  congr 1
  exact Finset.sum_coe_sort ((n : ℕ).divisorsAntidiagonal) (fun p => f p.1 * g p.2)

end TDLean.Zeta
