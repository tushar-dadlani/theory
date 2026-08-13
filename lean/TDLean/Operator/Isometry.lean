/-
  TDLean.Operator.Isometry -- the prime-shift isometries `Sₙ`, and where commutativity breaks.

  `Sₙ δₘ = δₙₘ`. These are the operators the Bost–Connes crossed product is built from, and
  the point of this file is the asymmetry

      Sₙ* Sₙ = 1      but      Sₙ Sₙ* ≠ 1

  so each `Sₙ` is an **isometry, not a unitary**: `Sₙ Sₙ*` is the projection onto multiples of
  `n`. This is exactly why BC is a crossed product by a *semigroup of isometries* rather than
  by a group — and it is why `MonoidAlgebraZero.v:30 adj_no_inverse` is not an obstruction to
  the construction but the very feature it is built on.

  The covariance relation `N Sₙ = Sₙ (N + log n)` is the dynamics: `Sₙ` raises energy by
  `log n`, which is the generator of the BC time evolution `σ_t(Sₙ) = n^{it} Sₙ`.

  ## Honest scope

  This is the isometry semigroup and its covariance, not the crossed-product C*-algebra: no
  C*-completion, no KMS states, no phase transition in the KMS sense. Those remain unbuilt.
-/
import TDLean.Operator.Number

namespace TDLean.Operator

open TDLean.Zeta Complex

/-- `k / n` as a positive natural, given `n ∣ k`. -/
def pdiv (k n : ℕ+) (h : (n : ℕ) ∣ (k : ℕ)) : ℕ+ :=
  ⟨(k : ℕ) / (n : ℕ), Nat.div_pos (Nat.le_of_dvd k.pos h) n.pos⟩

theorem mul_pdiv (k n : ℕ+) (h : (n : ℕ) ∣ (k : ℕ)) : n * pdiv k n h = k := by
  apply PNat.coe_injective
  rw [PNat.mul_coe]
  exact Nat.mul_div_cancel' h

/-- `Sₙ`, the shift `δₘ ↦ δₙₘ`, written on coefficient sequences. -/
noncomputable def shift (n : ℕ+) (f : ℕ+ → ℂ) : ℕ+ → ℂ :=
  fun k => if h : (n : ℕ) ∣ (k : ℕ) then f (pdiv k n h) else 0

/-- `Sₙ*`, the adjoint: `δₖ ↦ δ_{k/n}` if `n ∣ k`, else `0`. On sequences it is just
    precomposition with multiplication by `n`, needing no division. -/
noncomputable def coshift (n : ℕ+) (f : ℕ+ → ℂ) : ℕ+ → ℂ := fun m => f (n * m)

theorem shift_apply_mul (n : ℕ+) (f : ℕ+ → ℂ) (m : ℕ+) : shift n f (n * m) = f m := by
  have hdvd : (n : ℕ) ∣ ((n * m : ℕ+) : ℕ) := by
    rw [PNat.mul_coe]; exact Dvd.intro _ rfl
  rw [shift, dif_pos hdvd]
  congr 1
  apply PNat.coe_injective
  simp [pdiv, PNat.mul_coe, Nat.mul_div_cancel_left _ n.pos]

theorem shift_apply_of_not_dvd {n k : ℕ+} (f : ℕ+ → ℂ) (h : ¬ (n : ℕ) ∣ (k : ℕ)) :
    shift n f k = 0 := by rw [shift, dif_neg h]

/-! ### `Sₙ` is an isometry -/

/-- **`Sₙ* Sₙ = 1`.** -/
theorem coshift_shift (n : ℕ+) (f : ℕ+ → ℂ) : coshift n (shift n f) = f := by
  funext m
  rw [coshift, shift_apply_mul]

/-- `Sₙ` preserves the ℓ² norm termwise, hence preserves `ℓ²`. -/
theorem ell2_shift {n : ℕ+} {f : ℕ+ → ℂ} (hf : Ell2 f) : Ell2 (shift n f) := by
  have hinj : Function.Injective (fun m : ℕ+ => n * m) := fun a b hab => by
    simpa using mul_left_cancel hab
  have hzero : ∀ k ∉ Set.range (fun m : ℕ+ => n * m), ‖shift n f k‖ ^ 2 = 0 := by
    intro k hk
    have hnd : ¬ (n : ℕ) ∣ (k : ℕ) := by
      intro hdvd
      exact hk ⟨pdiv k n hdvd, mul_pdiv k n hdvd⟩
    rw [shift_apply_of_not_dvd f hnd]
    simp
  rw [Ell2, ← hinj.summable_iff hzero]
  exact hf.congr fun m => by rw [Function.comp_apply, shift_apply_mul]

/-! ### The adjoint identity -/

/-- **`⟪Sₙ f, g⟫ = ⟪f, Sₙ* g⟫`.** -/
theorem ip_shift_adjoint (n : ℕ+) (f g : ℕ+ → ℂ) :
    ip (shift n f) g = ip f (coshift n g) := by
  have hinj : Function.Injective (fun m : ℕ+ => n * m) := fun a b hab => by
    simpa using mul_left_cancel hab
  have hzero : ∀ k ∉ Set.range (fun m : ℕ+ => n * m),
      (starRingEnd ℂ) (shift n f k) * g k = 0 := by
    intro k hk
    have hnd : ¬ (n : ℕ) ∣ (k : ℕ) := by
      intro hdvd
      exact hk ⟨pdiv k n hdvd, mul_pdiv k n hdvd⟩
    rw [shift_apply_of_not_dvd f hnd]
    simp
  have hmain := hinj.tsum_eq (Function.support_subset_iff'.mpr hzero)
  rw [ip, ip, ← hmain]
  exact tsum_congr fun m => by rw [shift_apply_mul, coshift]

/-! ### …but NOT a unitary -/

/-- `Sₙ Sₙ*` is the projection onto multiples of `n`. -/
theorem shift_coshift_apply (n : ℕ+) (f : ℕ+ → ℂ) (k : ℕ+) :
    shift n (coshift n f) k = if (n : ℕ) ∣ (k : ℕ) then f k else 0 := by
  by_cases h : (n : ℕ) ∣ (k : ℕ)
  · rw [if_pos h]
    obtain ⟨m, rfl⟩ : ∃ m : ℕ+, k = n * m := ⟨pdiv k n h, (mul_pdiv k n h).symm⟩
    rw [shift_apply_mul, coshift]
  · rw [if_neg h, shift_apply_of_not_dvd _ h]

/-- **`Sₙ Sₙ* ≠ 1`.** Witnessed at `n = 2` on `δ₁`: `1` is not a multiple of `2`, so the
    projection kills it. This single failure is the whole reason Bost–Connes is a crossed
    product by a semigroup of isometries and not by a group. -/
theorem shift_coshift_ne_id :
    shift 2 (coshift 2 (delta 1)) ≠ delta 1 := by
  intro h
  have h1 := congrFun h 1
  rw [shift_coshift_apply] at h1
  norm_num [delta] at h1

/-! ### The semigroup law -/

/-- `Sₘ* Sₙ* = S_{nm}*`, hence `Sₙ Sₘ = S_{nm}` on the isometry side. -/
theorem coshift_coshift (m n : ℕ+) (f : ℕ+ → ℂ) :
    coshift m (coshift n f) = coshift (n * m) f := by
  funext k
  simp only [coshift]
  congr 1
  rw [mul_assoc]

/-! ### Covariance: the dynamics -/

/-- **`N Sₙ = Sₙ (N + log n)`.** `Sₙ` raises the energy by `log n`. This is the crossed-product
    relation, and the generator of the Bost–Connes time evolution `σ_t(Sₙ) = n^{it} Sₙ`. -/
theorem numberOp_covariance (n : ℕ+) (f : ℕ+ → ℂ) :
    diag numberOp (shift n f) = shift n (fun m => (numberOp n + numberOp m) * f m) := by
  funext k
  by_cases h : (n : ℕ) ∣ (k : ℕ)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ+, k = n * m := ⟨pdiv k n h, (mul_pdiv k n h).symm⟩
    rw [diag, shift_apply_mul, shift_apply_mul, numberOp_mul]
  · rw [diag, shift_apply_of_not_dvd f h, shift_apply_of_not_dvd _ h, mul_zero]

/-- The commutator form: `Sₙ` is an eigenvector of the adjoint action of `N`, with
    eigenvalue `log n`. -/
theorem numberOp_commutator (n : ℕ+) (f : ℕ+ → ℂ) :
    diag numberOp (shift n f) - shift n (diag numberOp f)
      = numberOp n • shift n f := by
  funext k
  rw [numberOp_covariance]
  by_cases h : (n : ℕ) ∣ (k : ℕ)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ+, k = n * m := ⟨pdiv k n h, (mul_pdiv k n h).symm⟩
    simp only [Pi.sub_apply, Pi.smul_apply, shift_apply_mul, diag, smul_eq_mul]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, shift_apply_of_not_dvd _ h, smul_eq_mul]
    ring

end TDLean.Operator
