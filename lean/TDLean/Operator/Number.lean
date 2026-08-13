/-
  TDLean.Operator.Number -- the number operator `N` and the partition function `Tr(e^{−βN})`.

  Milestone 2 of `docs/ncg_monoid_algebra_thesis.md`: *"Define the number operator `N`
  (prime-power grading) and identify `Tr(e^{−βN})` with `ζ(β)` for `Re β > 1`."*

  `N δₙ = (log n) δₙ`, so `e^{−βN} δₙ = n^{−β}` and the trace is `∑ n^{−β} = ζ(β)`.

  Two facts make `N` a genuine *number* operator rather than an arbitrary diagonal:
  it is **additive** (`N(mn) = N(m) + N(n)`), so the state `δₙ` carries the energy of a
  multiset of prime quanta; and its eigenvalue decomposes over prime powers as
  `log n = ∑_{d ∣ n} Λ(d)`.

  ## Honest scope

  This is the **primon gas** — the commutative bosonic Fock picture, one mode per prime. It is
  *not* Bost–Connes, whose content is entirely the crossed product `ℂ[ℚ/ℤ] ⋊ ℕˣ` and its KMS
  states. LEDGER 3.2 already records that conflation. The divergence at `β = 1` proved below
  is the classical free-energy blow-up, the right *shadow* of the BC phase transition but not
  a KMS statement.
-/
import TDLean.Operator.Ell2C
import TDLean.Zeta.Telescope

namespace TDLean.Operator

open TDLean.Zeta Complex Filter Topology

/-- The **number operator**, diagonal with eigenvalue `log n` on `δₙ`. -/
noncomputable def numberOp : ℕ+ → ℂ := fun n => ((Real.log (n : ℕ) : ℝ) : ℂ)

/-! ### Why it is a *number* operator -/

/-- **Additivity.** `N(mn) = N(m) + N(n)` — the energy of a composite state is the sum of its
    parts, which is what makes `ℓ²(ℕ⁺)` a Fock space with one mode per prime. -/
theorem numberOp_mul (m n : ℕ+) : numberOp (m * n) = numberOp m + numberOp n := by
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.pos.ne'
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast n.pos.ne'
  simp only [numberOp, PNat.mul_coe]
  rw [← Complex.ofReal_add]
  congr 1
  push_cast
  exact Real.log_mul hm hn

/-- The ladder on a single prime mode: `N(pᵏ) = k·N(p)`. -/
theorem numberOp_pow (p : ℕ+) (k : ℕ) : numberOp (p ^ k) = (k : ℂ) * numberOp p := by
  simp only [numberOp, PNat.pow_coe]
  rw [show (((((p : ℕ)) ^ k : ℕ)) : ℝ) = (((p : ℕ) : ℝ)) ^ k by push_cast; ring,
    Real.log_pow]
  push_cast
  ring

/-- **The energy decomposes into prime-power quanta**: `log n = ∑_{d ∣ n} Λ(d)`.
    ORACLE: `Ell2Zeta.v:149 energy_eq_divisor_sum`. -/
theorem numberOp_eq_sum_vonMangoldt (n : ℕ+) :
    numberOp n = ∑ d ∈ (n : ℕ).divisors, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) := by
  rw [numberOp, ← Complex.ofReal_sum]
  congr 1
  exact (ArithmeticFunction.vonMangoldt_sum).symm

/-- `N` is Hermitian: its eigenvalues `log n` are real. -/
theorem isHermitian_numberOp : IsHermitian numberOp :=
  fun n => Complex.conj_ofReal (Real.log ((n : ℕ) : ℝ))

/-! ### The Gibbs operator `e^{−βN}` -/

/-- `e^{−βN}`, diagonal with entries `exp(−β·log n)`. -/
noncomputable def gibbs (β : ℂ) : ℕ+ → ℂ := fun n => Complex.exp (-β * numberOp n)

/-- `e^{−β log n} = n^{−β}`: the Gibbs operator *is* the zeta kernel. -/
theorem gibbs_eq_zetaKernel (β : ℂ) : gibbs β = zetaKernel β := by
  funext n
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hne : (((n : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have hcast : (((n : ℕ)) : ℂ) = ((((n : ℕ) : ℝ)) : ℂ) := by push_cast; ring
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log (n : ℕ) : ℝ) : ℂ) := by
    rw [hcast, Complex.log, Complex.arg_ofReal_of_nonneg hn.le]
    simp
  rw [gibbs, zetaKernel, Complex.cpow_def_of_ne_zero hne, hlog, numberOp]
  congr 1
  ring

/-! ### The partition function -/

/-- `Tr(e^{−βN})`, as the sum of diagonal matrix elements. -/
noncomputable def partitionFunction (β : ℂ) : ℂ :=
  ∑' n : ℕ+, ip (delta n) (diag (gibbs β) (delta n))

/-- **`Tr(e^{−βN}) = ζ(β)` for `Re β > 1`** — milestone 2 of the NCG thesis doc,
    machine-checked. -/
theorem partitionFunction_eq_zeta {β : ℂ} (hβ : 1 < β.re) :
    partitionFunction β = zetaSeries β := by
  rw [partitionFunction, gibbs_eq_zetaKernel]
  exact trace_zetaKernel hβ

/-- Each energy level contributes `e^{−βE}` with `E = log n`. -/
theorem partitionFunction_term (β : ℂ) (n : ℕ+) :
    ip (delta n) (diag (gibbs β) (delta n)) = Complex.exp (-β * numberOp n) :=
  ip_delta_diag _ n

/-! ### Divergence at `β = 1` -/

/-- **The partition function blows up as `β → 1⁺`.** The classical free-energy divergence at
    the critical temperature — the right shadow of the Bost–Connes phase transition, though
    not itself a KMS statement. It comes straight from the pole of `ζ`, which
    `zetaCont = 1/(s−1) + zetaDiffSum` isolates by construction. -/
theorem partitionFunction_diverges :
    Tendsto (fun σ : ℝ => ‖partitionFunction (σ : ℂ)‖) (𝓝[>] (1 : ℝ)) atTop := by
  -- `zetaDiffSum` is continuous at `1`, hence bounded near it
  have hcont : ContinuousAt zetaDiffSum 1 :=
    (differentiableAt_zetaDiffSum (by norm_num)).continuousAt
  have hbdd : ∀ᶠ s in 𝓝 (1 : ℂ), ‖zetaDiffSum s‖ < ‖zetaDiffSum 1‖ + 1 :=
    (hcont.norm).tendsto.eventually_lt_const (by linarith)
  -- pull back along `σ ↦ (σ : ℂ)`
  have hmap : Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun σ : ℝ => ((σ : ℝ) : ℂ)) := Complex.continuous_ofReal
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun σ : ℝ => σ - 1) := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have : (1 : ℝ) < σ := hσ
      simp only [Set.mem_Ioi]
      linarith
  have hpole : Tendsto (fun σ : ℝ => 1 / (σ - 1) - (‖zetaDiffSum 1‖ + 1))
      (𝓝[>] (1 : ℝ)) atTop := by
    have hinv : Tendsto (fun σ : ℝ => (σ - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hshift
    have hone : Tendsto (fun σ : ℝ => 1 / (σ - 1)) (𝓝[>] (1 : ℝ)) atTop := by
      simpa [one_div] using hinv
    have h2 := Filter.tendsto_atTop_add_const_right _ (-(‖zetaDiffSum 1‖ + 1)) hone
    simpa [sub_eq_add_neg] using h2
  refine tendsto_atTop_mono' _ ?_ hpole
  filter_upwards [self_mem_nhdsWithin, hmap.eventually hbdd] with σ hσ hb
  have hσ' : (1 : ℝ) < σ := hσ
  have hre : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ'
  have hz : partitionFunction ((σ : ℝ) : ℂ) = zetaCont ((σ : ℝ) : ℂ) := by
    rw [partitionFunction_eq_zeta hre, zetaCont_eq_zetaSeries hre]
  have hsub : ((σ : ℝ) : ℂ) - 1 ≠ 0 := by
    intro h
    have hr : σ - 1 = 0 := by
      have hc := congrArg Complex.re h; simpa using hc
    linarith
  have hnorm : ‖(1 : ℂ) / (((σ : ℝ) : ℂ) - 1)‖ = 1 / (σ - 1) := by
    rw [norm_div, norm_one]
    congr 1
    rw [show ((σ : ℝ) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hsplit : zetaCont ((σ : ℝ) : ℂ)
      = 1 / (((σ : ℝ) : ℂ) - 1) + zetaDiffSum ((σ : ℝ) : ℂ) := rfl
  rw [hz, hsplit]
  have htri := norm_sub_norm_le (1 / (((σ : ℝ) : ℂ) - 1)) (-(zetaDiffSum ((σ : ℝ) : ℂ)))
  rw [sub_neg_eq_add, norm_neg, hnorm] at htri
  linarith [hb]

end TDLean.Operator
