/-
  TDLean.Zeta.NonVanishing -- C9 item 3: ζ has no zero on the line `Re s = 1`.

  NO COQ ORACLE. From-scratch rule in force.

  The Hadamard--de la Vallee Poussin argument, run on `−ζ′/ζ` rather than `log ζ`, so that
  no Euler product is needed (see `Mertens.lean`). Given a zero at `1 + i t₀` (`t₀ ≠ 0`) of
  order `m ≥ 1`, and order `m' ≥ 0` at `1 + 2i t₀`, multiplying Mertens' inequality by
  `(σ − 1) > 0` and letting `σ → 1⁺` gives `3 − 4m − m' ≥ 0`, which is false.

  The three limits come from `LogDerivOrder.tendsto_sub_mul_logDeriv_of_factor`, used with
  exponent `−1` at the pole `s = 1` and with the zero orders at the other two points.
-/
import TDLean.Zeta.Mertens
import TDLean.Zeta.LogDerivOrder
import TDLean.Zeta.Identity

namespace TDLean.Zeta

open Complex Filter Topology

/-! ### `zetaCont` is analytic off the pole -/

theorem isOpen_punctured_halfplane : IsOpen ({s : ℂ | 0 < s.re} \ {1}) :=
  (isOpen_halfplane 0).sdiff isClosed_singleton

theorem analyticAt_zetaCont {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : AnalyticAt ℂ zetaCont s := by
  have hdon : DifferentiableOn ℂ zetaCont ({s : ℂ | 0 < s.re} \ {1}) := fun z hz =>
    (differentiableAt_zetaCont hz.1 (by simpa using hz.2)).differentiableWithinAt
  exact hdon.analyticOnNhd isOpen_punctured_halfplane s ⟨hs, by simpa using hs1⟩

/-! ### The pole at `s = 1` as an order `−1` factorisation -/

/-- `(s − 1)·ζ(s)`, extended analytically through `s = 1` where it takes the value `1`. -/
noncomputable def zetaPoleFactor (s : ℂ) : ℂ := 1 + (s - 1) * zetaDiffSum s

theorem zetaPoleFactor_one : zetaPoleFactor 1 = 1 := by simp [zetaPoleFactor]

theorem analyticAt_zetaPoleFactor {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ zetaPoleFactor s := by
  have hdon : DifferentiableOn ℂ zetaPoleFactor {s : ℂ | 0 < s.re} := fun z hz =>
    ((differentiableAt_const 1).add ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_zetaDiffSum hz))).differentiableWithinAt
  exact hdon.analyticOnNhd (isOpen_halfplane 0) s hs

theorem zetaCont_eq_poleFactor {s : ℂ} (hs1 : s ≠ 1) :
    zetaCont s = (s - 1) ^ (-1 : ℤ) * zetaPoleFactor s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [zetaCont, zetaPoleFactor, zpow_neg_one]
  field_simp

/-! ### Finiteness of the order on the line `Re s = 1` -/

/-- `zetaCont` does not vanish identically near a point of the line `Re s = 1`: any
    neighbourhood contains points with `Re s > 1`, where `zetaCont = ζ ≠ 0`. -/
theorem analyticOrderAt_zetaCont_ne_top {z₀ : ℂ} (hz : z₀.re = 1) :
    analyticOrderAt zetaCont z₀ ≠ ⊤ := by
  rw [Ne, analyticOrderAt_eq_top, Metric.eventually_nhds_iff]
  rintro ⟨ε, hε, hball⟩
  have hmem : dist (z₀ + ((ε / 2 : ℝ) : ℂ)) z₀ < ε := by
    have hd : dist (z₀ + ((ε / 2 : ℝ) : ℂ)) z₀ = ε / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    rw [hd]; linarith
  have hre : 1 < (z₀ + ((ε / 2 : ℝ) : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re, hz]; linarith
  exact zetaSeries_ne_zero hre
    (by rw [← zetaCont_eq_zetaSeries hre]; exact hball hmem)

/-- Factorisation of an analytic function at a finite-order point, in punctured
    `zpow` form -- the shape `tendsto_sub_mul_logDeriv_of_factor` consumes. -/
theorem factor_of_analytic {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hne : analyticOrderAt f z₀ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ ((analyticOrderNatAt f z₀ : ℕ) : ℤ) * g z := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hne
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hfg] with z hz
  simpa [zpow_natCast, smul_eq_mul] using hz


/-! ### `L(Λ)` is minus the logarithmic derivative of the continuation -/

theorem LS_LamC_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    LS LamC s = -logDeriv zetaCont s := by
  rw [LS_vonMangoldt_eq hs, logDeriv_apply, deriv_zetaCont_eq hs, zetaCont_eq_zetaSeries hs]
  ring

/-! ### Approaching the line `Re s = 1` horizontally -/

theorem tendsto_line (t : ℝ) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)) (𝓝[>] (1 : ℝ))
      (𝓝[≠] ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : Continuous (fun σ : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 : ℝ) < σ := hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith

/-- `(σ − 1)·Re F(σ + it)`, the quantity whose three limits give the contradiction. -/
noncomputable def mertensW (t σ : ℝ) : ℝ :=
  (σ - 1) * (LS LamC ((σ : ℂ) + (t : ℂ) * Complex.I)).re

/-- **The limit transfer.** A local factorisation of `zetaCont` at `1 + it` with exponent `m`
    forces `mertensW t σ → −m` as `σ → 1⁺`. -/
theorem tendsto_mertensW {t : ℝ} {m : ℤ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g ((1 : ℂ) + (t : ℂ) * Complex.I))
    (hg0 : g ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hfac : ∀ᶠ z in 𝓝[≠] ((1 : ℂ) + (t : ℂ) * Complex.I),
      zetaCont z = (z - ((1 : ℂ) + (t : ℂ) * Complex.I)) ^ m * g z) :
    Tendsto (mertensW t) (𝓝[>] (1 : ℝ)) (𝓝 (-(m : ℝ))) := by
  have hT := (tendsto_sub_mul_logDeriv_of_factor hg hg0 hfac).comp (tendsto_line t)
  have hT2 : Tendsto (fun σ : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I)
      - ((1 : ℂ) + (t : ℂ) * Complex.I))
        * logDeriv zetaCont ((σ : ℂ) + (t : ℂ) * Complex.I))
      (𝓝[>] (1 : ℝ)) (𝓝 ((m : ℤ) : ℂ)) := hT
  have hre := (Complex.continuous_re.tendsto ((m : ℤ) : ℂ)).comp hT2
  simp only [Function.comp_def] at hre
  have hEq : ∀ᶠ (σ : ℝ) in 𝓝[>] (1 : ℝ),
      ((((σ : ℂ) + (t : ℂ) * Complex.I) - ((1 : ℂ) + (t : ℂ) * Complex.I))
          * logDeriv zetaCont ((σ : ℂ) + (t : ℂ) * Complex.I)).re = -(mertensW t σ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 : ℝ) < σ := hσ
    have hrez : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
      simpa using hσ'
    have hsub : (((σ : ℂ) + (t : ℂ) * Complex.I) - ((1 : ℂ) + (t : ℂ) * Complex.I))
        = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    simp only [hsub, mertensW]
    rw [Complex.re_ofReal_mul, LS_LamC_eq_neg_logDeriv hrez, Complex.neg_re]
    ring
  rw [tendsto_congr' hEq] at hre
  have := hre.neg
  simpa using this

/-! ### The three limits -/

theorem tendsto_mertensW_pole : Tendsto (mertensW 0) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have h : ((1 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = 1 := by norm_num
  have key := tendsto_mertensW (t := 0) (m := -1) (g := zetaPoleFactor)
    (by rw [h]; exact analyticAt_zetaPoleFactor (by norm_num))
    (by rw [h, zetaPoleFactor_one]; norm_num)
    (by
      rw [h]
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact zetaCont_eq_poleFactor (by simpa using hz))
  simpa using key

theorem tendsto_mertensW_zero {t : ℝ} (ht : t ≠ 0) :
    Tendsto (mertensW t) (𝓝[>] (1 : ℝ))
      (𝓝 (-(analyticOrderNatAt zetaCont ((1 : ℂ) + (t : ℂ) * Complex.I) : ℝ))) := by
  have hre : ((1 : ℂ) + (t : ℂ) * Complex.I).re = 1 := by simp
  have hz1 : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have ha : AnalyticAt ℂ zetaCont ((1 : ℂ) + (t : ℂ) * Complex.I) :=
    analyticAt_zetaCont (by rw [hre]; norm_num) hz1
  obtain ⟨g, hg, hg0, hfac⟩ := factor_of_analytic ha (analyticOrderAt_zetaCont_ne_top hre)
  have := tendsto_mertensW hg hg0 hfac
  simpa using this

/-! ### The contradiction -/

/-- **ζ has no zero on the line `Re s = 1`.** -/
theorem zetaCont_ne_zero_of_re_eq_one {t : ℝ} (ht : t ≠ 0) :
    zetaCont ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have h2t : (2 * t : ℝ) ≠ 0 := by simpa using ht
  set m₁ := analyticOrderNatAt zetaCont ((1 : ℂ) + (t : ℂ) * Complex.I) with hm1
  set m₂ := analyticOrderNatAt zetaCont ((1 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) with hm2
  -- the zero at `1 + it` has order at least one
  have hre : ((1 : ℂ) + (t : ℂ) * Complex.I).re = 1 := by simp
  have hz1 : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := fun h =>
    ht (by simpa using congrArg Complex.im h)
  have ha : AnalyticAt ℂ zetaCont ((1 : ℂ) + (t : ℂ) * Complex.I) :=
    analyticAt_zetaCont (by rw [hre]; norm_num) hz1
  have hfin := analyticOrderAt_zetaCont_ne_top hre
  have hm1ne : m₁ ≠ 0 := by
    intro h
    have hcast := Nat.cast_analyticOrderNatAt (f := zetaCont)
      (z₀ := (1 : ℂ) + (t : ℂ) * Complex.I) hfin
    rw [← hm1, h] at hcast
    exact (ha.analyticOrderAt_ne_zero.mpr hzero) (by simpa using hcast.symm)
  -- the three limits
  have Lsum : Tendsto (fun σ => 3 * mertensW 0 σ + 4 * mertensW t σ + mertensW (2 * t) σ)
      (𝓝[>] (1 : ℝ)) (𝓝 (3 * 1 + 4 * (-(m₁ : ℝ)) + -(m₂ : ℝ))) :=
    ((tendsto_mertensW_pole.const_mul 3).add
      ((tendsto_mertensW_zero ht).const_mul 4)).add (tendsto_mertensW_zero h2t)
  have hnn : ∀ᶠ (σ : ℝ) in 𝓝[>] (1 : ℝ),
      0 ≤ 3 * mertensW 0 σ + 4 * mertensW t σ + mertensW (2 * t) σ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 : ℝ) < σ := hσ
    have e0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (σ : ℂ) := by norm_num
    have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
        = (σ : ℂ) + 2 * (t : ℂ) * Complex.I := by push_cast; ring
    have hid : 3 * mertensW 0 σ + 4 * mertensW t σ + mertensW (2 * t) σ
        = (σ - 1) * (3 * (LS LamC (σ : ℂ)).re + 4 * (LS LamC ((σ : ℂ) + (t : ℂ) * Complex.I)).re
            + (LS LamC ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)).re) := by
      simp only [mertensW, e0, e2]; ring
    rw [hid]
    exact mul_nonneg (by linarith) (mertens_nonneg hσ' t)
  have hle := ge_of_tendsto Lsum hnn
  have h1 : (1 : ℝ) ≤ (m₁ : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm1ne
  have h2 : (0 : ℝ) ≤ (m₂ : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Headline.** The continuation of `ζ` has no zero on the closed half-plane `Re s ≥ 1`
    (the pole `s = 1` excepted, where `ζ` is not defined). -/
theorem zetaCont_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    zetaCont s ≠ 0 := by
  rcases lt_or_eq_of_le hs with h | h
  · rw [zetaCont_eq_zetaSeries h]; exact zetaSeries_ne_zero h
  · have hsim : s.im ≠ 0 := by
      intro him
      exact hs1 (Complex.ext (by rw [← h]; simp) (by simp [him]))
    have hform : s = (1 : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp [← h]) (by simp)
    rw [hform]
    exact zetaCont_ne_zero_of_re_eq_one hsim

/-! ### Non-vacuity -/

/-- The hypotheses are satisfiable: `zetaCont` is genuinely non-zero at `2`, a point of the
    region covered by the headline. -/
theorem zetaCont_ne_zero_nonvacuous : zetaCont 2 ≠ 0 :=
  zetaCont_ne_zero_of_one_le_re (by norm_num) (by norm_num)

end TDLean.Zeta
