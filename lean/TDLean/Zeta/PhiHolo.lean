/-
  TDLean.Zeta.PhiHolo -- C9 item 4: `−ζ′/ζ(s) − 1/(s−1)` is holomorphic on `Re s ≥ 1`.

  NO COQ ORACLE. `docs/newman_route_status.md` records "holomorphy of PhiMinus at s = 1" as
  ABSENT on the Rocq side -- it is that route's own gating blocker, because its `zetaC` has
  no Laurent/pole structure at `1` at all.

  Here it is nearly free, because the pole was isolated *by construction*:
  `zetaCont := 1/(s−1) + zetaDiffSum`, hence (`zetaCont_eq_poleFactor`)

      zetaCont s = (s − 1)^(−1) · zetaPoleFactor s,   zetaPoleFactor s = 1 + (s−1)·zetaDiffSum s

  with `zetaPoleFactor` analytic on `Re s > 0` and `zetaPoleFactor 1 = 1`. Splitting `logDeriv`
  across that product turns the subtraction of the pole into an *identity* rather than an
  estimate:

      −ζ′/ζ(s) − 1/(s−1)  =  −logDeriv zetaPoleFactor s

  So holomorphy reduces to `zetaPoleFactor ≠ 0`, which on `Re s ≥ 1` is exactly item 3.
-/
import TDLean.Zeta.NonVanishing

namespace TDLean.Zeta

open Complex Filter Topology

/-! ### `zetaPoleFactor` is `(s−1)·ζ(s)`, and is non-zero on `Re s ≥ 1` -/

theorem zetaPoleFactor_eq_mul {s : ℂ} (hs1 : s ≠ 1) :
    zetaPoleFactor s = (s - 1) * zetaCont s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [zetaCont_eq_poleFactor hs1, zpow_neg_one]
  field_simp

/-- **Non-vanishing of the pole factor on the closed half-plane.** At `s = 1` this is the
    normalisation `zetaPoleFactor 1 = 1`; elsewhere it is item 3. -/
theorem zetaPoleFactor_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : zetaPoleFactor s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · rw [h, zetaPoleFactor_one]; exact one_ne_zero
  · rw [zetaPoleFactor_eq_mul h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (zetaCont_ne_zero_of_one_le_re hs h)

/-! ### Splitting the logarithmic derivative across the pole -/

theorem logDeriv_zetaCont_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hpf : zetaPoleFactor s ≠ 0) :
    logDeriv zetaCont s = -1 / (s - 1) + logDeriv zetaPoleFactor s := by
  have hz0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  -- `zetaCont` agrees with the product on the open set `{1}ᶜ`, so their `logDeriv`s agree
  have heq : ∀ᶠ w in 𝓝 s, zetaCont w = (w - 1) ^ (-1 : ℤ) * zetaPoleFactor w := by
    filter_upwards [(isOpen_compl_singleton (x := (1 : ℂ))).mem_nhds hs1] with w hw
    exact zetaCont_eq_poleFactor hw
  rw [(logDeriv_eventuallyEq heq).self_of_nhds]
  have hd : DifferentiableAt ℂ (fun w : ℂ => (w - 1) ^ (-1 : ℤ)) s :=
    (differentiableAt_zpow.mpr (Or.inl hz0)).comp s (differentiableAt_id.sub_const 1)
  have hmul : logDeriv (fun w : ℂ => (w - 1) ^ (-1 : ℤ) * zetaPoleFactor w) s
      = logDeriv (fun w : ℂ => (w - 1) ^ (-1 : ℤ)) s + logDeriv zetaPoleFactor s :=
    logDeriv_mul s (zpow_ne_zero _ hz0) hpf hd (analyticAt_zetaPoleFactor hs).differentiableAt
  rw [hmul, logDeriv_sub_zpow 1 (-1) hz0]
  norm_num

/-! ### `Φ⁻`, the pole-subtracted logarithmic derivative -/

/-- `Φ⁻(s) := −ζ′/ζ(s) − 1/(s−1)`, defined so that it is manifestly holomorphic. -/
noncomputable def PhiMinus (s : ℂ) : ℂ := -logDeriv zetaPoleFactor s

/-- **The identity.** On `Re s > 1`, `Φ⁻` really is `L(Λ) − 1/(s−1) = −ζ′/ζ − 1/(s−1)`. -/
theorem PhiMinus_eq {s : ℂ} (hs : 1 < s.re) : PhiMinus s = LS LamC s - 1 / (s - 1) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hpf : zetaPoleFactor s ≠ 0 := zetaPoleFactor_ne_zero hs.le
  rw [PhiMinus, LS_LamC_eq_neg_logDeriv hs, logDeriv_zetaCont_eq hs0 hs1 hpf]
  ring

/-! ### The region of holomorphy -/

/-- The open set on which `Φ⁻` is holomorphic. It contains `{Re s ≥ 1}` by item 3. -/
def phiRegion : Set ℂ := {s : ℂ | 0 < s.re ∧ zetaPoleFactor s ≠ 0}

theorem isOpen_phiRegion : IsOpen phiRegion := by
  rw [isOpen_iff_mem_nhds]
  rintro s ⟨hs, hne⟩
  have h1 : ∀ᶠ w in 𝓝 s, 0 < w.re := (isOpen_halfplane 0).mem_nhds hs
  have h2 : ∀ᶠ w in 𝓝 s, zetaPoleFactor w ≠ 0 :=
    (analyticAt_zetaPoleFactor hs).continuousAt.eventually_ne hne
  filter_upwards [h1, h2] with w hw hw2 using ⟨hw, hw2⟩

theorem halfplane_subset_phiRegion : {s : ℂ | 1 ≤ s.re} ⊆ phiRegion := by
  intro s hs
  exact ⟨by simp at hs; linarith, zetaPoleFactor_ne_zero hs⟩

theorem differentiableAt_PhiMinus {s : ℂ} (hs : s ∈ phiRegion) :
    DifferentiableAt ℂ PhiMinus s := by
  obtain ⟨hs0, hne⟩ := hs
  have ha := analyticAt_zetaPoleFactor hs0
  have : PhiMinus = fun w : ℂ => -(deriv zetaPoleFactor w / zetaPoleFactor w) := rfl
  rw [this]
  exact ((ha.deriv.differentiableAt.div ha.differentiableAt hne)).neg

/-- **Headline (C9 item 4).** `Φ⁻ = −ζ′/ζ − 1/(s−1)` is holomorphic on an open set
    containing the closed half-plane `Re s ≥ 1`. This is the zeta-side input Newman needs. -/
theorem differentiableOn_PhiMinus : DifferentiableOn ℂ PhiMinus phiRegion :=
  fun _ hs => (differentiableAt_PhiMinus hs).differentiableWithinAt

/-! ### Non-vacuity -/

theorem PhiMinus_nonvacuous : (2 : ℂ) ∈ phiRegion :=
  halfplane_subset_phiRegion (by norm_num)

end TDLean.Zeta
