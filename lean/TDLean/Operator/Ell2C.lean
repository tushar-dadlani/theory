/-
  TDLean.Operator.Ell2C -- a genuine COMPLEX ℓ², with an adjoint.

  ORACLE (as a target to overtake): `spectral-theory/Ell2.v`, `Ell2Operator.v`, `Ell2Zeta.v`.

  ## The gap this fills

  The Rocq `Ell2` line is entirely over **ℝ**: `Ell2.v:49` is `nat → R`, `:179 ip` is
  `Σ f(n)g(n)` — a *symmetric bilinear* form with no conjugation — and `Ell2Zeta.v` takes
  `s : R`. A repo-wide search finds **zero** occurrences of `Cconj` in any `Ell2*` file, no
  `adjoint` operation anywhere, and no complex Hilbert space. "Self-adjointness" there
  (`Ell2Operator.v:66 Dmul_selfadjoint`) is symmetry of a real bilinear form.

  Over ℝ that is a genuinely weaker notion, and it is the wrong one for spectral theory: it is
  Hermitian self-adjointness that forces **real eigenvalues**, which is the entire logic of the
  Hilbert–Pólya program. This file supplies the complex version and that implication.

  ## What this is NOT

  Constructing an operator whose eigenvalues are the zeta zeros *is* the Hilbert–Pólya problem
  and is open. Nothing here approaches it. What is built is the **framework** in which such a
  statement can be made at all — a sesquilinear inner product, an adjoint, Hermitian
  self-adjointness, real spectrum, and the diagonal zeta operator whose formal trace is `ζ(s)`.

  mathlib's `lp (fun _ : ℕ+ => ℂ) 2` is a full Hilbert space and would serve for the analytic
  side; the hand-rolled version here is deliberate, so the statements line up with `Ell2.v`.
-/
import TDLean.Zeta.VonMangoldt

namespace TDLean.Operator

open TDLean.Zeta Complex

/-- Square-summability: membership in `ℓ²(ℕ⁺, ℂ)`. -/
def Ell2 (f : ℕ+ → ℂ) : Prop := Summable (fun n => ‖f n‖ ^ 2)

/-- The **sesquilinear** inner product, conjugate-linear in the first slot.
    This is what `Ell2.v:179 ip` lacks. -/
noncomputable def ip (f g : ℕ+ → ℂ) : ℂ := ∑' n, (starRingEnd ℂ) (f n) * g n

/-! ### Convergence -/

theorem summable_mul_norm {f g : ℕ+ → ℂ} (hf : Ell2 f) (hg : Ell2 g) :
    Summable (fun n => ‖f n‖ * ‖g n‖) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hf.add hg).mul_left (1 / 2))
  have h := sq_nonneg (‖f n‖ - ‖g n‖)
  nlinarith [norm_nonneg (f n), norm_nonneg (g n)]

theorem summable_ip {f g : ℕ+ → ℂ} (hf : Ell2 f) (hg : Ell2 g) :
    Summable (fun n => (starRingEnd ℂ) (f n) * g n) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_mul_norm hf hg))
  rw [norm_mul, RCLike.norm_conj]

/-! ### The diagonal operator -/

/-- Multiplication by a sequence: `Ell2Operator.v:44 Dmul`, over ℂ. -/
noncomputable def diag (a : ℕ+ → ℂ) (f : ℕ+ → ℂ) : ℕ+ → ℂ := fun n => a n * f n

/-- A bounded multiplier preserves `ℓ²`. -/
theorem ell2_diag {a f : ℕ+ → ℂ} {M : ℝ} (ha : ∀ n, ‖a n‖ ≤ M) (hf : Ell2 f) :
    Ell2 (diag a f) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hf.mul_left (M ^ 2))
  have hM : 0 ≤ M := le_trans (norm_nonneg (a 1)) (ha 1)
  have hn : ‖a n‖ ≤ M := ha n
  have h0 : 0 ≤ ‖a n‖ := norm_nonneg _
  have hsq : ‖a n‖ ^ 2 ≤ M ^ 2 := by nlinarith
  calc ‖diag a f n‖ ^ 2 = ‖a n‖ ^ 2 * ‖f n‖ ^ 2 := by
        rw [diag, norm_mul]; ring
    _ ≤ M ^ 2 * ‖f n‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hsq (by positivity)

/-! ### The adjoint — absent from the Rocq development -/

/-- **The adjoint identity.** `⟪D_a f, g⟫ = ⟪f, D_{ā} g⟫`. The conjugate on the multiplier is
    exactly the content that a real bilinear form cannot see. -/
theorem ip_diag_adjoint (a f g : ℕ+ → ℂ) :
    ip (diag a f) g = ip f (diag (fun n => (starRingEnd ℂ) (a n)) g) := by
  refine tsum_congr fun n => ?_
  simp only [ip, diag, map_mul]
  ring

/-- A multiplier is *Hermitian* when it is real-valued. -/
def IsHermitian (a : ℕ+ → ℂ) : Prop := ∀ n, (starRingEnd ℂ) (a n) = a n

theorem isHermitian_iff_im (a : ℕ+ → ℂ) : IsHermitian a ↔ ∀ n, (a n).im = 0 := by
  constructor
  · intro h n
    have := h n
    rw [Complex.ext_iff] at this
    have h2 : -(a n).im = (a n).im := by simpa using this.2
    linarith
  · intro h n
    apply Complex.ext <;> simp [h n]

/-- **Self-adjointness in the Hermitian sense.** -/
theorem ip_diag_selfadjoint {a : ℕ+ → ℂ} (ha : IsHermitian a) (f g : ℕ+ → ℂ) :
    ip (diag a f) g = ip f (diag a g) := by
  rw [ip_diag_adjoint]
  exact congrArg (ip f) (funext fun n => by rw [diag, diag, ha n])

/-! ### Eigenvectors, and the Hilbert–Pólya implication -/

/-- The standard basis vector. -/
noncomputable def delta (n : ℕ+) : ℕ+ → ℂ := fun m => if m = n then 1 else 0

theorem ell2_delta (n : ℕ+) : Ell2 (delta n) := by
  refine (summable_of_finite_support ?_)
  refine Set.Finite.subset (Set.finite_singleton n) ?_
  intro m hm
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  simp [Function.mem_support, delta, hne] at hm

/-- `δₙ` is an eigenvector of `D_a` with eigenvalue `a n`. -/
theorem diag_delta (a : ℕ+ → ℂ) (n : ℕ+) : diag a (delta n) = fun m => a n * delta n m := by
  funext m
  simp only [diag, delta]
  by_cases h : m = n <;> simp [h]

/-- The diagonal matrix element `⟪δₙ, D_a δₙ⟫ = a n`. -/
theorem ip_delta_diag (a : ℕ+ → ℂ) (n : ℕ+) : ip (delta n) (diag a (delta n)) = a n := by
  rw [ip, diag_delta]
  rw [tsum_eq_single n (fun m hm => by simp [delta, hm])]
  simp [delta]

/-- **The Hilbert–Pólya implication**, and the reason Hermitian self-adjointness (not the real
    symmetric form of `Ell2Operator.v`) is the right notion: a self-adjoint diagonal operator
    has **real** eigenvalues. -/
theorem eigenvalue_real_of_selfadjoint {a : ℕ+ → ℂ} (ha : IsHermitian a) (n : ℕ+) :
    (a n).im = 0 := (isHermitian_iff_im a).mp ha n

/-! ### The zeta operator -/

/-- `Z_s`, the diagonal operator with entries `n^{−s}`: `Ell2Zeta.v:74 z`, over ℂ. -/
noncomputable def zetaKernel (s : ℂ) : ℕ+ → ℂ := fun n => ((n : ℕ) : ℂ) ^ (-s)

/-- **The zeta trace.** The diagonal matrix elements of `Z_s` sum to `ζ(s)` for `Re s > 1`.
    ORACLE: `Ell2Zeta.v:122 zeta_partition` (finite partial traces, real `s`). -/
theorem trace_zetaKernel {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ+, ip (delta n) (diag (zetaKernel s) (delta n)) = zetaSeries s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hterm : ∀ n : ℕ+, ip (delta n) (diag (zetaKernel s) (delta n))
      = (1 : ℂ) / ((n : ℕ) : ℂ) ^ s := by
    intro n
    rw [ip_delta_diag, zetaKernel, Complex.cpow_neg, one_div]
  rw [tsum_congr hterm]
  rw [← LS_one_eq_zetaSeries hs0, LS]

/-- `Z_s` is Hermitian exactly when `s` is real — the operator-side shadow of the fact that
    the Rocq development could only ever take `s : R`. -/
theorem isHermitian_zetaKernel_of_real {σ : ℝ} : IsHermitian (zetaKernel (σ : ℂ)) := by
  intro n
  have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp : -((σ : ℝ) : ℂ) = (((-σ : ℝ)) : ℂ) := by push_cast; ring
  have hbase : (((n : ℕ)) : ℂ) = ((((n : ℕ) : ℝ)) : ℂ) := by push_cast; ring
  rw [zetaKernel, hexp, hbase, ← Complex.ofReal_cpow hn]
  exact Complex.conj_ofReal _

end TDLean.Operator
