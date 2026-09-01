# The Hilbert–Pólya program in this repo — an honest map

A constructive map of what the diagonal (prime) operator actually connects to in
this development, what has been **proved** (axiom-clean: only the four
classical-Reals axioms), and the **one load-bearing gap** that separates all of
this from a proof of the Riemann Hypothesis.

The Hilbert–Pólya idea: find a self-adjoint operator `H` whose eigenvalues are the
imaginary parts `t` of the nontrivial zeros `1/2 + it` of `ζ`. Self-adjointness ⇒
real eigenvalues ⇒ all zeros on `Re s = 1/2` ⇒ RH. This repo builds the operator
and the reflection geometry rigorously; it does **not** build the spectrum↔zeros
identification (that link is exactly as hard as RH).

---

## 1. The operator side (built, self-adjoint, trace = the ζ-data)

A genuine diagonal operator on the real ℓ² (standard basis `{e_i}`, already
diagonal), and its complex analogue on `nat → C`.

| Object | File | What is proved |
|---|---|---|
| `Dmul a` — diagonal multiplication operator | `Ell2Operator.v` | self-adjoint (`Dmul_selfadjoint`), bounded when the symbol is (`Dmul_bound`) |
| `z s n = n^{-s}`, `diag_trace (z s) N = Σ_{1}^N n^{-s}` | `Ell2Zeta.v` | the ζ-symbol trace (`diag_trace_eq`, `zeta_partition`) |
| trace `→ ζ(s)` for `s > 1` | `Ell2ZetaCont.v` | `operator_zeta_eq_cont` |
| `p`-sub-trace `→ (1 − p^{−s})^{−1}` | `Ell2Euler.v` | `euler_factor` — the local Euler factor as a geometric sub-trace |
| von Mangoldt operator `D_Λ`, trace `= ψ(N)` | `Ell2VonMangoldt.v` | `vm_trace_eq_psi` (Chebyshev ψ = spectral trace) |
| `M_σ := D_Λ · N^{−σ}`, eigenvalues `Λ(n)n^{−σ} ≥ 0` | `Ell2MellinVM.v` | self-adjoint, **positive**; trace `→ Φ(σ) = −ζ'/ζ(σ)`; at `σ=0`, trace `= ψ` |
| complex `M_s := CDmul(pterm s)`, trace `→ Φ(s)` | `CDiagOperator.v` | `trace_cv_Phi`, `trace_cv_neg_zeta_ratio` (trace **is** `−ζ'/ζ(s)`) |
| ψ(N) ≍ N (density in primorial bounds) | `ChebyshevBound.v` | `psi_upper`, `psi_lower` |

So the operator's spectral trace reproduces **every** analytic object that drives
the Perron/Newman apparatus: `ζ`, the Euler factors, `ψ`, and `Φ = −ζ'/ζ`. This is
solid and axiom-clean. The prime counts appear exactly as the user describes —
**density statements** (`psi_upper`/`psi_lower`) about the trace.

---

## 2. The Fourier / archimedean side (the "Fourier parts")

The multiplicative-group Fourier transform is the **Mellin transform**, and the
key repo fact is that it **is the Gamma factor**.

| Object | File | Fact |
|---|---|---|
| `mellin a c = ∫₀^∞ x^{a−1} e^{−cx} dx`, `Gam a = mellin a 1` | `GammaReal.v` | the archimedean integral |
| **`mellin a c = c^{−a} · Gam a`** | `MellinKernel.v` | `mellin_scale` — Mellin = scaling × Γ |
| Gaussian self-duality | `GaussSelfDual.v` | `fourier_self_dual` |
| theta functional equation `θ(1/t) = √t · θ(t)` | `GaussThetaTransform.v` | `theta_transform` |
| completed `J(s) = J(1−s)` | `RiemannThetaFE.v` | the symmetric integral |
| finite Fourier / DFT, Parseval, convolution | `Parseval.v`, `DFTConvolution.v` | `conv_theorem` |
| the `s ↦ 1−s` reflection as an `S²=I` involution, fixed at `1#2` | `FEInvolution.v` | `refl_fixed_iff` (abstract ℚ skeleton) |

---

## 3. The bridges built here (this task)

Two new axiom-clean files connect §1 to §2.

### `MellinOperatorBridge.v` — operator ↔ Mellin/Gamma
- **`mode_mellin`**: the operator's `n`-th eigenvalue `z s n = n^{−s}` **is** its
  own Mellin transform divided by `Γ(s)` (`mellin_scale` + unfold `z`). The
  diagonal operator's eigenvalue is literally an archimedean Mellin datum.
- **`trace_mellin_eq`**: the Γ-weighted partial trace `Γ(s)·diag_trace(z s) N` is
  the sum of the per-mode Mellin transforms.
- **`mellin_trace_cv`**: those summed Mellin transforms converge to `Γ(s)·ζ(s)` for
  `s>1` — the operator-theoretic realization of the classical
  `ζ(s)Γ(s) = ∫₀^∞ (Σ e^{−nt}) t^{s−1} dt` (heat kernel ↔ spectral zeta).

### `SpectralReflectionBridge.v` — reflection ↔ critical line, and a one-sided RH
- **`Srefl z = 1−z`** (the FE reflection): an involution (`Srefl_involutive`) with
  `S`-symmetric zeros (`zeros_S_symmetric = XiC_zero_reflect`). Its fixed **point**
  set is only `{1/2}` (`Srefl_fixed_point`) — *not* the line, since `1−(a+bi)=a+bi`
  forces `b=0`.
- **`Sbar z = 1 − conj z`** (reflection *across* the line): fixed **axis** is exactly
  the full critical line (`Sbar_fixed_iff : Sbar z = z ↔ Re z = 1/2`). This is
  `Srefl` composed with conjugation — the genuine "reflection fixed on the line."
- **`RH_iff_no_left` / `RH_iff_no_right`** (new): because reflected zero-pairs
  straddle the line (`Re z + Re(1−z) = 1`), RH is **equivalent** to excluding zeros
  from just one half of the strip (`Re < 1/2`, or `Re > 1/2`). Excluding half the
  strip suffices.

Supporting proved facts already in the repo: `ζ ≠ 0` on `Re = 1`
(`zetaC_line_nonzero`), `ζ ≠ 0` on `Re > 1` (`zetaC_nonzero`), `XiC` entire
(`XiC_entire`), the functional equation `XiC z = XiC(1−z)` (`XiC_symmetric`), and
the zero-pairing (`XiC_zero_reflect`).

---

## 4. The dilation / boundary-triple / Weyl chain (the spectral line of work)

A second, self-contained line of work replaces the "trace = `ζ`" diagonal operator
with a **Mellin-diagonal dilation** whose **boundary condition is the completed
`ξ`**, and studies it as a **boundary triple** (deficiency index `(1,1)`). It does
*not* close the gap of §5 either, but it sharpens it decisively: the reality of the
candidate eigenvalue-ordinates, previously *assumed*, is now a **theorem**, and the
zero count is realised as a genuine **phase winding**. Every file below is
axiom-clean (each ends with `Print Assumptions` on its headline results; only the
four standard classical-Reals axioms).

| File | Headline theorem(s) | Meaning |
|---|---|---|
| `CoherenceSingularity.v` | `coherence_line`, `XiC_crit_eq` | `ξ` is **real** on the critical line (the "coherence seam"); `xir t := Re ξ(½+it)` |
| `SelfDualCenter.v` | `self_dual_center` | weight-1 self-duality pins the seam at `Re = ½` |
| `BerryKeatingDilation.v` | `dilation_spectrum_is_zeros`, `hilbert_polya_target` | Mellin-diagonal dilation with boundary `B : ℝ → ℂ`; `spec Bxi t ⟺ ξ(½+it)=0`; the HP target stated as a `Prop` |
| `DilationBoundary.v` | `Bxi_even`, `Bxi_no_offaxis_zero` | the `x↔1/x` boundary match **is** the evenness of `ξ`; **no zero off the reflection axis** |
| `SelfAdjointExtension.v` | `icayley_real`, `extension_spectrum_real`, `hp_target_via_extension` | boundary triple; Cayley `c(z)=(z−i)/(z+i)`; **reality of the spectral point is DERIVED from the unit phase**, not inserted |
| `WeylFunction.v` | `zeros_are_Dirichlet_phase`, `scattering_trivial` | Weyl function `Wxi t = c(xir t)`; **zeros = the Dirichlet phase `−1`**; scattering matrix `ξ(1−s)/ξ(s) = 1` (the FE) |
| `WeylHerglotz.v` | `cayley_herglotz`, `phase_ordinate_bijection` | the Weyl map is **Herglotz** (upper half-plane → disk) and a **bijection** `ℝ ↔ U(1)∖{1}` |
| `ZeroCounting.v` | `xir_continuity_pt`, `sign_change_zero_up`, `alternation_zeros` | `xir` continuous (from `XiC` holomorphic); a **sign change ⇒ a zero** (IVT); `n` alternations ⇒ `n` zeros (Turing/Sturm lower bound) |
| `WeylWinding.v` | `Wxi_never_one`, `weyl_halfwinding_up`, `weyl_winding_count` | `Wxi` never touches `+1`; a sign change is a **half-winding** through the antipode `−1`; **counting zeros = counting phase windings** |
| `HilbertPolyaCapstone.v` | `berry_keating_summary`, `extension_target_refines_dilation_target`, `hilbert_polya_open` | packages the whole proven chain; the extension target **refines** the dilation target; the single open step as one `Prop` |

The end-to-end proven statement (`berry_keating_summary`): the boundary functional
is `ξ` and even; it has no zero off the reflection axis; a self-adjoint extension
*derives* a real spectral point from a unit phase; the Weyl function selects the
zeros at the Dirichlet phase `−1`; the scattering matrix is trivial (the FE); the
Weyl map is Herglotz and a bijection; and a sign change of `xir` is a half-winding
of the Weyl phase through `−1`. All unconditional and axiom-clean.

---

## 5. The one load-bearing gap (stated plainly)

Everything above is real and machine-checked. What is **missing** is the single
Hilbert–Pólya link:

> **The operator's spectrum is not the ζ-zeros.**

The spectrum of the operators in §1 is `{n^{−s}}` (for `Dmul (z s)`) or `{Λ(n)}` /
`{Λ(n)n^{−σ}}` (for the von Mangoldt operators) — **prime/integer data on the
diagonal**, not the ordinates `t` of the zeros `1/2 + it`. The trace *reproduces*
`ζ` and `−ζ'/ζ` as analytic functions, but reproducing `ζ` is not the same as
having the zeros *be* your eigenvalues. Berry–Keating asks for an operator whose
**eigenvalues** are those `t`; no transform in this repo carries the prime side to
a *zeros* side.

In the repo, that missing identification is **not proved**. It is now stated
**honestly and non-tautologically** by the §4 chain:

- **The current, honest statement of the gap** is
  `SelfAdjointExtension.hp_target_via_extension`, surfaced as one `Prop`:
  `HilbertPolyaCapstone.hilbert_polya_open`. It asserts the existence of a
  unit-phase sequence `u` whose Cayley-preimage ordinates enumerate exactly the
  on-seam zeros. Crucially, the **reality** of those ordinates is *no longer part
  of the gap* — it is the theorem `icayley_real` (a unit phase yields a real
  spectral point). What remains open is only that the **geometric** boundary phase
  realising `XiC`'s zeros is that specific `u` — i.e. that the operator whose
  boundary-triple Weyl function is `Wxi` is the geometric Berry–Keating dilation.
  This is a genuine existence target, never asserted true.

  ⚠ **Read "only" with care.** One open `Definition` reads as nearly finished, and this one
  is not: a `Definition` can encode arbitrarily much, and `hilbert_polya_open` encodes
  essentially the whole Hilbert–Pólya conjecture. The surrounding scaffolding being
  axiom-clean does not make the gap small. See `rh_routes.md` §4.

- **Legacy scaffolding, superseded.** An older file `SpectralTripleRH.v` (line 250)
  contains `Axiom berry_keating_correspondence`, whose conclusion `on_critical_line_q
  (1#2)` unfolds to `1#2 == 1#2` — a **tautology**; `st_self_adjoint : True` (line
  209) and the Merkle/JSON "certificates" are `True`-placeholders, not proofs. Read
  those as statements of intent. The §4 chain **replaces** that tautological
  assertion with the honest `Prop` above and an axiom-clean body around it.

Closing the gap — proving the geometric phase `u` exists / that the spectrum is the
zero ordinates — is **equivalent to RH itself**. The honest status: the operator,
the reflection geometry, the boundary-triple reality derivation, the Weyl-function
identification, and zero-counting-as-winding are all built and axiom-clean; the
single geometric-phase existence step is open, and the one-sided reduction
(`RH_iff_no_left`) remains a genuine narrowing of the target, not a proof.

---

## What a next real step would look like

Not another `Axiom`. The gap is now sharp: identify the **geometric phase** — an
operator whose boundary-triple Weyl function is `Wxi` (equivalently, discharge
`hilbert_polya_open`). Concrete incremental routes:
- (a) exhibit a concrete self-adjoint operator whose resolvent/determinant equals
  the completed `ξ`, or whose Weyl function is `Wxi` (turning "trace = `ζ`" /
  "boundary = `ξ`" into "spectrum = zeros");
- (b) an analytic zero-free-region result that, via `RH_iff_no_left`, chips away at
  one half of the strip (`zetaC_line_nonzero` is the `Re = 1` edge of such a region);
- (c) a genuine **argument-principle / N(T) asymptotic** built on top of the
  zero-counting-as-winding already proved (`weyl_winding_count`) — the Weyl-term
  `N(T) ~ (T/2π)ln(T/2π) − T/2π` — which would need `ξ` growth/Stirling on vertical
  lines.
All are hard; (b) and (c) are the plausibly incremental ones within the repo's
current analytic machinery. The unconditional achievement to build on: zeros are
counted as **half-windings of the Weyl phase through the Dirichlet phase `−1`**
(`WeylWinding.weyl_winding_count`).
