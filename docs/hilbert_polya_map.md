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

## 4. The one load-bearing gap (stated plainly)

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

In the repo, that missing identification is **not proved** — it is asserted:

- `SpectralTripleRH.v` line 250: `Axiom berry_keating_correspondence`. Its
  conclusion is `on_critical_line_q (1#2)`, which unfolds to `1#2 == 1#2` — a
  **tautology**, true regardless of the hypothesis. So `RH_from_spectral_triple`
  (line 260) proves `1#2 == 1#2`, not RH.
- `st_self_adjoint : True` (line 209), `on_critical_line := True`-style
  placeholders, and the Merkle/JSON "certificates" are not Coq proofs of anything
  about ζ.

These files should be read as *scaffolding / statements of intent*, not proofs.
Closing the gap — actually proving that the operator's spectrum consists of the
zero ordinates — is **equivalent to RH itself**. The honest status: the operator
and the reflection geometry are built and axiom-clean; the eigenvalue = zero
identification is open, and the one-sided reduction (`RH_iff_no_left`) is a genuine
narrowing of the target, not a proof of it.

---

## What a next real step would look like

Not another `Axiom`. Either (a) a proof that some concrete self-adjoint operator's
resolvent/determinant equals the completed `ξ` (turning "trace = `ζ`" into
"spectrum = zeros"), or (b) an analytic zero-free-region result that, via
`RH_iff_no_left`, chips away at one half of the strip. Both are hard; only (b) is
plausibly incremental within this repo's current analytic machinery
(`zetaC_line_nonzero` is the `Re = 1` edge of exactly such a region).
