# The wave sieve and the zeta zeros

## The question

Can the prime **wave sieve** (`PrimorialWaveSieve.v`: `pw p n = sin(π n/p)`, product = sieve, primes detected
as survivors) be **connected to the zeta zeros**?

## The honest answer

**Partially, and formally; not fully.** The literal analytic bridge — the **explicit formula**
`ψ(x) = x − Σ_ρ x^ρ/ρ` (a prime sum over the zeros `ρ`) — is a monumental result that is **not in this
repository** and is out of reach to formalize now. But a real bridge exists at the level of the **dual waves**
and a **chain of already-proven facts**, with the missing analytic links named rather than faked.

## The two dual waves (proved, `WaveSieveSpectral.v`)

The primes enter the two sides of the prime–zero duality as two kinds of "genuine wave":

| | prime side (multiplicative/`n`) | zero side (frequency/`log x`) |
|---|---|---|
| wave | `sin(π n/p)` — period `p`, real | `e^{i t·log x}` — frequency `t`, complex |
| Fourier form | `roots_wave p j = Σ_{k<p}(w_p^j)^k` | Berry–Keating eigenfunction `x^{−1/2+it}` |
| detects | **nodes / peaks at multiples of `p`** | selected `t` = zeta-zero ordinates |
| lemma | `roots_wave_div`, `sin_roots_dual` | `zero_wave_mod`, `zero_wave_factor` |

- **`roots_wave_div`**: `Σ_{k<p}(w_p^j)^k` **peaks (`= p`)** exactly when `p | j`, vanishes otherwise — the
  roots-of-unity/character dual of `sin(π n/p)` (from `RootsOfUnity.dft_orthogonality` + `wpow_eq_one_iff`).
- **`sin_roots_dual`**: the sieve's `sin`-wave **node** at `n` ⟺ the roots-of-unity **peak** at `n` ⟺ `p | n`.
  Same divisibility detector, real-sinusoid vs. complex-character.
- **`zero_wave c t = e^{i t·log c}`** is a **unit-modulus** frequency-`t` character (`zero_wave_mod`), and
  `x^{−1/2+it} = x^{−1/2}·(zero wave)` (`zero_wave_factor`) — the Berry–Keating eigenfunction
  (`BerryKeatingDilation.dilation_character`) whose boundary-selected spectrum is the zeros.

`wave_duality` bundles both. Standard classical-Reals axioms only.

## The chain that links them (already-proven facts)

```
sieve primes                                        [PrimorialWaveSieve.primes_via_wave]
   │  each prime p = an Euler factor (1 − p^{−s})   [the s-dual of sin(π n/p)]
   ▼  CEulerProductConv.cEF_cv
ζ(s) = ∏_p (1 − p^{−s})^{−1}                          [Re s > 1]
   │  von Mangoldt:  Σ Λ(n) n^{−s} = −ζ'/ζ(s)         [CVonMangoldtZeta.phi_eq_neg_zeta_ratio,
   ▼                                                   CDiagOperator.trace_cv_neg_zeta_ratio]
−ζ'/ζ(s)   (poles = the zeros; Ell2MellinVM.mvm_trace_0 : σ=0 trace = Chebyshev ψ)
   │  ξ = completed ζ:  XiC(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)   [ZetaXiLink.XiC_is_completed_zeta, real s>1]
   ▼
XiC z = 0   ⇔   spec Bxi (Im z)                       [BerryKeatingDilation.spec_Bxi_zero]
   = the Berry–Keating spectrum, eigenfunctions x^{−1/2+it} = the "zero waves"
```

Every arrow is a `Qed` theorem in the repo (the prime→ζ arrows hold on `Re s > 1`).

## What's proven vs. the two gaps

**Proven (this file + cited):** the prime-wave ↔ roots-of-unity Fourier dual; the `e^{it log x}` zero-wave as a
formal unit-modulus character; and every individual link of the chain above.

**The frontier (NOT in the repo — the honest gap):**
1. **A complex-analytic `zetaC ↔ XiC` continuation off `Re s > 1`.** The prime/trace facts live where ζ has
   *no* zeros (`Re s > 1`); carrying them to the zero locus needs an identity connecting `zetaC`'s complex
   zeros to `XiC`'s — only the real `s>1` link (`XiC_is_completed_zeta`) exists.
2. **The explicit formula / Mellin operator-intertwiner** — the actual identity summing the prime side
   (`Σ Λ(n) n^{−s}`) over the zero-ordinates (the `Bxi`-spectrum). Nothing in the repo sums over zeros; the
   Perron tool (`PerronKernel`) stops at the `1/s` residue.

These two gaps **are** the explicit formula / the Hilbert–Pólya realization — the genuine open frontier. The
Berry–Keating "zeros = spectrum" step is itself conditional on `hp_target_via_extension` (and RH on `RH_XiC`).

## Summary

The wave sieve connects to the zeta zeros through **two dual wave families** (both now formal) and a **chain of
proven bridges** through ζ and `−ζ'/ζ` to `spec Bxi` — a structural, honest connection. Turning it into the
analytic prime↔zero *identity* (the explicit formula) is the load-bearing piece that remains unformalized, and
is named as such rather than asserted.
