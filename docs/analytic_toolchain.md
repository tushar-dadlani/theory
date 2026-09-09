# The analytic toolchain — what already exists

**Read this before writing any new analytic file.** It exists because in a single
session I rebuilt four things that were already in `spectral-theory/`, and then
declared a fifth missing that was also already there. The repo is large enough
that "I don't remember seeing it" is worth nothing.

`docs/README.md` already says: *"Do not quote a claim of absence from these files
without checking `spectral-theory/` first."* This page is the concrete version of
that warning for the Dirichlet-series / complex-analysis half of the repo.

## The incident record (2026-09, L-function work)

| what I wrote | what already existed |
|---|---|
| `CHyperIter.Chyper_iter` | `CHyperbolaSwap.Chyperbola_swap` |
| "the tail estimate is remaining work" | `CDirichletProduct.cdirichlet_product` — complete |
| `VonMangoldtReal.vonmangoldt_R` | `VonMangoldtGlobal.vonmangoldt_identity` |
| `VonMangoldtReal.Lam_le_ln` | `CVonMangoldtSeries.Lam_le_ln` |
| `LambdaConv.lambda_conv` | `CVonMangoldtZeta.conv_term_eq` |
| `LambdaConv.Cls_scal_r` | `CListSum.Cls_scal_r` |
| "derivative continuity near s=1 needs building" | `CDerivHoloDisk.holo_deriv_fun` |

Cost: three files of duplicated work, plus a wrong roadmap I gave the user twice.

## If you need X, it is at Y

### Dirichlet series
| need | have |
|---|---|
| product of two absolutely convergent Dirichlet series | `CDirichletProduct.cdirichlet_product` |
| the finite hyperbola rearrangement over C | `CHyperbolaSwap.Chyperbola_swap` |
| `zeta(s) = sum n^{-s}` on `Re s > 1` | `CDirichlet.zetaC_eq_dirichlet` |
| absolute convergence from a majorant (C) | `CSeries.Cseries_abs_cv` |
| absolute convergence from a majorant (R) | `CSeries.Rseries_abs_cv` |
| the p-series `sum n^{-a}`, `a > 1` | `CZetaTerm.pseries_cv` |
| `ln x <= (1/c) x^c` | `CZetaTerm2.ln_le_rpow` |
| `ln` monotone | `CZetaTerm2.ln_le'` (NOT `ln_le`, which does not exist) |

### von Mangoldt
| need | have |
|---|---|
| `sum_{d|n} Lambda(d) = ln n` | `VonMangoldtGlobal.vonmangoldt_identity` (`dsum Lam n`) |
| `Lambda(n) <= ln n` | `CVonMangoldtSeries.Lam_le_ln` |
| `Lambda >= 0` | `Chebyshev.Lam_nonneg` |
| `Phi(s) = sum Lambda(n) n^{-s}` convergent | `CVonMangoldtSeries.Phi`, `Phi_spec` |
| the majorant `ln(n) n^{-Re s}` | `CVonMangoldtSeries.blam`, `blam_sum_cv` |
| `Phi * zeta = -zeta'`, and `Phi = -zeta'/zeta` | `CVonMangoldtZeta.phi_zeta_eq_neg_zeta'`, `phi_eq_neg_zeta_ratio` |
| the convolution collapse `sum_{d|n} a_d b_{n/d} = ln n * g(n)` | `CVonMangoldtZeta.conv_term_eq` |
| `zeta'(s) = sum (-ln n) n^{-s}` | `CZetaDerivDirichlet.dcterm_series_eq` |
| the MULTIPLICATIVE form `prod_{d|n} vexp(d) = n` | `DirichletVonMangoldtGen.vonmangoldt` |

### complex analysis
| need | have |
|---|---|
| `|e^w - 1 - w| <= 3|w|^2 e^{|w|}` | `CexpRemainder.Cexpf_remainder_w` |
| the derivative of a holomorphic function is holomorphic | `CDerivHoloDisk.holo_deriv_fun`, `deriv_holo_disk` |
| differentiable ==> continuous | `CHoloCalculus.is_Cderiv_cont` |
| Cauchy integral formula for the derivative | `CCauchyDeriv.cauchy_deriv` |
| locally uniform limit of holomorphic is holomorphic | `CMorera.unif_limit_holo` (entire approximants) |
| ... same, disk-local approximants | `CMoreraDisk.unif_limit_holo_disk` |
| `Cpw` base multiplicativity | `CPowMul.Cpw_base_mul` |
| `Cpw` exponent additivity, modulus | `CexpFull.Cpw_split`, `Cpw_mod`, `Cpw_RtoC` |

Note the shape shared by `unif_limit_holo`, `holo_deriv_fun` and friends: they
are stated on a disk **centred at 0** and demand GLOBAL pointwise continuity of
the approximants. Applying them to a half-plane function needs the shift/clamp
adapter — see `CLHolo3` (`shwL`/`fnwL`/`gwL`) or `CCauchyAnalytic.clampw`.
That adapter is the real cost, not the theorem.

## Summation conventions — the recurring friction

Four different partial-sum notations are in play. Most wasted effort in this area
is reindexing, not mathematics.

| notation | shape | where |
|---|---|---|
| `Cpsum a N` | `sum_{k=0}^{N} a k` (0-indexed, C) | `CSeries` — used by `Cseries_cv` |
| `sum_f_R0 f N` | `sum_{k=0}^{N} f k` (0-indexed, R) | stdlib — used by `Un_cv` |
| `Cls l f` / `Rls l f` | `sum over a list` | `CListSum` / `RealMobius` — used by `cdirichlet_product`, `divisors` |
| `CS F X` / `RS F X` | `sum_{n=1}^{X}` (1-indexed) | `CHyperIter` / `HyperbolaSplit` — used by the hyperbola work |

Bridges that already exist: `CDirichlet.Cpsum_shift_eq_Cls`,
`CVonMangoldtZeta.Rls_seq_S_eq_sumf`, `CDirichlet.CUn_cv_pred_S`,
`Un_cv_pred_S`.

**Build in the `Cls`/`divisors` convention** if the result is meant to feed
`cdirichlet_product`. `CS`/`RS` were introduced for the hyperbola method and
nothing else consumes them.

## Verified absent as of 2026-09-09

Only two, and both were checked by grep across `spectral-theory/*.v` on that
date. Re-check before relying on this.

- **`L(s, chi_0)` for the principal character.** `dchar p g 0` appears only as a
  term (`GaussSum.v:187`); there is no `L`-series for it and no factorisation
  `L(s,chi_0) = zeta(s)(1 - p^{-s})`. Note `CLHolo1.LFun` is gated on
  `HA : 0 < A < p-1`, which excludes it by construction.
- **Dirichlet's theorem itself** — the `s -> 1+` limit argument that combines
  `LFunOne.LFun_one_nonzero_all`, `CharOrthogonality.char_orthogonality_pair`
  and `CLLogDeriv.LFun_logderiv`.

## How to check, in one line

    grep -rn "<name or a distinctive fragment of the statement>" spectral-theory/*.v

and for a capability rather than a name, grep the *concept*: `divisors`,
`Cseries_cv`, `is_Cderiv`, `Lam`, `unif_limit`, `Cpw`. The file headers in this
repo are unusually informative — `head -25` on a candidate file usually settles it.
