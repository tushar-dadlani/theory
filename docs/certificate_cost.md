# The cost of a machine-checked certificate for a zero of ξ

This note records what it costs, in one specific formal proof system, to
certify that the *n*-th nontrivial zero of the Riemann ξ function exists.
Everything below is either **measured** in this development or **derived**
from measured quantities; the two are marked.

It is an **upper-bound / proof-length** result. There is no lower bound
here, and Section 5 explains at some length why this is not, and cannot
be, an argument about P vs NP.

---

## 1. What is certified

`spectral-theory/ThirdZero.v`:

```coq
three_distinct_zeros_exist :
  exists t1 t2 t3,
    10 < t1 < 16 /\ 16 < t2 < 22 /\ 22 < t3 < 26 /\
    XiC (crit t1) = C0 /\ XiC (crit t2) = C0 /\ XiC (crit t3) = C0
```

Each zero comes from a sign change of `xir t = Re (XiC (1/2 + it))`,
certified by interval arithmetic over ℚ and `vm_compute`. Axioms: the four
standard classical-Reals ones only.

## 2. The measured decay law

Using an independent (non-Coq) evaluation of
`Xi(t) = Re[(1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s)]` at `s = 1/2+it`, over the first
13 inter-zero intervals, `t ∈ [15.7, 60.0]`:

| quantity | measured |
|---|---|
| decay of peak \|Ξ\| between zeros | **2.7e14×** |
| implied rate | **0.749** vs predicted π/4 = 0.785 |
| bits of cancellation `log2(0.5/\|Ξ\|)` | 9.2 at t=15.7 → **57.1** at t=60.0 |
| slope | **1.081 bits per unit t** |

The gap between 0.749 and π/4 is the `t^{7/4}` polynomial factor pulling the
other way. The law `|Ξ(t)| ~ C t^{7/4} e^{-πt/4}` fits with a bounded,
oscillating residual — the `|ζ(1/2+it)|` factor.

## 3. The measured certificate cost

Three points, all from this development:

| t | Re TC margin | rule | panels | enclosure width |
|---|---|---|---|---|
| 16 | 3.0e-06 | midpoint | 768 | — |
| 22 | 1.6e-08 | Simpson | 512 | 5.9e-09 |
| 26 | 9.6e-10 | Simpson | 1024 | 1.8e-11 |

The margin falls ~200× from t=16 to t=22 and another ~17× to t=26, tracking
`|Ξ| ~ t^{7/4} e^{-πt/4}`. The panel count does **not** track it, because the
quadrature order rose from 2 to 4 in between — which is the point.

**Derived.** For a quadrature of order `2k`, `n ~ margin^{-1/(2k)}` and
`margin ~ e^{-πt/4}`, hence

> **n ~ exp(π t / (8k))**

Raising the order divides the exponent; it never removes it. At t = 100:
midpoint 1e17, Simpson 3e8, order-8 1.8e4.

## 4. Where the exponential actually lives

```
Xi(t) = -(1/2)(1/4+t^2) . pi^{-1/4} . |Gamma(1/4+it/2)| . Z(t)
        \_________________________________________/   \__/
          strictly POSITIVE, ~e^{-pi t/4}, CLOSED FORM   O(1)
```

This is a theorem, not a remark — `spectral-theory/XirSignZ.v`:

```coq
xir_sign_Z       : forall t, xir t = - cpos t * Zfun t
cpos_pos         : forall t, 0 < cpos t
Amod_closed_form : |A(t)| = pi^{-1/4} * |Gamma(1/4+it/2)|
```

`(1/2)s(s-1) = -(1/2)(t²+1/4)` at `s = 1/2+it` — real and negative — and the
archimedean factor has modulus `π^{-1/4}|Γ(1/4+it/2)|`, positive and in
closed form. **The sign of `xir` does not depend on it.**

Our quadrature computes `xir` as `1/2 - (1/4+t²)·Re TC`, a difference of two
quantities of size `1/2`. That is where the 1.08 t bits go. `Z` has no such
cancellation. Changing to Riemann's other formula for ξ (integration by
parts, removing the additive 1/2) does **not** help — the integral would
still be exponentially small by oscillatory cancellation. Only dividing out
the known `|Γ|` factor removes it.

## 5. Why this is *not* a P vs NP argument

Four independent reasons, any one of which is fatal:

1. **It is an upper bound on one algorithm, not a lower bound over all
   algorithms.** Every cost figure here is of the form "*n* panels
   *suffice*". Nothing shows any *n* is *necessary*. Hardness is exactly the
   lower-bound direction, and we have none.
2. **Exponentially better algorithms are known and in routine use.**
   Riemann–Siegel is `O(√t)`; Odlyzko–Schönhage amortises to `t^{o(1)}` per
   zero. All zeros to height ~1e13 have been verified, and isolated zeros
   near 1e24. Our exponential is an artifact of the formulation.
3. **Nothing here is a decision problem, let alone NP-complete.** Locating a
   zero of a real analytic function is a numerical/real-complexity question.
   Even the *good* algorithms are exponential in the bit-length of `t`,
   which is unremarkable and unrelated to P vs NP (computing `2^n` is
   likewise exponential in `|n|`).
4. **The exponential comes from an avoidable cancellation in our own
   representation.** Section 4 exhibits it and Sections 6–7 remove it. A
   defect of a chosen encoding is not a complexity separation.

The honest positive statement is a *proof-complexity* one: we have a
measured law for the size of a machine-checked certificate that a zero
exists, in one specific formal system.

## 6. The polynomial route: Γ's direction

`spectral-theory/GammaDir.v`, `GammaArg.v`, `ThetaEnclose.v`:

```coq
Uvec_eq    : Uvec t = Cexp (theta t)
theta t    = -(t/2) ln pi - Pang (1/4 + i t/2)
Pang z     = atan(Im z/Re z) + gamma Im z
             + sum_{k>=1} [ atan(Im z/(k+Re z)) - Im z/k ]
Wangl_tail2: |tail after N| <= Re z Im z / N + Im z^3 / (2 N^2)
```

**No `arg` function and no complex logarithm anywhere.** Directions are
carried as `PosDir phi c := exists r > 0, c = Cexp phi * r`, determined only
mod 2π — which is all `cos` and `sin` need. The plan flagged a wrong branch
of `arg Γ` as the likeliest silent error; it is structurally impossible.

**|Γ| is never computed.** The Weierstrass product's *modulus* converges
like `|z|²/N`; its *angle* like `Im z/N`, because the leading `Im z/k`
cancels. Only the angle decides `sign(Z)`. Measured tail at t = 26:

| N | bound |
|---|---|
| 200 | 0.0437 |
| 500 | 0.0109 |
| 1000 | 0.0044 |

**Measured result** (`theta_26_bounds`): `5.048 <= theta 26 <= 5.084`,
containing the true 5.0709489. Runtime 21 s. Width 0.035, fully accounted
for: 0.0218 truncation + 0.0121 from the width of γ + 0.0009 from ln π.

Supporting constants, all certified here: `ln 2`, `ln pi`
(`LnConstants.v`), and Euler–Mascheroni `gamma` to 9.3e-4
(`GammaConst.v`) — the repo previously had only `0 <= gamma <= 1`.

## 7. The polynomial route: ζ on the line

`spectral-theory/ZetaTrap.v`, `ZetaEM.v`:

```coq
zetaC_trapezoid : zetaC s = 1/(s-1) + 1/2 + sum_{n>=0} htermC s n
htermC_tail     : |tail after M| <= Kh(s) (M+1)^{-Re s} / (M+1)
```

The repo represented ζ by the *first-order* Euler–Maclaurin defect, whose
proved bound is `2|s| n^{-Re s-1}`. At t = 26 that tail is `104/√N` — about
**1e8 terms** for 1e-2. Replacing the left endpoint by the trapezoid gains a
full power of n, and the difference telescopes so nothing is lost:

| representation | per-term | tail at t=26 | M for 1e-2 |
|---|---|---|---|
| `gtermC` | `2\|s\|n^{-1.5}` | `104/√N` | ~1e8 |
| `htermC` | `(1/6)\|s\|\|s+1\|n^{-2.5}` | `75.3/N^{1.5}` | **~550** |

No Bernoulli numbers and no general Euler–Maclaurin formula: one order of
correction suffices, and the trapezoid defect is bounded by two applications
of `mvt_sandwich`, machinery already present.

**Measured** (`ZetaEnclose.v`, M = 50, K = 8): `Re ∈ [0.495892018,
0.495893823]`, `Im ∈ [1.339039429, 1.339041224]`, against an independent
head-plus-partial of `0.4958929 + 1.3390403i`. Width 1.8e-6.

## 8. Two engineering facts worth recording

Both were found by measurement after a wrong prediction, and both cost real
time.

- **`Iexp_base` is a first-order bracket.** Its relative width is `≈z²`,
  amplified by `2^m` through the squarings, so the halving count `m` — not
  the rounding precision `p` — controls accuracy. Raising every rounding
  precision moved an enclosure width by 0.1%; raising `m` from 25 to 36 moved
  it from 5.9e-9 to 1.8e-11. The same trap recurred in the ζ evaluator:
  `m = 3` gives a useless width of 1.37 where `m = 36` gives 4.5e-4.
- **Threading the log table through the ζ sum bought only 2×.** The change
  was O(M²) → O(M) and I expected an order of magnitude; measured 4m43s →
  2m23s at M = 20, bit-identical output. The log table was never the
  bottleneck — the exp and trig evaluations are, and they were already one
  per index. Further speed must come from the transcendentals.

## 9. The comparison

`spectral-theory/ThirdZeroCheap.v`:

```coq
xir_26_neg_cheap : xir 26 < 0
```

The same fact as `ThirdZeroT26.xir_26_neg`, by the polynomial route.
Both are in the build; neither depends on the other.

| | expensive route | cheap route |
|---|---|---|
| where | `ThirdZeroChk26` / `ThirdZeroT26` | `ThetaEnclose` / `ZetaEnclose` / `ThirdZeroCheap` |
| what is computed | `Re TC` by quadrature | `theta` and `zeta` |
| size | **1024 Simpson panels** | **40 trapezoid terms**, 200 arctan terms |
| exp halvings | 36 | 28 |
| decided quantity | `xir ~ 1e-9` | `Z(26) in [0.79, 2.10]` |
| `\|Gamma(1/4+it/2)\|` | implicit in the 1e-9 | **never computed** |

The margin is the whole story. The quadrature must resolve a quantity
of size `1e-9` obtained as a difference of two quantities of size `1/2`
-- 1.08 bits of cancellation per unit `t`, Section 2. The cheap route
decides a quantity of size `1.4` with an interval of width `1.3`. The
exponentially small factor is still there, but `xir_sign_Z` proves it
is positive and in closed form, so it never has to be resolved.

**Measured, at t = 26.** With M = 550 the zeta enclosure is

    Re zeta in [0.4903651812, 0.5104155098]   (true 0.5005035361)
    Im zeta in [1.3253855434, 1.3454360345]   (true 1.3355300007)

both of width 0.0201, giving `Z(26) in [1.3964, 1.4557]`; that run took
2h57m. But sizing `M` from the tail bound rather than from the margin
in `Z` was over-provisioning by a factor of ~50: M = 40 gives a tail
bound of 0.4937, `Z(26) in [0.79, 2.10]`, and the same conclusion in
about 10 minutes. The committed theorem uses M = 40.

## 10. Status

Complete and axiom-clean: every section above. What is **not** done is
any lower bound -- see Section 5 -- and the extension of Sections 6-8
to other `t`, which needs only new constants, not new theory.
