# The zero-enumeration gap (Gap A)

What it would take to *construct* an enumeration of `XiC`'s zeros, rather than assume one.
Written after a direct audit of the axiom budget, the counting machinery, and the
`ZeroEnum`/`ZeroEnumG` call sites. Every claim below was checked against source, not recalled.

## 1. The problem

`ZeroEnumG rho Gseq` (`spectral-theory/XiHcof.v:53-59`) is **assumed in 13 files and proved
in none**. It gates the whole Hadamard chain — `XiHadamardOrderOne.xi_hadamard_factor`,
`XiSubQuadLog.xi_subquadlog`, `XiLogDerivZeros.xi_logderiv_zeros` — and hence any de la
Vallée Poussin zero-free region built on the partial-fraction expansion of `ζ'/ζ`.

The companion hypothesis `Hlow : forall n, 1 <= Cmod (rho n)` was reduced to a
normalisation question by `XiZeroModulus.xi_zero_modulus_lower`; see that file's footer.

## 2. The obstruction is not choice

`spectral-theory/XiZeroEnum.v:9-16` says turning the per-radius zero lists into a function
"is exactly `choice`", and `spectral-theory/CZeroFactorDisk.v:34-40` says extracting a
derivative function from pointwise holomorphy "would need a choice axiom this development
does not use". **Both overstate the obstruction.** `XiTMSelect.v:13-20` draws the line
correctly and is the accurate statement in the repo.

The four-axiom budget already contains three `Prop`→data eliminators:

| mechanism | gives | already used at |
|---|---|---|
| `Raxioms.completeness : forall E : R -> Prop, bound E -> (exists x, E x) -> {m \| is_lub E m}` | an **arbitrary Prop predicate** → a real, as data | `LimSup.v:94-105` builds a whole `nat -> R`; `Ell2.v:592` builds an ℓ² limit vector |
| `sig_forall_dec`; `ConstructiveEpsilon.epsilon_smallest` (axiom-free) | `(exists n : nat, P n) -> {n \| P n}`, with minimality | `XiTMSelect.natsel:40` |
| `sig_not_dec` + `classic` | `{P} + {~P}` for **any** Prop | `CDescription.prop_dec` |

`completeness` is a **Lemma**, not an Axiom — `Raxioms.v:453`, proved from
`sig_forall_dec`/`sig_not_dec`. `R` itself is sealed by opaque ascription
(`RbaseSymbolsImpl : RbaseSymbolsSig`, `Rdefinitions.v:65`), so its Dedekind-cut
representation is inaccessible and `completeness` is the only way in.

The operative distinction is therefore

> **choice** (pick one of many) — out of budget, versus
> **description** (name the unique one) — in budget.

`CDescription.v` makes this concrete: `R_definite_description`, `C_definite_description`,
and `Cderiv_fun`, which manufactures a derivative *function* from pointwise existence
using only `is_Cderiv_unique` and `completeness`. `prop_dec`'s `Print Assumptions` is
exactly `sig_not_dec` + `classic`.

An enumeration ordered by (modulus, then argument) is uniquely determined, hence
*describable*. Note that `XiZeroEnum.v:21-26` discards sortedness "for no gain" — but for
construction sortedness is precisely the gain, since it is what makes the enumeration
canonical.

## 3. The geometry: three instruments that never meet

**Jensen is an exposure meter.** `∫log|ξ|` around a circle, minus `log|ξ(0)|`, bounds how
many zeros fit inside. It measures total darkness, never what cast it. *Every* count in the
repo has the shape `INR (length L) <= bound` with `L` an **input** —
`ZetaWindowCount.zeta_window_count:514`, `ZetaNTBound.zeta_N_bound:182`,
`XiZeroDensity.xi_count_peel:150`, `CPeelBound.peel_count_explicit:173`. Every one would be
true of a function with no zeros at all. Upper bound, and blind.

**IVT on the critical line is a tripwire.** `xir t = Re XiC(1/2+it)`
(`CoherenceSingularity.v:94`) is real-valued; a certified sign change forces a zero between,
and `IVT_interv` returns its location as **data** (`ZeroCounting.sign_change_zero_up:78`).
This is the only place in the repo where a zero becomes an object rather than a bound. It
has fired nine times — `NineZeros.nine_zeros:63`, heights ≤ 49, each zero pinned to an
interval of width 3–6, sign facts by `vm_compute` quadrature. `ZeroCountSandwich:54` brackets
the count in `|z| < 50` between 9 and `Bxi 50 ≈ 731`. But the tripwire sees only zeros *on
the line*, and only where a wire was laid by hand.

**The argument principle is the reconciliation** — `CArgPrincipleRect.arg_principle_rect:244`,
axiom-clean — but it has **never been pointed at `XiC` or `zetaC`**; its only consumer is a
toy example on `f(z) = z`. And even it takes the count as `length l` of a *hypothesised*
list, so it does not manufacture a number either.

The enumeration lives exactly where the meter and the tripwire meet. They do not meet.

**What a construction would look like.** You never pick a zero. You sweep a circle outward
from the origin and record the radii at which the zero count jumps; each such radius is the
supremum of a definable set, and `completeness` turns a supremum into data. Then you sweep a
ray around each critical circle for the angles. A radar scan, not a selection — which is why
no choice is needed.

## 4. What actually blocks it — mathematics, in order

1. **Infinitude of the zeros.** Clause 3 alone forces it: if `rho` were eventually constant
   at `w`, every `takeN rho N` being a peel list makes `XiC` divisible by `(z−w)^N` for all
   `N`, so `XiC ≡ 0`. The scan needs a k-th jump for every k, and `completeness`'s `bound E`
   hypothesis fails without it. **Nowhere proved.** Nine zeros are known to exist; only
   *upper* bounds on counts are known. A plausible route: assume finitely many, peel with
   `CZeroListFactor.DivBy_distinct`, apply `CBorelBound.order_one_step_uncond` to get
   `ξ = P(z)·A·e^{bz}`, and contradict via Γ's superexponential growth on the real axis
   (`StirlingSharp.Tlog_sharp` gives `ln(N!) ≥ N ln N − N + 1`). Not attempted.
2. **No count is ever data.** The one place a list *is* produced is `CZeroFree.v:98`,
   `bounded_has_max` + `classic` — the witness of a classically-chosen maximal length, an
   opaque `Prop` witness. A scan predicate must be rebuilt from scratch.
3. **No directedness.** Nothing relates peel lists at different radii — no `incl`,
   `Permutation` or sublist lemma in `CPeelBound.v`, `CZeroFree.v` or `CZeroListFactor.v`.
   This is what blocks upgrading a per-radius cofactor to a single entire one.
4. **`Gseq` needs the derivative at each peeled zero.** In budget, by §2 — this one is
   solved by `CDescription.Cderiv_fun`.

## 5. Clause audit: most of `ZeroEnum` is dead

Measured by grepping every destructuring of `ZeroEnum`/`ZeroEnumG`:

| clause | status |
|---|---|
| 1 — `rho n <> C0` | used (`XiHcof.v:86,125`, `XiHcofCoh.v:68`), but **re-derived from `Hlow`** at `XiLogDerivZeros.v:284-287`, so redundant |
| 2 — moduli escape | **never used anywhere.** Destructured and rebuilt at `XiHcof.v:63` and nowhere applied |
| 3 — every prefix is an `XiPeel` | **the workhorse.** Sole route to `enum_sum_bound` → `hadamard_prod_cv` → `TM`/`Msel`/`Pinf` |
| 4 — per-radius zero-free cofactor | `ZeroEnum`'s form **never used**; `ZeroEnumG`'s eventually-form used in exactly one place, `XiHcof.Hcof_ne0:120` |

So the live content is clause 3 plus `ZeroEnumG`'s clause 4.

## 6. What is now proved unconditionally

`XiPeelComplete.v` applies `CZeroFree.cofactor_zero_free` to `XiC` — all four of its
hypotheses were already discharged in `XiZeroCount.v`, and no file had ever applied it:

```coq
xi_peel_complete : forall R, 0 < R -> exists l G,
  (forall z, XiC z = Cmul (prodfac l z) (G z))
  /\ disk_holo G (4*R+2) /\ ptcont G
  /\ (forall w, In w l -> Cmod w < R) /\ (forall z, Cmod z < R -> G z <> C0)

xi_zeros_caught : ... /\ (forall z, Cmod z < R -> XiC z = C0 -> In z l)
```

This is the **per-radius form of both live clauses**, unconditionally. It is *not* `XiPeel l`:
`XiPeel` (`XiZeroDensity.v:109`) demands one cofactor holomorphic on *every* disk, and the
list here moves with the radius. Closing that is blocker 3.

## 7. Cost

| option | cost |
|---|---|
| what is done here | ~230 lines, landed, axiom-clean |
| infinitude of zeros (blocker 1) | a real theorem; est. 400–800 lines |
| full polar-scan construction | est. 1500–2000+ lines, gated on blocker 1 |
| `Hlow` constant 1 → r0 | 18 files, 188 occurrences, load-bearing in exactly one (`XiHadamardUnif.dev_unif:113-121`) |
| add a fifth axiom (functional choice) | a few lines — but every downstream theorem then carries it |
