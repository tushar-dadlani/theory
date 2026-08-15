# The Gauss limit — the clear next content for `GammaC ≠ 0`

This is the **only remaining mathematical content** to make `XiC_zero_iff_zetaC_zero` unconditional. The
foundations are committed and axiom-clean: `CInfProd.v` (infinite products), `CSine.v` (complex sine),
`GammaGaussBounds.v` (`one_minus_pow_le_exp : 0≤t≤N → (1−t/N)^N ≤ e^{−t}`). What remains is the **Gauss-limit
representation of Gamma**, in two theorems (A: the IBP closed form; B: the convergence interchange), then a
short assembly (C) that closes the goal.

## Status (2026-08)

- **A (IBP closed form) — DONE**, axiom-clean in `GammaGaussLimit.v`:
  `betaI_eq : betaI s N = N!/prodshift s (S N)`, and the change of variables `cov_partial`/`cov_general`.
- **B (convergence interchange) — DONE**, axiom-clean in `GammaGaussLimit.v`. The crux (no repo DCT, hand-rolled):
  `exp_sub_pow_bound` (uniform `e^{−t}−(1−t/N)^N ≤ t²/(N−t)`), `compact_cv` (`∫_a^b tnk_N → ∫_a^b gnk`), the
  sub-integral bounds `betaI_sub_le` / `gnk_sub_le_Gam` (partial ≤ improper limit), `upper_bound`
  (`N^s betaI ≤ Gam`), `lower_bound` (`∫_d^A tnk ≤ N^s betaI`), `Gam_approx`, assembled by an ε/2 squeeze into
  ```
  gauss_limit      : Un_cv (fun N => N^s * betaI s N) (Gam s)
  gauss_limit_fact : Un_cv (fun N => N^s * (N! / prodshift s (S N))) (Gam s)
  ```
- **C (Weierstrass assembly + complex lift + `GammaC≠0`) — PARTIALLY DONE** → `GammaWeierstrass.v`:
  - **C.1 (product converges) — DONE**: `ln_lower_bound` (calculus, via MVT), `Wprod_cv` (`Wprod N → exp(Winf)`,
    log-sum decreasing + bounded below by a telescoping `s²` majorant).
  - **C.2 (real identity) — DONE**: `prodshift_RQ`, `RQ_Wprod`, `recip_G_eq`, then along `N = S n`
    `real_weierstrass : Gam s · Pval = 1` (`Pval = s·e^{Winf}·e^{sγ}`), giving `Gam_ne0`, `Gam_pos : 0 < Gam s`.
    The Euler–Mascheroni `γ` now appears on the archimedean (Γ) side, unconditionally.
  - **C.3 (complex lift + discharge) — IN PROGRESS** → `GammaCWeierstrass.v`:
    - **C.3.1 (complex product + agreement) — DONE**: the complex factor `wcf z k = (1+z/k)e^{−z/k}`
      has `dev = |wcf z k − 1| = O(1/k²)` (ring identity `−w²+(1+w)Rem` + `CexpRemainder.Cexpf_remainder`,
      summable via a `1/k²` telescoping bound), so `CInfProd.Pprod_cv` gives `Wc z`; `Pc z = z·e^{γz}·Wc z`
      with the anchor `Pc_agree : Pc (RtoC s) = RtoC (Pval s Hs)`.
    - **C.3.2 (product holomorphy) — IN PROGRESS**:
      - **enabling lemma DONE** (`CexpfDeriv.v`): `Cexpf_deriv : is_Cderiv Cexpf w (Cexpf w)` — proven directly
        from `Cexpf_remainder` + the addition formula (the survey thought this didn't exist); plus the chain
        rule `Cexpf_comp_deriv`.
      - **factor + finite-product holomorphy DONE** (`GammaCHolo.v`): `wfac_deriv` (each `(1+w/n)e^{−w/n}`
        holomorphic, via `Cderiv_mul_affine`/`Cderiv_comp_affine`), `Pprod_wcf_holo` (every finite partial
        product `∏_{k=1}^N wcf_k` holomorphic, by induction with `Cderiv_mul`).
      - **REMAINING, the hard brick**: holomorphy of the *infinite limit* `is_Cderiv Wc z (Wc z · S z)`,
        `S z = ∑ −z/(k(k+z))`. No "uniform limit ⇒ holomorphic" lemma exists, so a bespoke uniform-tail
        difference-quotient (`sum_deriv2`-style: `S` converges `O(1/k²)`, uniform tail + 2nd-order remainder).
    - **C.3.3 (reach + discharge) — REMAINING, easy once C.3.2 lands**: `F z = GammaC z · Pc z − C1` is
      holomorphic (`Cderiv_mul` + `GammaC_entire` + C.3.2), vanishes on `ℝ₊` (`Pc_agree` + `GammaC_agree` +
      `real_weierstrass`), so `CWalk.reach` gives `GammaC·Pc = 1` on `{Re>0}`, hence `GammaC ≠ 0`; specialize
      at `halfz z` to discharge `CZetaStripId.XiC_zero_iff_zetaC_zero` / `ZetaStripConfinement.H_gamma`.

## Target (achieved)

```
gauss_limit_fact : forall s (Hs : 0 < s),
  Un_cv (fun N => Rpower (INR N) s * (INR (fact N) / prodshift s (S N))) (Gam s Hs).
```
i.e. `Gam(s) = lim_N  N^s · N! / (s(s+1)···(s+N))`.  (`prodshift s (S N) = s(s+1)···(s+N)`,
`GammaExtend.v:46`; `prodshift_shift : s·prodshift(s+1)N = prodshift s (S N)`, `:49`.)

---

## Content A — the truncated integral and its closed form (IBP)

Define the two integrals (mirror `GammaReal.gnear`/`gtail`, packaged via `ImproperCv0`):

- **Beta integral** `betaI s N := ∫₀¹ u^{s−1}(1−u)^N du` (improper at `u=0` when `s<1`; converges for `s>0`).
- **Truncated Gauss integral** `truncG s N := ∫₀^N (1−t/N)^N t^{s−1} dt`.

**A1. `betaI_eq : betaI s N = INR (fact N) / prodshift s (S N)`.**
Induction on `N`. The recursion is one integration by parts on `[0,1]`:
```
betaI s N = (N / s) · betaI (s+1) (N−1)          [IBP: d(u^s/s) = u^{s−1}, boundary terms vanish]
betaI s 0 = ∫₀¹ u^{s−1} du = 1/s .
```
So `betaI s N = N!/(s(s+1)···(s+N))`.
- *Template:* `GammaRecur.v` does exactly this IBP on an improper integral — `Gs_deriv` (`:22`, the explicit
  antiderivative) + `ContinuousCoV.FTC_antideriv` (`ContinuousCoV.v:30`), with boundary terms killed by
  `boundary_zero`/`boundary_infty` (`GammaRecur.v:54,69`). Here the antiderivative of `u^{s−1}(1−u)^N` for the
  IBP is `u^s/s·(1−u)^N`; both boundary terms are `0` (`u^s→0` as `u→0⁺` since `s>0`; `(1−u)^N=0` at `u=1`).
- Reuse `ZetaContinuation.Rpower_deriv` (`:32`) for `d/du u^{s−1}`, `prodshift_shift` for the denominator
  recursion, and the `ImproperCv0` reconstruction (`gnear_sig` pattern) for `∫₀¹`.

**A2. `truncG_cov : truncG s N = Rpower (INR N) s · betaI s N`.**
Change of variables `t = N·u`, `dt = N du`, `(1−t/N)^N = (1−u)^N`, `t^{s−1} = (Nu)^{s−1} = N^{s−1}u^{s−1}`:
```
∫₀^N (1−t/N)^N t^{s−1} dt = N^{s−1}·N ∫₀¹ (1−u)^N u^{s−1} du = N^s · betaI s N .
```
- *Tool:* `ContinuousCoV.cov_continuous` (`:48`) — change of variables for a `C1` monotone map; here `g u = N u`.
  `Rpower (INR N) s` supplies `N^s` (`Rpower_pow`/`Rpower_mult` to split `(Nu)^{s−1}`).

**⇒ `truncG s N = Rpower (INR N) s · INR(fact N) / prodshift s (S N)` = the target's `N`-th term.**

---

## Content B — the convergence interchange (the genuinely new step)

**B0. `truncG_cv : forall s (Hs:0<s), Un_cv (fun N => truncG s N) (Gam s Hs).`**

There is **no dominated/monotone-convergence-in-parameter lemma** in `ImproperCv0/1`; hand-roll it with ε/3.
Fix `s>0`. Write `Gam s = ∫₀^∞ e^{−t}t^{s−1}`. For a cut `A>0` and `N ≥ A`:
```
|truncG s N − Gam s|
   ≤ ∫₀^A |(1−t/N)^N − e^{−t}| t^{s−1} dt        (head)
   + ∫_A^N |(1−t/N)^N − e^{−t}| t^{s−1} dt        (mid)
   + ∫_N^∞ e^{−t} t^{s−1} dt .                    (tail)
```
- **mid + tail ≤ 2·∫_A^∞ e^{−t}t^{s−1} dt**, because `0 ≤ (1−t/N)^N ≤ e^{−t}` (**`one_minus_pow_le_exp`**, done)
  so `|(1−t/N)^N − e^{−t}| ≤ e^{−t}` on `[A,N]`, and `(1−t/N)^N=0` for `t≥N`. Choose `A` with
  `∫_A^∞ e^{−t}t^{s−1} < ε/6`  — the **tail of `Gam`'s `gtail`**, `→0` as `A→∞` (from its `ImproperCv1` spec:
  `pint1_le_improper`, `improper_mono`, `GammaReal.gtail_sig`).
- **head → 0**: on the compact `[0,A]`, `(1−t/N)^N → e^{−t}` **uniformly**, so `∫₀^A |·| ≤ A·sup_{[0,A]}|·| → 0`;
  pick `N₀` with `sup_{[0,A]}|(1−t/N)^N − e^{−t}| < ε/(3A)` for `N ≥ N₀`.

The two new sub-lemmas B needs (neither is in the repo):

- **B1. Pointwise limit** `one_minus_pow_cv : forall t, 0≤t → Un_cv (fun N => (1−t/INR N)^N) (exp (−t))`.
  Proof: for `N>t`, `(1−t/N)^N = exp(N·ln(1−t/N))` (via `exp_pow_nat`, `GammaGaussBounds.v:16`), and
  `N·ln(1−t/N) → −t` by squeeze `−t/(1−t/N) ≤ N·ln(1−t/N) ≤ −t` (both bounds `→ −t`), using
  `ln(1−x) ≤ −x` and `ln(1−x) ≥ −x/(1−x)` (from the elementary `ln x ≤ x−1`, cf.
  `CZetaRegular2.ln_le_x1`), then `continuity_seq exp`.
- **B2. Uniform version on `[0,A]`** (or monotonicity of `N ↦ (1−t/N)^N` + Dini). Cleanest: monotone increasing
  in `N` on `[0,A]` (Bernoulli/AM-GM) + continuity + `Dini`/`Un_cv_squeeze0` on the compact. Alternatively a
  uniform rate from the squeeze bounds in B1.

Tools for B: `improper_mono`, `pint1_le_improper` (`CImproperIntegral.v:21,132`), `improper_bounded_cv`
(`ImproperCv1.v:84`), `UL_sequence`, `Un_cv_le`, `Rle_cv_lim`, `Un_cv_squeeze0` (`GammaFunction.v:77`),
`growing_cv`.

---

## Content C — assembly (short, once A+B are done)

1. **`gauss_limit`** = A2 ∘ A1 ∘ B0:  `Un_cv (fun N => N^s N!/prodshift s (S N)) (Gam s)`.
2. **Real Weierstrass** `Gam(s)·P(s) = 1`, `P(s) = s·e^{γs}·∏_{n≥1}(1+s/n)e^{−s/n}`: regroup
   `1/(N^s N!/prodshift) = s·∏_{k=1}^N(1+s/k)·e^{−s·ln N} = s·e^{s(H_N−ln N)}·∏(1+s/k)e^{−s/k}`, and take `N→∞`
   using `EulerMascheroni.gamma_is_limit` (`H_N−ln N → γ`) and **`CInfProd.Pprod_cv`** for
   `∏(1+s/k)e^{−s/k}` (its `dev` is `(1+s/k)e^{−s/k}−1 = O(1/k²)`, summable → hypothesis of `Pprod_cv`).
3. **Lift to `GammaC(z)·P(z) = 1` on `{Re>0}`** by the identity theorem `CWalk.reach`: both sides holomorphic
   (`GammaC_entire`; `P` entire via `Pprod_cv` + `sum_deriv` holomorphy template), agreeing on the real axis
   (`GammaC_agree` + step 2). Then **`GammaC_ne0 : ∀ z, 0<Re z → GammaC z ≠ C0`** in one line (`GammaC·P=1` ⇒
   neither is `0`).
4. **Discharge** the `GammaC(z/2) ≠ 0` hypothesis in `CZetaStripId.XiC_zero_iff_zetaC_zero` (and
   `ZetaStripConfinement.H_gamma`), making the strip zero-equivalence unconditional.

---

## Ordering / files

- `GammaGaussLimit.v` — `betaI`, `betaI_eq` (A1), `truncG`, `truncG_cov` (A2), `one_minus_pow_cv` (B1),
  uniform version (B2), `truncG_cv` (B0), `gauss_limit`. **This is the hard file** (A1 IBP induction + B0
  interchange). `GammaGaussBounds.one_minus_pow_le_exp` is already the B dominator.
- `GammaWeierstrass.v` — C: `P`, `Gam·P=1`, lift, `GammaC_ne0`; then edit `CZetaStripId.v` to drop the
  hypothesis.

**Crux risk:** A1 (the improper-IBP induction — but `GammaRecur.v` is the verbatim template) and B0/B2 (the
hand-rolled compact-uniform + tail-domination DCT — genuinely new, no repo DCT). Everything else is reuse.
