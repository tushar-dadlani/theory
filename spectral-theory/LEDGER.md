# Spectral-theory ledger — an honest audit

This ledger states plainly **what is proved, at what strength, and where the honest
boundaries are** for the spectral-theory arc. It exists because the repository carries
ambitious names (e.g. `millennium-problems/`) and the value of this machinery depends
entirely on not confusing a *formalized skeleton* with a *solved problem*.

Every file below is machine-checked with **zero `Admitted`** in the stated results. The
distinction that matters is (a) axiom status, (b) genuine theorem vs structural analogy,
and (c) complete structure vs curated bundle.

---

## 1. Axiom status

"Axiom-free" = `Print Assumptions` reports **"Closed under the global context"** (constructive
ℚ/ℤ/ℕ; no classical logic, no functional extensionality). The ℝ files deliberately use the
standard classical `Reals` axioms and are **quarantined** — nothing axiom-free depends on them.

| Axiom-free (ℚ/ℤ/ℕ) | Uses classical `Reals` axioms (quarantined) |
|---|---|
| `PrimonGas`, `LadderOps`, `MobiusReciprocal`, `VonMangoldt`, `PosetMobiusFTC` | `EulerFactorR`, `LadderDerivR`, `VonMangoldtR`, `MobiusReciprocalR` |
| `FreeDivMeet`, `BiView`, `BiViewProduct`, `ProductFormula`, `Padic` | `HeatFlow`, `MassGap` (bundled master), `Involution`, `Landauer`, `LandauerBound`, `WalshHadamardHilbert` |
| `PosetTopology`, `FiniteTopology`, `ChainTower`, `InvLimit` | |
| `PadicIntegers`, `PadicMetric`, `PadicRing` | |
| the ℚ-sweep: `WalshHadamardHilbertQ`, `InvolutionQ`, `LandauerQ`, `HeatFlowQ`, `MassGapQ`, `LandauerBoundL` | `ComplexField` (custom `C = ℝ[i]`; footprint = R only) |

The `LandauerBound` (real `ln 2`) vs `LandauerBoundL` (parameter `L`, axiom-free) split is the
template: the one genuinely transcendental fact is isolated in an ℝ file, everything structural
is axiom-free.

---

## 2. Genuine theorem vs structural analogy

**Genuine theorems** — the stated result is literally proved about the stated object:

- **Euler product (finite)** `PrimonGas.euler_product`: `Σ_states ∏ x_p^{k_p} = ∏_p Σ_{k<K} x_p^k`.
  A true finite distributive identity.
- **Euler product formula for ζ(2)** `EulerProductZeta.euler_product_zeta2`: `∏_{p prime, p≤B} (1−p⁻²)⁻¹
  → ζ(2)` as `B→∞` — the genuine *infinite* Euler product identity **at `s=2`**, unconditional,
  built from the finite distributive identity above by reindexing along the factorization
  bijection and squeezing between the ζ-partial-sums and `ζ(2)`. Honest scope: existence of the
  product limit `= ζ(2)` (itself an existence limit, **not** the value `π²/6`); general `s`,
  `−ζ'/ζ`, and zeta *zeros* are still absent.
- **Analytic zeta-squared** `ZetaSquareAnalytic.zeta_square_analytic` (quarantined ℝ): the Dirichlet
  series of the divisor function at `s=2` converges to ζ(2)²,
  **`∑_{n≤N} τ(n)/n² → ζ(2)²`** (`zeta_two_sq_tau`, with ζ(2)² = `(proj1_sig zeta2_converges)²`). Proved
  by the classical **Dirichlet hyperbola squeeze**: the ordered-factorization double sum
  `Spart N = ∑_{a·b≤N} 1/(ab)²` (`zeta_two_sq_hyperbola`) is sandwiched
  `box(⌊√N⌋) ≤ Spart N ≤ box(N)` with `box M = (∑_{a≤M} 1/a²)²`, and both bounds → ζ(2)² (via
  `CV_mult` on the ζ(2) limit + a `Nat.sqrt` reindex), closed by a local `squeeze_const_upper`; the τ
  labelling comes from `Spart N = ∑_{n≤N} τ(n)/n²` (`Spart_eq_Dpart`), a `Permutation` of the
  hyperbola pairs with `⋃_{n≤N} {(d,n/d): d∣n}`. Reuses the ζ(2) arc (`RecipSquareBound.Rlsum`/
  `seqsum_zpart`/`incl_sum_le`, `ZetaConverge.zeta2_converges`, `growing_ineq`) and the algebraic τ
  (`DirichletDivisor.dtau_as_div`). This is the **analytic** counterpart of the axiom-free coefficient
  identity `DirichletZetaSquare` (ζ²↔τ). `Print Assumptions` = the quarantined trio
  (`sig_forall_dec`, `sig_not_dec`, `functional_extensionality_dep`) — **not** axiom-free. Honest scope:
  convergence to ζ(2)² as a limit; the value `π²/6`, general `s`, and any complex-analytic ζ stay absent.
- **MASTER umbrella for the ζ(2) arc** `ZetaMaster.zeta_arc` (quarantined ℝ): a single conjunction
  bundling the headline results of the whole ζ(2)/analytic-ζ thread, as a curated index (each conjunct is
  exactly the corresponding standalone theorem, assembled by a positional `conj` term). Five movements:
  **(I)** ζ(2)=Σ1/n² converges (`zeta2_converges`); **(II)** finite reciprocal-square sums ≤ ζ(2)
  (`recip_sq_nodup_bound`); **(III)** the Euler product ∏(1−p⁻²)⁻¹ → ζ(2) (`euler_product_zeta2`) and its
  per-set bound (`euler_factor_le_zeta`); **(IV)** the primorial Euler tower → ζ(2) (`tower_is_zeta2`);
  **(V)** the analytic ζ² (`zeta_two_sq_hyperbola`, `Spart_eq_Dpart`, `zeta_two_sq_tau`: ∑τ(n)/n² → ζ(2)²).
  Everything is relative to the limit `proj1_sig zeta2_converges` (no π²/6). `Print Assumptions zeta_arc`
  = the quarantined classical-ℝ trio (`sig_forall_dec`, `sig_not_dec`, `functional_extensionality_dep`) —
  **not** axiom-free. (Bundle, not new mathematics — the ℝ-side companion of the axiom-free
  `DirichletMaster`.)
- **De-quarantining ζ(2): a constructive real** `ZetaConstructive.zeta2c_cv` (**axiom-free**) — the start
  of rebuilding the ζ arc without the classical-ℝ axioms. Diagnosis: the whole arc's three axioms enter
  through a *single* door, `growing_cv` (completeness of the classical Dedekind reals) in
  `ZetaConverge.zeta2_converges`; p-adic/"prime-based" completions live at the finite places and cannot
  reach the archimedean ζ(2) (the repo's own `ProductFormulaQ` proves the orthogonality), so the correct
  "different cut" is the **Cauchy cut with explicit modulus** — which is exactly Rocq's stdlib
  `Reals.Cauchy.ConstructiveCauchyReals` (`CReal`), the axiom-free real that classical ℝ is *quotiented
  from*. **`CRealCv`** builds an axiom-free convergence calculus on `CReal`: `cvQ a x` (a rational
  sequence → a `CReal`) and the bridge `cvQ_of_regular` (a rational sequence with an explicit Cauchy
  modulus has a `CReal` limit, via stdlib `CRealComplete`) — the constructive replacement for
  `growing_cv`. **`ZetaConstructive`** then rebuilds **ζ(2) = Σ1/n² as an axiom-free `CReal`** `zeta2c`,
  proving `zeta2c_cv : cvQ zpartQ zeta2c` — the rational partial sums `zpartQ` are shown *regular* by
  porting the same telescoping estimate `1/(k+1)² ≤ 1/k − 1/(k+1)` to ℚ (`zpartQ_tele`/`zpartQ_cauchymod`).
  `Print Assumptions zeta2c_cv` = **Closed under the global context**. This de-quarantines the arc's
  foundational node; π²/6 stays out of scope (ζ(2) is a limit `zeta2c`, no value).
- **The axiom-free analytic ζ²** `ZetaSquareConstructive.zeta_two_sq_tau_constructive` (**axiom-free**) —
  the de-quarantined counterpart of `ZetaSquareAnalytic`: **`cvQ DpartQ (zeta2c * zeta2c)`**, i.e.
  ∑_{n≤N} τ(n)/n² → ζ(2)², now with **no** classical-ℝ axioms. The `CRealCv` convergence calculus is
  extended with the analytic layer — `cvQ_squeeze` (two-sided) and `cvQ_sq` (square of a bounded
  convergent, via the `(A+x)(A−x)` identity and `CReal_abs`-triangle) — both axiom-free on stdlib
  `CReal`. The hyperbola combinatorics of `ZetaSquareAnalytic` is redone over ℚ/`qsum` (`qsum_prodsep`,
  `qsum_perm`, `qsum_const`, the `qsum_incl_le_w` NoDup-domination stack; `pairbox_perm` /
  `NoDup_flat_map_disjoint` copy across `nat`/list-only), giving `box_sq`, `box_lower`, `Spart_le_box`,
  `divpairs_sum`, `Spart_eq_Dpart` over ℚ; then the squeeze `boxQ(⌊√N⌋) ≤ SpartQ ≤ boxQ` with both
  bounds → ζ(2)² (via `cvQ_sq` on `SMQ → zeta2c` + `cvQ_reindex` with `Nat.sqrt`). `Print Assumptions
  zeta_square_constructive` (the umbrella bundling `zeta2c_cv`, `Spart_eq_Dpart`, `SpartQ_cv`,
  `zeta_two_sq_tau_constructive`) = **Closed under the global context**. The whole ζ² result is now
  axiom-free — the ℝ-quarantined `ZetaMaster`/`ZetaSquareAnalytic` versions remain as the classical
  parallel. Verdict on the "see what comes out" experiment: stdlib `CReal` was pleasant (only its
  high-level API was touched), so no hand-roll was needed. Still out of scope: π²/6, general `s`.
- **The monotone-limit ε-principle** `CRealCv.cvQ_term_le` (**axiom-free**): a term of a monotone
  rational sequence is ≤ its `CReal` limit — `cvQ a x → (a monotone) → ∀n, inject_Q (a n) ≤ x`. The
  constructive replacement for `growing_ineq`. Proved cleanly via **ℚ-density** (`CRealQ_dense`:
  `a<b → {q | a < inject_Q q < b}`) used twice — no raw-`seq`/`Qpower` dissection of `CRealLt`: from a
  hypothetical `x < inject_Q (a n0)` get rationals `x < q' < q < a n0`, take the gap `p := Qden (q−q')`
  (with `Qle_1_Qden`), and `cvQ` forces `a m < q` for large `m` while monotonicity gives `a n0 ≤ a m`,
  contradiction.
- **Axiom-free umbrella for the constructive ζ arc** `ZetaMasterConstructive.zeta_arc_constructive`
  (**axiom-free**): the constructive companion to `ZetaMaster`, bundling the movements rebuilt over
  `CReal`: **(I)** ζ(2)=Σ1/n² exists (`zeta2c_cv`); **(II)** the finite reciprocal-square bound
  `recip_sq_le_zeta2c` — a NoDup list of positive integers has **`Σ 1/mᵢ² ≤ ζ(2)`** (the strict form,
  via `recip_sq_partial_bound`'s `qw`/nat `qsum_incl_le_qw` stack, then `SMQ_le_zeta2c` = `cvQ_term_le`
  on the monotone partials); **(V)** ∑τ(n)/n² → ζ(2)² (`zeta_two_sq_tau_constructive`), with the
  hyperbola sum `SpartQ_cv` and the τ identity `Spart_eq_Dpart`. `Print Assumptions
  zeta_arc_constructive` = **Closed under the global context**. Remaining vs the 5-movement classical
  `ZetaMaster`: movements **(III)** the Euler product and **(IV)** the primorial tower are **not yet
  ported** to `CReal` (they remain only in the quarantined `ZetaMaster`).
- **The FULL Euler product → ζ(2), constructive** `EulerProductConstructive.euler_product_constructive`
  (**axiom-free**) — movement III fully ported to `CReal`, matching classical
  `EulerProductZeta.euler_product_zeta2`: **`cvQ (fun N => ∏_{p prime ≤ N} 1/(1−p⁻²)) zeta2c`** with the
  *true* rational Euler factors `p²/(p²−1)`. Proved by the squeeze `zpartQ N ≤ ∏(…) ≤ ζ(2)`
  (`cvQ_squeeze_const_upper`, new in `CRealCv`): **lower** `zpartQ N ≤ ZpartialQ ≤ ZfactorQ`
  (`zpartQ_le_Zpartial` via the smooth-covering `code_surj`+`entry_pow_le_code`+`gstates_complete`, then
  `ZpartialQ_le_ZfactorQ`); **upper** `inject_Q (ZfactorQ) ≤ ζ(2)` via `cvQ_le_const` on the geometric
  product-of-limits **`Zpartial_cv_Zfactor`** (`ZpartialQ K → ZfactorQ`), each `ZpartialQ K ≤ ζ(2)`
  (`Ptrunc_le_zeta2c`: `euler_reindex` → `qsum` of `1/code²` over distinct positive codes →
  `recip_sq_le_zeta2c`). The convergence uses the telescoping `ZpartialQ K = ZfactorQ·∏(1−fugᵏ)`
  (`Zpartial_factored`), `1−∏(1−εᵢ) ≤ Σεᵢ` (`one_minus_prod_le_sum`), and an explicit `(1/4)^K ≤ 1/(K+1)`
  decay modulus (`quarter_pow_le` via `Qinv_le`+`nat_lt_pow2`) with `ZfactorQ ≤ 2^len` (`ZfactorQ_bound`)
  and `modulus_bound`. `CRealCv` gains `cvQ_squeeze_const_upper` + `cvQ_le_const`. Reuses the axiom-free
  ℚ machinery (`PrimonGas`/`EulerReindex`/factorization) verbatim; the truncated form
  `euler_product_trunc` (diagonal-truncated factors) is also kept. `Print Assumptions
  euler_product_constructive` = **Closed under the global context**.
- **The primorial Euler tower, constructive** `PrimorialTowerConstructive` (**axiom-free**) — movement
  IV ported to `CReal`, the last one. `cvQ_tower` is the constructive analogue of the classical (abstract)
  `PrimorialZeta.tower_is_zeta2`: a **monotone** rational rung sequence whose rungs are each ≤ ζ(2) and
  eventually dominate the ζ(2) partial sums converges to ζ(2) (proved from `zeta2c_cv` + `abs_le_neg`).
  Its concrete instance `primorial_tower_zeta2` — the Euler factor product `∏_{p≤n} 1/(1−p⁻²)` over a
  growing prime set → ζ(2) — verifies the three hypotheses: monotonicity via a `primes_upto` prefix
  decomposition + `ZfactorQ_app` + `ZfactorQ_ge1` (each factor `efacQ p ≥ 1`); the ≤ ζ(2) rung bound via
  the extracted `ZfactorQ_le_zeta2c`; domination via `zpartQ_le_ZfactorQ_primes`. `Print Assumptions` =
  **Closed under the global context**.
- **MASTER umbrella: the full axiom-free ζ(2) arc** `ZetaArcConstructive.zeta_arc_free` (**axiom-free**)
  — the constructive companion to the quarantined `ZetaMaster.zeta_arc`, now covering **all five
  movements** over `CReal`: (I) `zeta2c_cv`, (II) `recip_sq_le_zeta2c`, (III) `euler_product_constructive`,
  (IV) `cvQ_tower`, (V) `zeta_two_sq_tau_constructive` — assembled by a positional `conj` term (a new
  leaf file, to avoid the import cycle through `ZetaMasterConstructive`). `Print Assumptions
  zeta_arc_free` = **Closed under the global context**. Every movement of the classical `ZetaMaster`
  (which rests on `sig_forall_dec`/`sig_not_dec`/`functional_extensionality_dep`) is now reproved without
  them. Still out of scope, as for the classical arc: the value π²/6 and general `s`.
- **THE BASEL PROBLEM: ζ(2) = π²/6** `BaselZeta.basel` (quarantined ℝ) — the value the whole ζ(2)
  arc converges to, `proj1_sig ZetaConverge.zeta2_converges = PI²/6`, via the elementary Cauchy
  cotangent squeeze in four milestones. **M1 `BaselTrig`**: `cot²x < 1/x² < 1+cot²x` on (0,π/2)
  (from `sin_lt_x` + a new `x<tan x` by MVT on `sin x−x·cos x`) and a `Un_cv` sandwich. **M2
  `BaselCotPoly`**: the **binomial theorem over the complex ring** `Cbinomial` (built from scratch
  on `ComplexField`, Pascal reindex + boundary terms), then `sin((2m+1)θ) = sin^(2m+1)θ·Pcot(cot²θ)`
  by extracting `Im (cosθ+i sinθ)^(2m+1)` (de Moivre) with the `i^(2j+1)=(−1)^j·i` parity. **M3
  `BaselVieta`** (the crux, no reuse): a minimal `list R` polynomial layer — `Peval`, a
  synthetic-division factor theorem, "≤deg distinct roots ⇒ zero" (`too_many_roots`), function-zero
  ⇒ coeff-zero (Peval continuity) — hence **Vieta's sum of roots** `vieta_sum : Σr_k = −a_{m−1}/a_m`;
  applied to `Pcot m` (roots the distinct `cot²(kπ/(2m+1))`, k=1..m) with `C(2m+1,3)/C(2m+1,1) =
  m(2m−1)/3` gives `cot_sq_sum : Σ cot²(kπ/(2m+1)) = m(2m−1)/3`. **M4 `BaselZeta`**: summing the M1
  bounds and using `cot_sq_sum` sandwiches `zpart` between two rationals → π²/6 (`lowb_cv`/`upb_cv`
  via a `/INR(S n)→0` majorant), and `UL_sequence` pins the limit. `Print Assumptions basel` = the
  quarantined classical-ℝ axioms only (no `Admitted`, no custom axioms). π²/6 is inherently
  classical (π is archimedean), so this is quarantined, not axiom-free. **Out of scope:** general
  ζ(2k), the sharp `ψ(x)∼x`, and any contour/zeros argument.
- **MASTER umbrella for the Basel arc** `BaselMaster.basel_arc` (quarantined ℝ) — a single
  conjunction bundling the four milestones: (M1) the squeeze `cot²x<1/x²<1+cot²x`
  (`BaselTrig.cot_sq_bounds`), (M2) `sin((2m+1)θ)=sin^(2m+1)θ·Pcot(cot²θ)`
  (`sin_eq_sinpow_Pcot`), (M3) `Σcot²(kπ/(2m+1))=m(2m−1)/3` (`cot_sq_sum`), (M4)
  `proj1_sig zeta2_converges = π²/6` (`basel`) — assembled by a positional `conj` term.
  `Print Assumptions basel_arc` = the quarantined classical-ℝ axioms only.
- **The primon-gas phase transition** `HagedornTransition.hagedorn_transition` (quarantined ℝ) — the
  Hagedorn transition of the Riemann/primon gas (which `PrimonGas` models by unique factorization) at
  the critical temperature `b_c = 1`.  The partition function is the partial sum
  `Zpart b N = Σ_{k≤N}(k+1)^(−b) → ζ(b)`.  **Subcritical `b>1`:** `Zpart_cv` — it is *finite*
  (`growing_cv`: monotone + bounded, the upper bound via **Cauchy condensation** `Zpart b (2^m−1) ≤
  1 + (1−r^m)/(1−r)`, `r = 2^{1−b} ∈ (0,1)`, from a dyadic block bound + `Rpower` algebra).
  **Critical `b=1`:** `Zpart1_diverges` — it *diverges* (harmonic series unbounded, `H_{2^m} ≥ 1+m/2`
  via a dyadic doubling `H_{2n+2} ≥ H_{n+1}+½`).  Bundled: `hagedorn_transition = (∀b>1, ∃l,
  Un_cv (Zpart b) l) ∧ (∀M, ∃N, Zpart 1 N > M)`.  `Print Assumptions` = the quarantined classical-ℝ
  axioms only.  This is the genuine, real-variable phase transition attached to ζ (non-analyticity of
  the free energy at `β_c=1`); the *complex-analytic* boundary phenomena (Lindelöf μ, critical line,
  zeros) remain out of scope — they need the contour machinery this stdlib-only repo does not build.
- **Analytic continuation of ζ to Re(s)>0 (real axis)** `ZetaContinuation.zeta_analytic_continuation`
  (quarantined ℝ) — the Euler–Maclaurin/Abel continuation, the honest analytic successor to
  `HagedornTransition` (the `b_c=1` divergence reappears as the pole at `s=1`).  With the closed-form
  unit-interval integral `∫_n^{n+1}x^(−s)dx = ((n+1)^{1−s}−n^{1−s})/(1−s)` (so no step-function
  integration), the term `gterm s n = (n+1)^{−s} − ∫_{n+1}^{n+2}x^{−s}dx` yields the **partial
  identity** `zeta_EM_identity`: `Zpart s N = Σ_{n≤N} gterm s n + ((N+2)^{1−s}−1)/(1−s)`.  A **per-term
  MVT bound** `0 ≤ gterm s n ≤ (n+1)^{−s}−(n+2)^{−s}` (`g_bound`, via `Rpower_deriv` + `MVT_cor2` +
  `Rpower_negexp_antimono`) + a telescoping majorant give convergence of `Σ gterm s` for **all** `s>0`
  (`gterm_cv`, `growing_cv`).  Hence `ζ̃(s) := 1/(s−1) + Σ gterm s` is defined on `(0,∞)∖{1}` and,
  for `s>1`, **equals the Dirichlet value** `ζ(s)=Σn^{−s}` (`zeta_analytic_continuation`, via
  `zeta_continuation_extends` + `Zpart_cv` + `UL_sequence`; the tail `(N+2)^{1−s}→0` from
  `Rpower_neg_cv0`).  `Print Assumptions` = the quarantined classical-ℝ axioms only.  This is the
  real-variable Euler–Maclaurin formula — the exact expression whose ℂ-version is the analytic
  continuation; it does **not** prove holomorphy (no complex-analysis layer), and the functional
  equation / μ-triangle / zeros stay out of scope.
- **The Gamma pillar (integer): the factorial integral** `GammaFunction.gamma_n_eq_factorial`
  (quarantined ℝ) — `Γ(n+1) = ∫_0^∞ tⁿe^(−t)dt = n!`, one of the two pillars of the ζ functional
  equation (the other, Poisson/theta, needs Fourier — not stdlib).  Built **without
  integration-by-parts**, via the *recursive antiderivative* `A_n(t) = −tⁿe^(−t) + n·A_{n−1}(t)`,
  whose derivative is `tⁿe^(−t)` (`Aanti_deriv`, simple induction + product rule), so the Newton
  integral over `[0,N]` is `A_n(N) − A_n(0)` (`gam_newton` transparent, `newton_val`) with
  `A_n(0) = −n!` (`Aanti_0`) and `A_n(N) → 0` (`Aanti_lim0`).  The one analytic input is the growth
  limit `Nᵏe^(−N) → 0` (`poly_exp_cv0`), obtained from `exp x ≥ (x/(k+1))^(k+1)` (`exp_lb`, from
  `exp_ineq1` + `exp(n·y)=(exp y)ⁿ` + `pow_incr` — no Taylor-series library).  Delivers
  `Un_cv (fun N => NewtonInt (gam n) 0 (INR N) _) (INR (fact n))` and the integer recurrence
  `gamma_recurrence : (n+1)! = (n+1)·n!` (the shadow of `Γ(s+1)=s·Γ(s)`).  `Print Assumptions` = the
  quarantined classical-ℝ axioms only.  **Honest scope:** INTEGER Gamma (`tⁿ`, nat power); the real
  `Γ(s+1)=s·Γ(s)` needs `Rpower` + a poly≤exp bound for real `s`, and `Γ(½)=√π` needs the Gaussian
  integral — both beyond stdlib.  This is a pillar, **not** the functional equation (which also needs
  Poisson/theta summation).
- **Riemann–Lebesgue (C¹): Fourier-convergence milestone F1** `FourierRL.RL_cv` (quarantined ℝ) —
  `Un_cv (fun n => ∫_a^b g(t)·sin((n+½)t) dt) 0` for a stdlib `C1_fun` g, the first brick of
  Fourier-series pointwise convergence (the route toward Poisson → the ζ FE, on top of the existing
  `DirichletKernel`).  Proved by integration by parts through stdlib's **FTC**: `H(t)=−g(t)cos(λt)/λ`
  is bundled as a `C1_fun` (`Hc1`) with derivative `H'=g·sin(λ·)−g'·cos(λ·)/λ` (`H_deriv`,
  `Hval_cont`), so `FTC_Riemann` gives the IBP identity (`RL_ibp`), and `RiemannInt_P13/P17/P18/P19`
  (linearity + `|∫f|≤∫|f|`) give the bound `|∫g·sin(λt)| ≤ (|g(a)|+|g(b)|+∫|g'|)/|λ|` (`RL_bound`),
  whence `RL_cv`.  `Print Assumptions` = the quarantined classical-ℝ axioms only.  **Finding (the
  honest report):** even F1 — the "easy" half — was a heavy stdlib-`RiemannInt` slog (`C1_fun`/`derive`
  bookkeeping, all-implicit-arg plumbing on the `RiemannInt_P*` lemmas).  **F2** (the kernel
  representation `S_n f − f = (1/2π)∫(f(x+t)−f(x))D_n(t)dt`) is the flagged high-risk step: it needs
  change-of-variables + periodicity + sum/integral interchange, which stdlib `RiemannInt` lacks
  cleanly — this is precisely where a Coquelicot dependency (its `RInt` substitution/Fubini lemmas)
  would collapse the effort.  F3 (the removable singularity of `g(t)=(f(x+t)−f(x))/sin(t/2)`) then
  needs `f∈C²`.
- **The Ford-circle tangency theorem** `FordCircles.ford_circles` (**axiom-free**) — the Ford circle at
  a reduced `p/q` (q>0) is centred at `(p/q, 1/(2q²))` with radius `1/(2q²)`; the centre-distance
  collapses exactly (`ford_identity`): `dist² = (r₁+r₂)² + ((ad−bc)²−1)/(b²d²)`.  Since `ad−bc∈ℤ`:
  `ad−bc=±1` ⟺ Farey neighbours ⟹ externally **tangent** (`ford_tangent`); `ad≠bc` ⟹ **never
  overlap** (`ford_no_overlap`, from `|ad−bc|≥1`); `|ad−bc|≥2` ⟹ strictly **disjoint**
  (`ford_disjoint`).  Done entirely over **ℚ** (`inject_Z`, `field`, `nia`), so `Print Assumptions
  ford_circles` = **Closed under the global context** — pure arithmetic, no classical Reals.  This is
  the geometric substrate of the Farey / modular / θ-function story (Ford circles = horocycles at the
  cusps of `PSL(2,ℤ)`); it is **not** the analytic theta transformation `θ(1/t)=√t·θ(t)`, which still
  needs Poisson/Fourier or contours.  The modular skeleton, honestly labelled.
- **THE FUNCTIONAL-EQUATION SKELETON — a fixed-point involution** `FEInvolution` (**axiom-free**): the
  ζ functional equation `ξ(s)=ξ(1−s)` *in shape* — invariance under an INVOLUTION with one fixed
  point.  Over ℚ, `refl s := 1−s` is an involution (`refl_involution`) whose **unique fixed point is
  `s = 1/2` — THE CRITICAL LINE** (`refl_fixed_unique`, `refl_fixed_iff`); in the critical-line-centred
  coordinate it is **negation** `u ↦ −u` (`refl_is_negation`), the self-adjoint `S²=I` reflection whose
  fixed locus is its `+1` axis; and a function with `F(1−s)=F(s)` satisfies the FE shape `F(s)=F(1−s)`
  (`FE_reflects`), self-dual at `1/2` (`FE_selfdual_at_critical`).  The **modular face**: the theta
  transformation `θ(1/t)=√t·θ(t)` is invariance under `S : τ↦−1/τ`, i.e. on a Ford/Farey index `a/b ↦
  −b/a` = `(a,b)↦(−b,a)` (`Smod`); this **preserves the tangency determinant `ad−bc`**
  (`Smod_preserves_det`), hence Farey neighbours ↦ Farey neighbours and tangent Ford circles ↦ tangent
  Ford circles (`Smod_preserves_tangency` — the `det=±1` condition is exactly
  `FordCircles.ford_tangent`'s hypothesis), with `S²=−I` acting trivially on ℚ (`Smod_sq`).  **Honest
  boundary:** this is the SHAPE (involution, fixed point = critical line, self-duality, modular
  symmetry) — **not** the analytic `ξ(s)=ξ(1−s)`, which needs the self-dual invariant VALUE
  `∫e^{−πx²}=√π=Γ(½)`, the irreducible archimedean residue — exactly as `FordCircles` is the modular
  skeleton without the analytic θ.  `Print Assumptions` = **Closed under the global context**.
- **THE SELF-DUAL VALUE √π = Γ(½), NOW A THEOREM (axiom DISCHARGED)** `FEResidue.Gamma_half_is_sqrt_pi`
  (**axiom-free**) — this file once ISOLATED the functional equation's one archimedean residue as a
  single `Axiom Gamma_half_selfdual : Γ(½)²=π`; that axiom is now **proven and removed**.  Over `CReal`,
  with `piR := ConstructivePi.constructive_pi` (the Wallis π) and `GammaHalf :=
  ConstructiveSqrtPi.constructive_sqrt_pi` (its bisection root), `Gamma_half_selfdual : GammaHalf² == piR`
  is `ConstructiveSqrtPi.gamma_half_sq_eq_pi` and `GammaHalf_pos : inject_Q 1 ≤ GammaHalf` is
  `gamma_half_pos`; `Gamma_half_is_sqrt_pi` bundles them at `fe_fixed_point = FEInvolution.critical =
  1/2`.  Everything structural around the FE is axiom-free (the `s↦1−s` involution with fixed point 1/2
  `FEInvolution`, the modular `S` preserving Ford tangency, finite/algebraic Poisson `finite_poisson_R`,
  integer Gamma `GammaFunction`), and now so is the VALUE.  `Print Assumptions` = **Closed under the
  global context** — the FE arc has no axioms left.  **HONEST BOUNDARY (the whole point):** `π`/`√π`
  here are the WALLIS / central-binomial constructions taken as the constructive definitions; their
  identification with the CIRCLE π and the GAUSSIAN INTEGRAL `∫e^{−πx²}=√π` (i.e. that this is the
  value the analytic `ξ(s)=ξ(1−s)` carries at `s=1/2`) is Wallis's / the Gaussian's theorem, classical
  and NOT formalized.  The value now EXISTS axiom-free; the analytic θ-bridge to the Gaussian is the
  remaining archimedean content, and it never was what `FEResidue` isolated (it isolated the VALUE).
- **FINITE POISSON SUMMATION** `FinitePoisson.finite_poisson` (quarantined ℝ) — the discrete shadow
  of Poisson, on the DFT cluster: for `N = d·m`, `Σ_{r<m} (DFT_N f)(r·d) = m · Σ_{a<d} f(a·m)`
  (summing the DFT over the dual subgroup `{rd}` recovers `f` summed over the subgroup `{am}`).
  Proof: swap the double sum (`Csum_swap`), pull `f(k)` out, and the inner geometric sum
  `Σ_{r<m}(wc_N^{dk})^r` is `m` if `m∣k` and `0` otherwise (`orth_val`, via `sum_pow_eq_0/1` +
  `wc`-primitivity — from `w_primitive` and `wc·w=1`, `Cpow_Cmul`); then the subgroup reindex
  `k=am+b` keeps only `b=0` (`sum_multiples`, `Csum_delta`).  Quarantined via `ComplexField`
  (`C=ℝ×ℝ`), so `Print Assumptions` shows the classical-ℝ axioms.  **Honest scope:** the FINITE,
  elementary Poisson formula — NOT the continuous `Σ_n f(n)=Σ_k f̂(k)` (which needs improper integrals
  + the blocked Fourier convergence) and NOT progress on the FE.  It closes the discrete-Fourier arc
  (`DFTInversion`/`Parseval`) with its Poisson identity.
- **THE CONTINUOUS-POISSON LEFT SIDE, as a CReal** `PoissonLHS.poisson_lhs_cv` (**axiom-free**) — the
  first brick prying at *knot 1* (constructive integration).  `finite_poisson_R` is the discrete
  shadow of Poisson but lives over the ALGEBRAIC cyclotomic ring ℚ(ζ_N) — its roots of unity are not
  reals, so it has **no literal CReal limit** (a genuine world-mismatch, stated in the header).  The
  object it shadows is the CONTINUOUS Poisson `Σ_{n∈ℤ}f(n)=Σ_{k∈ℤ}f̂(k)`, whose LEFT side is a lattice
  sum that IS a CReal.  We build it for the archetype `f(x)=1/(1+x²)` (classical identity
  `Σ_{n∈ℤ}1/(1+n²)=π·coth π`): the bilateral partial sums `P N = 1 + 2·Σ_{n=1}^{N} 1/(1+n²)` are
  rational, monotone, and Cauchy with the EXPLICIT modulus `N=2p` from the telescoping tail
  `Σ_{n>i}1/(1+n²) ≤ 1/i` (via `1/(1+n²) ≤ 1/(n(n−1)) = 1/(n−1)−1/n`, `g_tele`/`tail_tele`), fed to
  `CRealCv.cvQ_of_regular` to give `poisson_lhs : CReal` with `cvQ P poisson_lhs`.  **Honest boundary:**
  this is the SUM side only; the Fourier RIGHT side `Σ_k f̂(k)`, `f̂(k)=π·e^{−2π|k|}`, needs the
  constructive integral `f̂=∫f·e^{−2πikx}dx` (knot 1) — the next brick.  `Print Assumptions` = **Closed
  under the global context**.
- **THE CONSTRUCTIVE RIEMANN INTEGRAL of a Lipschitz function on [0,1]** `CIntegral.cintegral_cv`
  (**axiom-free**) — the CORE brick of knot 1, the tool the continuous Fourier side of Poisson, the
  Gaussian integral `∫e^{−πx²}=√π` (the `FEResidue` axiom), and the real Γ all wait on.  For
  `f : ℚ→ℚ` that is `L`-Lipschitz (integer `L`, `Hlip : |f x − f y| ≤ L·|x−y|`), the dyadic Riemann
  sums `R k = 2^{−k}·Σ_{j<2^k} f(j·2^{−k})` (`R`) are rational and Cauchy.  The engine is the
  **doubling estimate** `doubling : |R k − R(S k)| ≤ B k − B(S k)` (`B k = 2^{−k}·L/2`): one dyadic
  refinement is a `qsum`-reindex into pairs (`qsum_pair`) whose two children are `sample k j` and
  `sample k j + 2^{−(k+1)}` (`sample_even`/`sample_odd`), so each cell moves the sum by ≤ the
  Lipschitz variation `L·2^{−(k+1)}` over that cell (`qabs_qsum` + `Hlip`, with `2^k·mesh k=1` from
  `pow2_mesh`).  It **telescopes** (`tele`) to `|R i − R j| ≤ B i − B j`, giving the explicit modulus
  `N = L·p` (`R_regular`, from `B_modulus : B(L·p) ≤ 1/p` via `2^{L·p} > L·p`, `pow2_ge`).
  `CRealCv.cvQ_of_regular` then delivers `cintegral : CReal` with `cvQ R cintegral` — the value
  `∫₀¹ f`, axiom-free.  **Honest scope:** left dyadic-endpoint sums on `[0,1]` for a Lipschitz
  integrand — the constructive-integral SEED.  Improper integrals (`∫_ℝ`), higher dimension, change
  of variables and Fubini (what the Gaussian `∫e^{−πx²}` and the Mellin transform actually need)
  build ON this; they are the rest of knot 1.  `Print Assumptions` = **Closed under the global
  context**.
- **THE IMPROPER INTEGRAL ∫₀^∞ f, as a CReal** `ImproperIntegral.improper_integral_spec`
  (**axiom-free**) — the range-extension of `CIntegral`'s `[0,1]` integral, the second knot-1 rail.
  `∫₀^∞ f = Σ_{m≥0} ∫_m^{m+1} f`: each unit cell `∫_m^{m+1} f` is `cintegral` of the `m`-shifted
  integrand `shift m := t ↦ f(m+t)`, which is Lipschitz with the **same** constant `L` (translation
  preserves the bound, `shift_lip`), so it is a `CReal` (`cell m`).  The engine (`Section
  CRealSeries`, reusable) is a **summable series of CReals**: given `|cell m| ≤ Bd m` (`Hcell`) and a
  tail-summability modulus for the rational bound `Bd` (`Htail`), the partial sums `psum` are Cauchy
  (`psum_diff_bound : |psum(i+d) − psum i| ≤ Σ_{i≤m<i+d} Bd m`, by CReal triangle induction;
  `psum_cauchy`), and `ConstructiveRcomplete.CRealComplete` gives the limit `series_limit`.  The cell
  magnitudes are controlled by `CIntegral.cintegral_abs_le` (the integral is ≤ its sup on the cell,
  proved via `Rsum_abs_le` + `cvQ_le_const`/`cvQ_opp`).  Instantiated (`Section Improper`) at
  `cell m := cintegral (shift m) L …`, `Bd` a summable decay bound (`Hbd`), giving
  `improper_integral : CReal` with the convergence `improper_integral_spec`.  **Honest scope:** the
  RANGE extension (the tails), for a Lipschitz integrand with a summable cell bound; `∫_ℝ f = ∫₀^∞ f +
  ∫₀^∞ (f∘neg)`.  The remaining piece of knot 1 is the 2-D / change-of-variables step (the Gaussian
  `∫e^{−πx²}=√π`, which discharges the `FEResidue` axiom).  `Print Assumptions` = **Closed under the
  global context**.
- **A CONSTRUCTIVE π, axiom-free** `ConstructivePi.constructive_pi_cv` (**axiom-free**) — the repo's
  first constructive π.  The Wallis / central-binomial ratio `4²ⁿ(n!)⁴/((2n)!²·n)` written as the
  telescoping recursion `cπ₀=4, cπ_{k+1}=cπ_k·(1−1/(2k+3)²)` (no factorials, `mlt`/`mlt_compl`): it is
  positive (`cpi_pos`), DECREASING (each factor `<1`, `mlt_lt1`), bounded in `[π,4]` (`cpi_le4`), and
  Cauchy — the step `cπ_k−cπ_{k+1}=cπ_k/(2k+3)² ≤ 4/((2k+1)(2k+3))` telescopes (`cpi_step`, `cpi_tele`)
  to the explicit modulus `N=Pos.to_nat p` (`cpi_regular`), fed to `CRealCv.cvQ_of_regular` for
  `constructive_pi : CReal` with `cvQ cpi constructive_pi`.  Makes the **π side** of the FEResidue value
  `Γ(½)²=π` a concrete construction rather than an abstract parameter.  **Honest scope:** this is the
  Wallis limit, *classically equal* to π, taken here as its constructive definition; its identification
  with the circle / analytic π is Wallis's theorem (classical, not formalized).  `Print Assumptions` =
  **Closed under the global context**.
- **A CONSTRUCTIVE SQUARE ROOT, and a constructive √π** `ConstructiveSqrtPi.constructive_sqrt_pi_cv`
  (**axiom-free**) — stdlib's constructive reals have NO square root, so we build one: rational
  BISECTION `bis fuel lo hi a` on `[1,2]` with the explicit precision `|bis²−a| ≤ 4·(hi−lo)·(½)^fuel`
  (`bis_prec`; the `4`-from-`hi≤2` bound makes the `(½)^fuel` telescope cleanly through the recursion,
  `bis_range`).  Applied to the central-binomial π-approximants (`cpi n ∈ [2,4]`, `cpi_ge2`/`cpi_le4`),
  it gives a rational sequence `sq n = bis n 1 2 (cpi n) → √π`, in `[1,2]` (`sq_range`), with
  `|sq n² − cpi n| ≤ 4·half n` (`sq_prec`) and Cauchy (via `|sqᵢ−sqⱼ| ≤ |sqᵢ²−sqⱼ²|/2`, `sq_lip`, +
  the `half`/`cpi` moduli, `sq_regular`), fed to `cvQ_of_regular` for `constructive_sqrt_pi : CReal`
  with `cvQ sq constructive_sqrt_pi`.  **The discharge is complete:** `cvQ_sq` gives `cvQ (sq²) (√π²)`,
  the closeness `|sq n²−cpi n| ≤ 4·half n → 0` gives `cvQ (sq²) π` (`cvQ_close`), and limit uniqueness
  (`cvQ_unique`, via the `CRealQ_dense` archimedean argument) forces `gamma_half_sq_eq_pi :
  constructive_sqrt_pi² == constructive_pi`; with `gamma_half_pos : inject_Q 1 ≤ constructive_sqrt_pi`
  (via `cvQ_opp` + `cvQ_le_const`), these are exactly `FEResidue`'s value relation — so its axiom is now
  a theorem.  **Honest boundary** unchanged: `√π` is the Wallis construction; `√π = ∫e^{−πx²}` stays
  classical.  `Print Assumptions` (all) = **Closed under the global context**.
- **THE CENTRAL-BINOMIAL SANDWICH `4^M/(2M+1) ≤ C(2M,M) ≤ 4^M`** `CentralBinomialBound`
  (**axiom-free**) — the first brick toward the Chebyshev prime bound `ψ(x) ≍ x`.  Since `C(2M,M) =
  (2M)!/(M!)²`, we state it as pure ℕ factorial inequalities, avoiding binomial / Pascal / unimodality
  entirely: `central_upper : (2M)! ≤ 4^M·(M!)²` and `central_lower : 4^M·(M!)² ≤ (2M+1)·(2M)!`.  Each
  is a one-line induction — the factorial recurrence turns the step into `(2M+2)(2M+1) ≤ 4(M+1)²`
  (upper) and `2(M+1) ≤ 2M+3` (lower), closed by `nia`; spot-checked at `M=3` (`central_bounds_M3`).
  This is EXACTLY the numerical input the contour-free Chebyshev bound needs: with `D(N) = log(N!) −
  2·log(⌊N/2⌋!) = log((2M)!/(M!)²)`, these give `(log2)·N − log(N+1) ≤ D(N) ≤ (log2)·N`, i.e. `D(N) ≍
  N` — the estimate that, with `Chebyshev.order_swap_identity` (`Σ_{n≤N}log n = Σ_{d≤N}Λ(d)⌊N/d⌋`) and
  the `T(N)−2T(⌊N/2⌋)` squeeze, yields `ψ(x) ≍ x`.  **Honest scope:** this bound is axiom-free (pure
  ℕ); the *Chebyshev assembly on top* (the squeeze + dyadic telescoping) uses `ln`/ℝ and so will be
  quarantined — and `ψ ≍ x` is the Chebyshev BOUND, not the PNT `ψ ~ x`.  `Print Assumptions` = **Closed
  under the global context**.
- **THE ALGEBRAIC NYQUIST–SHANNON BRIDGE** `BandlimitedInterp.nyquist_sampling` (**axiom-free**) —
  the first genuine *discrete→continuous* sampling theorem that lands **below** the classical-ℝ
  quarantine, via the isolation *bandwidth = polynomial degree*.  A signal band-limited to
  bandwidth `N` is a degree-`<N` polynomial (`qdegle p (N-1)`); the theorem's two halves, over the
  full evaluation continuum ℚ (every `x:Qc`): **(uniqueness / anti-aliasing)** `sampling_unique` —
  two band-limited signals agreeing at more than their degree-many distinct nodes agree
  **everywhere** (the samples pin the whole function), a one-step consequence of the ℚ[X]
  polynomial identity theorem `QPolyPIT.poly_roots_eval` applied to their difference
  (`qdegle_qsub`); **(existence / reconstruction)** `sampling_reconstruct` — for any distinct
  nodes and prescribed sample values there is such a signal, built by an explicit **Newton
  incremental interpolant** `newton` (each new node adds a correction `c·∏(X−bⱼ)` that vanishes on
  the earlier nodes and, via the field inverse at the nonzero `∏(a−bⱼ)` — `pprod_ne`,
  `Qcmult_inv_l` — hits the new sample), with the sharp degree bound `newton_degle` (`N` nodes ⟹
  degree ≤ `N−1`).  `sampling_alias` is the constructive contrapositive (the offending node is
  found by finite search on `Qc`'s decidable equality, `Forall_Exists_dec` — no classical logic).
  Built entirely on the axiom-free ℚ[X] tower (`QPoly`/`QPolyDiv`/`QPolyMul`/`QPolyRoot`/`QPolyPIT`
  over `Qc`), so `Print Assumptions nyquist_sampling` = **Closed under the global context**.  The
  algebraic **sibling** of the finite trigonometric `WalshSampling` (same principle — #samples =
  bandwidth, undersampling aliases, discrete data fixes a continuum — needing no complex analysis).
  **Honest scope:** the ALGEBRAIC (polynomial-degree) Nyquist; the genuine *trigonometric* Nyquist
  on `T=ℝ/ℤ` (band-limited = Fourier support in `[−N,N]`) needs a constructive Fourier analysis
  over ℝ (constructive trig, improper integrals, L²) the repo does not build — `RootsOfUnity.w`/
  `EulerFormula.Cexp` are classical `cos`/`sin`, and the only integral present is `FourierRL`'s
  bounded `RiemannInt`.  The continuum here is ℚ, not the completed ℝ.  This is **rung 1** of the
  discrete→continuous isolation ladder documented in `docs/BRIDGES.md`.
- **AN AXIOM-FREE PRIMITIVE N-th ROOT OF UNITY** `QPolyQuot` (**axiom-free**) — the algebraic ζ that
  replaces the transcendental `RootsOfUnity.w N = cos(2π/N)+i·sin(2π/N)` (which carries the
  classical-ℝ quarantine axioms via `ComplexField`).  Working in the cyclotomic quotient
  `R = ℚ[x]/(Φ_N)`, presented as a **setoid on `qpoly`** with equality `req a b := Φ_N | (a−b)` (the
  repo's `qdivides` is functional, which makes the quotient laws cheap), we prove `zeta_pow_N`
  (ζ^N=1), `zeta_pow_sub_unit` (**ζ^m−1 is a UNIT for 0<m<N**), `zeta_primitive` (ζ^m≠1), `wc_w_1`
  (the inverse root ζ^{N−1}), and `one_neq_zero_R`.  The crux — primitivity needs **NO irreducibility
  of Φ_N**: the unit ζ^m−1 comes from Bézout coprimality of Φ_N and X^m−1, which follows from `X^N−1`
  being SQUAREFREE (`QPolySqfree.qsqfree_Xn1`) via the factorisation `X^N−1 = Φ_N·D_N` and
  `qsqfree_mul_copr`, plus the gcd descent `d|X^m−1 ⇒ d|X^{gcd(m,N)}−1 | D_N` (general N, via
  `Xn1Gcd.pdiv_gcd` + the `divisors g ⊆ properdivs N` sublist-product argument).  `Print Assumptions`
  = **Closed under the global context**.
- **ROOTS-OF-UNITY ORTHOGONALITY at ζ** `CycloOrthogonality.{cyclo_orth_vanish,r_orthogonality}`
  (**axiom-free**) — the fact the whole DFT rests on, proved at ζ **without** instantiating the
  abstract-field `AlgebraicOrthogonality.algebraic_orthogonality` (which needs a field / Φ_N
  irreducible).  Instead the vanishing branch cancels by the EXPLICIT unit ζ^m−1 (Stage-1
  `zeta_pow_sub_unit`) in the geometric identity `(ζ^m−1)·Σ_{k<N}ζ^{km}=ζ^{mN}−1≡0`.  Ships a small
  `req` congruence toolkit (`req_refl/sym/trans`, `req_qmul`, `req_qadd`, `req_rpow`, `req_rsum`).
  `Print Assumptions` = **Closed under the global context**.
- **THE DISCRETE FOURIER CLUSTER, DE-QUARANTINED** (**axiom-free**) — the ζ from `QPolyQuot` + the
  orthogonality from `CycloOrthogonality` give axiom-free algebraic companions, added **in-place**
  alongside the (necessarily quarantined) classical-ℂ theorems: `DFTInversion.dft_inversion_R`
  (F⁻¹F = id), `DFTConvolution.conv_theorem_R` (the DFT diagonalises cyclic convolution), and
  `FinitePoisson.finite_poisson_R` (`Σ_{r<m} DFT_R(dm) f(r·d) = m·Σ_{a<d} f(a·m)`).  Each carries the
  `req`-level finite-sum plumbing it needs (`rsum` swap/scale/delta/reindex, a fold↔permutation
  bridge, root periodicity, the two-index `orthogonality_2_R`, and — for finite Poisson — a
  generic-length geometric orthogonality with the generalized unit `zeta_sub_unit_gen`).  All three
  `Print Assumptions` = **Closed under the global context**.  **Honest boundary:** the *identities*
  port, but `Parseval.parseval_norm`/`plancherel` POSITIVITY (`|·|²≥0`) and `GaussSum`/
  `QuadraticGaussSum` absolute values (`|g|²=p`) are **Archimedean** — ℚ(ζ_N) is not ordered — and
  stay quarantined.  The C `dft_inversion`/`conv_theorem`/`finite_poisson` remain as the classical
  companions (`C=ℝ×ℝ` inherently carries the axioms; a refactor cannot make *them* axiom-free).
- **Product formula over ℚ** `ProductFormulaQ.product_formula` (`_int` + `_Q`): Ostrowski's
  `∏_v |x|_v = 1` for nonzero rationals — for a positive integer `n`, `n = ∏_p p^{v_p(n)}`
  (via `code_surj`) so `|n|_∞·∏_p |n|_p = 1`; for `a/b` the quotient of the two integer
  instances. **Axiom-free** — genuine, because for a *rational* input `|x|_∞` is itself rational
  (a ratio of coded integers), so no ℝ is constructed. This is the honest **adelic bridge**:
  finite valuations determine archimedean size *on rational points*. It does **not** build
  `ℝ=ℚ_∞` (the completion at `∞`, a separate factor `𝔸_ℚ=ℝ×𝔸_f` orthogonal to the profinite
  tower `∏_p ℤ_p=lim ℤ/nℤ`); Γ-factors, `ξ(s)`, the functional equation, and ζ special values
  (π²/6) are archimedean-local and stay out of reach — the file's closing note pins where the
  quarantined Reals axioms would re-enter (Cauchy/Dedekind completion).
- **Profinite completion, explicit** `ProfiniteCRT.profinite_crt`: the finite/non-archimedean
  factor `𝔸_f` of `𝔸_ℚ = ℝ × 𝔸_f`, machine-checked as (1) the **CRT ring iso**
  `ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ` (coprime `m,n`) — `crt_iso` with explicit Bézout reconstruction
  inverting the reduction pair, `crt_roundtrip` closing the round-trip via `Gauss`, reduction a
  ring hom (`Zplus_mod`/`Zmult_mod`); and (2) the **inverse system** `Ẑ = lim_n ℤ/nℤ` — commuting
  projections (`proj_compat`), the prime-power tower `ℤ/p^{k+1}→ℤ/pᵏ` (`tower_proj`), directedness
  (`system_directed`). **Axiom-free**: built from finite discrete data. Iterating CRT over
  `n=∏_p p^{v_p}` gives `Ẑ ≅ ∏_p ℤ_p`. Honest ceiling (same as ProductFormulaQ): this is the
  finite factor only; `ℝ=ℚ_∞` (the archimedean completion, hence Γ-factors/`ξ(s)`/functional
  equation/ζ special values) is the separate factor it never reaches.
- **THE 2-ADIC INTEGERS ARE A CANTOR SET — the first continuum-cardinality result**
  `PadicUncountable.Zp2_uncountable` (**axiom-free**): **no map `ℕ → ℤ₂` is surjective**, i.e.
  `|ℤ₂| > ℵ₀ = |ℚ|`.  Wires the repo's existing p-adic carrier (`PadicIntegers.Zp` at `p=2` — the
  inverse limit `lim ℤ/2ⁿ` of coherent residue sequences) to **Cantor's diagonal** (proved
  abstractly on `A→Prop` as `category-topos/CategoryInterval.cantor`; here its Boolean/Turing
  instance `stream_uncountable`).  At `p=2` the p-adic integers **are** the Cantor space: a binary
  stream `ℕ→bool` is exactly a coherent 2-adic residue sequence, giving the injection
  `{0,1}^ℕ ↪ ℤ₂` (`ofbits`, `ofbits_inj`) with its digit-reading retraction (`bit`, `bit_ofbits`);
  Cantor's `¬ f x x` is then run on the 2-adic digits (`Zp2_uncountable`).  Because the digits are
  `bool` (discrete-branching), the diagonal stays **pointwise/constructive** — no functional
  extensionality, no classical axiom — so `Print Assumptions` = **Closed under the global context**.
  This is the **cardinality shadow of the discrete↔continuous quarantine wall**: ℤ₂ and `ℝ=ℚ_∞` are
  the two completions of the countable ℚ, and both jump to the continuum `2^ℵ₀`; the 2-adic jump is
  proved outright here (axiom-free), while the archimedean jump is exactly what forces ℝ behind the
  quarantined classical axioms.  (Contrast `InvLimit.InvLim`, proved to be the *countable* `ω+1`.)
- **ℵ₀ < 𝔟 ≤ 𝔡 — cardinal invariants on the convergence modulus** `DominatingModulus`
  (**axiom-free**): the first cardinal characteristics of the continuum strictly *inside* `(ℵ₀, 𝔠]`
  (the endpoints being ℵ₀ from the countability engines and `𝔠 = |ℤ₂|` from `PadicUncountable`).  A
  `CReal` (`CRealCv.cvQ_of_regular`) carries an explicit Cauchy **modulus** `precision ↦ index`
  (≅ ℕ→ℕ); the eventual-domination order `f ≤* g := ∃N,∀n≥N, f n ≤ g n` on these moduli is the order
  the **bounding** number 𝔟 (least ≤*-unbounded family) and **dominating** number 𝔡 (least ≤*-cofinal
  family) live on.  `countable_family_bounded` — every countable family `{fᵢ}` is dominated by one
  `g` (the windowed-max diagonal `g n = 1 + max_{i≤n} fᵢ n`) — gives **ℵ₀ < 𝔟**; `no_countable_
  dominating` gives **ℵ₀ < 𝔡** (the strictly-larger gauge `S∘g` escapes any countable dominating
  family).  Same "escape past every listed function" as Cantor's diagonal (which gave the top
  endpoint), now on the modulus order; reading: no countable set of convergence gauges converges
  every CReal.  `Print Assumptions` = **Closed under the global context**.  (Coq can't decide the
  *values* 𝔟, 𝔡 — that needs forcing — only the ZFC-provable `> ℵ₀` backbone.)
- **THE CICHOŃ DIAGRAM AS A FINITE POSET** `CichonPoset.cichon_poset` (**axiom-free**): the diagram
  of cardinal characteristics of the continuum (`ℵ₁, add(𝒩), add(ℳ), cov(𝒩), cov(ℳ), non(𝒩),
  non(ℳ), 𝔟, 𝔡, cof(ℳ), cof(𝒩), 𝔠`) as a genuine finite partial order.  The 12 nodes (`Node`) and
  the **15 covering arrows** (`arrow`, the ZFC-provable `≤` edges) generate the order `cle` = their
  reflexive-transitive closure; `cichon_poset` proves it **reflexive, transitive, and ANTISYMMETRIC**
  (antisymmetry via a `rank` linear extension — every arrow strictly increases rank, so a 2-cycle is
  impossible).  It is genuinely PARTIAL, not a chain: `covN_addM_incomparable` shows `cov(𝒩) ⊥
  add(ℳ)`, certified by an **up-set** (`upCovN` — an Alexandrov open in the sense of
  `PosetTopology.Op`) that contains one but not the other, `cle` propagating membership upward
  (`cle_up`).  Repo ties: `bottom` (`ℵ₁` is least) and `top` (`𝔠` is greatest) are the endpoints —
  `𝔠 = 2^ℵ₀ = |ℤ₂|` from `PadicUncountable`, `ℵ₀ < everything` from the diagonals — and the interior
  edge `b_le_d` (`𝔟 ≤ 𝔡`) is exactly the `DominatingModulus` pair.  So the whole cardinality arc is a
  poset with ℵ₀ below the bottom, `𝔠 = |ℤ₂|` at the top, and 𝔟, 𝔡 pinned `> ℵ₀` in the interior.
  `Print Assumptions` = **Closed under the global context**.
- **Local–global compatibility** `LocalGlobalCompat` (`fabs_is_recip` + `local_global_compat`):
  the valuation description of `𝔸_f` (`ProductFormulaQ.fabs = ∏_p |·|_p`) and the ring
  description (`ProfiniteCRT`: `Ẑ = lim ℤ/nℤ = ∏_p ℤ_p`) read the **same** exponents. Global:
  `fabs ps ks == /inject_Z(code ps ks)` (`∏_p |n|_p = 1/n`). Local: for `n = code (p::ps')(k::ks')`,
  the CRT-split modulus `p^k` (ring component `ℤ/p^{v_p}ℤ`) is the reciprocal of the local abs
  value `|n|_p = p^{−v_p}` that `fabs` peels off — same `k = v_p(n)`. **Axiom-free.** The
  non-archimedean local–global principle; `ℝ=ℚ_∞` stays the separate archimedean factor.
- **Custom complex field** `ComplexField.complex_field_axioms`: `C = ℝ[i] = ℝ×ℝ` with **every
  complex-number axiom proved as a theorem** (field laws — `ring`/`field` registered; `i²=−1`;
  `c = Re+i·Im`; `ℝ↪C` injective ring hom; conjugation involution/hom; `c·c̄ = |c|² ≥ 0`).
  Deliberate replacement for an opaque/external `C`: `Print Assumptions` = **exactly** the two
  quarantined classical-`ℝ` axioms (`sig_forall_dec`, `functional_extensionality_dep`), so **no
  new axiom** enters — the "complex axioms" are Qed lemmas, not assumptions. Genuine field;
  footprint = R. **Weak/strong layering** `ComplexField.ring_core_generalization`: the `Im·Im`
  coupling is parameterised as `i²=δ` (`Cmulg δ`); the **ring core is genuine for every δ**
  (`Cring_theory_g` — `ℝ[e]/(e²=δ)` a commutative ring, no use of `−1`), `i²=−1` (`Ci_sq`) is a
  *downstream* `δ=−1` fact (via `Cig_sq`: `e²=δ`), and the **field cap** adds the *single* honest
  hypothesis `δ<0` (`Cnorm2g_pos`, nonzero norm-form off `0`). Trichotomy `δ<0/=0/>0` =
  complex/dual/split-complex. Same footprint (2 axioms); refactor keeps all public names, so the
  ~15 downstream `C`-files compile unchanged.
- **Bridge into ℤ — Gaussian integers** `GaussianIntegers.gaussian_integers`: the same parametric
  ring core run over `ℤ`, `ZI = ℤ[e]/(e²=δ) = ℤ×ℤ`, and over `ℤ` it is **AXIOM-FREE** ("Closed under
  the global context") — strictly cleaner than the `ℝ` version. Weak ring core for every `δ`
  (`ZIring_theory_g`); `i²=−1` a downstream `δ=−1` fact. **The bridge is the multiplicative norm**
  `N_δ:ZI→ℤ`, `N_δ(a)=Re²−δ·Im²`, a genuine ring→ℤ homomorphism `N_δ(a·b)=N_δ(a)·N_δ(b)`
  (`ZInorm_mul`) with `a·conj a = N_δ(a)` (`ZImulg_conj`). Gaussian case: `ℤ↪ZI` ring hom, and the
  **units = norm-1 elements = {1,−1,i,−i}** (`unit_norm` + `gaussian_units` + `norm1_unit`), all
  genuine theorems. Arithmetic shadow of `ComplexField`; `δ<0/=0/>0` = Gaussian/dual/split integers.
  Entry point for sums-of-two-squares / Gaussian-prime number theory.
- **ℤ[i] is a Euclidean domain** `GaussianDivision.ZI_euclid` (**axiom-free**): the cornerstone of
  unique factorisation in `ℤ[i]`. For `b ≠ 0` there exist `q, r` with `a = q·b + r` and
  `N(r) < N(b)`. Construction: `znear` rounds each rational coordinate of `a·conj(b)/N(b)` to the
  nearest integer (`znear_spec`: `|x − q·d| ≤ d/2`, via `Z.div_mod` + `nia`); then
  `r·conj(b) = (X−qx·d, Y−qy·d)` coordinatewise, so `N(r)·d = N(r·conj b) = (X−qx d)²+(Y−qy d)² ≤
  d²/2 < d²` (using `ZInorm_mul`, `ZInorm_conj`, `ZImulg_conj`), giving `N(r) < N(b)`. Closed under
  the global context. **Next:** gcd/Euclidean algorithm, Bézout, irreducible=prime, unique
  factorisation, and the Gaussian-prime classification — the ℤ[i] engine the general Jacobi
  identity `r₂(n)=4·S(n)` needs.
- **ℤ[i] divisibility, gcd and Bézout** `GaussianGCD.ZI_bezout` (**axiom-free**): divisibility
  `ZIdvd a b := ∃c, b=a·c` (with `refl`/`trans`/`add`/`sub`/`mul_r`/`0` lemmas), and the **Bézout
  property**: every pair `x,y` has a gcd `g = u·x + v·y` that divides both `x` and `y` and is divided
  by every common divisor. Proved by **well-founded induction on `N(y)`** (the Euclidean algorithm
  `gcd(x,y)=gcd(y, x mod y)` via `ZI_euclid`), with no recursive `gcd` function — the norm decrease
  from `GaussianDivision` powers the recursion. Closed under the global context. **Next:** Euclid's
  lemma (irreducible ⇒ prime) from Bézout, then existence + uniqueness of factorisation, then the
  Gaussian-prime classification.
- **ℤ[i] units, associates, Euclid's lemma** `GaussianIrreducible.ZI_euclid_lemma` (**axiom-free**):
  units = norm-1 elements = `{1,−1,i,−i}` (`ZIunit_norm`, `ZIunit_cases`); ℤ[i] is an **integral
  domain** (`ZI_no_zero_div`, `ZImul_cancel_l`) since the norm is multiplicative and `N(z)=0 ⟺ z=0`;
  associates via units, with mutual divisibility of nonzero elements ⟹ associate
  (`dvd_antisym_assoc`). **Euclid's lemma**: for `p` irreducible, `p | a·b ⇒ p | a ∨ p | b` — proved
  **constructively** from Bézout: `g = gcd(p,a) = u·p+v·a` and `g | p`, so `p = g·k` gives (unit `g`)
  or (unit `k`) — the split is on the *factorisation*, not on decidability of `p|a`; unit `k` ⟹ `p ~ g
  | a`, unit `g` ⟹ `1 = U·p + V·a` ⟹ `p | b`. This is the uniqueness half of unique factorisation in
  ℤ[i]. Closed under the global context. **Next:** existence of factorisation (norm induction), then
  the Gaussian-prime classification.
- **ℤ[i] factorisation existence** `GaussianFactorization.factor_exists` (**axiom-free**): every
  nonzero non-unit is a product of irreducibles. Constructive: the nearest-integer quotient is
  **exact** when `a | z` (`ZIdiv_exact`, since `znear(c·d, d)=c`), so **divisibility is decidable**
  (`ZIdvdb`/`ZIdvd_dec`) with no search; a **bounded box search** over `{N(a) ≤ N(z)}`
  (`gbox`/`pdiv_list`) then either returns a proper divisor (`1 < N(d) < N(z)`) or certifies
  irreducibility (`pdiv_nil_irreducible` — the disjunction `unit a ∨ unit b` for `z=a·b` comes from
  deciding `N(a)=1`, not excluded middle). Strong induction on `N` splits `z = d·(z/d)` into two
  smaller non-units and concatenates their factor lists. Together with Euclid's lemma this is
  **unique factorisation in ℤ[i]**. Closed under the global context. **Next:** the Gaussian-prime
  classification (`2` ramifies, `p≡1 (4)` splits, `p≡3 (4)` inert).
- **Gaussian-prime classification** `GaussianPrimes.gaussian_prime_classification` (**axiom-free**):
  the engine `norm_prime_irreducible` (if `N(π)` is a rational prime then `π` is irreducible, since
  `N(π)=N(a)·N(b)` forces a norm-1 factor), and the three cases over a rational prime: **`2`
  ramifies** — `2 = (1+i)(1−i)` with `1+i` a Gaussian prime of norm 2 (`two_ramifies`/`two_eq`);
  **`p≡1 (4)` splits** — `p = a²+b² = (a+bi)(a−bi)` via Fermat (`sum2_prime1`), with `a+bi` a
  Gaussian prime of norm `p` (`prime1_splits`); **`p≡3 (4)` inert** — `p` stays a Gaussian prime of
  norm `p²` (`prime3_inert`), because a factor of norm `p` would make `p` a sum of two squares,
  impossible for `p≡3 (4)` (via `prime_mult` + `two_squares_iff` — `q3even p` fails as `p` divides
  itself to the odd power 1). This completes the ℤ[i] arithmetic engine (Euclidean division → gcd →
  Bézout → Euclid's lemma → unique factorisation → prime classification) that the general Jacobi
  identity `r₂(n)=4·S(n)` builds on. Closed under the global context.
- **ℤ[i] coprime split** `GaussianCoprime.gaussian_split` (**axiom-free**): the surjectivity core of
  r₂-multiplicativity. If `N(z)=m·n` with `gcd(m,n)=1` then `z=x·y` with `N(x)=m`, `N(y)=n`. Take
  `x = gcd_{ℤ[i]}(z, m)` (`ZI_bezout`); then `N(x) | m` two ways — `N(x) | N(z)=mn` and `N(x) |
  N(m)=m²` give `N(x) | gcd(mn,m²)=m` (`Z.gcd_mul_mono_l` + the `Nat.gcd`→`Z.gcd` bridge `nat_gcd_Z`);
  and **conjugating the Bézout identity** `x = u·z + v·m` shows `(m) | x·conj(x) = ZtoZI(N x)` — the
  cross term carries `z·conj z = m·n` — so `m | N(x)` (`ZtoZI_dvd`, off the real coordinate). Hence
  `N(x)=m` and `y=z/x` has norm `n`. Closed under the global context. **Next:** the 4-to-1 count
  `r₂(m)·r₂(n)=4·r₂(mn)` (each norm-`mn` element has exactly 4 splits — its unit orbit), then the
  multiplicative-agreement assembly for the full `r₂(n)=4·S(n)`.
- **r₂ is multiplicative (up to 4)** `R2Multiplicative.r2_mult` (**axiom-free**): `gcd(m,n)=1 ⇒
  r₂(m)·r₂(n) = 4·r₂(mn)`. Via `r₂(n)=#{N(z)=n}` (`Lnorm`), the product map `(x,y)↦x·y` on
  norm-`m`×norm-`n` pairs is **surjective** onto norm-`mn` elements (`gaussian_split`) and exactly
  **4-to-1**: every fibre is the unit orbit `{(x₀·u, y₀·conj u) : u∈units}` of size 4
  (`fiber_length_4`), because a second split `x·y=x₀·y₀` with matching norms forces `x~x₀` — `x`, `y₀`
  are ℤ[i]-coprime (their norms `m`, `n` are coprime, so their gcd has norm 1) so `x | x₀·y₀ ⇒ x | x₀`
  via Bézout (`split_unique`). A generic key-partition count (`count_by_key`: every fibre size `c` ⇒
  `|domain|=c·|image|`) then gives `r₂(m)·r₂(n) = |norm-m × norm-n| = 4·|norm-mn| = 4·r₂(mn)`. Closed
  under the global context. **This completes both multiplicativity facts** (`S_mult`, `r2_mult`) and
  all prime-power values on both sides; the general `r₂(n)=4·S(n)` now needs only the
  multiplicative-agreement assembly over the prime factorisation.
- **JACOBI'S TWO-SQUARE FORMULA** `R2Jacobi.jacobi_two_squares` (**axiom-free**): for `n ≥ 1`,
  `r₂(n) = 4·(d₁(n) − d₃(n))` — the exact count of representations `n = a²+b²` equals four times the
  excess of divisors `≡1` over divisors `≡3 (mod 4)`. The **multiplicative-agreement assembly**:
  `r₂` and `4·S` agree on prime powers (`r2_ppow_eq_4S`, casing `2`/`p≡1`/`p≡3` against `r2_2pow`/
  `r2_1pow`/`r2_3pow` and `S_prime_pow_*`), and both `r₂` and `S` are multiplicative on coprimes
  (`r2_mult`, `S_mult`), so by strong induction peeling one prime power `p^v ∥ n` (`nat_padic`,
  `gcd_pow_coprime`): `4·r₂(n) = r₂(p^v)·r₂(m') = (4·S(p^v))·(4·S(m')) = 16·S(n)`, giving
  `r₂(n) = 4·S(n) = 4·(d₁−d₃)` (`jacobi_full` + `S_as_d1d3`). This is the genuine classical theorem,
  machine-checked with **zero axioms**, resting on the full ℤ[i] unique-factorisation tower
  (`GaussianDivision`…`GaussianCoprime`), the three prime-power counts, and both multiplicativities.
  Closed under the global context. The `vm_compute` check `jacobi_upto` (n ≤ 200) is now a corollary,
  not the evidence.
- **Legendre symbol + Euler's criterion** `LegendreSymbol` (**axiom-free**, QR brick 1): the
  foundation for quadratic reciprocity. Defines `(a/p) : ℤ` (`0` if `p∣a`, else `±1` by whether
  `a^((p-1)/2) ≡ 1`), and proves **Euler's criterion** `a^((p-1)/2) ≡ (a/p) (mod p)`
  (`legendre_euler`) — the half-power `pw p a ((p-1)/2)` squares to `a^(p-1)=1` (Fermat), so is `1`
  or `p-1` (`euler_pm1`, via `sqrt1`). Plus **complete multiplicativity** `(ab/p)=(a/p)(b/p)` on units
  (`legendre_mult_unit`): both sides are `±1` congruent mod `p` to `pw a·pw b` (Euler + `pw_mul_base`),
  and a sign is pinned by its residue mod an odd prime (`sign_mod_inj`). Reuses `fermat`, `sqrt1`,
  `unit_not_div`, `not_div_pow`, `pw_add`. Closed under the global context. **Next (QR bricks 2–5):**
  Gauss's lemma `(a/p)=(-1)^μ`, Eisenstein's `⌊ka/p⌋`-sum refinement, the lattice-point count, and
  the assembly `(p/q)(q/p)=(-1)^(((p-1)/2)((q-1)/2))`.
- **Gauss's lemma** `GaussLemma.legendre_gauss` (**axiom-free**, QR brick 2): `(a/p) = (-1)^μ`, where
  `μ = #{ k ∈ [1,(p-1)/2] : (k·a) mod p > (p-1)/2 }` (`mu`). The combinatorial heart: the
  least-absolute residues `fres k` of `a, 2a, …, ((p-1)/2)a` are a **permutation** of `1..(p-1)/2`
  (`fres_perm` — injective since `fres i = fres j` forces `i≡±j` and `i+j<p` rules out the minus,
  via `cancel_mod`), so taking the product mod `p`, `a^((p-1)/2)·((p-1)/2)! ≡ (-1)^μ·((p-1)/2)!`
  (`prod_res_val`/`prod_res_sign`), and cancelling the unit `((p-1)/2)!` (`fact_coprime`) gives
  `a^((p-1)/2) ≡ (-1)^μ`, hence `(a/p)=(-1)^μ` by Euler's criterion + `sign_mod_inj`. Uses a reusable
  `Zprod` (product-over-list) layer with permutation-invariance, sum-over-product, and sign-count
  lemmas. Closed under the global context. **Next (QR bricks 3–5):** Eisenstein's `μ ≡ Σ⌊ka/p⌋
  (mod 2)`, the lattice-point count, and the assembly.
- **Eisenstein's refinement** `EisensteinLemma.legendre_eisenstein` (**axiom-free**, QR brick 3): for
  an odd prime `p` and an **odd** unit `a`, `(a/p) = (-1)^(Σ_{k=1}^{(p-1)/2} ⌊k·a/p⌋)`. From the
  division identity `k·a = p·⌊k·a/p⌋ + (k·a mod p)` summed over `k` (`eis_div`), the permutation
  `Σ fres = Σ k` (`eis_perm`), and the residue split `Σ res + 2U = Σ fres + p·μ` (`eis_res`), one gets
  `(a-1)·Σk + 2U = p·(Σ⌊⌋ + μ)`; with `a`, `p` odd this forces `2 | (Σ⌊⌋ + μ)`, i.e. `μ ≡ Σ⌊k·a/p⌋
  (mod 2)` (`eis_parity`), so Gauss's `(a/p)=(-1)^μ` becomes `(-1)^(Σ⌊⌋)`. Adds a reusable `Zsum`
  (sum-over-list) layer. Closed under the global context. **Next (QR bricks 4–5):** the lattice-point
  count `Σ⌊kq/p⌋+Σ⌊kp/q⌋ = ((p-1)/2)((q-1)/2)` and the assembly.
- **Lattice-point count** `ReciprocityCount.reciprocity_count` (**axiom-free**, QR brick 4): for
  distinct odd primes `p,q`, `fsum p q + fsum q p = ((p-1)/2)·((q-1)/2)`, where `fsum p q =
  Σ_{k=1}^{(p-1)/2} ⌊k·q/p⌋`. Pure elementary counting over ℕ/lists: the lattice points `(k,j)` in
  `[1,(p-1)/2]×[1,(q-1)/2]` split into **below** (`p·j < q·k`) and **above** (`q·k < p·j`) the line
  `q·x = p·y`, with *no* point on it (`p ∤ q·k` for `k ≤ (p-1)/2`, `p≠q`, via `p_ndvd`). Each row
  count `#{j : p·j < q·k}` is exactly `⌊k·q/p⌋` (`count_row`: `p·j<q·k ↔ j ≤ ⌊q·k/p⌋`, and
  `⌊q·k/p⌋ ≤ (q-1)/2`); summing rows (`count_list_prod`) gives `below = fsum p q`, the transpose
  (`count_transpose`) gives `above = fsum q p`, and `below`+`above` partition the box
  (`filter_length`). Self-contained list layer. Closed under the global context. **Next (QR brick
  5):** apply Eisenstein twice and multiply.
- **THE LAW OF QUADRATIC RECIPROCITY** `QuadraticReciprocity.quadratic_reciprocity` (**axiom-free**,
  QR brick 5 / capstone): for distinct odd primes `p, q`,
  `(q/p)·(p/q) = (-1)^(((p-1)/2)·((q-1)/2))`. Assembled in a few lines: Eisenstein's refinement gives
  `(q/p) = (-1)^(Σ⌊kq/p⌋)` and `(p/q) = (-1)^(Σ⌊kp/q⌋)` (the two floor sums `Tsum`/`fsum` coincide
  definitionally), their product is `(-1)^(Σ⌊kq/p⌋ + Σ⌊kp/q⌋)`, and the lattice-point count
  (`reciprocity_count`) makes the exponent `((p-1)/2)·((q-1)/2)`. To let the numerator exceed the
  modulus, the whole Euler/Gauss/Eisenstein layer was generalized from `1≤a≤p-1` to `~ p∣a`
  (`fermat_gen`). Gauss's-lemma proof of Gauss's reciprocity, machine-checked with **zero axioms** —
  a landmark classical theorem, resting on Fermat/`sqrt1`/order machinery (bricks 1–2), the
  Eisenstein floor identity (brick 3), and a pure lattice-point double-count (brick 4). Closed under
  the global context. The **two supplements** are also proved (`first_supplement`,
  `second_supplement`): `(-1/p) = legendre p (p-1) = (-1)^((p-1)/2)` (Euler's criterion + `-1 ≡ p-1`,
  via `Zpow_mod_cong`); and `(2/p) = (-1)^((p²-1)/8)` (Gauss's lemma at `a=2`: the count `mu p 2 =
  (p-1)/2 − ((p-1)/2)/2` (`mu_two`) has the same parity as `(p²-1)/8 = h(h+1)/2` (`parity_h`, via the
  `2x mod 4` / `mod 4` bridge)). All axiom-free — quadratic reciprocity and both supplements are
  complete.
- **Euclid: infinitely many primes** `EuclidPrimes.euclid_primes` (**axiom-free**, Dirichlet brick 1):
  for every `m` there is a prime `p > m`. Classic argument over `nat`: `m! + 1` has a prime divisor
  `p` (`nat_prime_divisor`, via `has_prime_divisor` + the `Z`↔`nat` bridge `Zdiv_nat`); if `p ≤ m`
  then `p | m!` (`divide_fact`) and `p | m!+1`, so `p | 1` (`Nat.divide_sub_r`), absurd. The
  foundation for the arithmetic-progression results. Closed under the global context.
- **The order lemma → primes ≡ 1 (mod n)** `OrderPrimeMod.order_prime_mod` (**axiom-free**,
  Dirichlet brick 2): if a prime `q` divides `a^n − 1` but divides **no** `a^d − 1` for any proper
  divisor `d | n` (`d < n`), then the multiplicative order of `a` mod `q` is exactly `n`, hence
  `n | q − 1`, i.e. `q ≡ 1 (mod n)`. Proof reduces `a` to `r = a mod q ∈ [1,q−1]` (`~q∣a`), turns
  `q | x−1` into `x ≡ 1 (mod q)` (`dvd_pred_iff`), so `q | a^k−1 ↔ pw q r k = 1` (`pw_a_pow`,
  base-invariance of the residue power); then `ord_divides` forces `ord q r | n`, `ord_period` +
  the "no proper divisor" hypothesis rules out `ord q r < n`, so `ord q r = n`, and `ord_div_pm1`
  gives `n | q−1`. The arithmetic core of "infinitely many primes ≡ 1 (mod n)"; the remaining piece
  is a cyclotomic `Φ_n` supplying, for each `n`, an integer with a primitive prime divisor.
- **Integer polynomials ℤ[X]** `IntPoly` (**axiom-free**, Dirichlet brick 3a — cyclotomic
  foundation): polynomials as `list Z` (low degree first), with the **evaluation homomorphism** —
  `eval` commutes with `padd` (`eval_add`), `pscale` (`eval_scale`), `pmul` (`eval_mul`) and sends
  `pmonom n` to `X^n` (`eval_monom`). Semantic divisibility `pdivides p q := ∃r, ∀x, eval q x =
  eval p x · eval r x` (reflexive, transitive). Delivers the **geometric divisibility**
  `Xn1_dvd : m | n → pdivides (X^m−1) (X^n−1)` with an **explicit integer cofactor** `geo m k =
  1 + X^m + ⋯ + X^{(k−1)m}` (via the telescoping `(X^m−1)·geo m k = X^{mk}−1`, `geo_telescope`),
  and its evaluated form `Xn1_dvd_val : m | n → (a^m−1 | a^n−1)` in ℤ. This is the reusable base the
  cyclotomic `Φ_n` and the product identity `∏_{d|n} Φ_d = X^n−1` will be built on. Closed under the
  global context.
- **Dirichlet, the case n = 4** `DirichletMod4.dirichlet_1_mod_4` (**axiom-free**): a genuine
  arithmetic-progression theorem — **infinitely many primes ≡ 1 (mod 4)**: for every `m` there is a
  prime `q > m` with `q mod 4 = 1`. Fully elementary via `x²+1` and the order lemma: set `a = 2·m!`,
  `N = a²+1`; a prime divisor `q` of `N` (from `EuclidPrimes.nat_prime_divisor`) is `> m` (else
  `q | m! | a` and `q | a²+1` give `q | 1`), odd (`N` is odd as `a` is even), divides `a⁴−1 =
  (a²+1)(a²−1)`, and divides neither `a`, `a²−1`, nor `a−1` (each would force `q | 2`, so `q = 2`).
  Hence `order_prime_mod` makes `ord_q(a) = 4`, so `4 | q−1`, i.e. `q ≡ 1 (mod 4)`. The first
  complete Dirichlet-type theorem here (the general-`n` version awaits the cyclotomic `Φ_n`). Closed
  under the global context.
- **Monic division in ℤ[X]** `PolyDiv.monic_div` (**axiom-free**, Dirichlet brick 3b — cyclotomic
  foundation): Euclidean division by a MONIC polynomial — for any `f` and any monic `g` of degree
  `d ≥ 1` there are integer polynomials `q, r` with `∀x, eval f x = eval q x · eval g x + eval r x`
  and `degle r (d−1)` (degree of `r` below `d`). Coefficients stay in ℤ precisely because `g` is
  monic: each step subtracts `(lead f)·X^k·g`, cancelling the top term with **no coefficient
  division** (`monic_div_aux`, by induction on a degree bound of `f`; the cancellation uses only
  `coeff` of `padd`/`pscale`/`pshiftk`, never the full multiplication convolution). Supporting layer:
  `coeff` (i-th coefficient), the operations `pneg`/`psub`/`pshiftk` with their `eval` and `coeff`
  laws, the degree-bound predicate `degle`, and `monic g d := coeff g d = 1 ∧ degle g d`. This is the
  primitive that will define `Φ_n` as the exact quotient of `X^n−1` by `∏_{d|n,d<n} Φ_d` and feed the
  squarefreeness/gcd arguments for `∏_{d|n} Φ_d = X^n−1`. Closed under the global context.
- **Product of monics is monic** `PolyMonic.monic_pmul` (**axiom-free**, Dirichlet brick 3c —
  cyclotomic foundation): the multiplication↔coefficient theory of ℤ[X]. Proves the **convolution
  formula** `coeff (p·q) i = Σ_{j=0}^{i} coeff p j · coeff q (i−j)` (`coeff_pmul`, via `conv_cons`),
  the **degree bound** `deg(p·q) ≤ deg p + deg q` (`degle_pmul`), and the **leading coefficient**
  `coeff (p·q) (dp+dq) = coeff p dp · coeff q dq` (`coeff_pmul_top`, by splitting the convolution
  sum at `j = dp` — only that term survives the two degree bounds). Hence `monic_pmul : monic p dp →
  monic q dq → monic (pmul p q) (dp+dq)`. This is exactly what makes the cyclotomic divisor
  `∏_{d|n,d<n} Φ_d` monic, so `PolyDiv.monic_div` can define `Φ_n` as the exact quotient of `X^n−1`
  by it. Closed under the global context.
- **Computable monic division** `PolyDivComp.pdivmod_spec` (**axiom-free**, Dirichlet brick 3d —
  cyclotomic foundation): `PolyDiv.monic_div` only asserts *existence* of `q, r`; to define `Φ_n` as
  an actual quotient without invoking choice (which would break axiom-freeness), this gives a division
  **function** `pdivmod n f g d` (leading-term cancellation as a `Fixpoint` on the degree bound `n`)
  with the full spec: `∀x, eval f x = eval q x · eval g x + eval r x`, `degle r (d−1)`, **and**
  `degle q (n−d)` — the quotient degree bound, which is exactly what will pin down that `Φ_n` is monic
  of degree `φ(n)`. Supporting `degle` algebra (`degle_padd`, `degle_pscale`, `degle_pmonom`,
  `degle_mono`, `coeff_pmonom_hi`). Closed under the global context.
- **Quotient of a monic by a monic is monic** `PolyDivQuot.monic_div_monic` (**axiom-free**,
  Dirichlet brick 3e — cyclotomic foundation): `monic f n → monic g d → 1 ≤ d ≤ n → monic (quotient
  of f by g) (n−d)`. This is what makes `Φ_n = (X^n−1)/∏_{d|n,d<n}Φ_d` monic of degree `φ(n)`. Needs
  the **coefficient-level** division identity `coeff f i = coeff (q·g) i + coeff r i` (`pdivmod_coeff`
  — the eval-level spec cannot pin a leading coefficient), which rests on a little pmul coefficient
  algebra: distributivity over `padd` (`coeff_pmul_padd_l`), pulling out a scale
  (`coeff_pmul_pscale_l`), and `X^k·g = pshiftk k g` (`coeff_pmul_pmonom_l`), plus the `pmonom`
  coefficient values (`coeff_pmonom_lo`/`_eq`, via `pmonom_repeat`). The leading coefficient of the
  quotient is then extracted at index `n` using `coeff_pmul_top`. Closed under the global context.
- **The cyclotomic polynomials Φ_n, defined and monic** `Cyclotomic.cyclotomic_monic` (**axiom-free**,
  Dirichlet brick 3f): defines `Φ_1 = X−1` and `Φ_n = (X^n−1)/∏_{d|n,d<n}Φ_d` (n ≥ 2) as an actual
  integer polynomial — a fuel-recursion `Phi_f` (fuel independence `Phi_f_indep` via strong induction,
  so `Phi n := Phi_f n n` is well-defined), the divisor degree taken from `Totient.phi` (no separate
  degree recursion). Proves **`Φ_n is monic of degree φ(n)`** by strong induction: the proper-divisor
  product `∏_{d|n,d<n}Φ_d` is monic (`monic_fold_pmul` + IH) of degree `Σ_{d|n,d<n} φ(d) = n − φ(n)`
  (via `Totient.totient_divisor_sum` and `divisors_perm`), and dividing the monic `X^n−1` by it gives a
  monic quotient (`PolyDivQuot.monic_div_monic`), of degree `n − (n−φ(n)) = φ(n)` — using `1 ≤ n−φ(n)
  ≤ n` from `phi_lt`/`phi_ge_1`. **Sanity-checked by `vm_compute`**: `Φ_1..Φ_6` equal the classical
  `X−1, X+1, X²+X+1, X²+1, …, X²−X+1`. The product identity `∏_{d|n}Φ_d = X^n−1` (remainder zero) is
  the next brick. Closed under the global context.
- **Bézout identity for X^a−1** `Xn1Bezout.xn1_bezout` (**axiom-free**, Dirichlet brick 3g — product
  identity): `∃ u v ∈ ℤ[X], u·(X^a−1) + v·(X^b−1) = X^{gcd(a,b)}−1`, proved by the Euclidean
  algorithm on the exponents mirrored on the polynomials — one division step `X^b = X^{m·(b/m)}·X^{b
  mod m}` gives `X^b−1 = X^{b mod m}·(X^m−1)·(geo m (b/m)) + (X^{b mod m}−1)`, and strong induction on
  the first exponent closes it (witnesses built from the sub-call via `psub`/`pmul`/`pmonom`/`geo`). No
  ℚ[X] machinery — everything stays in ℤ[X]. This expresses the greatest common `X^d−1` as an integer
  combination, the foundation for the coprimality of the cyclotomic factors needed for `∏_{d|n} Φ_d =
  X^n−1`. Closed under the global context.
- **Common divisors of X^a−1, X^b−1 divide X^{gcd(a,b)}−1** `Xn1Gcd.pdiv_gcd` (**axiom-free**,
  Dirichlet brick 3h): `pdivides g (X^a−1) → pdivides g (X^b−1) → pdivides g (X^{gcd(a,b)}−1)`.
  Immediate from `xn1_bezout`: writing `X^{gcd}−1 = u·(X^a−1) + v·(X^b−1)`, any `g` dividing both
  right-hand terms divides the left. First step toward `gcd(Φ_i,Φ_j) | X^{gcd(i,j)}−1`. Closed under
  the global context. **NOTE (boundary):** the *next* step — full coprimality of distinct cyclotomic
  factors — cannot be done in ℤ[X]: there is no integer-polynomial Bézout `s·Φ_i + t·Φ_j = 1` (e.g.
  `−Φ_1 + Φ_2 = 2`, and no combination gives 1). The product identity `∏_{d|n}Φ_d = X^n−1` therefore
  needs either a **polynomials-over-ℚ** layer (ℚ[X] gcd/Bézout + squarefreeness of X^n−1) or ℤ[X]
  unique factorisation — a substantial development, not a single brick.
- **ℚ[X] foundation** `QPoly` (**axiom-free**, ℚ[X] layer brick 1): polynomials over ℚ as `list Qc`
  (canonical rationals, so equality is Leibniz `=` and `ring`/`field` apply). Mirrors `IntPoly`+`PolyDiv`
  over ℚ: `qeval` with the evaluation homomorphism (`qeval_add`/`qeval_scale`/`qeval_mul`/`qeval_monom`/
  `qeval_Xn1`/`qeval_shiftk`), and the coefficient/degree layer (`qcoeff`, `qdegle`, `qmonic`) with the
  coefficient laws (`qcoeff_add`/`_scale`/`_neg`/`_sub`/`_shiftk`). This is the base for ℚ[X]
  Euclidean division, gcd, Bézout and squarefreeness of `X^n−1` — where distinct cyclotomics ARE
  coprime — which will give `∏_{d|n}Φ_d = X^n−1` over ℚ and (monic-integer quotient) back over ℤ.
  Closed under the global context.
- **ℚ[X] Euclidean division** `QPolyDiv.qdivmod_spec` (**axiom-free**, ℚ[X] layer brick 2): `f = q·g +
  r` with `deg r < d`, `deg q ≤ n−d`, for any `g` of degree `d` with **nonzero** leading coefficient
  `cl` (not necessarily monic — over the field ℚ each step divides `cl`). Ports `PolyDivComp` with the
  field division `c := lead(f)/cl` cancelling the top term (`c·cl = lead(f)` by `field`). This is the
  step the ℚ[X] gcd/Euclidean algorithm runs on. Closed under the global context.
- **ℚ[X] degree machinery** `QPolyDeg` (**axiom-free**, ℚ[X] layer brick 3a): the Euclidean-gcd needs
  the ACTUAL degree/leading coefficient. `qnorm` strips trailing zeros (`Qc_eq_dec` decides zero),
  `qdeg p := length (qnorm p) − 1`, `qlead p := qcoeff p (qdeg p)`. Proves: coefficients are unchanged
  by normalization (`qcoeff_qnorm`), the leading coefficient of a nonzero polynomial is nonzero
  (`qlead_nonzero`, via `qnorm_top_nz`), a degree bound bounds the degree (`qdegle_qdeg`), and the
  degree bound is genuine (`qdegle_above`). Foundation for the ℚ[X] gcd (brick 3b). Closed under the
  global context.
- **ℚ[X] extended Euclidean algorithm** `QPolyGcd.qeuclid_spec` (**axiom-free**, ℚ[X] layer brick 3b):
  `qeuclid fuel f g = (h, u, v)` with `u·f + v·g = h`, `h | f`, `h | g` (once `fuel > deg g`). Fuel
  recursion: base cases `g = 0` (→ `h = f`) and `g` a nonzero constant `c` (→ `h = 1`, via `0·f +
  (1/c)·g = 1`); otherwise divide (`QPolyDiv.qdivmod`) and recurse on `(g, f mod g)`, whose degree
  strictly drops (`qdegle_qdeg`). Support: `qdivides` in ℚ[X] with `qdivides_refl`/`_one`/`_zero`/
  `_lincomb`, `qeval_all_zero`, `qeval_qnorm` (normalization preserves evaluation). `h` is a common
  divisor carrying a Bézout combination — for coprime `f, g` it is forced constant, giving `u·f + v·g
  = 1` after scaling: the coprimality tool for the cyclotomic factors. Closed under the global context.
- **Coprimality → product divides in ℚ[X]** `QPolyCoprime.qcopr_product_divides` (**axiom-free**,
  ℚ[X] layer brick 4): `qcopr f g` := every common divisor of `f, g` is a nonzero constant. From the
  extended-Euclid common divisor `h` (with `u·f + v·g = h`), coprimality forces `h` constant, giving
  the Bézout identity `u·f + v·g = 1` after scaling (`coprime_bezout`). Hence the classical
  `qcopr p q → p | M → q | M → (p·q) | M` — the mechanism by which `∏_{d|n} Φ_d` divides `X^n−1` once
  the cyclotomic factors are shown pairwise coprime. Closed under the global context.
- **Factor theorem in ℚ[X]** `QPolyRoot.factor_theorem` (**axiom-free**, ℚ[X] layer brick 5a): `qeval
  p a = 0 → ∃ q, ∀x, qeval p x = (x−a)·qeval q x`. Divide `p` by the monic `X − a` (`qdivmod`); the
  remainder is a constant equal to `p(a) = 0`, so the division is exact (`qeval_const_of_degle0` gives
  that a degree-0 polynomial is its constant term; `qc_one_neq_zero` for the monic leading coeff). The
  first step of the polynomial identity theorem (a nonzero polynomial has finitely many roots), which
  the derivative-based squarefreeness of `X^n−1` will rest on. Closed under the global context.
- **Polynomial identity theorem in ℚ[X] (functional form)** `QPolyPIT.poly_roots_eval` (**axiom-free**,
  ℚ[X] layer brick 5b): a polynomial of degree ≤ n vanishing at more than n distinct points is
  identically zero (as a function). Proof: peel one root `a` with the degree-bounded factor theorem
  (`factor_theorem_deg`: `p = (X−a)·q` with `deg q ≤ n−1`, quotient bound from `qdivmod`); the other
  roots are roots of `q` (ℚ has no zero divisors, `Qcmult_integral`), so `q ≡ 0` by induction, hence
  `p ≡ 0`. The classical root-counting identity theorem. Closed under the global context.
- **Coefficient-form PIT in ℚ[X]** `QPolyCoeffPIT.qeval_zero_norm` (**axiom-free**, ℚ[X] layer brick
  5c-part1): `(∀x, qeval p x = 0) → qnorm p = []` — vanishing as a function ⟹ all-zero coefficients,
  the bridge from eval-based to coefficient-level reasoning. Proof: constant term is `p(0)=0`; then
  `x·(tail)(x) ≡ 0` so the tail vanishes at every nonzero point; supplying `deg(tail)+1` distinct
  nonzero rationals `qnat(S k) = Q2Qc(inject_Z(S k))` (`qnat_inj`, `qnat_Sk_nz`, `NoDup_map_inj`), the
  functional PIT forces the tail to vanish everywhere, and structural recursion closes it. This is
  what lets the identity `X^n−1 = h²·k` (obtained from `h²∣X^n−1` at eval level) become a polynomial
  equation to differentiate for squarefreeness. Closed under the global context.
- **ℚ[X] multiplication ↔ coefficients** `QPolyMul.qcoeff_qmul_top` (**axiom-free**, ℚ[X] layer brick
  5c-part2): the ℚ port of `PolyMonic` — convolution formula `qcoeff (p·q) i = Σⱼ qcoeff p j · qcoeff
  q (i−j)` (`qcoeff_qmul`), degree bound `deg(p·q) ≤ deg p + deg q` (`qdegle_qmul`), and leading
  coefficient `qcoeff (p·q)(dp+dq) = qcoeff p dp · qcoeff q dq` (`qcoeff_qmul_top`). Together with
  `QPolyDeg` this yields `deg(p·q) = deg p + deg q` (leadings multiply, ℚ has no zero divisors), so a
  divisor of a nonzero constant is itself constant — the closing step of the squarefreeness argument.
  Closed under the global context.
- **Formal derivative in ℚ[X]** `QPolyDeriv` (**axiom-free**, ℚ[X] layer brick 5c-part3): `qderiv`
  differentiates coefficient-wise. Delivers the **product rule** `(p·q)′ = p′·q + p·q′` at eval level
  (`qderiv_mul_eval`, via linearity `qderiv_add_eval`/`qderiv_scale_eval` and the cons recurrence
  `qderiv_cons_eval`, built on `qderiv_aux_shift`), that **`qderiv` respects functional equality**
  (`qderiv_resp_eval`, via the coefficient formula `qcoeff_qderiv i = qnat(S i)·qcoeff p (S i)`,
  coeff-form PIT `qeval_ext_coeff`, and the easy direction `qcoeff_ext_eval`), and **`(X^n−1)′ =
  n·X^{n−1}`** (`qeval_qderiv_Xn1`). Rational-index arithmetic handled by `qnat_S`
  (`qnat (S k) = qnat k + 1`, via `Q2Qc_plus`). With the ℚ[X] gcd this gives squarefreeness of
  `X^n−1`. Closed under the global context.
- **Squarefreeness of X^n−1 in ℚ[X]** `QPolySqfree.qsqfree_Xn1` (**axiom-free**, ℚ[X] layer brick 5d):
  `qsqfree M := (h²∣M → h constant)`, and `1 ≤ n → qsqfree (X^n−1)`. Proof wires together the whole
  ℚ[X] layer: `h²∣X^n−1` ⟹ (coeff-PIT) `X^n−1 = h²·k` as polynomials ⟹ (product rule, twice)
  `h ∣ (X^n−1)′`, with `(X^n−1)′ = n·X^{n−1}` (`qeval_qderiv_Xn1`); also `h ∣ X^n−1`; the Bézout
  `X·(nX^{n−1}) − n·(X^n−1) = n` gives `h ∣ [n]` (a nonzero constant, `n ≥ 1`), so `h` is constant by
  degree-of-product (`divides_const_deg0`, using `qcoeff_qmul_top` + `qlead_nonzero`). Also
  `qsqfree_mul_copr`: a squarefree product has coprime factors (`qcopr`) — the tool by which the
  cyclotomic factors of `X^n−1` are shown pairwise coprime (brick 6). Closed under the global context.
- **The embedding ℤ[X] ↪ ℚ[X]** `QPolyEmbed` (**axiom-free**, ℚ[X] layer brick 6a): `emb p := map Z2Qc
  p` (`Z2Qc z := Q2Qc (inject_Z z)`) is a ring homomorphism — `emb (p+q) = emb p + emb q` (`emb_padd`),
  `emb (p·q) = emb p · emb q` (`emb_pmul`, via `emb_pscale`), `emb (X^n−1) = X^n−1` (`emb_Xn1`), with
  `Z2Qc` itself a ring hom (`Z2Qc_add`/`_mul`/`_opp`/`_0`/`_1`, injective `Z2Qc_inj`; `Q2Qc_mult` the
  multiplicative companion of `Q2Qc_plus`). Evaluation commutes at integer points: `qeval (emb p)
  (Z2Qc a) = Z2Qc (eval p a)` (`qeval_emb`). This lets the ℚ[X] squarefreeness/coprimality machinery
  act on the integer cyclotomic polynomials and transfer results back. Closed under the global context.
- **Transferring ℤ[X] facts to ℚ[X]** `QPolyTransfer` (**axiom-free**, ℚ[X] layer brick 6b-bridge):
  the workhorse `qeval_ext_Z` — two ℚ polynomials agreeing at every integer point `Z2Qc a` agree
  everywhere (a ℚ polynomial is pinned by its values on ℤ, since ℚ is infinite; via `poly_roots_eval`
  with the distinct points `qnat k`). Consequences: `pdivides_emb` (ℤ-divisibility ⟹ ℚ-divisibility of
  the embeddings), `qXn1_dvd` (`m∣n → (X^m−1)∣(X^n−1)` in ℚ[X]), `qxn1_bezout` (the Bézout identity for
  `X^a−1` transferred to ℚ[X] via `Z2Qc_pow`/`Z2Qc_Xn1val`), and `qdiv_gcd` (common divisors of
  `X^i−1, X^j−1` divide `X^{gcd(i,j)}−1` over ℚ). These are exactly the tools the cyclotomic
  coprimality argument runs on. Closed under the global context.
- **Products of cyclotomic factors over ℚ** `QProd` (**axiom-free**, ℚ[X] layer brick 6b-products):
  `qprod l := ∏_{d∈l} emb(Φ_d)`, permutation-invariant (`qprod_perm`), splitting over append
  (`qeval_qprod_app`), with every listed factor dividing it (`qdivides_qprod_in`), factoring out one
  element via `remove` (`qprod_remove`, using `in_split` + `Permutation_middle` + `remove_app_mid`),
  and the key **product-over-sublist divisibility** `qdivides_qprod_incl`: `incl l1 l2 → NoDup l1 →
  NoDup l2 → qprod l1 ∣ qprod l2`. This is the combinatorial tool behind the pairwise coprimality of
  the cyclotomic factors of `X^n−1` (e.g. `X^{gcd(i,j)}−1 ∣ Dprod_i` because divisors of `gcd(i,j)`
  are a sublist of the proper divisors of `i`). Closed under the global context.
- **Product-divisibility toolkit** `QPolyProdDvd` (**axiom-free**, ℚ[X] layer brick 6b/7-toolkit):
  `qdiv_deg_zero` (`g∣r`, `deg r < deg g`, `g≠0` ⟹ `r = 0` — forces the division remainder `R_n` to
  vanish); `qcopr_mul` (coprimality preserved by products, via `qcopr_restrict` + Euclid's lemma
  `qcopr_euclid`: coprime to `A` and dividing `A·B` ⟹ divides `B`); `qcopr_qprod` (coprime to each
  `Φ_d` ⟹ coprime to `∏Φ_d`); and `qprod_dvd` (NoDup, pairwise-coprime factors each dividing `M` ⟹
  their product divides `M`). These wire the coprimality/product-divisibility into the shape needed for
  `∏_{d|n,d<n}Φ_d ∣ X^n−1`. Closed under the global context.
- **THE CYCLOTOMIC PRODUCT IDENTITY** `CyclotomicProd.cyclotomic_prod` (**axiom-free**, ℚ[X] layer
  brick 7 — capstone): `∏_{d|n} Φ_d = X^n − 1`, and its consequence **`Phi_dvd_pow`: `Φ_n(a) ∣ a^n −
  1`** over ℤ. Proved by strong induction over ℚ[X] wiring together the entire layer: the proper-divisor
  factors `Φ_d` are pairwise coprime (`qsqfree_Xn1` + `qsqfree_mul_copr` + `qdiv_gcd` + the
  divisor-sublist product divisibility `qdivides_qprod_incl`; the `gcd(i,j)=i` case handled by symmetry
  `qcopr_sym`), so `∏_{d|n,d<n} Φ_d ∣ X^n−1` over ℚ (`qprod_dvd`); the monic-division remainder is then
  forced to zero (`qdiv_deg_zero`, `Phi_eq` relating `Φ_n` to `pdivmod`), and the identity transfers
  back to ℤ at integer arguments (`qeval_ext_Z`, `Z2Qc_inj`). Supporting: `emb_Dprod`/`emb_monic`/
  `emb_degle` (embed the ℤ cyclotomics), the divisor-membership iffs, `divisors_incl_properdivs`. This
  is the final gate for general-`n` Dirichlet: with `Φ_n(a) ∣ a^n−1` and `OrderPrimeMod`, a prime
  divisor of `Φ_n(a)` not dividing `n` is a primitive divisor, hence `≡ 1 (mod n)`. Closed under the
  global context.
- **Formal derivative in ℤ[X]** `IntPolyDeriv` (**axiom-free**, general-`n` Dirichlet brick): `pderiv`
  differentiates coefficient-wise; delivers the product rule `(p·q)′ = p′·q + p·q′` (`pderiv_mul_eval`)
  and `(X^n−1)′ = n·X^{n−1}` (`peval_pderiv_Xn1`). Cleaner than the ℚ version (integer index
  coefficients, `Z.of_nat (S k) = Z.of_nat k + 1`). This is the tool for the prime-divisor lemma: a
  prime `q` dividing two distinct cyclotomic factors `Φ_e(a), Φ_n(a)` makes `a` a double root of
  `X^n−1` mod `q`, so `q ∣ (X^n−1)′(a) = n·a^{n−1}`, forcing `q ∣ n`. Closed under the global context.
- **ℤ[X] identity theorem + derivative respects equality** `IntPolyDerivResp` (**axiom-free**): `eval_ext_coeff_Z`
  (functionally-equal ℤ polynomials have equal coefficients — obtained by embedding into ℚ[X] and invoking the
  ℚ identity theorem, `qeval_ext_Z` + `qeval_ext_coeff`), the derivative coefficient formula `pcoeff_pderiv`
  (`coeff (p′) i = (i+1)·coeff p (i+1)`), and `pderiv_resp_eval` (`(∀a, p(a)=q(a)) ⟹ ∀a, p′(a)=q′(a)`). Lets us
  differentiate the cyclotomic factorization `X^n−1 = ∏_{d∣n}Φ_d` term-by-term. Closed under the global context.
- **Primitivity / primitive-divisor lemma** `PrimeDivisorPhi.phi_primitive` (**axiom-free**): if a prime `q`
  divides `Φ_n(a)` but `q ∤ n`, then `q ∤ a^d − 1` for every proper divisor `d ∣ n` (i.e. `a` has
  multiplicative order exactly `n` mod `q`). Double-root argument over ℤ (no `F_q[X]` needed): if
  `q ∣ a^d − 1 = ∏_{e∣d}Φ_e(a)` then `q ∣ Φ_e(a)` for a proper divisor `e`; `q` then divides two distinct
  factors of `X^n−1 = Φ_n·∏_{d<n}Φ_d`, so differentiating (product rule) gives `q ∣ (X^n−1)′(a) = n·a^{n−1}`;
  `q ∤ a ⟹ q ∤ a^{n−1} ⟹ q ∣ n`, contradiction. Feeds `OrderPrimeMod.order_prime_mod` (⟹ `n ∣ q−1`).
  Closed under the global context.
- **Dirichlet's theorem, the `≡ 1 (mod n)` case (general `n`)** `DirichletAP.dirichlet_primes_1_mod_n`
  (**axiom-free — THE CAPSTONE**): for every `n ≥ 1` there are infinitely many primes `q ≡ 1 (mod n)`
  (for every bound `B`, a prime `q > B` with `n ∣ q − 1`). Proof: fix `n, B`; let `A = n·M!` with
  `M = B + |Φ_n| + 3` (`|Φ_n|` = sum of abs of coefficients). Monic growth (`monic_eval_lower`, via the
  coefficient-sum bound `abs_eval_degle`) gives `Φ_n(A) ≥ 2`, so it has a prime divisor `q`. Since
  `Φ_n(A) ≡ Φ_n(0) = ±1 (mod A)` (`a_dvd_eval_sub`, `phi0_unit`), `q ∤ A`; as `n ∣ A` and every prime
  `≤ B` divides `M! ∣ A`, we get `q ∤ n` and `q > B`. Then `PrimeDivisorPhi.phi_primitive` shows `a`
  has order exactly `n` mod `q`, and `OrderPrimeMod.order_prime_mod` gives `n ∣ q − 1`. Bridges
  `nat ↔ ℤ` divisibility/powers throughout. Closed under the global context. **This completes the
  cyclotomic proof of Dirichlet's theorem for primes `≡ 1 (mod n)`.**
- **The binomial Hopf algebra on ℤ[X]** `HopfPoly` (**axiom-free** — first Hopf-algebraic result): `ℤ[X]`,
  the coordinate ring of 𝔾ₐ, with coproduct `Δ(p) = p(X+Y)`, counit `ε(p) = p(0)`, antipode
  `S(p)(X) = p(−X)`. `H⊗H` is represented concretely as `list poly` (tensor `t = Σ_i X^i ⊗ row_i`) with a
  faithful bivariate evaluation `beval t x y = Σ_i x^i·row_i(y)`; the master lemma `beval_Delta` gives
  `beval (Δ p) x y = p(x+y)`, and every axiom is verified through it (polynomials compared up to
  evaluation): `Delta_mult`/`Delta_unit` (Δ an algebra morphism), `coassoc` (`p(x+y+z)` two ways),
  `counit_left`/`counit_right`, `antipode_left`/`antipode_right` (both convolutions `S⋆id`, `id⋆S`
  collapse to `p ↦ p(0)·1`), `X_primitive` (`Δ X = X⊗1 + 1⊗X`), and `derivation_leibniz` — the bridge
  showing the formal derivative (`IntPolyDeriv`) is the derivation generated by the primitive `X`, with
  Leibniz = the coderivation law. Closed under the global context.
- **The multiplicative bialgebra on ℤ[X] + group-like elements** `HopfGrouplike` (**axiom-free** — the
  group-like / group-algebra side of the duality): the *same* `ℤ[X]` and concrete tensor model as
  `HopfPoly`, but with the multiplicative coproduct `Δ×(p) = p(X·Y)` and counit `ε(p) = p(1)`. Master
  lemma `beval_Deltam`: `beval (Δ× p) x y = p(x·y)`. From it: `Deltam_mult`/`Deltam_unit` (algebra
  morphism), `coassocm` (`p(x·y·z)` two ways), `Deltam_cocomm` (cocommutative), `counitm_left`/`_right`.
  The payoff is **group-like elements** (`grouplike a := Δ×(a)=a⊗a ∧ ε(a)=1`): `X_grouplike` shows
  `Δ× X = X⊗X` (contrast `HopfPoly.X_primitive`'s `Δ X = X⊗1+1⊗X` — the *same* `X` is group-like here,
  primitive there), `grouplike_monom` (all `Xᵏ` are group-like), `grouplike_mul`/`grouplike_one` (closed
  under product, with unit) — exhibiting the multiplicative monoid of monomials as the group inside the
  algebra, dual to `HopfPoly`'s primitives (the abelian Lie algebra). Honest boundary: over `ℤ[X]` this
  is a *bialgebra*, not a full Hopf algebra (an antipode would need `X⁻¹`); the finite group algebra
  `ℤ[X]/(Xⁿ−1) = k[ℤ/nℤ]` restores the antipode `S(X)=Xⁿ⁻¹` (a future brick, needs modular convolution;
  the ℂ-Fourier orthogonality already in `DirichletModP` uses the classical Reals axioms and so lies
  outside the axiom-free core). Closed under the global context.
- **The finite group algebra k[ℤ/nℤ] + Hopf duality with k^G** `HopfGroupAlgebra` (**axiom-free**):
  elements are `nat → Z` (indices mod `n`); the group algebra has convolution product
  `(a⋆b)_k = Σ_{i+j≡k} a_i b_j` (`gconv`), unit `e_0` (`gunit`), diagonal coproduct, augmentation counit,
  and inversion antipode `S(e_g)=e_{−g}` (`ginv`). Paired with the function algebra `k^G` (pointwise
  product) via `⟨a,φ⟩ = Σ_g a_g φ_g` (`dot`), the fundamental Hopf duality is proved:
  `product_coproduct_duality` (`⟨a⋆b,φ⟩ = Σ_{i,j} a_i b_j φ_{i+j}` — convolution dual to the `k^G`
  coproduct), `coproduct_product_duality` (`⟨a,φ·ψ⟩ = Σ_g a_g φ_g ψ_g` — diagonal coproduct dual to
  pointwise product), `counit_unit_pairing`/`counit_augmentation` (unit ↔ counit), and the antipode
  axiom `antipode_axiom`/`antipode_is_eps_unit` (`m∘(S⊗id)∘Δ = η∘ε`). Entirely combinatorial —
  convolution is defined as an indicator double sum, so the duality reduces to a Fubini swap
  (`sumf_swap`) plus a sifting lemma (`sumf_sift`) over the finite index set; **no roots of unity /
  DFT** (that route needs the classical Reals axioms). This is the genuine group-algebra side of the
  duality; `HopfGrouplike` was the group-like/coordinate-ring side. Closed under the global context.
  Also rounds out the algebra structure (all axiom-free, equalities pointwise on representatives `k < n`):
  `gconv_comm` (convolution commutative), `gconv_distrib_l`/`_r` (bilinear), `gconv_unit_l`/`_r` (`e_0` a
  two-sided unit), `gconv_assoc` (**associativity** — via the duality: `⟨(a⋆b)⋆c,φ⟩ = Σ_{i,j,m} a_i b_j c_m
  φ_{i+j+m} = ⟨a⋆(b⋆c),φ⟩` for all `φ` by `dot_L`/`dot_R`, coefficients extracted with delta functions
  `dot_delta` — so `k[ℤ/nℤ]` is a commutative ring), and `ginv_involutive` (`S² = id`, from `−(−g) ≡ g`).
- **The group algebra k[G] for an ARBITRARY finite abelian group** `HopfGroupAlgebraGen` (**axiom-free**):
  generalises the cyclic case to any finite abelian `G`, presented abstractly by a carrier `A` with
  decidable equality `Aeq` (a `reflect` spec), a complete NoDup enumeration `elts`, and group operations
  `op`/`e`/`inv` with the left group axioms + commutativity as hypotheses (`(i+j) mod n ↦ op x y`,
  `seq 0 n ↦ elts`, `_=?_ ↦ Aeq`, modular facts ↦ group axioms). Derives the needed group facts
  (`inv_involutive`, right identity, `Aeq_sym`/`Aeq_refl`), then ports the entire `k[ℤ/nℤ]` development:
  the two duality theorems (`product_coproduct_duality`, `coproduct_product_duality`), counit/unit
  duality, the antipode axiom (`antipode_axiom`, `antipode_is_eps_unit`), and the full commutative-ring
  structure of convolution (`gconv_comm`, `gconv_distrib_l`/`_r`, `gconv_unit_l`/`_r`, `gconv_assoc` via
  the duality, `ginv_involutive`). Because `elts` contains **every** element, all identities hold
  unconditionally (no representative guard). Non-vacuity is witnessed by a concrete instance —
  `ℤ/2ℤ = (bool, xorb, false, id)` — with `z2_associative`, `z2_unit` obtained by applying the general
  theorems, confirming the abstract hypotheses are jointly satisfiable. Closed under the global context.
- **Monoidality: k[G×H] ≅ k[G]⊗k[H]** `HopfGroupTensor` (**axiom-free**): the group-algebra functor is
  monoidal. The isomorphism is *currying* (`f : A×B → ℤ ↔ F : A → B → ℤ`); its content is that currying
  is an algebra morphism: `gconv_prod_tensor` shows it carries the product-group convolution `gconvGH`
  (over `list_prod eltsA eltsB`, with the componentwise `opAB`/`ABeq`) to the tensor-product convolution
  `tconv` on `k[G]⊗k[H]`. `gunit_prod_tensor` shows the unit is a pure tensor (`e_{G×H} = e_G ⊗ e_H`), and
  `tconv_elementary` shows `tconv` is genuinely the tensor product of the two convolutions — on
  elementary tensors, `(u⊗v)⋆(u'⊗v') = (u⋆_A u')⊗(v⋆_B v')`. Purely combinatorial: needs only
  `Σ over list_prod = nested Σ` (`sumf_list_prod`), an indicator factorisation (`ABeq = AeqA && BeqB`),
  and one Fubini swap — **no group axioms** at all (a pure identity of finite sums). Closed under the
  global context.
- **The Dirichlet convolution ring + Möbius inversion** `DirichletConv` (**axiom-free**): arithmetic
  functions `ℕ → ℤ` with `(f ∗ g)(n) = Σ_{d·e=n} f(d) g(e)` — convolution in the monoid `(ℕ_{>0}, ×)`, the
  number-theoretic sibling of the group-algebra convolution (defined as an indicator double sum over
  `[1,n]`, so the proofs mirror `HopfGroupAlgebra`). The full **commutative ring**: `dconv_comm`
  (commutative, Fubini swap), `dconv_assoc` (**associative** — both associations equal the symmetric
  triple sum `Σ_{a·b·c=n} f(a)g(b)h(c)`, reached by extending the inner convolution to the fixed range
  `[1,n]` (`dconv_extend`) and collapsing the intermediate factor (`sumf_collapse`), reconciled via
  commutativity), `dconv_eps_l`/`_r` (two-sided unit `ε(n)=[n=1]`), `dconv_distrib_l`/`_r`; plus
  `dconv_as_div` (bridge to `Σ_{d∣n} f(d) g(n/d)`). Number-theory payoffs: `phi_done_eq_id` (**`φ ∗ 1 =
  id`** — Euler's `Σ_{d∣n} φ(d) = n` as a convolution identity), the Möbius function `mu` **defined by
  its recurrence** (`mu_f` by strong recursion so that `mu_one`: `μ ∗ 1 = ε` holds essentially by
  construction — no multiplicativity/prime-factorisation machinery needed), `mobius_inversion`
  (`g = f ∗ 1 ⟹ f = g ∗ μ`, a two-line consequence of associativity + `μ∗1=ε` + unit), and
  `phi_mobius` (**`φ = id ∗ μ`**, i.e. `φ(n) = Σ_{d∣n} μ(d)·(n/d)`, immediate from `φ∗1=id` by
  inversion). This fuses the Hopf/convolution thread with the arithmetic — the group-algebra
  convolution and the Dirichlet convolution are the same machine. Closed under the global context.
- **Multiplicativity of μ and φ** `DirichletMult` (**axiom-free**): a function `f : ℕ → ℤ` is
  `multiplicative` if `f(1)=1` and `f(mn)=f(m)f(n)` for coprime `m,n≥1`. The core is `dconv_mult` —
  the Dirichlet convolution of two multiplicative functions is multiplicative — proved on the **coprime
  divisor bijection** `divisors(mn) ↔ divisors(m)×divisors(n)` (reused from `JacobiRHS.divisors_mul_perm`),
  turning `(f∗g)(mn)` into a product of the two convolutions via `sumf_sep`. From it: `done_mult`
  (constant `1`), `did_mult` (`id`, completely multiplicative); **`mu_mult`** — μ is multiplicative, by
  strong induction on the product `m·n` (the term `μ(ab)−μ(a)μ(b)` vanishes off `(a,b)=(m,n)` by the IH,
  and `μ∗1=ε` makes both remaining sums vanish, via `sumf_single_gen`); and **`phi_mult`** — φ is
  multiplicative, immediate from `φ = id ∗ μ` (`phi_mobius`) and `dconv_mult`. Closed under the global
  context.
- **The divisor functions τ, σ, σ_k** `DirichletDivisor` (**axiom-free**): `τ = 1 ∗ 1` (`dtau`), `σ = id ∗ 1`
  (`dsigma`), `σ_k = id_k ∗ 1` (`dsigmak`, with `id_k(n)=n^k`). Since `1`, `id`, `id_k` are multiplicative
  (`did_mult`, `didk_mult` — `id_k` completely multiplicative), all three are multiplicative by
  `dconv_mult`: `dtau_mult`, `dsigma_mult`, `dsigmak_mult`. Also their standard values via `dconv_as_div`:
  `dtau_as_div` (`τ(n) = #divisors(n)`), `dsigma_as_div` (`σ(n) = Σ_{d∣n} d`), `dsigmak_as_div`
  (`σ_k(n) = Σ_{d∣n} d^k`). Closed under the global context.
- **Prime-power values of μ, φ, τ, σ** `DirichletPPow` (**axiom-free**): since all four are multiplicative
  they are determined by prime-power values, computed here within the ring. Key lemma `arith_ppow_split`:
  for `p` prime and `k ≥ 1`, any `f` satisfies `f(p^k) = (Σ_{d∣p^k} f) − (Σ_{d∣p^{k-1}} f)` (from
  `divisors(p^k) = {p^0,…,p^k}`, i.e. `JacobiRHS.divisors_prime_pow`, plus `sumf_seq_last`). Consequences:
  `mu_p` (`μ(p) = −1`), `mu_ppow_ge2` (`μ(p^k) = 0` for `k ≥ 2`) — both from `μ∗1=ε` (`Sigma_mu_div`);
  `phi_ppow`/`phi_ppow_nat` (`φ(p^k) = p^k − p^{k-1}`) — from `φ∗1=id` (`phi_done_eq_id`); `tau_ppow`
  (`τ(p^k) = k+1`, by counting divisors) and `sigma_ppow` (`σ(p^k) = Σ_{j≤k} p^j`). Closed under the
  global context.
- **Von Mangoldt identity (multiplicative form)** `DirichletVonMangoldt` (**axiom-free, reflective**):
  the additive `Σ_{d∣n} Λ(d) = log n` with `log` stripped by exponentiation — `∏_{d∣n} vexp(d) = n`,
  where `vexp = exp∘Λ` (`vexp(p^k)=p` for `k≥1`, else `1`) is defined **computably** (least prime factor
  `least_factor` + `strip`-out-all-`p`-factors). Sample `Example`s (`vexp 8 = 2`, `vexp 12 = 1`,
  `vmprod 12 = 12`) hold by `reflexivity`, and `vonmangoldt_upto` **validates the identity by reflection**
  for `1 ≤ n ≤ 100` (`vm_compute`). Honest boundary: this is computational validation, following the
  repo's own reflective pattern (cf. `JacobiRHS.jacobi_upto`); the fully general proof reduces to unique
  factorization / prime-power peeling over `nat`, a further infrastructure brick. Closed under the global
  context.
- **Prime-power peeling + reduce-to-prime-powers induction** `DirichletPeel` (**axiom-free**): the
  factorization infrastructure. `nat_ppow_peel`: every `n ≥ 2` splits as `n = p^v · m` with `p` prime,
  `v ≥ 1`, `p ∤ m`, `m ≥ 1`, and `m < n` — built by bridging `PrimeFactorizationExists.padic_val` (over ℤ)
  to `nat` via `has_prime_divisor`. `mult_ind`: to prove `P n` for all `n ≥ 1`, it suffices to prove `P 1`
  and the step `P m ⟹ P (p^v · m)` (`p` prime, `p ∤ m`, `v ≥ 1`) — strong induction + peeling. This is the
  reusable engine for any "reduce to prime powers" argument (e.g. the general `∏_{d∣n} vexp(d) = n`, or
  reconstructing `n` from its prime-power factors). Closed under the global context.
- **Semantic lemmas for computable `vexp` (prime-power case)** `DirichletVexpSem` (**axiom-free**): proves,
  about the computable `vexp` (= `exp∘Λ`, defined via `least_factor`+`strip`), that `vexp(p^v) = p`
  (`vexp_ppow`) and hence `∏_{d∣p^k} vexp(d) = p^k` (`vmprod_ppow`) — i.e. the von Mangoldt identity **on
  prime powers now fully proven** (upgrading `DirichletVonMangoldt`'s reflective check for this case). The
  work is reasoning about the computational primitives: `strip_pow` (`strip` removes all `p` from `p^v`,
  giving `1`), `find_first`/`seq_split_at`/`least_factor_least` (a `find`-returns-the-least-divisor
  characterisation), and `least_factor_ppow` (`least_factor(p^v)=p`, via `JacobiRHS.div_prime_pow`: a
  divisor of a prime power is a prime power). Honest boundary: the general `∏_{d∣n} vexp(d)=n` additionally
  needs the *coprime* semantic lemma `vexp(ab)=1` for coprime `a,b≥2` (needing `least_factor` prime + a
  `strip`-reverse), then `mult_ind` (`DirichletPeel`) — a further step. Closed under the global context.
- **`vexp` coprime lemma** `DirichletVexpCoprime` (**axiom-free**): the remaining `vexp` fact —
  `vexp_coprime`: `vexp(a·b) = 1` for coprime `a,b ≥ 2`. Builds the two named primitives: `find-min`
  (`find_seq_least` ⟹ `least_factor_min`: `least_factor n` is `≤` every divisor `≥2`; plus
  `least_factor_ge2`) and `strip-reverse` (`strip n n q = 1 ⟹ n = q^k`), plus `prime_dvd_pow`
  (`prime | a^k ⟹ prime | a`) and `prime_factor_ex`. A prime factor of `a` and of `b` would each have to
  equal `least_factor(ab)`, impossible when `gcd(a,b)=1`. Closed under the global context.
- **The GENERAL von Mangoldt identity** `DirichletVonMangoldtGen` (**axiom-free — the payoff**):
  **`∏_{d∣n} vexp(d) = n`** for all `n ≥ 1` (`vonmangoldt`), the multiplicative von Mangoldt identity now
  *fully proven* (no longer only the reflective check). Proof by `DirichletPeel.mult_ind`: for
  `n = p^v·m` (`p` prime, `p∤m`), the coprime divisor bijection (`divisors_mul_perm`) splits the product,
  and `vexp_ppow` (`vexp(p^i)=p`) + `vexp_coprime` (`vexp(p^i·b)=1`, `b≥2`) evaluate every factor:
  `∏_{d∣p^v·m}vexp = (∏_{d∣m}vexp)·∏_{i=1}^{v} p = m·p^v = n`. Uses a paired-product toolkit
  (`prodp`/`prodp_list_prod`) to handle the `list_prod` from the bijection, and `gcd_ppow_coprime`.
  Closed under the global context.
- **MASTER umbrella for the Dirichlet thread** `DirichletMaster.dirichlet_theory` (**axiom-free**): a
  single conjunction bundling the headline results of the whole arithmetic-functions arc, as a curated
  index (each conjunct is exactly the corresponding standalone theorem, assembled by a positional
  `conj` term). Six sections: **(I)** the Dirichlet convolution ring — `dconv_comm`, `dconv_assoc`,
  `dconv_eps_l/r` (unit ε), `dconv_distrib_l/r` (bilinearity), and `dconv_as_div` (divisor-sum form);
  **(II)** Möbius — `mu_one` (μ∗1=ε), `mobius_inversion`, `phi_mobius` (φ=id∗μ), `phi_done_eq_id`;
  **(III)** multiplicativity — `dconv_mult` and `mu`/`φ`/`τ`/`σ`/`σ_k` multiplicative;
  **(IV)** prime-power values — `mu_p` (−1), `mu_ppow_ge2` (0), `phi_ppow`, `tau_ppow`, plus τ/σ as
  divisor sums; **(V)** the reduce-to-prime-powers induction `mult_ind`; **(VI)** von Mangoldt —
  `vexp_ppow`, `vexp_coprime`, and the general `vonmangoldt` (∏_{d∣n} vexp d = n). `Print Assumptions
  dirichlet_theory` = closed under the global context. (Bundle, not new mathematics — an at-a-glance
  statement of what the thread proves.)
- **Zeta-squared at the coefficient level** `DirichletZetaSquare` (**axiom-free**): reads the Dirichlet
  thread through the ζ-series dictionary (ζ↔`done`, 1/ζ↔`mu`, ζ²↔`done∗done`=`dtau`, ζ/ζ(2s)↔`|mu|`)
  and proves the genuinely new companion identity for **ζ(s)²/ζ(2s)**. **Part A** makes ζ²↔τ explicit
  (`zeta_sq_is_tau`: `dconv done done = dtau`; τ multiplicative; τ(p^k)=k+1; τ = #divisors — the
  ordered-factorization/hyperbola count), all by reuse. **Part B** `musq n := Z.abs (mu n)` (squarefree
  indicator) is multiplicative (`musq_mult`, from `mu_mult` + `Z.abs_mul`), with `musq p = 1`,
  `musq (p^k)=0` (k≥2). **Part C** `two_om := |mu| ∗ done` (coefficients of ζ²/ζ(2s)) is multiplicative
  and `two_om (p^k) = 2` for k≥1 (`divisors_ppow_sum`). **Part D — the main theorem**
  `two_om_eq : two_om n = 2^ω(n)`: a self-contained boolean prime test `primeb` bridged to
  `prime (Z.of_nat n)` via `Znumtheory.prime_alt`, `omega n := #(prime divisors)`, the peel-step
  `omega (p^v·m) = S(omega m)` (a `NoDup_Permutation` of `filter primeb (divisors (p^v·m))` with
  `p :: filter primeb (divisors m)`, using `prime_dvd_mult_nat`/`prime_dvd_pow`), then `mult_ind`. So
  **(|mu|∗1)(n) = number of squarefree divisors = 2^(#distinct primes)**. **Part E**: a
  `vm_compute` reflective cross-check `zsq_upto : zsq_check 100 = true` and a positional-`conj` umbrella
  `zeta_square`. `Print Assumptions zeta_square` = closed under the global context. This is the
  *algebraic* (coefficient-level) ζ²; the analytic statement ∑τ(n)/n² = ζ(2)² remains deferred (it would
  bridge to the quarantined-Reals ζ(2) arc).
- **r₂ as a ℤ[i] norm-count** `GaussianNormCount.r2_as_gnorm` (**axiom-free**): the bridge
  `r₂(n) = #{ z ∈ ℤ[i] : N(z) = n }` — R2Count's lattice-point count re-read in ℤ[i] under
  `(a,b) ↔ a+bi` (via `length_filter_map` + the definitional match of the two boxes). This is the
  foundation for counting norm-`n` elements through unique factorisation, the last conceptual step to
  the general Jacobi identity `r₂(n)=4·S(n)`. Closed under the global context. **Next (the payoff):**
  count norm-`n` elements via the Gaussian factorisation — `r₂` multiplicative on coprimes and the
  prime-power counts (`r₂(2^k)=4`, `r₂(p^k)=4(k+1)` for `p≡1`, `4·[k even]` for `p≡3`) — then combine
  with `JacobiRHS` (`S` multiplicative + prime powers) for `r₂(n)=4·S(n)`.
- **ℤ[i] prime-power count machinery** `GaussianPrimePowerCount` (part 1, **axiom-free**): the shared
  base for the three prime-power values `r₂(2^k)=4`, `r₂(p^k)=4(k+1)` (`p≡1`), `4·[k even]` (`p≡3`).
  Gaussian powers `ZIpow` with `N(a^m)=(N a)^m` (`ZIpow_norm`) and nonzero (`ZIpow_nonzero`);
  extraction of an irreducible factor `irr_factor_exists` (head of the nonempty `factor_exists`
  list); and **prime-power divisibility** `prime_pow_dvd` (`π` irreducible, `π | a^m ⇒ π | a`, by
  induction via Euclid's lemma, `π ∤ unit`). These pin down the Gaussian-prime structure of a
  norm-`p^k` element, the reusable core of all three counts. Closed under the global context.
  **Next:** the case decompositions + `NoDup_Permutation` counts (`p=2`/`p≡3` first, then split
  `p≡1`).
- **ℤ[i] norm-`p^k` decompositions** `R2PrimePower.decomp_p3` / `decomp_p2` (Milestone A structural
  half, **axiom-free**): for the single-prime-family cases, every norm-`p^k` Gaussian integer is a
  unit times a power of the prime over `p`. **`p≡3 (4)` (inert)**: `N(z)=p^k ⇒ z = u·(ZtoZI p)^j`
  with `k=2j` (so `k` must be even). **`p=2` (ramified)**: `N(z)=2^k ⇒ z = u·(1+i)^k`. Both by strong
  induction on `N(z)`: `z·conj z = (base)^k` (`z_conj_pow`), so any irreducible factor divides
  `(ZtoZI p)^k` — for `p≡3`, `prime_pow_dvd` + inertness makes it an associate of `ZtoZI p`; for
  `p=2`, `2 = (−i)(1+i)²` (`two_eq_sq`) routes it through `(1+i)²` to `(1+i)` — so the prime divides
  `z`, peel it off and recurse. Uses the associate helpers `irr_dvd_irr_assoc` (irreducible ∣
  irreducible ⇒ associate) and `assoc_dvd_r`. From these, the **prime-power counts**
  `R2PrimePower.r2_prime_power_2_3`: `r₂(2^k)=4` (`r2_2pow`) and `r₂(p^k)=4·[k even]` for `p≡3 (4)`
  (`r2_3pow`). Via the bridge `r₂(n)=#{N(z)=n}` (`r2_as_gnorm`), the norm-`p^k` elements are exactly
  the 4 associates `assoc4` of the base power (unit × base^j, `in_assoc4`); a `NoDup_Permutation`
  between the norm-filtered box (`gbox_NoDup`) and that 4-element list (or `[]` when `p≡3` and `k`
  odd, since the decomposition forces `k` even) gives the count. Closed under the global context.
  **Next (Milestone B):** the split case `p≡1 (4)` — `r₂(p^k)=4(k+1)` (two conjugate Gaussian-prime
  families `π₀,π̄₀`, `k+1` exponent splits × 4 units, distinctness via cancellation +
  `prime_pow_dvd`).
- **ℤ[i] split-prime non-associate + decomposition** `R2PrimePowerSplit` (Milestone B structural
  half, **axiom-free**): for `p≡1 (4)`, `p = a²+b² = q₀·q₁` with `q₀=a+bi`, `q₁=a−bi` its conjugate.
  **`q0_not_assoc_q1`**: `q₀` and `q₁` are *not* associates — checking the 4 unit multiples forces
  `b=0`/`a=0` (⇒ `p` a square, impossible by `prime_not_sq`) or `a=±b` (⇒ `p=2·square` even,
  impossible for odd `p`). **`decomp_p1`**: `N(z)=p^k ⇒ z = u·q₀^i·q₁^(k−i)` with `i≤k`, by strong
  induction on `N(z)` — `z·conj z = (q₀q₁)^k = q₀^k·q₁^k`, so an irreducible factor divides `q₀^k` or
  `q₁^k` (Euclid on the product), hence (via `prime_pow_dvd` + associate) equals `q₀` or `q₁`; peel
  it off and recurse. From these, the **split count** `r2_1pow`: `r₂(p^k)=4(k+1)` for `p≡1 (4)`. The
  `4(k+1)` norm-`p^k` elements `u·q₀^i·q₁^(k−i)` (`0≤i≤k`, `u` a unit) are all distinct
  (`base_distinct`): distinct exponents can't coincide even up to a unit, since `q₀^i·q₁^(k−i)` twist
  would force `q₀ | q₁^d` (`prime_pow_dvd`) hence `q₀ ~ q₁`, contradicting `q0_not_assoc_q1`. A
  `NoDup_Permutation` (`count_eq_list`) between the norm-filtered box and the explicit
  `list_prod`-of-`(exponent, unit)` list (`splitlist`, length `4(k+1)` via `length_list_prod`) gives
  the count. Closed under the global context. **All three prime-power counts are now proved**
  (`r2_2pow`, `r2_3pow`, `r2_1pow`); assembling the general `r₂(n)=4·S(n)` additionally needs
  `S_mult` + `r₂`-multiplicativity.
- **Sums of two squares — two pillars** `SumTwoSquares.sum_two_squares_pillars` (**axiom-free**):
  (1) **Brahmagupta–Fibonacci** `sum2_mul` — sums of two squares closed under multiplication,
  `(a²+b²)(c²+d²)=(ac−bd)²+(ad+bc)²`, proved as *exactly* Gaussian-norm multiplicativity
  (`ZInorm_mul`); (2) **`−1` a QR mod `p` for `p ≡ 1 (mod 4)`** `neg1_QR` — `∃x, x²+1 ≡ 0 (mod p)`,
  from the from-scratch cyclicity `units_cyclic` (`x=g^{(p−1)/4}`, its square a non-trivial root of
  `1`) + the sqrt-of-1 fact `sqrt1` (Euclid via `prime_mult_nat`). Both genuine theorems.
  These are the two *ingredients* of Fermat's `p ≡ 1 (mod 4) ⟹ p = a²+b²`, now assembled below.
  The global valuation-parity iff (deferred there) is now **completed** in `TwoSquaresFull` (below).
- **Fermat's two-square theorem** `FermatTwoSquares.fermat_two_squares` (**axiom-free**): every prime
  `p ≡ 1 (mod 4)` is a sum of two squares, `p = a²+b²` — a genuine classical theorem of number
  theory, reached entirely within the repo. Proof = **Euler's descent**: `neg1_QR` seeds `p ∣ x²+1`,
  `nearest_rep` reduces to `m·p = u²+1` with `0<m<p`, and `descent_step` uses Brahmagupta–Fibonacci
  (`sum2_mul`, `ring`) + cancellation (`Z.mul_reg_l`) to produce `r·p = A²+B²` with `0<r<m`
  (`r≠0` since else `m∣p`, barred by `prime_divisors` for `1<m<p`); `descent_fuel` iterates the
  decreasing `m` (induction on `Z.to_nat m`) to `m=1`. Built on the from-scratch cyclicity tower +
  the Gaussian-integer bridge; no external axioms. `Print Assumptions` = Closed under the global
  context.
- **Two-square converse + characterisation engine** `SumTwoSquaresConverse.two_squares_characterisation`
  (**axiom-free**): `neg1_not_QR` — `−1` is *not* a QR mod a prime `q ≡ 3 (mod 4)` (mirror of
  `neg1_QR`, from the order theory: an `x²≡−1` has order 4 ⟹ `4∣q−1`); the **obstruction**
  `prime3_obstruction` — `q ≡ 3 (mod 4)` prime, `q ∣ a²+b²` ⟹ `q∣a ∧ q∣b` (Bezout + `neg1_not_QR_Z`);
  the **necessity engine** `prime3_descent` — such a `q` divides a sum of two squares to an even power
  (`q²∣n`, `n/q²` still sum2); and the **sufficiency blocks** (`2`, squares, products via `sum2_mul`,
  primes `≡1 mod4` via Fermat). All genuine theorems, both directions of the classical
  characterisation. **Boundary (now lifted):** the global valuation-parity *iff* is completed in
  `TwoSquaresFull` (next).
- **FULL two-square characterisation** `TwoSquaresFull.two_squares_iff` (**axiom-free**): for `n>0`,
  `sum2 n ↔ (∀ prime q ≡ 3 (mod 4), even q-valuation of n)` — the complete classical Fermat–Euler
  theorem. Both directions by strong induction (`Z.lt_wf`): necessity via `prime3_descent` +
  `pow_split2` + `even_shift2`; sufficiency via `has_prime_divisor` + `padic_val` + `q3even_transfer`
  (Euler hypothesis carried to the cofactor by Euclid `prime_mult`/`prime_ndvd_pow`) + `prime_mod4`
  case split (`sum2_2` / Fermat `sum2_prime1` / even-power `sum2_sq`) + `sum2_mul`. Uses only
  **per-prime** coprimality/cancellation — *not* a general valuation-additivity theorem (which was
  declined). `Print Assumptions` = Closed under the global context. A genuine classical number-theory
  theorem, machine-checked with zero axioms. **Not done:** a reusable valuation function, or `n=0`.
  (Counting representations is now started in `R2Count`, below.)
- **Counting two-square representations `r₂(n)`** `R2Count.two_squares_count` (**axiom-free**): defines
  `r₂(n) = #{(a,b)∈ℤ² : a²+b²=n}` as a decidable bounded count (`filter` over the box
  `[−⌊√n⌋,⌊√n⌋]²`, since a representation forces `|a|,|b| ≤ √n`), and proves two structural facts.
  **(1) Positivity ↔ representability:** `r₂(n) > 0 ↔ sum2 n`, hence by `two_squares_iff`, for `n>0`,
  `r₂(n) > 0 ↔ q3even n` — the full arithmetic test for when the count is nonzero.
  **(2) The factor of 4 in Jacobi:** `4 | r₂(n)` for `n>0`, proved directly — the Gaussian-unit
  rotation `(a,b) ↦ (−b,a)` (mult by `i`) is a **fixed-point-free order-4** action on the solution set
  (general lemma `div4_of_free_order4`: a `NoDup` list closed under such an `f` has length divisible by
  4, by orbit removal via strong induction). Everything is over ℤ/ℕ/lists — no Reals — so `Print
  Assumptions` = Closed under the global context. **Not done:** the full Jacobi count
  `r₂(n) = 4(d₁(n)−d₃(n))` (a deeper theta/Gaussian-integer result) — its RHS is built in
  `JacobiRHS` (below).
- **Jacobi's formula — the RHS** `JacobiRHS.jacobi_rhs` (**axiom-free**): builds the right-hand side of
  `r₂(n) = 4·Σ_{d|n} χ₄(d)` and checks the identity reflectively. Defines `χ₄` (the nontrivial
  character mod 4, `+1/−1/0`) and proves it **completely multiplicative** (`chi4_mul`, 16-case mod-4
  analysis); the divisor sum `S(n) = Σ_{d|n} χ₄(d)` (over `Totient.divisors`) equals `d₁(n)−d₃(n)`
  (`S_as_d1d3`); and the **prime-power values** `S(2^k)=1`, `S(p^k)=k+1` for `p≡1 (4)`, `S(p^k)=[k even]`
  for `p≡3 (4)` (`S_prime_pow_*`, via `divisors_prime_pow`: divisors of `p^k` are exactly `p^0…p^k`,
  proved with a nat/ℤ divisibility bridge + `Nat.gauss`). The full identity `r₂(n) = 4·S(n)` is
  **verified by `vm_compute` for n ≤ 200** (`jacobi_upto`). `Print Assumptions` = Closed under the
  global context. `S` is also proved **multiplicative on coprimes** (`S_mult`): `gcd(m,n)=1 ⇒
  S(mn)=S(m)·S(n)`, via the divisor-product permutation `divisors(mn) ~ {a·b : a|m, b|n}`
  (`divisors_mul_perm`, a `NoDup_Permutation` — existence of the split from `Nat.divide_mul_split`,
  uniqueness from the coprime gcd identity `gcd(a·b,m)=a`, `gcd_prod_l`) plus the sum-over-product
  distributivity `fold_prod_mul` and `chi4_mul`. **Not done (deferred):** `S(n)>0 ↔ q3even n`, and the
  general `r₂(n)=4·S(n)` — the ℤ[i] unique-factorisation engine and all three prime-power counts now
  exist (`GaussianDivision`…`R2PrimePowerSplit`), so what remains is `r₂`-multiplicativity + a
  multiplicative-agreement assembly.
- **A number as a field — the triad `1/x, x, x^x` in `𝔽_p`** `FpField.Fp_field_triad`
  (**axiom-free**): the prime `p` makes `ℤ/pℤ` a field; the inverse is a power `1/x = x^{p−2} mod p`
  with `x·(1/x) ≡ 1` proved as `fermat` (`inv_correct`), self-power `x^x = pw p x x`, so the triad is
  `pw p x` at exponents `{p−2, 1, x}` (`triad_powers_of_x`). In discrete-log space (base a primitive
  root, `DirichletModP.dlog`) it is `{L·(p−2), L, x·L} mod p−1` — reciprocal = negation, self-power =
  scaling by `x` (`dlog_triad`), collapsing to `1` at `x=1` (`triad_collapse`). Genuine theorems,
  reusing the from-scratch cyclicity tower; the reused `dlog` lemmas are axiom-free so `Print
  Assumptions` = Closed under the global context.
- **Self-power dynamics `x ↦ x^x mod p`** `SelfPowerDynamics.self_power_dynamics` (**axiom-free**):
  the self-power map as a dynamical system on `𝔽_p*`. `selfpow_exp_reduce` — the careful
  base/exponent asymmetry `x^x mod p = pw p x (x mod (p−1))` (exponent reduces mod `p−1`, base stays
  `x`), giving `selfpow p (p−1) = 1`; `selfpow_unit` (stays on units); fixed points
  `selfpow_fixed_ord` (`x^x ≡ x ⟺ ord(x) ∣ (x−1)`, cancel a unit via `cancel_mod`); and the capstone
  **eventual periodicity** `orbit_eventually_periodic` via a newly-built constructive pigeonhole
  `orbit_collision` (`existsb` double-search + `NoDup_incl_length`: `p` iterates can't be distinct in
  `p−1` units) + `orbit_shift`. One step linearises in discrete-log space to scaling by `x`
  (`orbit_dlog_step`, from `FpField.dlog_triad`). **Honest scope:** no cycle-length count, no
  fixed-point uniqueness, no pre-period-tail analysis. `Print Assumptions` = Closed under the global
  context.
- **Counting self-power fixed points** `SelfPowerFixedCount.self_power_fixed_count` (**axiom-free**):
  `nfix p = #{x∈[1,p−1] : x^x ≡ x}` as a rigorous computable count (`length (filter …)`), with the
  set-characterisation `fixed_pts_ord` (`ord(x) ∣ (x−1)`), the universal **sandwich
  `1 ≤ nfix p ≤ p−2`** (odd p: `x=1` always fixed ⇒ `≥1`; `x=p−1` never fixed ⇒ `≤p−2`; pins
  `nfix 3 = 1`), and computed values `nfix ∈ {1,1,1,2}` for `p∈{2,3,5,7}` (`vm_compute`, capped at
  `p=7` by unary-`nat` `x^x`). **Analogy boundary:** `nfix p` is an *irregular* function — no
  closed-form or asymptotic is proved or claimed; the count beyond the bounds and small table is
  left open. `Print Assumptions` = Closed under the global context.
- **The "inessential ℝ", made precise** `AlgebraicOrthogonality.algebraic_orthogonality`
  (**axiom-free**): DFT/character orthogonality proved over an *abstract field* with an *abstract
  root of unity* (`apow w N = 1`) — `w^m=1 ⟹ Σ w^{km} = N·1`, `w^m≠1 ⟹ Σ = 0`, pure geometric
  series (`ageom`) + field cancellation. Zero axioms, no ℝ/ℂ/trig. A measured **axiom-footprint
  contrast** then pins where ℝ enters: the same vanishing law over our `ℂ` for an *abstract* root
  (`c_orth_vanish`) carries **2** axioms (field-of-ℝ, *not* the order axiom `sig_not_dec`); the
  *analytic* root `exp(2πi/N)` (`c_orth_w`, via `w_pow_N`) carries **3**. Conclusion: the quarantined
  ℝ-axioms of the entire character/DFT/Dirichlet layer are cosmetic — the orthogonality is axiom-free
  field algebra; ℝ enters solely through the analytic realisation of a concrete root of unity.
- **Euler's formula / circle group** `EulerFormula.euler_circle_group` (quarantined ℝ): `Cexp t =
  cos t + i·sin t` proved to be a group homomorphism `(ℝ,+) → (ℂ*,×)` onto the unit circle —
  `Cexp 0 = 1`, `Cexp(a+b)=Cexp a·Cexp b` (one identity = `cos_plus` **and** `sin_plus`),
  `|Cexp t|²=1`, `Cinv(Cexp t)=Cconj(Cexp t)=Cexp(−t)`, de Moivre `(Cexp t)ⁿ=Cexp(n·t)`, `Cexp 2π=1`,
  and `w N = Cexp(2π/N)` (with `w_pow_N` re-derived from Euler). This is the analytic backbone that
  *manufactures* the root of unity the axiom-free orthogonality (`AlgebraicOrthogonality`) consumes —
  the precise locus of the quarantined ℝ. Genuine theorem; classical Reals axioms (via cos/sin).
- **Gauss sum `|g(χ)|² = p`** `GaussSum.gauss_sum_abs` (quarantined ℝ): for a nonprincipal Dirichlet
  character `χ` mod a prime `p` and additive root `ζ = w p`, the Gauss sum `g(χ) = Σ χ(n)ζⁿ` has
  `g(χ)·conj g(χ) = p` — a genuine classical theorem (a complex character sum whose modulus² is the
  integer `p`), the marquee union of the analytic + number-theory threads. Proof (the arc's largest)
  uses the multiplicative reindex `a=(b·c) mod p` (`units_perm`), `dchar_mul` + `|χ|=1`, the geometric
  series of the `p`-th roots (`β(c)`, `sum_pow_eq_0`), and `Σχ=0` (`dirichlet_orthogonality`). Only the
  3 classical-ℝ axioms — and by `AlgebraicOrthogonality` even that is confined to the analytic root.
  **Analogy boundary:** the *value/sign* of `g(χ)` (the deep Gauss-sign theorem) and non-prime moduli
  are not done.
- **Quadratic Gauss sum `g² = χ(−1)·p`** `QuadraticGaussSum.quadratic_gauss_sum_sq` (quarantined ℝ):
  for an *odd* prime `p` and the order-2 (Legendre) character `χ = dchar p g ((p−1)/2)`, the Gauss sum
  squares to `χ(−1)·p`, and since `χ(−1) = ±1`, `g² = +p` or `−p`. Builds directly on `GaussSum`: the
  already-proved `|g|² = g·conj g = p` (`gauss_abs`) plus the *reflection* `conj g = χ(−1)·g`
  (`gauss_conj_chi`), which holds because the quadratic character is **real-valued** (`chi_real`, via
  `w(p−1)^{2·a₀·k} = 1` for `2a₀ = p−1`). Then `p = g·conj g = χ(−1)·g²`. The reflection uses the
  reindex `b ↦ (p−1)·b mod p` (`Sf_reindex_mul`) and `wc_p^{(p−1)x mod p} = w_p^x` (inverse-of-root,
  `wc_reindex`). Uses the same quarantined classical-ℝ axioms as the character layer. **Not done:** the
  *sign* `χ(−1) = (−1)^((p−1)/2)` (needs `g^((p−1)/2) ≡ −1`), i.e. `+p` for `p≡1 (4)` vs `−p` for
  `p≡3 (4)`.
- **Dirichlet kernel** `DirichletKernel.dirichlet_kernel_thm` (quarantined ℝ): the Fourier-convergence
  kernel `D_n(t) = Σ_{k=−n}^n e^{ikt}`, two faces. Real closed form `dirichlet_kernel`:
  `(1+2Σ_{k=1}^n cos kt)·sin(t/2) = sin((n+½)t)` (telescoping `2cosA sinB = sin(A+B)−sin(A−B)`),
  division-free, and the divided corollary. Complex skeleton `dk_geom`:
  `(Cexp t−1)·DK n t = Cexp(−nt)·(Cexp(t)^{2n+1}−1)` = `geom_sum` via `EulerFormula.Cexp`. Genuine
  theorem; classical Reals axioms (via cos/sin). (The real↔complex identification `DK = RtoC(Dsum)`
  — a symmetric-pair Csum reindex — is not spelled out; both faces are proved independently.)
- **Chebyshev polynomials** `ChebyshevPoly.chebyshev_poly` (quarantined ℝ): `Tₙ` of the first kind
  (recurrence `T_{n+2}=2x·T_{n+1}−Tₙ`, `T₂=2x²−1`, `T₃=4x³−3x`) with the defining identity
  `Tcheb_cos : Tₙ(cos t)=cos(nt)` (two-step induction, cosine recurrence via product-to-sum), the de
  Moivre link `Tcheb_Re : Tₙ(cos t)=Re((Cexp t)ⁿ)`, `Tₙ(1)=1`, and the `n` roots at `cos((2k+1)π/2n)`
  (`cos_odd_pihalf`). Genuine theorem; classical Reals axioms (via cos/sin). Distinct from the
  number-theoretic `Chebyshev.v` (ψ function).
- **N-th roots of unity + DFT orthogonality** `RootsOfUnity` (`w_pow_N`, `w_primitive`,
  `dft_orthogonality_delta`): in the custom `C`, `w N = exp(2πi/N)` with `(w N)ᴺ = 1` (De Moivre),
  and the character sum `Σ_{k<N} (w N)^{jk} = N` (if `(w N)ʲ=1`) or `0` — the complex-DFT
  orthogonality, general-`N` cousin of `WalshHadamard.H²=8I`. The vanishing branch is pure
  `C`-field algebra (geometric series + `aᴺ=1`); trig enters only for `(w N)ᴺ=1`.
  **Primitivity is proved** (`w_primitive`: `(w N)ʲ ≠ 1` for `0<j<N`, from `cos(2πj/N) < 1`
  strictly — `cos_lt_1` via `cos x = 1−2sin²(x/2)`), so orthogonality holds in the
  **unconditional Kronecker-delta form** `dft_orthogonality_delta`: for `j < N`, `Σ = N·[j=0]`
  — the exact input for ℂ-DFT inversion `F⁻¹F = id`. Quarantined Reals axioms (via `C`/trig).
- **Complex DFT inversion** `DFTInversion.dft_inversion`: on the custom `C`, `IDFT (DFT f) k = f k`
  (`k < N`) with `(DFT f) m = Σ_{k<N} f k·(wc N)^{mk}`, `(IDFT g) k = (1/N)Σ_{m<N} g m·(w N)^{mk}`,
  `wc N = conj(w N)` — the finite Fourier transform on `ℂ` is invertible (`F⁻¹F = id`), the ℂ
  analogue of `WalshHadamard.H²=8I`. Engine: two-index orthogonality `orthogonality_2` (off-diagonal
  vanishing from injectivity `w_pow_inj`, i.e. primitivity) + finite Fubini (`Csum_swap`) + delta
  extraction (`Csum_delta`) — all pure `C`-field algebra. Quarantined Reals axioms (via `C`/trig).
- **DFT convolution theorem** `DFTConvolution.conv_theorem`: the DFT diagonalises cyclic
  convolution — `DFT (f⋆g) m = DFT f m · DFT g m` for `(f⋆g)(n)=Σ_{k<N} f k·g((n−k) mod N)`.
  New ingredient: a cyclic shift permutes `{0..N−1}` (`rotation_perm` via `NoDup_Permutation_bis`
  + shift injectivity) ⟹ reindexing `Csum_reindex`; with root periodicity `Cpow_wc_mod` it gives
  the shift theorem `dft_shift`, then finite Fubini (`Csum_swap`) finishes. With `DFTInversion`
  this is the full finite-Fourier toolkit on `C`. Quarantined Reals axioms (via `C`/trig).
- **Parseval / Plancherel** `Parseval` (`plancherel`, `parseval_norm`): the DFT is (up to `N`) an
  **isometry** — `Σ_k f k·conj(g k) = (1/N)Σ_m F̂_m·conj(Ĝ_m)`, and `Σ_k |f k|² = (1/N)Σ_m |F̂_m|²`.
  Same `orthogonality_2` + Fubini + delta engine as inversion, plus conjugation commuting with the
  transform (`conj_wc_pow`). Completes finite Fourier analysis on `C` (inversion + convolution +
  isometry). Quarantined Reals axioms (via `C`/trig).
- **Characters of ℤ/Nℤ** `CharactersModN` (`characters_of_Z_mod_N`): `χ_a(n)=(w N)^{an}` are the
  characters of the cyclic group `(ℤ/Nℤ,+)`, forming the dual group `ℤ/Nℤ` (`chi_add`, `chi_mul`,
  `chi_pow_N`), with **both orthogonality relations** of the character table (`char_orthogonality_row/col`:
  `Σ χ_a conj(χ_b) = N·[a=b]`) — the DFT orthogonality in character language. **Honest ceiling:**
  these are characters of the *cyclic* group `ℤ/Nℤ`, the abelian orthogonality underlying Dirichlet
  characters; a Dirichlet char mod `N` is a character of the *multiplicative* `(ℤ/Nℤ)*` — cyclic
  ⟹ these via a primitive root, but `(ℤ/Nℤ)*`, primitivity, and L-series are NOT built.
  Quarantined Reals axioms (via `C`/trig).
- **Units mod p + Fermat** `ZmodPStar` (Phase 1 of the actual-Dirichlet-mod-p build):
  `fermat : 1≤a≤p−1 ⟹ a^{p−1} mod p = 1` — **axiom-free**. Units group `(ℤ/pℤ)*` closure
  (`mulmod_in_units`), cancellation (`cancel_mod` via `Gauss`), and Fermat via the
  units-permutation product argument (`units_perm`, `Pi_coprime`). `nat`↔`ℤ` primality bridged
  through `mod` (`prime_mult_nat`, `Zof_nat_divide_inv`). Foundation for the from-scratch
  primitive-root / Dirichlet build (now COMPLETE, Phases 1–5).
- **Euler totient + divisor sum** `Totient` (Phase 2): `totient_divisor_sum : Σ_{d∣n} φ(d) = n`
  — **axiom-free**. Partition of `[1,n]` by `n/gcd(k,n)` into `φ`-sized fibers
  (`count_key_eq_phi` via a membership-`Permutation`, `disjoint_filter_sum`). Counting input for
  the order-counting primitive-root proof (Phase 4).
- **Roots bound over 𝔽_p** `PolyRootsFp` (Phase 3): `dth_roots_bound : #{a∈[1,p−1] : a^d mod p = 1}
  ≤ d` — **axiom-free**. Minimal polynomial theory over `ℤ` + synthetic division (`sdiv`) + factor
  theorem (`factor_mod`) + Lagrange bound `roots_le` (strong induction on degree, `𝔽_p` an
  integral domain via `prime_mult`, `NoDup_incl_length`), instantiated at `X^d−1`. The
  field-theoretic input for the order-counting primitive-root proof (Phase 4).
- **Multiplicative order mod p** `ZmodOrder` (Phase 4a): `ord p a` (least positive period),
  with `ord_least`, `ord_divides`, `ord_div_pm1` (via Fermat), `pow_inj_below` (powers below the
  order are distinct). **Axiom-free.** Foundation for the order-counting primitive-root proof;
  the counting/squeeze (`ψ(d)≤φ(d)`, `Σψ=Σφ=p−1 ⟹ ∃` primitive root) is Phase 4b.
- **(ℤ/pℤ)\* is cyclic** `PrimitiveRoot.units_cyclic` (Phase 4b): for prime `p`, `∃ g, ord p g = p−1`
  (a primitive root) — proven from scratch, unconditionally, **axiom-free**. Order-counting:
  `psi_le_phi` (`ψ(d)≤φ(d)` via surjectivity-onto-roots `root_is_power` + `gcd_of_order`),
  `sum_psi` (`Σψ=p−1`), squeeze against `Totient.totient_divisor_sum` (`Σφ=p−1`) ⟹ `ψ=φ` ⟹
  `ψ(p−1)=φ(p−1)≥1`. This is the genuine cyclicity theorem the whole Dirichlet arc rests on;
  every ingredient axiom-free. Feeds the Dirichlet-character construction (Phase 5).
- **Dirichlet characters mod p + orthogonality** `DirichletModP.dirichlet_characters_mod_p` (Phase 5):
  genuine Dirichlet characters `χ_a` mod a prime `p` (via discrete log base a primitive root:
  `χ_a(n) = (w(p−1))^{a·dlog n}` on units, 0 on multiples of `p`) with `χ_a(1)=1`, period `p`,
  vanishing on multiples, and the orthogonality `Σ_{n<p} χ_a(n)conj(χ_b(n)) = (p−1)[a=b]` —
  reindexing units→exponents (`powers_units_perm`) onto `CharactersModN.char_orthogonality_row`
  (`N=p−1`). Quarantined Reals axioms (via `C`/trig). **Completes the 5-phase from-scratch
  Dirichlet-mod-p build**: the number-theory core (Phases 1–4b, `(ℤ/pℤ)*` cyclic) is axiom-free;
  only Phase 5's `ℂ`/trig is quarantined.
- **Finite Dirichlet L-function / Euler product** `DirichletLEuler.dirichlet_L_function`: the genuine
  theorem-content is **complete multiplicativity** of the character — `dchar_mul` (`χ(mn)=χ(m)χ(n)`)
  and `dchar_pow` (`χ(qᵏ)=χ(q)ᵏ`), proved from scratch via the discrete-log homomorphism
  `dlog_mul` (`dlog(uv)≡dlog u+dlog v mod (p−1)`, from `pw_mod` + `pow_inj_below`); this closes the
  "complete multiplicativity" bullet `DirichletModP` had only advertised. Plus the local Euler factor
  `local_euler_factor` (`(1−χ(q)x)·Σ_{k<K}χ(qᵏ)xᵏ = 1−(χ(q)x)^K`, genuine geometric closed form) and
  the finite Euler product `dirichlet_L_euler_product` (`PrimonGas` state-sum machinery ported to `C`
  as `euler_product_C`, at character-twisted fugacities: `Σ_states ∏_q(χ(q)x_q)^{k_q} = ∏_q Llocal_q`).
  **Analogy boundary, stated honestly:** the *finite* Euler product = product of local factors is
  proved; `L(s,χ)=∏(1−χ(q)q⁻ˢ)⁻¹=Σχ(n)n⁻ˢ` as an *infinite* product/series (needing the
  state↔integer unique-factorisation bijection and convergence) stays prose. Quarantined Reals axioms
  (via `C`/trig).
- **Möbius inversion**, three forms — all genuine over the stated (single-prime / chain) domain:
  `MobiusReciprocal` (`(1−x)·psum = 1−x^K`, `∏(1−p⁻ˢ)=1/ζ` finite form), `VonMangoldt`
  (`Λ = μ⋆log`, `Σ_{d|pᵐ}Λ = log pᵐ`), `PosetMobiusFTC` (zeta/Möbius transforms mutually inverse).
- **CRT coincidence** `FreeDivMeet.crt_lattice_coincidence`: genuine, but proved **at the two
  prime-power axis generators**, not the full interior lattice (see §3).
- **p-adic ultrametric** `Padic`, `PadicMetric`: genuine ultrametric (norm / strong triangle).
- **Order → topology** `PosetTopology`: genuine Alexandrov topology + `monotone ⇒ continuous`;
  `FiniteTopology` a genuine finite instance; `ChainTower` a genuine inverse system.  The Galois
  connection `α ⊣ γ` (single biconditional `α x ≤ y ↔ x ≤ γ y`) is shown to generate the whole
  closure calculus — unit/counit and the *derived* monotonicity of `α,γ`, then `cl=γ∘α` extensive/
  monotone/idempotent (`cl_extensive`/`cl_monotone`/`cl_idempotent`).
- **ZETA = THE LINEARIZED GALOIS CLOSURE** `ZetaClosureBridge.zeta_pos_iff_dclose` (**axiom-free**):
  makes precise the slogan *Möbius/zeta is the ring-linearized, invertible version of a Galois
  connection*.  On the single-prime chain both operators aggregate over the **same** down-set list
  `seq 0 (S n)`; only the monoid differs.  The **Boolean/order layer** `dclose P n := existsb P
  (seq 0 (S n)) = ⋁_{d≤n} P d` is a genuine **closure operator** (`dclose_extensive`/`_monotone`/
  `_idempotent` — exactly the `PosetTopology.cl` laws a Galois connection yields), and the **additive/
  ring layer** is `PosetMobiusFTC.zeta_t` on the indicator `ind P`.  The bridge — *reading `+` as `⋁`,
  i.e. testing the sum for nonzero* — is `0 < zeta_t (ind P) n ↔ dclose P n = true`.  Capstone
  contrast: `dclose_lossy` exhibits distinct predicates (`{1}` vs `{1,3}`) with **equal** closure
  (`dclose_first_at_1`: the closure sees only the least true position), so the closure is
  non-injective and has **no inverse** — whereas `zeta_t` is a bijection (`ftc_1`/`ftc_2`).  *That* is
  why Möbius inversion needs the group `(+)` (subtraction = inclusion–exclusion) and cannot exist over
  the idempotent join `(⋁)`.  `Print Assumptions` = **Closed under the global context**.
- **Inverse limits** `InvLimit` (ω+1), `PadicIntegers` (`ℤ_p`), `PadicRing` (`ℤ_p` a commutative
  semiring): genuine, with the deferrals in §3.
- **Analytic Euler factor / log-derivative** `EulerFactorR`, `VonMangoldtR`, `LadderDerivR`:
  genuine limits/derivatives over ℝ — but **per single prime factor**, not summed over all primes.
- **The 3-symbol algebra `{I,N,F}`** `INFMonoid`: a genuine theorem identifying it as the
  commutative monoid `({+1,−1,0},×) = (𝔽₃,×)` (via an injective hom `val`) whose unit group is
  the Walsh sign group `Z/2 = {I,N}`, and — via `sym_of_mu` — **exactly the value-monoid of the
  Möbius function on prime powers** (`MobiusReciprocal.mu_pp`), `F` = the squarefree collapse.
  Axiom-free. (Honest: this is a proved structural *identification*/bridge between the two arcs,
  not a claim beyond it.) `INFProduct` inducts it to `n` observers: the `n`-fold monoid
  `({I,N,F})ⁿ` (`op_n` commutative monoid) with product-sign `val_n`, proving the homomorphism
  `val_n_op`, the free-split `val_n_app` (`val_n (a++b) = val_n a·val_n b` — arbitrary
  observer/observed partition), the one-`F` veto `val_n_zero_iff` (`val_n l = 0 ⟺ In F l`), and
  `val_n_mu` (= `μ` of a product of `n` prime-powers). "Observer" stays an *interpretation* of a
  coordinate/prime; the theorems are about the product monoid. Axiom-free.
- **Hermitian operator on the observer/observed/observation triad** `ObserverTriad`: a genuine
  self-adjoint (Hermitian-over-ℝ = symmetric) operator `M` with real spectrum `{0,+√2,−√2}` and
  an orthogonal eigenbasis (`M_self_adjoint`, `eig_*`, `ortho_*`), the eigenvalue-0 mode being
  the observer−observed kernel. Axiom-quarantined (ℝ). Honest: the role names are
  interpretation; the theorems are about the symmetric operator. `ObserverSwap` adds the
  involution cousin — the observer↔observed swap `S` (self-adjoint + `S²=I`, spectrum `{+1,−1}`)
  realising the unit group `{I,N}` of `INFMonoid` (`IZR(val N)=−1`, `IZR(val I)=+1`), with `v0`
  simultaneously `M`'s kernel and `S`'s `−1` mode, plus the reflection residue decomposition.
  `ObserverSpectral` shows `M` and `S` are **commuting observables** (`[M,S]=0`) simultaneously
  diagonalized by `{v0,vp,vm}` — the finite spectral picture of simultaneously-measurable
  observables (`v0` = `(0,−1)`, `vp/vm` = `(±√2,+1)`). Axiom-quarantined; role names interpretation.
- **Finite Fourier + sampling** `WalshHadamard` (DFT on `F₂ⁿ`: shift, convolution, `H²=8I`
  inversion, Parseval), `WalshSampling` (the finite Shannon–Nyquist sampling theorem: comb
  transform `Ĥ 1_H = |H| 1_{H⊥}`, Poisson summation, band-limited reconstruction), and
  `WalshUncertainty` (the **Donoho–Stark discrete uncertainty principle**: `f≠0 ⟹
  |supp f|·|supp Ĥf| ≥ 8 = |F₂³|` — the l¹/l∞ argument done entirely over `ℤ`, the complement
  to sampling: it bounds *why* you cannot localize in space and frequency at once): all **genuine
  theorems** about the actual transform (axiom-free). The *bridge* framing — Poisson summation as
  the shadow of `ζ`'s functional equation, and Fourier/sampling inversion as the finite instance
  of Perron's contour inversion (cousin: `PosetMobiusFTC` = Möbius inversion) — is honest
  **lineage/shared-structure**, **not** a formalized `Ĥ → ζ` theorem (which needs the contour).

**Structural analogies** — a real theorem is proved, but about a *toy model*; it is **not** a
statement about the classical object it evokes. These must never be cited as progress on the
hard problem:

- `MassGap` — "mass gap" = the spectral gap `⅓` of a toy `𝔽₂³` diffusion; the `E=mc²`/mass
  reading is an interpretation, **not** Yang–Mills. (The nat-level gap is a real theorem; the
  physics identification is analogy.)
- `BitDensity`, `BitCountContrast` — the "critical-line symmetry" is the binomial complement
  `C(n,k)=C(n,n−k)`, and the "growth contrast" is boundedness of a finite bit-count vs the
  (unformalized) `N(T)`. **Explicitly analogies** — the repo has no `ζ`, no zeros, no `N(T)`.
- `SpectralTripleRH` and relatives — spectral-triple *scaffolding*, not a proof of RH.

**No result in this arc proves, or materially advances, RH, the Yang–Mills mass gap, or any
Millennium problem.** The arc formalizes the *elementary skeleton* (Euler product ↔ CRT,
Möbius inversion, order→topology, inverse limits/completions) that those problems sit far above.

---

## 3. Complete structure vs curated bundle

Each file's `*_master`/bundle theorem collects **selected** facts, not necessarily a complete
structure. Known gaps between "what the name suggests" and "what is proved":

- **`FreeDivMeet`**: the CRT coincidence at the axis generators (`FreeDivMeet`), now extended
  to the full **order embedding** `code u ∣ code v ↔ fle u v` (`FreeDivMeetIso.code_order_iso`),
  i.e. `Div(pᵃqᵇ) ≅ [0..a]×[0..b]` as posets. What is still **not** proved is the *lattice-
  operation* form `gcd(pⁱqʲ,pⁱ'qʲ') = p^min·q^min` as an equation (the order iso gives the
  poset structure; the explicit coordinatewise gcd/lcm formula is not separately derived).
  `PrimeFactorizationN` now **generalizes the order embedding to `n` distinct primes**
  (`code_order_iso_N`) and adds **injectivity** (`code_inj`); `PrimeFactorizationExists` adds
  **surjectivity** onto the `{ps}`-smooth positives (`code_surj`, via a total `p`-adic
  valuation). Together (`code_bijection_smooth`) `code` is a full **bijection** exponent-tuples
  ↔ `{first n primes}`-smooth positives — unique factorization over the first `n` primes, both
  existence and uniqueness. Axiom-free.
- **`PadicRing` / `PadicRingOpp`**: the commutative **semiring** axioms (`PadicRing`) *and* the
  **additive inverse** (`PadicRingOpp.Zadd_opp_l`, with `neg_coh` handling nat truncated
  subtraction) are now proved — so `ℤ_p` is a proved **commutative ring**. Only the Coq
  `Add Ring` *tactic registration* (setoid Proper boilerplate) is still not done; the ring
  axioms themselves are complete.
- **Möbius / von Mangoldt / FTC**: proved for the **single prime** (chain), the **two-prime
  product of chains** for the FTC (`ProductFTC`), and lifted to the **two-prime product** for
  Möbius (`ProductMobius.mu2_reciprocal`: `(1−x)(1−y)`) and von Mangoldt
  (`ProductMobius.vm2_interior_zero`: Λ supported on prime-power axes). All generalise to `k`
  primes by iteration. The general **arbitrary-`ℕ⁺`** divisor-sum forms (needing divisor
  enumeration / factorisation of a general `n`) are still **not** proved.
- **Infinite process**: `ZetaConverge.zeta2_converges` proves the infinite sum `Σ_{n≥1} 1/n² =
  ζ(2)` **converges** (existence, not the value `π²/6`; the same telescoping bound gives
  `Σ 1/nˢ` for all `s ≥ 2`) — the first genuinely-infinite, over-all-numbers object.
- **Primorial-relativized Euler product**: `PrimorialEuler` builds the primorial tower
  `EP n = ∏_{first n primes} (1−p⁻²)⁻¹` and proves each rung is a finite Euler product
  (`EP_is_limit`) and the tower is monotone (`EP_monotone`), mirroring the primorial's growth.
  `PrimorialEulerBound.EP_converges` now proves the tower **converges** (the rungs are uniformly
  bounded, `EP n ≤ 2`, via a telescoping majorant `M n = 2−2/(n+2)`, under `P i ≥ i+2` which the
  actual primes satisfy) — so the primorial-relativized Euler product **exists as a limit**.
  `PrimorialZeta.tower_is_zeta` then proves — **rigorously, modulo one isolated hypothesis** —
  that the tower's limit **is ζ(2)**: given the two consequences of the Euler factorization
  `EP n = Σ_{{first n primes}-smooth m} 1/m²` (namely `∀n, EP n ≤ ζ(2)` and
  `∀N, ∃n, zpart N ≤ EP n`), the analytic squeeze (`growing_ineq` + `lim_le` + `Rle_antisym`)
  gives `Un_cv (EP P) ζ(2)`. So the two infinite processes (`Σ 1/n²` and the product tower)
  provably share a limit. The factorization crux has two halves; the **uniqueness** half is now
  **done**: `PrimeFactorizationN` proves `code ps : exponent-tuples → {first n primes}-smooth
  numbers` (`∏ pᵢ^{kᵢ}`) is an **order embedding** and **injective** (`code_inj`,
  `code_order_iso_N`) — unique factorization over the first `n` primes, as a bijection onto its
  image, generalizing `FreeDivMeetIso` from 2 to `n` distinct primes (axiom-free, via the
  `p`-adic cancellation `prime_pow_cancel`). The **existence** half is now **also done**:
  `PrimeFactorizationExists` proves `code ps` **surjective** onto the `{ps}`-smooth positives
  (`code_surj`) — every `m>0` whose prime divisors lie in `ps` has an exponent tuple — via the
  total `p`-adic valuation (`padic_val`, well-founded recursion on `0≤·<m`) and
  `has_prime_divisor` (every `m>1` has a prime divisor, via stdlib `not_prime_divide`). So
  `code_bijection_smooth` makes `code` a genuine **bijection** exponent-tuples ↔ `{ps}`-smooth
  positives — both halves of the factorization crux complete, **fully axiom-free**. The
  **reindexing** is now also done: `EulerReindex` proves (over ℚ, axiom-free) `weight_fug`
  (the primon-gas weight with fugacity `1/p²` equals `1/(code ps ks)²`) and hence `euler_reindex`
  — the finite Euler product `∏ᵢ Σ_{k<K} pᵢ⁻²ᵏ = Σ_{occupation states} 1/(code ps ks)²`, a sum
  of `1/m²` over the (pairwise distinct, `codes_distinct`) smooth numbers `m = code ps ks`.
  What remains open toward `∏_p = ζ(2)` is then: (i) tying this ℚ reindexing to the ℝ tower
  `EP`/`zpart` and taking `K→∞` (the analytic bridge), and (ii) "every `m ≤ pₙ` is
  `{first n primes}`-smooth" (a property of the prime *enumeration* `P` — that it lists all
  primes in order — not of `code`). The **ℝ-side domination** for (i) is now proved:
  `RecipSquareBound.recip_sq_nodup_bound` — any finite set of distinct positive integers sums
  (of `1/m²`) to at most `ζ(2)` (via `incl_sum_le` over `List.remove` + `seqsum_zpart` +
  `growing_ineq`). This is the tight bound (`ζ(2) < 2`) that gives `EP n ≤ ζ(2) = Hupper` once
  the ℚ→ℝ transport of `euler_reindex` feeds `EP n`'s reindexed (distinct-smooth-number) form
  into it. **That transport is now done**: `EulerProductZetaBound.euler_factor_le_zeta` proves,
  for any list `ps` of distinct primes, the finite Euler product `∏_{p∈ps}(1−p⁻²)⁻¹ ≤ ζ(2)` —
  i.e. **`Hupper` for the concrete prime enumeration** — via `Q2R` transport of `euler_reindex`
  (`euler_partial_reindex_R`: the ℝ partial product = sum of `1/m²` over the coded numbers),
  `codes_nat_nodup`/`code_pos` (distinct positive integers, using `gstates_nodup`),
  `recip_sq_nodup_bound`, and `K→∞` (`euler_product_R` + `lim_le`). So the full chain
  **primon gas → reindex → factorization bijection → ζ(2) domination → `EP ≤ ζ(2)`** is
  machine-checked (quarantined Reals axioms). **`Hlower` is now also done**, and the arc is
  **closed**: `EulerProductZeta.euler_product_zeta2` proves the unconditional Euler product
  formula `∏_{p prime, p≤B}(1−p⁻²)⁻¹ → ζ(2)` — a squeeze between `zpart_le_euler` (`Hlower`, via
  a prime enumeration `primes_upto`, `small_smooth`, factorization *existence* `code_surj` with
  bounded exponents `entry_pow_le_code`/`gstates_complete`, and `incl_sum_le`) and the constant
  `ζ(2)` (Hupper). This is the genuine classical Euler product identity at `s=2`. What is **not**
  done (deliberately, and cleanly separable): the *value* `π²/6`; general `s` and the `−ζ'/ζ`
  Dirichlet series; and the nat-indexed `PrimorialZeta.tower_is_zeta2` repackaging (which would
  need an *ordered* "nth prime" enumeration — the `primes_upto`/bound-indexed form here sidesteps
  that and is the more natural statement).
  Also still **not** proved: the value `π²/6`, `ζ` as a general infinite-product identity for
  `s≠2`, `−ζ'/ζ`, and the `1<s<2` range.
- **Contour-free prime bridge** (`AbelSummation`): the analytic zeta→primes bridge runs through a
  *contour integral* (Perron + residue theorem, invariant = winding number), which our system
  has no machinery for (no ℂ, no Cauchy, no analytic continuation, no zeros). We instead build
  its **elementary shadow**: `abel_summation` (summation by parts) is the discrete
  integration-by-parts that replaces the contour shift; combined with `Λ = μ⋆log` it is the
  pre-Riemann toolkit for Chebyshev's `ψ(x) ≍ x`. **Status:** the tool (`abel_summation`) **and**
  the arithmetic crux — the general-`n` identity `Σ_{d|n} Λ(d) = log n` — are **done**.
  `VonMangoldtGlobal.vonmangoldt_identity` proves it for a genuine global `Λ:ℕ→ℝ`, entirely in
  `nat` (`Nat.gauss`) + `R` (only `ln` pulls the quarantined classical Reals axioms), via: `spf`
  proved prime; the **coprime divisor split** `c=gcd(c,a)·gcd(c,b)` (`split_divisor`, the Gauss
  keystone); the **divisor-list bijection** `divisors(a·b)≅divisors(a)×divisors(b)`
  (`divisors_prod_perm`, `dsum_prod`); `Λ` with `Lam_mul_zero` (`Λ(d·e)=0` for coprime `d,e≥2`,
  via `is_pow_true_pow`+`prime_dvd_prime_pow`); **multiplicativity** `dsum Λ (a·b)=dsum Λ a+
  dsum Λ b` (`dsum_mult`, pure sum manipulation); the **prime-power base** `dsum Λ (p^k)=ln(p^k)`
  (`dsum_primepow`); and the strong-induction **assembly** (peel `p=spf n`, `n=p^a·m` coprime via
  `pval`, `dsum_mult`+base+IH+`ln_mult`). This closes the "general-`n` divisor sums" gap. The
  **order swap is now also done** (`Chebyshev.order_swap_identity`): `Σ_{n≤N} log n =
  Σ_{d≤N} Λ(d)⌊N/d⌋` — the Dirichlet-hyperbola / elementary-Perron bridge, proved without Fubini
  (both sides satisfy `f(S N)=f N + dsum Λ(S N)`, key nat fact `⌊(N+1)/d⌋=⌊N/d⌋+[d∣N+1]`). What
  remains for `ψ(x)≍x` is the **final squeeze**. Its **combinatorial building blocks are now
  built** (`Chebyshev`): `Lam_nonneg` (`Λ≥0`), the floor lemma `floor_half_step`
  (`⌊N/d⌋−2⌊N/(2d)⌋=(⌊N/d⌋)mod 2∈{0,1}`), and `ψ`. These give (via `order_swap_identity`) the
  sandwich `ψ(N)−ψ(⌊N/2⌋) ≤ D(N) ≤ ψ(N)` with `D(N)=T(N)−2T(⌊N/2⌋)=Σ_d Λ(d)·((⌊N/d⌋)mod 2)`,
  reducing `ψ≍x` to the single **numerical input** `D(N)≈N·log 2`. The **factorial–log bridge
  is now built** (`Chebyshev.Tlog_eq_ln_fact`: `T(N)=Σ_{n≤N}log n = log(N!)`), so
  `D(N)=log(N!/(⌊N/2⌋!)²)=log C(2M,M)`. The remaining `ψ≍x` pieces (a dedicated ~pass): the
  **binomial↔factorial** identity `C(n,k)·k!·(n−k)! = n!`, the **row sum** `Σ_k C(n,k)=2^n`
  (generalizing `BitDensity.cube3_total`), **unimodality** `C(2M,M) = max_k C(2M,k)` ⟹
  `4^M/(2M+1) ≤ C(2M,M) ≤ 4^M`, the reformulation `D=Σ_d Λ(d)·((⌊N/d⌋)mod 2)` (order-swap +
  range extend), and the `T(N)−2T(⌊N/2⌋)` telescoping. **Hard ceiling:** the *sharp* `ψ(x)∼x` (PNT), the explicit
  formula, and anything about zeta *zeros* genuinely require the contour step / complex analysis
  we deliberately do not build.
- **Analytic layer** (`EulerFactorR`, `EulerProductR`, `LadderDerivR`, `NxnZero`, `VonMangoldtR`):
  the single Euler factor, the **finite** Euler product (`EulerProductR`), the number operator as a
  derivative (`LadderDerivR`), and now the number-weighted series `Σ k xᵏ = x/(1−x)²`
  (`NxnZero.number_series`, built on the from-scratch `n·xⁿ→0`) are proved. The **infinite**
  Euler product, full `ζ`, `−ζ'/ζ = Σ Λ(n)n⁻ˢ` over all primes, and general term-by-term
  differentiation are **not** proved (stdlib-only; no analysis library).
- **`ChainTower`/`InvLimit`**: the tower's inverse limit is **ω+1** (profinite completion of the
  chain), *not* `ℤ_p`. `ℤ_p` is the separate `PadicIntegers` tower (`ℤ/pⁿ`, reduction maps).
- **`Padic`**: the ultrametric on ℚ; the **completion** to `ℚ_p` (Cauchy quotient) is **not**
  built — `PadicIntegers`/`PadicMetric` realize `ℤ_p` as an inverse limit instead.

---

## 4. What this arc *is*

A clean, interlocking, almost-entirely-axiom-free formalization of the **conceptual scaffold**
linking elementary number theory, order theory, and finite topology: Euler product ↔ CRT,
Möbius inversion (three forms), order → Alexandrov topology, and inverse-limit completions
(`ω+1`, `ℤ_p`). Its value is that every individual claim is small, true, and machine-checked,
and the honest boundaries above are stated rather than blurred. It is a trustworthy sandbox,
not a proof of anything deep.
