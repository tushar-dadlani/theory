# Fock spaces ↔ ∞ / 0 / the dynamics — the map

_What in this repo links a Fock-space picture to the repo's notions of infinity, zero, and the dynamics.
Marked throughout for what is a proven construction vs. a latent analogy vs. an openly-flagged gap._

## One picture links all four: `Tr(e^{−sH}) = ζ(s)`

The **primon gas**: each prime `p` is a bosonic **mode**, an integer `n = ∏ p^{k_p}` is an occupation state,
its energy is `log n = Σ k_p log p` (additive over modes). The heat semigroup `e^{−sH}` of the log-Hamiltonian
`H = diag(log n)` has **partition function ζ(s)**. That single equation is the hub:

- **dynamics** = the flow `e^{−sH}` (imaginary-time / Mellin scaling); `s` (or `β`) = (imaginary) time / inverse temperature;
- **∞** = the archimedean completion — the Γ-factor "mode at infinity" (`Γ(s)ζ(s)`) and the profinite/primorial
  tower of all occupation states `n → ∞`;
- **0** = the vacuum (0-particle ground state), the trivial zeros forced by the ∞-mode `1/Γ`, and the nontrivial
  zeros of ζ (the would-be operator spectrum);
- they **meet at the self-dual center `Re = 1/2`**, the fixed point of the functional-equation involution.

**Now a proven theorem** (`spectral-theory/Ell2Partition.v`):
```
partition_function_is_zeta : forall b, 1 < b ->
  { Z | Un_cv (fun N => diag_trace (z b) N) Z
        /\ (forall N, diag_trace (z b) N = diag_trace (fun n => exp ((-b) * Hlog n)) N) }
```
`Tr_N(e^{−bH}) = ∑_{n=1}^N e^{−b log n} = ∑ n^{−b} → ζ(b)` for `b > 1`.

## Fock-space ingredients we have (two registers)

**(a) Combinatorial / second-quantized primon gas** (over ℚ/ℝ, on lists & monomials — no Hilbert completion):
- `PrimonGas.v` — `weight`(:118), `gstates`(:125), `energy`/`energy_additive`(:178,:186) energies `log p`,
  `euler_product`(:146), `primon_gas`(:218).
- `LadderOps.v` — `create`(:40)/`annihilate`(:41)/`number`(:42), `Dx`/`Nx`(:46,48) `N = x d/dx`,
  `annihilate_vacuum`(:54), Weyl relation `weyl`(:91) `[D,M]=1`.
- `LadderDerivR.v` — analytic number operator `N = x d/dx`, energies `log p` as derivatives.
- `HagedornTransition.v` — the KMS/critical-temperature behaviour: `Zpart b N = ∑(k+1)^{−b}` diverges at `b=1`
  (`Zpart1_diverges`:81), converges for `b>1` (`Zpart_cv`:180) — the primon-gas phase transition = ζ's pole.

**(b) One-particle ℓ² Hilbert space + diagonal self-adjoint operators** (the rigorous single-particle sector):
- `Ell2.v` — completed `ℓ²(ℕ)` over ℝ (`Ell2`:49, `ip`:179, `Ell2_complete`:570).
- `Ell2Operator.v` — `Dmul`(:44) diagonal operator, `Dmul_selfadjoint`(:66), `Dmul_bound`(:79).
- `Ell2Zeta.v` — `z s n = n^{−s}` (`Z_s = e^{−sH}`)(:74), `Hlog = diag(log n)`(:142),
  `zeta_is_exp_neg_sH`(:145), `diag_trace`(:60), `zeta_partition : Tr Z_s = ζ`(:122),
  `vonmangoldt_zeta_trace`(:133).
- `Ell2VonMangoldt.v` / `Ell2MellinVM.v` / `CDiagOperator.v` — the von Mangoldt operator `D_Λ` and its
  Mellin regularisation, traces `→ ψ`, `→ −ζ'/ζ`.
- `BerryKeatingH.v` — the `xp` Hamiltonian `H = qp+pq`(:27), `H_selfadj`(:29), vacuum `omega0`(:38),
  `omega0_H = 0`(:51).

**(c) The bosonic Fock tower on `Ell2`** (`Ell2Fock.v`) — by unique factorisation the primon Fock space over
the prime modes **is** `ℓ²(ℕ≥1)` itself (occupation vector `(k_p)` ↔ integer `∏ p^{k_p}` = basis vector `e_n`):
- `Nop p = diag(v_p n)` — per-prime number/occupation operator, `Nop_eigen : N_p e_i = v_p(i)·e_i`;
- `crea p : e_m ↦ e_{p·m}` (creation), `anni p : e_n ↦ e_{n/p}` (annihilation);
- `anni p (crea p (e m)) = e m` (`a_p a_p† = I`, creation is an isometry); distinct modes commute
  (`crea_crea_e`); vacuum `e_1` with `anni p (e 1) = 0` and `N_p(e 1) = 0`; all operators keep basis vectors in
  `ℓ²`. Bundled in `primon_fock_tower`.

No CCR/CAR on a *completed* many-body space, no √-normalised ladder / coherent states yet — the tower is the
occupation-number (multiplicative-shift) representation on the single `Ell2`. Closest in spirit:
`PrimonGas`+`LadderOps`; closest in rigour: `Ell2`+`Ell2Operator`+`Ell2Fock`.

## Dynamics (the flow)

- **Heat semigroup / imaginary-time evolution** `Z_s = diag(n^{−s}) = e^{−sH}`, `H = Hlog = diag(log n)`
  (`Ell2Zeta.v`). Partition function = ζ (`Ell2Partition.partition_function_is_zeta`).
- **von Mangoldt operator** `D_Λ` (`Ell2VonMangoldt.vm_eigen`:36), trace `= ψ` (`vm_trace_eq_psi`:66);
  Mellin-regularised `M_s` (`Ell2MellinVM.v`, `CDiagOperator.trace_cv_neg_zeta_ratio`:85) trace `→ −ζ'/ζ`.
- **Mellin = the scaling/dilation flow** — `MellinOperatorBridge.v` (`mode_mellin`:27, `mellin_trace_cv`:49):
  summed Mellin modes `→ Γ(s)ζ(s)` (heat-kernel ↔ spectral zeta). `MellinKernel.mellin_scale`: Mellin = scaling × Γ.
- **The FE involution** `Srefl : z ↦ 1−z` (`SpectralReflectionBridge.v`:41, `Srefl_involutive`:44) — a ℤ/2
  symmetry of the dynamics; the new `RH_iff_no_left/right`(:102,116).
- **Berry–Keating dilation** `Hdil = −i(x d/dx + ½)` (`BerryKeatingDilation.v`) → boundary triple
  (`SelfAdjointExtension.v`, deficiency (1,1)) → Weyl function `Wxi` (`WeylFunction.v`) → zeros-as-phase-windings
  (`WeylWinding.v`) → `HilbertPolyaCapstone.v`. The most quantum-dynamical content, axiom-clean; reality of
  candidate ordinates is a *theorem* (`icayley_real`), but the spectrum=zeros step is an open `Prop`.

## Infinity

- **The archimedean place ∞ = the "mode at infinity" Γ** completing the finite-prime Fock modes:
  `MellinOperatorBridge.mellin_trace_cv` realises `Γ(s)ζ(s)`; Γ is the archimedean Euler factor of
  `ξ = ½s(s−1)·π^{−s/2}Γ(s/2)·ζ(s)`. ∞ is **not primitive**: `|n|_∞ = 1/∏_p|n|_p`
  (`ArchimedeanTower.archimedean_reconstruct`:60), the product-formula dual of the primes.
- **The tower of all occupation states `n → ∞`** = the profinite/primorial completion:
  `ProfiniteInteger.Zhat = lim Z/n!Z = ∏_p Z_p` (the factorial tower `M n = n!` — the same `N!` as the Gauss
  limit), `PrimorialInfinity.adele_split : A_Q = R × A_f`(:104) (finite-prime Fock factor `A_f` × archimedean
  `R`), `ProductFormulaQ.v`, `ArakelovDegree.v`.
- The Hagedorn transition (`b → 1⁺`) is the high-temperature limit where ζ diverges.

## Zero

- **The vacuum / 0-particle ground state** — `annihilate_vacuum`(LadderOps:54), `omega0_H = 0`(BerryKeatingH:51).
- **The trivial zeros** `ζ(−2m) = 0` — forced by the archimedean ∞-mode `1/Γ_ext(x/2)` vanishing at Γ's poles
  (`ZetaTrivialZeros.zeta_ext_trivial_zero`:50); `ζ(0) = −½` at the FE pole (`ZetaZero`).
- **The nontrivial zeros** `XiC z = C0` — the spectrum the Hilbert–Pólya operator *would* carry
  (`RiemannHypothesis.v`:33), the open target of the Berry–Keating chain.
- **`0` as the ring origin dual to ∞** — `p^∞ = 0` (`ProfiniteLimits.padic_top_is_zero`:53, the ∞/0/−∞
  triangle `infinity_zero_neginfty`), adjoined absorbing `0` (`MonoidAlgebraZero.AZero`).

## Where it all meets: the self-dual center `Re = 1/2`

The `0 ↔ ∞` duality **is** the functional equation `s ↔ 1−s`. Its involution `Srefl`/`Sbar` is fixed exactly on
the critical line (`SelfDualCenter.self_dual_center`:45), and that `½` is the same `½` as the theta self-dual
weight `θ(1/t) = t^{1/2}θ(t)` (`SelfDualCenter` → `GaussSelfDual`). So the archimedean "point at infinity" and
the zeros meet at the self-dual center — the fixed point of the dynamics' symmetry.

**Tie-in to the Γ-nonvanishing work** (`GammaWeierstrass.v` / `GammaCWeierstrass.v`): proving `Γ ≠ 0` on `{Re>0}`
is exactly the statement that the archimedean ∞-mode contributes **only poles (trivial zeros), never zeros** —
"the mode at infinity adds no spurious excitations." And `γ` (Euler–Mascheroni), built for the prime-side
Mertens/Nicolas work, now appears on the archimedean Γ side via the Weierstrass product — the same constant on
both sides of the `R × A_f` split.

## The honest gaps (flagged by the repo's own docs)

1. **No literal Fock space** — only the one-particle ℓ² + combinatorial occupation states.
2. **No wired spectral triple `(A, H, D)`** — `docs/ncg_monoid_algebra_thesis.md` flags the number/Dirac
   operator `D`, the crossed product, and `Tr(e^{−βD}) = ζ` + KMS as **open**. (`Ell2Partition` supplies the
   `Tr(e^{−βH}) = ζ` half on the one-particle space.)
3. **The Hilbert–Pólya gap** — every proven operator's *spectrum* is integer/prime data `{n^{−s}}`/`{Λ(n)}`,
   **not** the zeros; `docs/hilbert_polya_map.md §5` says closing it ≡ RH.
4. Legacy `SpectralTripleRH.v:250 Axiom berry_keating_correspondence` is a tautology; superseded by
   `SpectralTripleRH_closed.v` + the `HilbertPolyaCapstone` chain.

## What would make more of the link real (next steps)

- **Done:** `Ell2Partition.partition_function_is_zeta` — `Tr(e^{−bH}) = ζ(b)`, `b>1`.
- **Done:** `Ell2VMPartition.vm_partition_converges` — `Tr(D_Λ · e^{−bH}) = ∑ Λ(n) n^{−b} → −ζ'/ζ(b)`, `b>1`.
- **Done:** `Ell2Fock.primon_fock_tower` — the bosonic Fock tower on `Ell2` (per-mode number/creation/
  annihilation operators, `a_p a_p† = I`, commuting modes, vacuum `e_1`).
- **Larger, remaining:** the √-normalised CCR (`[a_p, a_p†] = 1`) and adjoint structure as bounded/unbounded
  operators with full ℓ² reindexing; wiring the full NCG spectral triple with the `Ẑ^×` symmetry (the `ncg`
  thesis milestone); and — the deep gap — an operator whose *spectrum* is the ζ-zeros (`hilbert_polya_map §5`).
