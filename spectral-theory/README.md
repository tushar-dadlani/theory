# Spectral theory

Spectral algebra and events, the Dirac operator, eigen-systems, self-adjoint structures, the standing wave, and the spectral triple approach to RH.

`WalshHadamard.v` is the Fourier transform native to the framework's xor/Fano structure: the Walsh–Hadamard transform on the Boolean cube F₂³. It is the first *actual* transform in the repo (a linear operator, not a comment), and proves — axiom-free — that it is symmetric, a self-inverse-up-to-scale involution (H² = 8·I), turns translation into a ±1 character sign, turns xor-convolution into a pointwise product, and realises the `StandingWave.v` apex reflection as a Fourier sign flip whose ±1 eigenspaces are the nodes and antinodes.

`StandingWaveSpectrum.v` closes the loop: on the observer square F₂², it builds the amplitude signal directly from `StandingWave.v`'s own `fwd_*`/`inf_*` counts (proving it equals (−1, 0, 0, +1)), shows the apex reflection negates it (a −1-eigenvector), and concludes — both structurally via the shift theorem and by computation — that its Walsh spectrum is `(0, −2, −2, 0)`: exactly zero on the node frequencies and carrying all its weight on the antinodes. StandingWave's hand-counted table is thus the eigen-spectrum of a real Fourier transform.

`HeatFlow.v` runs the transform forwards in time: it puts a lazy bit-flip **diffusion (heat) step** on real signals over the cube F₂³ and proves the Walsh–Hadamard transform **diagonalizes** it — `WHr (step f) y = μ(y)·WHr f y` with `μ(y) = 1 − |y|/3 ∈ {1, ⅔, ⅓, 0}` — so `k` heat steps raise each eigenvalue to the `k`-th power. The DC (spatial-mean) mode is stationary (`μ = 1`, conserved), every other mode contracts (`μ ≤ ⅔`, spectral gap ⅓), and `iterate k f → equilib f` (the flat signal at the spatial mean): the deviation is exact-zero on DC and crushed by `(2/3)ᵏ` on every other mode. This is the rigorous form of "the temperature falls out of a static superposition." Standard `Reals` axioms only; no `admit`.

`MassGap.v` makes the "gap = mass gap" identification precise. Reading a Walsh mode `χ_y` as a state of energy `|y|` (number of flipped bits = quanta), it proves the bridge `μ(y) = 1 − |y|/3` (so `HeatFlow`'s decay eigenvalue is set by the energy), that the vacuum (`y=0`) is massless and stationary, and that the lightest excitation (`|y|=1`, `μ=2/3`, the slowest-decaying transient) has energy 1. That single number `1` is then shown to be simultaneously the `EigenSystem.spectral_gap` of the energy spectrum, the `physics.has_mass_gap` of the excitation spectrum, and — via `E=mc²` at `c=1` — the rest mass of the lightest excitation (`gap_is_mass_gap`). The nat statements are axiom-free (`cube_spectral_gap` is "Closed under the global context"); the bundled master theorem uses the standard `Reals` axioms only for the `μ` bridge.

`Involution.v` is the honest form of "no involution is free." A reversible (orthogonal) involution is lossless — we proved `Rop` orthogonal — so that slogan is *false* as an axiom and is **not** assumed. What is true and proved is the **residue decomposition**: every `f = sym f + anti f`, where `sym f = (f+Rop f)/2` is `Rop`-fixed (the free, conserved part) and `anti f = (f−Rop f)/2` is `Rop`-negated (the residue, a −1-eigenvector); the residue vanishes exactly on fixed points, the two sectors are orthogonal, and the reflection is not globally free (the standing-wave amplitude is a *pure* residue). The residue is precisely the antisymmetric/antinode part a diffusion dissipates — the residue is the seed of the flow. Standard `Reals` axioms only; no `admit`.

`Landauer.v` charges the cost of the involution to the diffusion. It puts a lazy bit-flip diffusion `stepQ` on the square (`Rop`'s space) and proves the residue is an exact ½-eigen-sector — `stepQ (anti f) = ½·anti f` — because `e0 ⊕ e1 = DIAG` makes the two neighbours `Rop`-conjugate and they cancel. Defining dissipated heat as lost L²-energy `⟨g,g⟩ − ⟨stepQ g, stepQ g⟩`, it shows `heat_dissipated (anti f) = ¾·‖anti f‖² ≥ 0`, strictly `> 0` whenever the residue is nonzero, and `= 0` exactly when `f` was already `Rop`-fixed. This is the honest "no involution is free" for the *irreversible reset*: erasing the residue always costs strictly positive energy (Landauer's structure, not `kT ln 2` — there's no temperature in the model; the cost is charged to the diffusion, not the free involution). Standard `Reals` axioms only; no `admit`.

`LandauerBound.v` is the genuine `kT ln 2` — the information/thermodynamics accounting of the same erasure. It defines the Bernoulli (Shannon) entropy `Hb` and proves, as pure theorems, that a fair bit has entropy `ln 2` (`Hb (1/2) = ln 2`), a deterministic bit has entropy 0, and so erasing a fair bit drops entropy by exactly `ln 2`. With `k, T > 0` as section variables (no physical constant added to the base), the model's minimum dissipated heat `k·T·ΔH` for that erasure is exactly `k·T·ln 2`, strictly positive; the inequality form takes the second law (`Q ≥ kT·ΔS`) as an *explicit hypothesis*, not an axiom, and yields `Q ≥ kT ln 2`. So the `ln 2` is proved and the `kT` is the carried physical conversion. This is the textbook Landauer floor for the one bit of information in the involution residue. Standard classical-`Reals` axioms only; no `admit`.

`BitDensity.v` builds the **bit density of states** and its symmetry about ½. On the n-bit cube a state's energy is its Hamming weight, and the number of states at energy `k` is the binomial `C(n,k)`. It proves (pure nat, axiom-free) that this density is **symmetric under the complement involution `k → n−k`** (`dos_symmetric`: `C(n,k)=C(n,n−k)`), that the complement is an involution whose fixed point is the half-weight `n/2`, and that the 3-bit density is the row `[1;3;3;1]` (summing to `2³`, matching `MassGap.excite`'s multiplicities). This is the discrete shadow of the critical line: the bit density is organized by the same complement/functional-equation involution about ½ as zeta's `s → 1−s`. **Honest scope:** an *analogy*, not a theorem about actual zeta zeros — the repo has no real zeta function, no zero-counting `N(T)~(T/2π)ln(T/2π)`, and no GUE spacing; only the shared symmetry-about-½ is formalized. Axiom-free ("Closed under the global context").

`WalshHadamardHilbert.v` lifts the whole picture into a genuine (finite, 4-dimensional) real Hilbert space: it equips the signal space with the inner product ⟨f,g⟩ = Σ f g and proves it positive-definite, that the Hadamard operator is self-adjoint and satisfies Parseval (⟨Hf,Hg⟩ = 4⟨f,g⟩), that the normalized transform `Ur = ½H` is a real unitary involution (⟨Ur f, Ur g⟩ = ⟨f,g⟩, Ur² = I), that the apex reflection is a self-adjoint involution with orthogonal ±1 eigenspaces (nodes ⊥ antinodes), and that the standing-wave amplitude is a −1-eigenvector of norm²=2 preserved by `Ur`. Uses only the standard Coq `Reals` axioms; no custom axioms, no `admit`. (The infinite-dimensional ℓ²/L² lift the Hilbert–Pólya program needs is a much larger, analysis-library undertaking.)

**25 proof file(s):**

- `BitDensity.v`
- `DiracDiagonal.v`
- `DiracOnCategory.v`
- `EigenSystem.v`
- `FanoSelfAdjoint.v`
- `FredholmDirac.v`
- `HeatFlow.v`
- `Involution.v`
- `KappaInvariant.v`
- `MassGap.v`
- `KappaOmega.v`
- `KroneckerSelfAdjoint.v`
- `Landauer.v`
- `LandauerBound.v`
- `PrimorialSpectralTheory.v`
- `SpectralAlgebra.v`
- `SpectralEvent.v`
- `SpectralPrism.v`
- `SpectralTripleRH.v`
- `SpectralTripleRH_closed.v`
- `StandingWave.v`
- `StandingWaveSpectrum.v`
- `TriadicSpectral.v`
- `WalshHadamard.v`
- `WalshHadamardHilbert.v`
