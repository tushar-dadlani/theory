# Spectral theory

Spectral algebra and events, the Dirac operator, eigen-systems, self-adjoint structures, the standing wave, and the spectral triple approach to RH.

`WalshHadamard.v` is the Fourier transform native to the framework's xor/Fano structure: the Walsh–Hadamard transform on the Boolean cube F₂³. It is the first *actual* transform in the repo (a linear operator, not a comment), and proves — axiom-free — that it is symmetric, a self-inverse-up-to-scale involution (H² = 8·I), turns translation into a ±1 character sign, turns xor-convolution into a pointwise product, and realises the `StandingWave.v` apex reflection as a Fourier sign flip whose ±1 eigenspaces are the nodes and antinodes.

`StandingWaveSpectrum.v` closes the loop: on the observer square F₂², it builds the amplitude signal directly from `StandingWave.v`'s own `fwd_*`/`inf_*` counts (proving it equals (−1, 0, 0, +1)), shows the apex reflection negates it (a −1-eigenvector), and concludes — both structurally via the shift theorem and by computation — that its Walsh spectrum is `(0, −2, −2, 0)`: exactly zero on the node frequencies and carrying all its weight on the antinodes. StandingWave's hand-counted table is thus the eigen-spectrum of a real Fourier transform.

`HeatFlow.v` runs the transform forwards in time: it puts a lazy bit-flip **diffusion (heat) step** on real signals over the cube F₂³ and proves the Walsh–Hadamard transform **diagonalizes** it — `WHr (step f) y = μ(y)·WHr f y` with `μ(y) = 1 − |y|/3 ∈ {1, ⅔, ⅓, 0}` — so `k` heat steps raise each eigenvalue to the `k`-th power. The DC (spatial-mean) mode is stationary (`μ = 1`, conserved), every other mode contracts (`μ ≤ ⅔`, spectral gap ⅓), and `iterate k f → equilib f` (the flat signal at the spatial mean): the deviation is exact-zero on DC and crushed by `(2/3)ᵏ` on every other mode. This is the rigorous form of "the temperature falls out of a static superposition." Standard `Reals` axioms only; no `admit`.

`WalshHadamardHilbert.v` lifts the whole picture into a genuine (finite, 4-dimensional) real Hilbert space: it equips the signal space with the inner product ⟨f,g⟩ = Σ f g and proves it positive-definite, that the Hadamard operator is self-adjoint and satisfies Parseval (⟨Hf,Hg⟩ = 4⟨f,g⟩), that the normalized transform `Ur = ½H` is a real unitary involution (⟨Ur f, Ur g⟩ = ⟨f,g⟩, Ur² = I), that the apex reflection is a self-adjoint involution with orthogonal ±1 eigenspaces (nodes ⊥ antinodes), and that the standing-wave amplitude is a −1-eigenvector of norm²=2 preserved by `Ur`. Uses only the standard Coq `Reals` axioms; no custom axioms, no `admit`. (The infinite-dimensional ℓ²/L² lift the Hilbert–Pólya program needs is a much larger, analysis-library undertaking.)

**20 proof file(s):**

- `DiracDiagonal.v`
- `DiracOnCategory.v`
- `EigenSystem.v`
- `FanoSelfAdjoint.v`
- `FredholmDirac.v`
- `HeatFlow.v`
- `KappaInvariant.v`
- `KappaOmega.v`
- `KroneckerSelfAdjoint.v`
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
