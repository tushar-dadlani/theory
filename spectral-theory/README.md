# Spectral theory

Spectral algebra and events, the Dirac operator, eigen-systems, self-adjoint structures, the standing wave, and the spectral triple approach to RH.

`WalshHadamard.v` is the Fourier transform native to the framework's xor/Fano structure: the Walsh–Hadamard transform on the Boolean cube F₂³. It is the first *actual* transform in the repo (a linear operator, not a comment), and proves — axiom-free — that it is symmetric, a self-inverse-up-to-scale involution (H² = 8·I), turns translation into a ±1 character sign, turns xor-convolution into a pointwise product, and realises the `StandingWave.v` apex reflection as a Fourier sign flip whose ±1 eigenspaces are the nodes and antinodes.

`StandingWaveSpectrum.v` closes the loop: on the observer square F₂², it builds the amplitude signal directly from `StandingWave.v`'s own `fwd_*`/`inf_*` counts (proving it equals (−1, 0, 0, +1)), shows the apex reflection negates it (a −1-eigenvector), and concludes — both structurally via the shift theorem and by computation — that its Walsh spectrum is `(0, −2, −2, 0)`: exactly zero on the node frequencies and carrying all its weight on the antinodes. StandingWave's hand-counted table is thus the eigen-spectrum of a real Fourier transform.

**18 proof file(s):**

- `DiracDiagonal.v`
- `DiracOnCategory.v`
- `EigenSystem.v`
- `FanoSelfAdjoint.v`
- `FredholmDirac.v`
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
