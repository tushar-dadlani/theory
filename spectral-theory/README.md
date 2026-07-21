# Spectral theory

Spectral algebra and events, the Dirac operator, eigen-systems, self-adjoint structures, the standing wave, and the spectral triple approach to RH.

`WalshHadamard.v` is the Fourier transform native to the framework's xor/Fano structure: the Walsh–Hadamard transform on the Boolean cube F₂³. It is the first *actual* transform in the repo (a linear operator, not a comment), and proves — axiom-free — that it is symmetric, a self-inverse-up-to-scale involution (H² = 8·I), turns translation into a ±1 character sign, turns xor-convolution into a pointwise product, and realises the `StandingWave.v` apex reflection as a Fourier sign flip whose ±1 eigenspaces are the nodes and antinodes.

**17 proof file(s):**

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
- `TriadicSpectral.v`
- `WalshHadamard.v`
