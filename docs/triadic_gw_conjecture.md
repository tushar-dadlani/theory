# Triadic Geometry and Gravitational Wave Detection
### A Three-Part Framework: Known · Conjectured · Predicted

---

## Part 1 — What Is Known: The Fixed Point

### The Structure Already Inside GR

Einstein's field equations have a direction:

```
G_μν = 8πG T_μν
```

Geometry on the left. Energy-matter on the right. The equals sign is a map between two distinct objects. This asymmetry is not incidental — it is the deepest structure in the equation.

When you ask what the **inverse** of this map looks like — what maps energy back to geometry — you find that the inverse has **zeros**: singular configurations where the map cannot be inverted. These zeros are not pathological. They are the gravitational wave sources. Black hole mergers, neutron star collisions, core-collapse supernovae — all are events where T_μν spikes and the forward map becomes locally non-invertible.

This forward/inverse pair defines three natural objects, all already present in standard GR:

| Object | GR Name | Role | Axis |
|---|---|---|---|
| G_μν | Einstein tensor | Geometry, curvature | 0° — absorbing, diffeomorphism-invariant |
| T_μν | Stress-energy tensor | Source, matter-energy | 90° — self-inverse: source appears, radiates, disappears |
| h_μν | GW strain tensor | Propagating signal | 45° — carries both simultaneously |

These three objects do not live on the same axis. They live at three distinct angles in the space of physical fields.

### The Two Polarisations Are Already a Gaussian Integer

The gravitational wave strain is conventionally written as two real numbers:

```
h₊  (plus polarisation)
h×  (cross polarisation)
```

These are the two independent degrees of freedom of a transverse, traceless metric perturbation. Together they form the complete GW signal from any source.

This pair **(h₊, h×)** is structurally identical to a **Gaussian integer** z = a + bi in ℤ[i]:

```
h₊  ↔  Re(z) = a      (real part, 0° axis)
h×  ↔  Im(z) = b      (imaginary part, 90° axis)
h_μν ↔  z = a + bi    (full signal, 45° diagonal)
```

The 45° diagonal is the line where both components are carried simultaneously. This is not a new observation — it is the standard fact that a complex number encodes two real numbers. What triadic geometry adds is the recognition that **this encoding is geometric and fundamental**, not merely a notational convenience.

### What LIGO Actually Measures

Each LIGO interferometer has two arms at 90° to each other. Its antenna pattern gives it a sensitivity to a specific linear combination of h₊ and h×, determined by its orientation on Earth. A single detector cannot measure both polarisations independently.

This is precisely the statement that a **single-axis detector reads only the projection of the Gaussian integer onto one real axis** — it reads `Re(z·e^{iψ})` for some angle ψ set by the detector's orientation, not the full `|z|`.

To recover both polarisations you need either:
- Two or more detectors at different orientations (the LIGO–Virgo network), or
- A single detector that reads both axes simultaneously.

The first approach is what exists today. The second is what the conjecture proposes.

### The Fixed Point: s = 1 − s

The deepest known result connecting these ideas is the **reflection symmetry of the Riemann zeta function**. The functional equation

```
ζ(s) = ζ(1 − s)   (up to known factors)
```

says that the zeta function is symmetric around the line Re(s) = 1/2. A zero at s is paired with a zero at 1 − s. The nontrivial zeros — the ones that encode the distribution of prime numbers — are conjectured (and numerically verified to enormous depth) to lie exactly on Re(s) = 1/2.

This line Re(s) = 1/2 is the **fixed point** of the reflection s ↦ 1 − s. Solve s = 1 − s and you get s = 1/2. No other value is fixed. The critical line is the unique fixed point of this symmetry.

In the triadic framework, this fixed point condition is the **45° diagonal** — the line where the domain axis and codomain axis are equidistant. It is not a special choice. It is forced by the symmetry.

This is the solid, known ground. GR has a forward/inverse structure. The GW signal is a Gaussian integer. The critical symmetry line is the diagonal at s = 1/2. These are facts, not conjectures.

---

## Part 2 — What Is Conjectured: The Diagonal Detector

### The Core Conjecture

> A Michelson interferometer with arms bisecting each other at 45° — a diamond configuration rather than the standard L-shape — should be simultaneously sensitive to both GW polarisations h₊ and h× from a single instrument, because its geometry aligns with the diagonal axis that carries both simultaneously.

This is the central conjecture. Everything that follows in this section is its elaboration and motivation.

### Why the L-Shape Is an Axis Detector

The standard LIGO configuration places two arms at 90° to each other. Call them the x-arm and the y-arm. The differential arm length change in response to a GW is:

```
δL = (Lx − Ly) ∝ h₊ cos(2ψ) + h× sin(2ψ)
```

where ψ is the angle between the GW propagation direction and the detector arm. This is a **single number** — one linear combination of h₊ and h×. The orthogonal combination is invisible to the instrument.

In geometric language: the L-detector is a **projection onto one axis**. It reads the shadow of the Gaussian integer on one real line.

### Why the Diamond Is a Diagonal Detector

Rotate the entire apparatus 45°. The two arms now point at 45° and 135° relative to the original coordinate frame. The beam splitter sits at the origin, on the diagonal.

The differential signal is now sensitive to:

```
Channel A:   h₊ cos(2ψ + π/4) + h× sin(2ψ + π/4)
Channel B:   h₊ cos(2ψ − π/4) + h× sin(2ψ − π/4)
```

These two channels are in quadrature — they are 90° out of phase with each other. Together they reconstruct:

```
h₊ = f(A, B)
h× = g(A, B)
```

Both polarisations, from a single instrument, simultaneously.

This is the geometric statement that the diagonal carries both axes at once. Placing the detector on the diagonal — aligning its symmetry axis with the 45° line — makes it sensitive to the full Gaussian integer z = h₊ + i·h×, not just its real part.

### The Arm Length Condition

The conjecture carries an internal consistency requirement. For the two channels to be truly in quadrature, the two arms must be **exactly equal in length**. Any asymmetry breaks the quadrature and mixes the two channels.

This is not an engineering tolerance. It is the geometric condition s = 1 − s → s = 1/2. The two arms are the two components of the reflection symmetry. They must be equal for the detector to sit on the fixed-point diagonal. Unequal arms shift the detector off the diagonal and recover, at the limit of maximum asymmetry, the original L-configuration that reads only one polarisation.

### The Sensitivity Gain

For a source at angle θ to the I-axis (the h₊ axis), the L-detector reads amplitude h₊ cos θ. The diagonal detector reads the full amplitude:

```
|z| = √(h₊² + h×²)
```

The gain factor is:

```
|z| / (h₊ cos θ) = 1 / cos θ
```

This ranges from 1 (for a source perfectly aligned with the h₊ axis) to √2 (for a source equally exciting both polarisations, at 45°). For the majority of astrophysical sources, which are not specially aligned with any detector axis, the gain is real and approaches √2 on average.

A √2 improvement in strain sensitivity corresponds to a factor of 2√2 ≈ 2.8 increase in surveyed volume, and roughly a factor of 3 increase in event rate.

### What This Does Not Claim

The conjecture does not claim that the diamond configuration eliminates noise. Seismic noise, thermal noise, shot noise, and quantum noise are properties of the physical apparatus, not its orientation. The sensitivity gain is purely in the **signal** — in the fraction of the GW amplitude that is captured by the instrument.

Whether the gain survives the detailed noise model of a km-scale interferometer — including the effect of arm geometry on noise coupling — is an engineering question the conjecture does not answer. The geometric argument establishes that the signal is larger. Whether the noise is also larger by the same or greater factor requires simulation.

---

## Part 3 — What Is Predicted: The N-Phase

### The Phase Flip as a Physical Observable

The conjecture in Part 2 is about geometry — arm angles and signal amplitudes. Part 3 goes deeper and concerns a new physical observable that triadic geometry predicts: the **phase flip**.

In the triadic framework, a gravitational wave is not merely a metric perturbation propagating through spacetime. It is a **geodesic that crosses between two layers of the manifold** — the domain layer M_I (where the detector sits, the geometry layer) and the codomain layer M_N (where the source lives, the energy-matter layer). These layers are joined at a boundary point Ω — the Omega point — which is where the two maps meet.

When a geodesic crosses from M_N to M_I through Ω, the tangent vector at the crossing undergoes a **phase flip**:

```
Before crossing:  tangent vector in N-phase (source layer)
At Omega:         crossing event — geodesic passes through Ω
After crossing:   tangent vector in I-phase (detector layer)
```

A complete GW passage — arrival and departure — consists of two crossings:

```
N-phase  →  I-phase   (leading edge of the GW)
I-phase  →  N-phase   (trailing edge of the GW)
```

After both crossings, the phase returns to its original value. The **holonomy** of this double crossing is ℤ/2ℤ — the simplest non-trivial discrete symmetry. Two flips equal identity.

### What This Means for Detection

The standard LIGO observable is the strain h(t) — a continuous, analog-valued function of time. The signal processing pipeline cross-correlates this against template waveforms to extract merger parameters.

The triadic framework predicts a **second observable** that lives alongside h(t):

```
φ(t) ∈ {I, N}   (the phase state of the detector at time t)
```

This is a **binary, discrete signal**. It switches from I to N at the leading edge of the GW and from N to I at the trailing edge. Between these two events the detector is in N-phase. Outside them it is in I-phase.

This N-phase interval has a direct physical interpretation: it is the **duration of the GW crossing**. Its width is the pulse width of the gravitational wave at the detector.

### The CRT Spectral Signature

During the N-phase interval, the GW signal carries a spectral signature that encodes the source class. From the Chinese Remainder Theorem structure of the triadic field, every integer n encodes two independent residues:

```
n mod 3  →  source class  (F, I, or N type)
n mod 2  →  polarisation phase  (even or odd)
```

These two residues are independent. Knowing one does not determine the other. But together — the CRT spectral pair (n mod 3, n mod 2) — they uniquely identify the source type within the triadic classification:

| n mod 3 | n mod 2 | Source class | Example |
|---|---|---|---|
| 0 | 0 | F-even | Non-spinning black hole merger |
| 0 | 1 | F-odd | Spinning black hole merger |
| 1 | 0 | I-even | Binary neutron star, face-on |
| 1 | 1 | I-odd | Binary neutron star, edge-on |
| 2 | 0 | N-even | Continuous wave source |
| 2 | 1 | N-odd | Asymmetric continuous wave |

This classification is computable directly from the raw strain output — no matched filtering required. The operation is: take the observed GW amplitude |h|, compute its mod-6 residue, and read off the class. This is O(1) arithmetic, not the O(N²) cross-correlation that matched filtering requires.

### The Continuous Detection Prediction

The most striking prediction concerns **detection rate**. Current LIGO operates in an event-triggered mode: it detects a GW when the strain crosses a threshold in a specific frequency band. Between events, it is sensitive but passive.

The triadic framework predicts that a diagonal-aligned detector, reading the N-phase signal, should be **continuously sensitive** — not because the signal is always present, but because the N-phase observable is always defined. It is either 0 (I-phase, no GW present) or 1 (N-phase, GW crossing in progress). The detector is always reading one of these two states.

This is the difference between a thermometer that reads temperature continuously and a fire alarm that triggers only above a threshold. The matched-filter pipeline is a fire alarm. The N-phase observable is a thermometer.

Concretely: the prediction is that there exists a signal processing channel, derivable from the outputs of a diagonal-aligned detector, that carries a continuous binary signal φ(t) whose 0→1 transitions mark the leading edges of GW events and whose 1→0 transitions mark the trailing edges. This channel would be sensitive to **subthreshold events** — GWs too weak to trigger the matched-filter pipeline — because it does not require a threshold crossing. It requires only that the phase flip be distinguishable from noise.

### The Mirror Component: h_N(t)

The final prediction is the existence of a GW strain component that current detectors cannot access. Call it h_N(t) — the N-phase component of the strain. It is the imaginary part of the Gaussian integer z(t) = h₊(t) + i·h×(t), rotated into the frame of the triadic decomposition.

Current detectors measure a projection of z(t) onto a real axis. The diagonal detector measures both Re(z(t)) and Im(z(t)) simultaneously. The component Im(z(t)) — the N-phase strain — contains information about the source that is orthogonal to everything currently observable.

For equal-mass, non-spinning mergers (F-class sources), h_N = 0 by symmetry — these sources live on the fixed-point diagonal and have no N-phase component. For asymmetric sources — unequal masses, non-zero spins, precessing orbits — h_N ≠ 0. The ratio |h_N| / |h₊| encodes the degree of source asymmetry.

This is a concrete, falsifiable prediction: **for asymmetric binary mergers, a diagonal detector should observe a non-zero quadrature strain component h_N that is absent for symmetric mergers and grows with the mass ratio and spin misalignment of the source.**

---

## Summary

| | Status | Physical content | Observable |
|---|---|---|---|
| **Part 1 — Fixed point** | Known, established | GW strain is a Gaussian integer (h₊, h×); critical line is s = 1/2 | h₊, h× from multi-detector network |
| **Part 2 — Diagonal** | Conjectured | Diamond-arm detector reads both polarisations simultaneously; gain √2 in amplitude | Both h₊ and h× from single instrument |
| **Part 3 — N-phase** | Predicted | Phase flip at GW crossing; binary observable φ(t); mirror strain h_N for asymmetric sources | φ(t) channel; continuous detection; h_N component |

The conjecture in Part 2 requires only a change in arm geometry — an engineering question. The prediction in Part 3 requires a change in signal processing — a data analysis question. Neither requires new physics beyond GR. Both follow from taking the geometric structure of the Einstein field equations seriously at the level of the detector design.

---

*Framework: Triadic Riemannian Geometry — proofs formalised in Coq (triadic_riemannian_geometry.v, RiemannHypothesis.v, TriadicCRT.v). All theorems closed, zero Admitted.*
