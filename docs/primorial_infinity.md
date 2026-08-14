# `(primorial)^∞`: how "infinity" is defined in this system

## The question

"How do we define many infinities in our system?" — thinking of infinity as **`(primorial)^∞`**, the
limit object as the primorial base grows without bound.

## The short answer

**There is no primitive `∞`.** The system never adjoins an infinite *value*; every notion of infinity is a
finite, first-order device. `(primorial)^∞` in particular is realized as the **profinite completion** of the
integers, and its three classical "faces" are now packaged as **one first-class object** with a proven
coherence between them. Everything below is **axiom-free** (`Print Assumptions` = *Closed under the global
context*): no `Admitted`/`Axiom`/`admit`.

## The three faces of `(primorial)^∞`

`(primorial)^∞` is genuinely three *kinds* of object — a poset, a ring, and a number — and the code keeps
them distinct on purpose:

| face | what it is | carrier |
|---|---|---|
| **(i) order** | the top of the exponent tower ω+1 = ℕ∪{∞} (single prime, `min`-truncation bonds) | `InvLimit.infty : InvLim` (`infty_top`) |
| **(ii) ring** | the profinite integers `Ẑ = lim Z/nZ = ∏_p Z_p` — the multiplicative `∏ p^∞` | `ProfiniteInteger.Zhat`, `PadicIntegers.Zp` |
| **(iii) archimedean** | the size at ∞, `\|n\|_∞ = 1/∏_p \|n\|_p` — reconstructed, not adjoined | `ArchimedeanTower.archimedean_reconstruct` |

## The new construction (3 files, axiom-free)

### `spectral-theory/ProfiniteInteger.v` — the carrier
`Zhat = lim_n Z/(n!)Z = lim Z/nZ = Ẑ`, packaged as coherent residue sequences over the **factorial** modulus
tower `M n = n!` (cofinal in divisibility: `S k ∣ (S k)!`, `cofinal`). A near-verbatim `p^n ⇒ fact n` port of
the proven `PadicIntegers.v`, hence axiom-free by the same proofs:

- object `Zhat := { a : nat -> nat | redcohF a }`, `redcohF a := ∀ n, a n = a (S n) mod n!`;
- ring ops descending to the limit (`Wzero/Wone/Wadd/Wmul`), ring-hom projections (`projW`);
- the diagonal embedding `Z ↪ Ẑ` (`embW`, `embW_add/mul`);
- universal property (`Wmediate`), cofinality, master theorem `profinite_integer`.

### `spectral-theory/ProfiniteBridge.v` — the bridges
- **`Phi : InvLim -> Zp p`** — the order ω+1 tower into the p-adic ring tower, `n ↦ p^(exponent at level n) mod pⁿ`.
  The load-bearing new proof `Phi_coh` shows the `min`-truncation bond of the order tower matches the `mod pⁿ`
  bond of the ring tower. `Phi_infty`: **the order-top `infty` is `p^∞ = 0` in every `Z_p`**. `Phi_emb`:
  naturals map to the capped p-adic powers.
- **`compW : Zhat -> Zp p`** — the component projection onto each `Z_p` (the ring face factors as `∏_p Z_p`,
  cf. `ProfiniteCRT.crt_iso`). Uses `ppow_div_M` (`p^k ∣ (p^k)!` from `EuclidPrimes.divide_fact`), `projW_gap`
  (iterated coherence), `mod_mod_div`. `compW_Wzero`: **`(primorial)^∞ = 0` in every completion `Z_p`**.

### `spectral-theory/PrimorialInfinity.v` — the unified object + payoff
```coq
Record PrimInf := { pi_order : InvLim; pi_order_top; pi_ring : Zhat; pi_bridge; pi_arch }.
Definition primorial_infinity : PrimInf := {| pi_order := infty; pi_ring := Wzero; ... |}.
```
The canonical inhabitant certifies the three faces are **one datum**:

> **`(primorial)^∞` is the order-top ω+1, is `0` in every completion `Z_p`/Ẑ, and is `1/∏_p|·|_p` at ∞.**

`primorial_infinity_coheres` bundles the coherence. Payoff **`adele_split`**: at a rational point,
`A_Q = R × A_f` — the archimedean size `|n|_∞` (R-factor, face iii) times the finite p-adic product `fabs`
(A_f-factor, face ii), glued by the product formula `|n|_∞ · ∏_p|n|_p = 1`.

## Honest scope

The genuinely new proofs are `Phi_coh` and `compW_coh`; the carrier is a mechanical port and the
archimedean/CRT ingredients are pure reuse (`archimedean_reconstruct`, `pf_int`, `crt_iso`). **Out of scope**
(deliberately): the *limit-level* isomorphism `Zhat ≅ ∏_p Z_p` and the infinite-CRT bijection — the ring face
factors via `crt_iso` at finite level only, exactly as `ProfiniteCRT` already states it.

## Where the other "infinities" live (for contrast)

- **poles / `1/0`** (Γ, ζ) — collapse to `C0` via the total `Rinv 0 = 0` convention, or are excluded by a
  hypothesis and written symbolically as `1/(s−1)` / cancelled (`ZetaPoleCancel`). Not values.
- **limits / integrals to `+∞`** — `ImproperCv1` / `CImp`: a limit over all `cv_infty` endpoint sequences to a
  *finite* value. No `Rbar`, no `is_lim_seq`, no `±∞` value anywhere.
- **divergence** — isolated as a pole, a Mellin weight `n^{−σ}`, or a θ self-dual involution. `FredholmDirac.v`:
  *"infinity … is divergence."*

So: the infinity is the **completion**, and the archimedean `∞` is **reconstructed from the finite data**
rather than adjoined — the system has, by design, no primitive `∞`.
