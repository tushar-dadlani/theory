# Monoid algebras of prime length: `M_p = (𝔽_p, ×)`

*Design note / build plan for a four-brick addition to `spectral-theory/`.*

## Context

The repo currently has two disconnected layers that both get called "the monoid algebra":

- **The base monoid** `{I, N, F}` (`spectral-theory/INFMonoid.v`, `INFProduct.v`) — proved to be
  the commutative monoid `({+1,−1,0}, ×) = (𝔽₃, ×)` and the value-monoid of μ on prime powers.
- **The algebra construction `k[M]`** — `HopfGroupAlgebra.v` (`k[ℤ/nℤ]`),
  `HopfGroupAlgebraGen.v` (`k[G]`, arbitrary finite abelian `G`), `HopfGroupTensor.v`
  (`k[G×H] ≅ k[G]⊗k[H]`, already proved with *no group axioms*), and `DirichletConv.v`
  (the genuine non-group instance, `(ℕ_{>0}, ×)`).

Nothing builds an algebra over `{I,N,F}`, and `{I,N,F}` is never presented as a member of a
family. It is one: `{I,N,F} = (𝔽₃, ×)` is the **p = 3** case of `M_p := (𝔽_p, ×)`, the
multiplicative monoid of the prime field — cardinality exactly `p`, an absorbing zero plus a
cyclic unit group of order `p−1`.

The goal is the prime-length family and its monoid algebra, with primality **load-bearing rather
than decorative**: `ℤ[M_p]` splits as `ℤ[ℤ/(p−1)] ⋉ ℤδ₀` precisely because `𝔽_p` is a field, so
the nonzero elements are closed under multiplication. For composite `n` this is false
(`2·2 = 0` in `ℤ/4`).

Intended outcome: five new/edited bricks, each axiom-free ("Closed under the global context"),
that (i) unblock `k[M]` for monoids with a zero, (ii) prove the splitting theorem and the
honest negative result that these algebras are *not* Hopf, (iii) identify `M_p` arithmetically,
(iv) exhibit `{I,N,F}` as the universal quadratic quotient of every `M_p` via the Legendre
symbol, and (v) factor the primorial-modulus algebra as a tensor product of prime-length ones.

## Two orthogonal axes: residues and exponents (smoothing)

`M_p` varies **one prime, in the residue direction**: the carrier is `ℤ/p`, the operation is
multiplication of residues, and the interesting structure is the zero and the unit group.

Smoothness varies **the number of primes, in the exponent direction**. A
`{p_1,…,p_k}`-smooth number is `∏ p_i^{k_i}`, so the multiplicative monoid of `y`-smooth
numbers is the *free* commutative monoid `ℕ^k`. The repo already has this, twice over:

- `FreeDivMeetIso.v` (:16, :99) — the free product-of-chains lattice `ℕ×ℕ` embeds in `(ℤ, ∣)`
  as **exactly the `{p,q}`-smooth numbers**, an order embedding, not just at the axes.
- `EulerReindex.v` (:114 `euler_reindex`, :143 `codes_distinct`) — `code ks = ∏ p_i^{k_i}` is a
  **bijection of occupation vectors onto `{ps}`-smooth numbers**.
- `EulerProductZeta.v:134 small_smooth` — every `m ≤ N+1` is `{primes ≤ N+1}`-smooth. This is
  the device that makes the whole Euler-product thread finite and axiom-free: **smoothing is
  the repo's finiteness discipline**, not an incidental lemma.

The consequence for the earlier audit: `INFProduct`'s length-`n` configurations *are* the smooth
truncation of `DirichletConv`'s `(ℕ_{>0}, ×)`, and `DirichletConv` is the colimit as the
smoothness bound rises. That is the conceptual bridge between the `{I,N,F}` layer and the
convolution-ring layer, and `EulerReindex`'s bijection is most of its proof.

These two axes are genuinely different — `M_p` is about residues mod one prime, smoothness about
exponents over many primes — and **the primorial is where they meet**.

## Brick 1 — `spectral-theory/HopfGroupAlgebraGen.v` (refactor, no new math)

`gconv` is unusable for a monoid with a zero only because the section declares
`Variable inv` / `Hypothesis op_inv_l`. Auditing the file: `inv` is used **only** by
`inv_involutive` (:47), `ginv` (:159), `SidDelta`/`antipode_axiom` (:213–:230), and
`ginv_involutive` (:332). Every other result — both dualities, `counit_unit_pairing`,
`counit_augmentation`, `gconv_comm`, `gconv_distrib_l/r`, `gconv_unit_l/r`, `dot_L`/`dot_R`,
`gconv_assoc` — is already inv-free.

Split into **nested** sections:

```
Section MonoidAlgebra.        (* A, Aeq, Aeq_spec, elts, elts_nodup, elts_all,
                                 op, e, op_assoc, op_comm, op_id_l *)
  ... sumf toolkit, gunit, gconv, dot, delta,
      dualities, counits, ring axioms ...
  Section GroupPart.          (* + inv, op_inv_l *)
    ... inv_involutive, ginv, SidDelta, antipode_axiom, ginv_involutive ...
  End GroupPart.
End MonoidAlgebra.
```

Nesting (not two sibling sections) is deliberate: the monoid variables stay in scope inside
`GroupPart`, so no proof body changes, and after both sections close every exported statement
keeps today's signature — the `z2_*` non-vacuity corollaries at :347–:381 compile unchanged.

`grep` confirms **nothing outside the file requires `HopfGroupAlgebraGen`**, so this is a
zero-blast-radius edit.

## Brick 2 — `spectral-theory/MonoidAlgebraZero.v` (the mathematical heart)

The zero-adjunction functor, as an *inductive* carrier — deliberately avoiding a
`{x | x < p}` sigma carrier here, so this brick has no guards, no dependent-`map`, no UIP
bookkeeping:

```coq
Inductive Adj (G : Type) : Type := AZero | AElt (g : G).
```

with `aop AZero _ = AZero`, `aop _ AZero = AZero`, `aop (AElt g) (AElt h) = AElt (opG g h)`,
`ae := AElt eG`, `aelts := AZero :: map AElt eltsG`, `Aeq` lifted from `G`'s.

Content:

1. **`Adj G` is a commutative monoid** — all of Brick 1's monoid hypotheses discharge by
   `destruct` + `G`'s laws. `NoDup`/completeness of `aelts` lift by `map_NoDup`/`in_map`.
   `|Adj G| = |G| + 1`, so **prime length ⟺ `|G| = p − 1`**.
2. **Absorption at the algebra level**: `gconv_zero_absorb : gconv x (delta AZero) = ε(x) · delta AZero`,
   where `ε` is `counit_augmentation`'s `bigsum`. So `ℤ·δ₀` is a two-sided idempotent ideal.
3. **The splitting theorem** — `ℤ[Adj G] ≅ ℤ[G] ⋉ ℤδ₀` with
   `(x, s)·(y, t) = (x·y, ε(x)t + ε(y)s + st)`. State it concretely as: `gconv` on `Adj G`
   restricted to the `AElt`-supported functions agrees with `gconv` on `G` (the subalgebra
   half), and the `AZero` coefficient of a product is the formula above (the ideal half).
   The augmentation counit is the structure constant coupling the two — the reason
   `counit_augmentation` reappears here.
   **DONE (both halves, general `f,g`, axiom-free):** `gconv_adj_elt_full : gconv f g (AElt h)
   = gconv_G (f∘AElt) (g∘AElt) h` (the `x·y` half) and `gconv_adj_zero_full : gconv f g AZero
   = ε(f∘AElt)·g(AZero) + ε(g∘AElt)·f(AZero) + f(AZero)·g(AZero)` (the exact `ε(x)t+ε(y)s+st`
   twist, computed from `(fZ+ε(fA))(gZ+ε(gA)) − ε(fA)ε(gA)`). These upgrade the earlier
   special cases (`gconv_adj_elt`, `gconv_adj_zero_coeff`, `gconv_zero_absorb`) to the general
   product law.
4. **`no_antipode`** (honest negative, ~5 lines): if `S` satisfied
   `m∘(S⊗id)∘Δ = η∘ε` then `S(δ₀) ⋆ δ₀ = δ_e`; but by (2) *every* product with `δ₀` lands in
   `ℤδ₀`, and `δ_e ∉ ℤδ₀` whenever `G` is nonempty. So a monoid algebra with an absorbing zero
   is a bialgebra, never Hopf — which explains structurally why the `{I,N,F}` thread never
   produced one, and mirrors the caveat already recorded in `HopfGrouplike.v`'s header.
5. **`adj_not_closed_under_product`**: `Adj G × Adj H` contains `(AZero, AElt h)` — a nonzero
   non-unit — so it is **not** of the form `Adj K`. The zero-adjunction functor does not commute
   with products. This is the structural reason primorial moduli need the tensor product of
   Brick 5 rather than another `Adj`, and the reason Brick 3's counterexample is what it is.
6. **Non-vacuity + the tie-back**: instantiate at `G := bool`/`xorb` (reusing
   `HopfGroupAlgebraGen`'s `z2_*` lemmas at :347–:363). `Adj bool` has order 3; give the
   explicit iso `Adj bool ≅ INFMonoid.Sym` (`AZero ↦ F`, `AElt false ↦ I`, `AElt true ↦ N`)
   and check it carries `aop` to `INFMonoid.op` — proving the p = 3 case *is* the existing
   3-symbol algebra, by `destruct`.

## Brick 3 — `spectral-theory/ZmodMultMonoid.v` (where primality enters)

The arithmetic identification, and the only brick with real carrier bookkeeping:

- **`prime p → (ℤ/p, ×) ≅ Adj((ℤ/p)^×)`** — primality *is* zero-adjunction: every nonzero
  residue is a unit. Consume `ZmodPStar.v` (unit closure under `mul_mod`, `unit_not_div`,
  `cancel_mod`, `fermat`) and `PrimitiveRoot.units_cyclic` (PrimitiveRoot.v:238, axiom-free)
  for `(ℤ/p)^× ≅ ℤ/(p−1)` cyclic. Combined with Brick 2 this gives `|M_p| = p` and
  `ℤ[M_p] ≅ ℤ[ℤ/(p−1)] ⋉ ℤδ₀`, hence (via `Cyclotomic`/`CyclotomicProd`/`QPolyQuot`) the
  cyclotomic factorisation of the group half.
- **Two composite counterexamples**, because one of them is misleading on its own:
  - `¬ ∃ G, (ℤ/4, ×) ≅ Adj G` — witnessed by `2`, a nonzero non-unit (`2·2 = 0`). Fails for
    **non-squarefreeness**.
  - `¬ ∃ G, (ℤ/6, ×) ≅ Adj G` — witnessed by `2, 3, 4`. `6 = n_2` is the second primorial and is
    **squarefree**, so this is the one that shows the obstruction is *compositeness*, not
    *squares*. Without it a reader concludes the splitting theorem only needs `n` squarefree.
    It also comes with the correct replacement structure (`ℤ[M_6] ≅ ℤ[M_2] ⊗ ℤ[M_3]`, Brick 5),
    so the counterexample and the generalisation are the same example.

**Risk, stated up front.** The repo's `nat`-with-`mod p` convention (`ZmodOrder.pw`,
`ZmodPStar`, `LegendreSymbol`) cannot satisfy Brick 1's *unguarded* `op_id_l`, since
`(1*x) mod p = x` fails for `x ≥ p`. Preferred fix: carry residues as
`{x : nat | Nat.ltb x p = true}` — a **boolean** proof field, so injectivity of the pair
needs only `Eqdep_dec`'s boolean UIP (axiom-free, no `proof_irrelevance`). Fallbacks, in order:
(a) state the iso as a bijection between `aelts` and `seq 0 p` at the level of index lists
rather than a type-level iso, keeping all arithmetic in `nat`; (b) fall back to guarded
statements in the established style of `HopfGroupAlgebra.v`, which already pays exactly this
`k < n` tax for the cyclic case. Bricks 1, 2 and 4 do not depend on which fallback lands.

## Brick 4 — `spectral-theory/LegendreMonoidHom.v` (`{I,N,F}` as universal quotient)

`val : Sym → ℤ` injective and multiplicative forces `ℤ/(p−1) ↪ ℤ^× = {±1}`, i.e. `p ≤ 3` — so
`INFMonoid.val_inj` is a p = 3 accident and the sign embedding does **not** generalize. What
generalizes is a surjection, and the repo already has it:

- Define `leg_sym p a : Sym` (`F` if `p | a`, else `I`/`N` by the half-power test) so that
  `val (leg_sym p a) = legendre p a` — matching `legendre`'s own case split at
  LegendreSymbol.v:96–98 definitionally.
- **Monoid homomorphism**: `legendre_mult_unit` (LegendreSymbol.v:174) is the unit case;
  extend across the zero case, where both sides are `0` by `Nat.Lcm0.mod_divide` and
  `Znumtheory.prime_mult` — two `destruct`s on whether `p ∣ a`, `p ∣ b`.
- **Surjectivity** onto `{I,N,F}` for odd `p`: `F` from `a = p`, `I` from `legendre_1`
  (LegendreSymbol.v:166), `N` from a non-residue, which exists because `units_cyclic` gives a
  generator whose half-power is `≠ 1`.
- Conclude: `{I,N,F}` is the **universal quadratic quotient** of every `M_p` — the order-2
  character surviving because `2 ∣ p−1` — and functorially the induced algebra map
  `ℤ[M_p] → ℤ[Sym]`.

Two scope notes:

- The natural extension to primorial moduli is the **Jacobi symbol**
  `(a/n_k) = ∏_i (a/p_i)`, whose composite with `val` is literally `INFProduct.val_n` — under
  which `val_n_zero_iff` reads "Jacobi vanishes iff `gcd(a, n_k) > 1`" and `val_n_app` reads
  "multiplicative in the modulus over any coprime split". **The repo does not have the Jacobi
  symbol**: `JacobiRHS.v` is Jacobi's *two-square formula* (`r2(n) = 4(d₁−d₃)`), unrelated. So
  this is new work, not a reuse — keep it out of Brick 4.
- A free extra instance that *is* present: `JacobiRHS.v`'s `chi4` is completely multiplicative
  with values `{+1,−1,0}`, i.e. another monoid hom onto `{I,N,F}`, at modulus 4. Cheap
  corroboration that the Brick 4 pattern is not special to prime moduli.

Optional follow-on (do not bundle): Brick 4 is also the missing link for the
`INFProduct.val_n_mu` versus `DirichletConv.mu` seam, reachable from
`DirichletPPow.mu_ppow`/`mu_ppow_ge2` plus `DirichletMult`'s multiplicativity.

## Brick 5 — `spectral-theory/PrimorialMonoidAlgebra.v` (where the two axes meet)

Let `n_k = p_1···p_k` be the k-th primorial. Two facts, one negative and one positive:

1. **Squarefree-smooth = `Div(n_k)` = the F-free part of `INFProduct`.** `val_n_zero_iff`
   (INFProduct.v:98) says one `F` vetoes a configuration; the surviving `{I,N}`-configurations
   are exactly the exponent vectors in `{0,1}^k`, i.e. the **squarefree** smooth numbers, i.e.
   the divisors of `n_k`, i.e. the Boolean cube `2^k`. So the primorial is the top of the F-free
   sublattice and `val_n_zero_iff` is the statement "μ is supported on divisors of `n_k`" — the
   squarefree collapse `INFMonoid` already names, read one dimension up.
   **DONE (the seam to the genuine Möbius function, axiom-free): `spectral-theory/MobiusINFSeam.v`.**
   `mu_smooth_val_n`: for `pks : list (prime, exponent)` with distinct primes,
   `DirichletConv.mu (∏ p_i^{k_i}) = INFProduct.val_n (map sym_of (map snd pks))`. Proved from the
   atomic seam `mu_ppow_eq_mu_pp : mu(p^k) = mu_pp k` (all k: `mu_1`/`mu_p`/`mu_ppow_ge2`) and
   `DirichletMult.mu_mult_prod` iterated with `DirichletVonMangoldtGen.gcd_ppow_coprime` for the
   coprimality (each head prime `∤` the smooth tail, via `prime_mult_nat` + `prime_div_prime`), then
   `INFProduct.val_n_mu`. So one `F` (some `k_i ≥ 2`) sends both sides to 0 — the squarefree veto IS
   `μ` vanishing — and `{I,N}` on squarefree smooth numbers is exactly `μ`.

2. **The primorial is where the residue monoid algebra factors as a tensor product.**
   `ProfiniteCRT.crt_iso` (ProfiniteCRT.v:117, axiom-free) gives `ℤ/mn ≅ ℤ/m × ℤ/n` for coprime
   `m, n`, with reduction multiplicative (`red_mul = Zmult_mod`, :135). A ring iso is in
   particular a monoid iso, so iterating over the primorial:

   ```
   (ℤ/n_k, ×)  ≅  ∏_{i ≤ k} (ℤ/p_i, ×)  =  ∏_{i ≤ k} M_{p_i}
   ```

   and then `HopfGroupTensor.v` — whose `Section Tensor` declares only `op`, `e`, `elts` with
   **no group axioms and no monoid axioms** (:79–:112) — applies verbatim to monoids with zeros:

   ```
   ℤ[M_{n_k}]  ≅  ⊗_{i ≤ k} ℤ[M_{p_i}]
   ```

   This is nearly free: `gconv_prod_tensor`/`gunit_prod_tensor`/`tconv_elementary` are already
   proved at the generality needed, so the work is instantiation plus the CRT induction, not new
   tensor theory.
   **DONE (general two-factor case, axiom-free): `spectral-theory/PrimorialTensorGen.v`.** For ANY
   coprime `m, n`, `crt_monoid_iso_gen` proves `M_{mn} ≅ M_m × M_n` — `crt x = (x mod m, x mod n)`
   is a multiplicative homomorphism (`crt_hom`, via `Nat.Div0.mul_mod` + `(a mod mn) mod m = a mod m`),
   is injective on `[0,mn)` (`crt_inj`, CRT injectivity cast to ℤ, reusing
   `ProfiniteCRT.sub_of_mod_eq`/`mul_divide_of_coprime`), and is a bijection of residue systems
   (`crt_perm : Permutation (map crt (seq 0 (m*n))) (list_prod (seq 0 m) (seq 0 n))`, via
   `NoDup_Permutation_bis`). `sumf_reindex_crt` is the general grid↔residue reindexing (the
   `reindex6` generalization). `primorial_tensor_factorization_gen` packages this with the generic
   `gconv_prod_tensor` — i.e. `PrimorialMonoidAlgebra.primorial_tensor_factorization` with its
   216-case `vm_compute` replaced by a proof valid for every coprime `m, n`. The k-fold primorial
   is then this two-factor step iterated (`primorial(k+1) = primorial(k) · p_{k+1}`, coprime).
   Prime enumeration comes from
   `PrimorialSpectralTheory.primorial_primes k = map kth_prime (seq 0 (S k))` (:137) with
   `primorial_primes_nested` (:146).

   Combined with Brick 2 item 5 (`Adj` does not commute with products), the honest statement is:
   **`Adj` handles one prime, tensor handles many, and the primorial is the crossover.** Neither
   construction subsumes the other.

3. **The tower.** `primorial_primes_nested` plus `ProfiniteCRT`'s `proj_compat` and
   `system_directed` make `ℤ[M_{n_1}] → ℤ[M_{n_2}] → ⋯` an inverse system whose algebra gains one
   prime-length tensor factor per level — the multiplicative analogue of the additive towers in
   `ChainTower.v` / `ProfiniteCRT.v`.

   **Scope note, to be recorded in `LEDGER.md`:** the limit of the *primorial* tower is
   `∏_p (𝔽_p, ×)`, **not** `∏_p ℤ_p`. Exponents never grow, since every modulus is squarefree.
   `∏_p ℤ_p` is the limit of the *prime-power* tower (`PadicIntegers.v`). `PrimorialSpectralTheory.v`'s
   CLAIM A ("the limit is the full adelic ring `∏_p ℤ_p`") conflates the two towers; this brick
   should state the correct limit rather than inherit that claim.

## Where this leads (not in scope)

The two axes are paired by the Legendre symbol: on a smooth number `m = ∏ p_i^{k_i}`,
`(m/p) = ∏ (p_i/p)^{k_i}` — the exponent-axis data of Brick 5 contracted against the
residue-axis character of Brick 4. Swapping which prime is the modulus and which is the argument
is exactly the shape of reciprocity, and the repo has that law fully proved and axiom-free
(`QuadraticReciprocity.v`, on `LegendreSymbol` + `GaussLemma` + `EisensteinLemma`). Worth naming
as the direction; not a deliverable here.

## Files

| File | Action |
|---|---|
| `spectral-theory/HopfGroupAlgebraGen.v` | edit — nested monoid/group sections |
| `spectral-theory/MonoidAlgebraZero.v` | new — `Adj`, splitting theorem, `no_antipode`, `Adj bool ≅ Sym` |
| `spectral-theory/ZmodMultMonoid.v` | new — `(ℤ/p,×) ≅ Adj((ℤ/p)^×)`, `ℤ/4` counterexample |
| `spectral-theory/LegendreMonoidHom.v` | new — `M_p ↠ {I,N,F}` |
| `spectral-theory/PrimorialMonoidAlgebra.v` | new — `ℤ[M_{n_k}] ≅ ⊗ ℤ[M_{p_i}]`, `Div(n_k)` = F-free part, tower + limit note |
| `_CoqProject` | append the four new files after `HopfGroupAlgebraGen.v` (before `INFMonoid.v` at :629 for Brick 2's tie-back) |

Reused, not rewritten: `HopfGroupTensor.v`'s polymorphic `sumf` toolkit (:29–:76) — the
precedent is `DirichletConv.v`, which requires `HopfGroupTensor` for exactly this; it lacks
`sumf_sift`/`sumf_single`, so prove those polymorphically once in Brick 2 rather than a fourth
time at a concrete index type. Also reused: `ZmodPStar`, `PrimitiveRoot.units_cyclic`,
`LegendreSymbol`, `HopfGroupAlgebraGen`'s `z2_*` witnesses, `INFMonoid.op`/`val`,
`HopfGroupTensor`'s `gconv_prod_tensor`/`gunit_prod_tensor`/`tconv_elementary` (Brick 5, already
at the needed generality), `ProfiniteCRT.crt_iso`, and
`PrimorialSpectralTheory.primorial_primes`/`kth_prime`.

Deliberately *not* reused: `EulerReindex`'s smooth-number bijection and
`FreeDivMeetIso`'s smooth embedding. They belong to the exponent axis and are cited above only to
locate `INFProduct` relative to `DirichletConv`; folding them in would merge two independent
threads in one pass.

## Verification

Build is `coq_makefile`-generated (Rocq 9.1.1), driven by `_CoqProject`:

1. Append the new files to `_CoqProject` in dependency order, then regenerate:
   `rocq makefile -f _CoqProject -o Makefile`.
2. `make spectral-theory/HopfGroupAlgebraGen.vo` first — it must compile with the `z2_*`
   corollaries untouched, confirming Brick 1 changed no signatures.
3. `make -j` per new brick, in order 2 → 3 → 4 → 5. Brick 5 depends on 2 and 3; Brick 4 is
   independent of 5, so they can be built in either order.
4. Every file ends with `Print Assumptions` on its headline theorems (repo standard); each must
   report **"Closed under the global context"**. Specifically check `no_antipode`, the splitting
   theorem, the `Adj bool ≅ Sym` iso, the Legendre hom, and the Brick 5 tensor factorisation —
   if the Brick 3 sigma carrier drags in `proof_irrelevance` or `functional_extensionality`, that
   is the signal to take fallback (a) or (b).
5. Sanity-check Brick 5 concretely before proving the general case: `vm_compute` the monoid iso
   `(ℤ/6, ×) ≅ M_2 × M_3` on all 6 residues, and check the F-free/`Div(n_k)` correspondence at
   `k = 2, 3` against `primorial_primes_1`/`primorial_primes_2` (which are already `vm_compute`
   lemmas at PrimorialSpectralTheory.v:141–142). Cheap, and it catches an off-by-one in the
   `AZero`-versus-unit indexing before the induction is attempted.
6. Full-repo regression: `make -j` from the root, since Brick 1 edits a compiled file.
7. Add the new bricks to `spectral-theory/README.md` in the established per-file prose style, and
   record in `spectral-theory/LEDGER.md` (the repo's honest-audit file): the Brick 3 fallback if
   taken, and the Brick 5 primorial-limit correction against `PrimorialSpectralTheory.v`'s
   CLAIM A.
