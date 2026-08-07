# Route B: the integral representation `Φ(s) = s ∫₁^∞ ψ(⌊x⌋) x^{−s−1} dx`  ✅ (sum-of-cells form)

For `Re s > 1`, built this session, all axiom-clean, pushed. Files (build order):

| Brick | File | Content |
|------|------|---------|
| — | `CFTC.v` | C-valued FTC for `x^{−s}`: `gC_FTC : CgderivInt s a b = gC s b − gC s a`, `gderivC s x = −s x^{−s−1}` |
| — | `CAbelSummation.v` | C-valued summation by parts `Cabel_summation` |
| IR1 | `CVonMangoldtAbel.v` | `phi_abel : Cpsum(pterm s) M = ψ(S M)(S M)^{−s} − Cabel_correction …`; `cell_increment` |
| IR3 | `CVonMangoldtIntegral.v` | `psi_weight_cv0`, `phi_correction_cv : correction → −Φ`, `phi_integral_rep : −correction → Φ`, `correction_cells` |

## End state

```coq
phi_integral_rep : CUn_cv (fun M => Copp (Cabel_correction (RtoC∘Lam) (gC s∘INR) M)) (Phi s H)
correction_cells : Cabel_correction (RtoC∘Lam)(gC s∘INR) M
                 = Cpsum (fun k => RtoC(psi k) · (gC s(INR(S k)) − gC s(INR k))) M
cell_increment   : gC s(INR(S k)) − gC s(INR k) = CgderivInt s (INR k)(INR(S k))   (= ∫_k^{k+1}(−s x^{−s−1})dx)
```

So `Φ(s) = lim_M Σ_{k=1}^{M} ψ(k)·(s ∫_k^{k+1} x^{−s−1}dx) = s ∫₁^∞ ψ(⌊x⌋) x^{−s−1} dx`,
the integral representation in the honest sum-of-cell-integrals sense (each cell increment is
a genuine Riemann integral via the C-valued FTC).

## One documented upgrade

To state it as a *single* Riemann integral `∫₁^N` of the step kernel `ψ(⌊x⌋)·x^{−s−1}` (rather
than a sum of cells), one needs Riemann-integrability of the step function on `[1,N]` (the
endpoint-jump / single-point-change argument, then `RiemannInt_P24` interval-additivity like
`GaussChasles.chasles_R`). Deferred; the cell-sum form is mathematically identical and is the
form Newman/Tauberian can consume.

## Remaining Route B
Milestone C (Newman's analytic theorem — greenfield C-valued contour integration + Cauchy)
and Milestone D (Tauberian ⇒ `ψ~x` ⇒ `pi_asymp_of_psi` ⇒ PNT).
