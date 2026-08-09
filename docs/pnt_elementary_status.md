# Elementary (Selberg/Erdős) PNT — status & the self-improvement path

_The elementary route is the shortest path to an unconditional, axiom-clean PNT.
The whole chain is `Admitted`/`Axiom`-free and now isolated to ONE research lemma._

## The reduction chain (all axiom-clean)

```
pnt (Un_cv pi_count/(N/ln N) 1)
  <= pnt_of_self_improve            (PNTUnconditional.v)        [DONE, this session]
       needs:  self_improve : forall L, is_limsup Vrem L -> 0 < L -> False
  <= pi_asymp_of_psi                (PNTConditional.v:52)
  <= psi_asymp_cv / Vrem_cv0        (PsiAsymp.v:48/39)
```
`pnt_of_self_improve` (by contradiction: `L0 := limsup Vrem ≥ 0`; if `0 < L0` the
self-improvement gives `False`, so `L0 = 0`, whence `psi ~ x`) is committed and
axiom-clean. **PNT now depends on exactly one lemma: `self_improve`.**

(The older `pnt_of_avg_below`/`dip_avg_below` route via the `Λ(d)/d` weight is a
dead end — the Mertens `2·Kup ≈ 6.8`-per-band tax kills thin dip bands. The
correct track is the log² Selberg inequality below.)

## The self-improvement `self_improve` — the Erdős core

Assume `α := limsup Vrem > 0`. Goal: derive `False` (via `α ≤ α − δ`).

**The key lever is ALREADY PROVED and unused:**
- `StarInequality.v:115` `star_inequality N` :
  `Vrem N · ln²N ≤ Rls (seq 1 N) (fun n => Λ2 n / n · Vrem(N/n)) + O(ln N)`.
- `SmoothingLemma.v:107` `lam2_over_n_bound` : `Σ_{n≤N} Λ2(n)/n = ln²N + O(ln N)`.
- `SelbergPin.v:109/207` `signed_pin`/`sign_oscillation`; `SelbergDynamics.v:60/84`
  `plateau_pos/neg` (excursions have positive multiplicative width);
  `SelbergSignedExtremes.Vrem_eq_absVsig:53`.

### Next concrete step: `self_improve_of_dip` (the Λ₂/ln² analog of `dip_avg_below`)

State the Λ₂-weighted dip and reduce `self_improve` to it via `star_inequality`:
```coq
Definition ind2 (b:R)(N n:nat) : R := if Rle_dec (Vrem (N/n)%nat) b then 1 else 0.
Definition dipw2 (b:R)(N:nat) : R := Rls (seq 1 N) (fun n => Lam2 n / INR n * ind2 b N n).
Definition lambda2_dip (L:R) : Prop :=
  exists b theta, b < L /\ 0 < theta /\
    exists K, forall N, (K<=N)%nat -> theta * (ln (INR N))^2 <= dipw2 b N.

Theorem self_improve_of_dip :
  forall L, is_limsup Vrem L -> 0 < L -> lambda2_dip L -> False.
```
Accounting (mirror `SelbergDip.dip_avg_below`, but `Λ2/ln²` in place of `Λ/ln`):
split `seq 1 N` at `q = N/N0` (`N0` from the `is_limsup` upper bound, so `n≤q ⇒
N/n≥N0 ⇒ Vrem(N/n) < α+ε`); on the bulk use `Vrem(N/n) < α+ε` minus the dip credit
`(α+ε−b)·Ddip`; on the tail `n>q` use `Vrem ≤ Kup−1` and the Λ₂-tail bound
`Σ_{n>q} Λ2/n = ln²N − ln²q + O(ln N) = O(ln N)` (from `lam2_over_n_bound` at `N`
and `q`; `ln²N − ln²(N/N0) = ln N0·(2ln N − ln N0) = O(ln N)`). Result:
`Σ Λ2/n·Vrem(N/n) ≤ (α+ε − (α−b)θ)ln²N + O(ln N)`, and `star_inequality` gives
`Vrem(N) ≤ α+ε − (α−b)θ + o(1)` for all large N; the `is_limsup` reach
(`Vrem(k) > α−ε` i.o.) then contradicts it for `ε < (α−b)θ/4`. ~200–300 lines,
concrete; needs `Lam2_nonneg` (Λ2 = Λ·ln + Σ Λ·Λ ≥ 0 for n≥1) as a small helper.
Reusable: `SelbergDip.v` helpers (`Rls_lin`, `Rls_scal'`, `ln_le'`, `tail_ln`,
`Ndiv_ge`), `Rls_app`, `Rls_le`.

### The crux: `lambda2_dip` (2d) — open research

Produce `b<α`, `θ>0` with `dipw2 b N ≥ θ·ln²N` for all large N. From
`sign_oscillation` + `signed_pin` (`Vsig` crosses 0 i.o. with positive
multiplicative width via `plateau_pos/neg`), `Vrem` dips below any `b>0` on a
`Λ2`-positive set of scales. **Must be executed as a GLOBAL estimate** (the set
where `Vrem(N/n) ≈ α` cannot carry almost-all the `Λ2`-mass), not per-band
summation (which risks the per-band `O(ln N)` tax × `~ln N` bands). This is the
historical hard theorem (Selberg's original / Tao's exposition); research-grade.

## Verification
`Print Assumptions pnt_of_self_improve` shows only the four classical axioms +
the `self_improve` hypothesis. Each new file: register in `_CoqProject`,
axiom-clean, commit with the `Co-Authored-By: Claude Opus 4.8` trailer, push to
`origin/riemann-functional-equation`.
