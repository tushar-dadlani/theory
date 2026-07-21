# Diamond Learning

**An explainable machine learning algorithm in the triadic universe.**

This document describes a complete machine-learning algorithm whose every step is formally verified in Coq (`Closed under the global context` — zero axioms beyond Coq's standard library) and whose every cell update has a single one-symbol reason.

---

## Contents

1. [The universe](#the-universe)
2. [The tensor](#the-tensor-the-actual-structure)
3. [The field rules (the entire algorithm)](#the-field-rules-the-entire-algorithm)
4. [The pipeline (5 steps)](#the-pipeline-5-steps)
5. [Step-by-step walkthrough](#step-by-step-walkthrough)
6. [Convergence](#convergence)
7. [Five proven invariants](#five-proven-invariants)
8. [Reading the trajectory plot](#reading-the-trajectory-plot)
9. [Why this is explainable](#why-this-is-explainable)
10. [How to run it](#how-to-run-it)
11. [Files](#files)

---

## The universe

In this universe, everything is symbolic, and the only primitive symbols are:

| Symbol | Axis | Meaning |
|---|---|---|
| `I` | 45° (diagonal) | identity / passthrough / certain |
| `N` | 90° (orthogonal) | inverse / partial / perturbation |
| `F` | 0° (linear) | absorbing / null / failure |

Two operators on two symbols `{0, 1}` produce three axes through the origin of the 2D plane. The single algebraic law is the **field equation** on `{I, N, F}`:

```
I · x = x          (identity passes through)
x · I = x
N · N = I          (two perturbations cancel — this is the resolver)
F · x = F          (failure absorbs)
x · F = F
```

These five lines are the entire learning algorithm. There are no gradients, no matrix multiplications, no backpropagation, no learning rate.

---

## The tensor (the actual structure)

The metric invariant tensor of the learning process is:

```
M : Axis × Op × Inv  →  Sym3
```

with three index types:

| Index | Cardinality | Values | Meaning |
|---|---|---|---|
| **Axis** | 3 | `{I, N, F}` | the three axes of the plane |
| **Op** | 4 | `{Pos, Dir, Mag, Phase}` | the four operator slots |
| **Inv** | 7 | seven-symbol invariant | `3 in + 1 map + 3 out` |

The construction is **3, 4, 7** — three axes, four operator slots, seven invariants. The cell count `3 · 4 · 7 = 84` is the **enumeration** (the bookkeeping you do when you list all cells); the **structure** is the rank-3 tensor itself.

The four operator slots `{Pos, Dir, Mag, Phase}` are: position on the axis, direction (sign / orientation), magnitude (distance from center), and phase (the `I/N/F` label). Together they fully describe a metric component.

The seven invariants are the seven-symbol bridge from the project: three input symbols on the three axes, one mapping operator (the diagonal `/`), and three output symbols mirroring the inputs.

---

## The field rules (the entire algorithm)

The whole learning step at one cell is:

```
M_out[a, o, i]  =  field3( M_in[a, o, i],  M_D[a, o, i] )
```

where `field3` is the field equation above. Tensor composition is **cell-wise**: no axis mixing, no aggregation across cells. Each of the 84 cells updates independently using its own pair of values.

Because there are only three possible cell values (`I`, `N`, `F`), there are only nine cell-pair cases, and they collapse to four reasons:

| Reason | Pattern | Meaning |
|---|---|---|
| `R_id_pass` | `I · I` (or `I · x`, `x · I` reducing to `x`) | identity passed through |
| `R_NN_resolve` | `N · N → I` | two perturbations cancelled |
| `R_F_absorb` | any cell involving `F` | failure absorbed |
| `R_diamond_active` | `I · N` or `N · I` (gives `N`) | the diamond contributed information |

The Coq theorem `explanation_total` proves these four exhaust every possible cell update.

---

## The pipeline (5 steps)

```
INPUT:   M_in   — prior tensor (3 × 4 × 7)
INPUT:   X      — dataset (n_samples × n_features)
OUTPUT:  M_out  — composed tensor (3 × 4 × 7, same shape)

  STEP 1.  SAMPLE the diamond:  pick 4 extreme points of X along two
           feature pairs — V_E, V_W (F-axis), V_N, V_S (N-axis).

  STEP 2.  RECOVER the unit:    center = mean of the 4 vertices
                                (the unique fixed point of reflection)
                                half_step = |V_E − center|
                                unit = 2 · half_step       ← RECOVERED

  STEP 3.  ASSEMBLE the 7-invariant:  3 vertices on F/N + center on I
                                      + 3 reflections = 7 symbols.

  STEP 4.  PROJECT onto cells:   tensor_from_diamond fills the (3,4,7)
                                 tensor M_D using inv_axis classification.

  STEP 5.  COMPOSE:              M_out[a,o,i] = field3(M_in[a,o,i], M_D[a,o,i])
```

The shape in equals the shape out: a `3 × 4 × 7` tensor goes in, the same shape comes out. Training is iteration of this pipeline; convergence is when one more iteration produces the same tensor.

---

## Step-by-step walkthrough

### Step 1 — sample the diamond

Pick two features of the dataset that you want to anchor the F-axis and the N-axis. Take the four extreme points:

- `V_E` = sample with the maximum value along the F-feature
- `V_W` = sample with the minimum value along the F-feature
- `V_N` = sample with the maximum value along the N-feature
- `V_S` = sample with the minimum value along the N-feature

These four points are a **diamond** — a closed shape with two perpendicular diagonals.

### Step 2 — recover the unit (the half-step)

In the triadic universe, you start without a unit. The diamond gives you one. Compute the center as the mean of the four vertices. The center is the unique fixed point of reflection through the diamond's symmetry. On the unit interval `[0, 1]`, this is the half-step: the value `s` satisfying `s = 1 − s`, namely `s = 1/2`. Doubling the half-step recovers the unit:

```
half_step = |V_E − center|
unit      = 2 · half_step
```

This is exactly the route from `HalfStepRecovery.v` (route 1: reflection fixed point) lifted into feature space. The unit isn't supplied — it's derived from the dataset's own symmetry.

### Step 3 — assemble the seven-invariant

The seven symbols of the dataset's mapping structure assemble naturally:

- **Three input symbols** `{I_in, N_in, F_in}` — one per axis
- **One map operator** `Map` — the diagonal that bridges domain to codomain
- **Three output symbols** `{I_out, N_out, F_out}` — the reflections

The function `inv_axis` classifies each invariant onto its axis: input/output `I` lives on the `I`-axis, input/output `N` on the `N`-axis, input/output `F` on the `F`-axis, and the map lives on the diagonal (`I`-axis).

### Step 4 — project onto the tensor

For each cell `(a, o, i)`:

- if the **operator slot** is `Phase`: cell value is `F` (the phase label is absorbing — it carries no scalar information itself)
- if the **axis** or the **invariant's axis** is `F`: cell value is `F` (the `F`-axis is absorbing)
- if the axis matches the invariant's axis (on-axis): cell value is `I` (active and aligned)
- otherwise (cross-phase between `I` and `N`): cell value is `N` (rotation between the two)

This gives the dataset tensor `M_D`, with the same `3 × 4 × 7` shape as `M_in`.

### Step 5 — compose

For each of the 84 cells:

```
M_out[a, o, i] = field3(M_in[a, o, i], M_D[a, o, i])
```

That's it. Same shape in, same shape out. No reduction, no aggregation, no cross-cell interaction.

---

## Convergence

Training is the iteration:

```
M ← compose(M, tensor_from_diamond(X))
```

Convergence is reached when one more iteration produces the same tensor. There are two natural regimes:

**Period-1 fixed point.** The tensor `M` satisfies `M = compose(M, M_D)`. Nothing moves. This happens when the diamond's information has been fully absorbed and the prior has stopped changing.

**Period-2 cycle.** `M ≠ compose(M, M_D)` but `M = compose(compose(M, M_D), M_D)`. This is the generic case in a triadic universe because of the involution rule `N · N = I`. The cells oscillate in counterphase: cells that were `N` flip to `I` (because `N · N = I`), and cells that were `I` may pick up an `N` from the diamond. After two epochs, every `N → I → ?` round trip closes.

A classical neural net only knows period-1 convergence (loss-below-threshold). The triadic universe naturally produces period-2 fixed points, and the algebra `field3` predicts exactly when they appear.

---

## Five proven invariants

These are the formal guarantees from `LearningPlot.v` (zero axioms). Any visualization or analysis of the learning trajectory must satisfy them.

| # | Invariant | Statement | Theorem |
|---|---|---|---|
| 1 | **Conservation** | `I + N + F = 84` at every epoch | `conservation` |
| 2 | **F-monotone** | `F` count never decreases | `F_monotone` |
| 3 | **Active non-increasing** | `I + N` count never grows | `active_non_increasing` |
| 4 | **Non-negative counts** | `I, N, F ≥ 0` (always trivially) | by typing |
| 5 | **Convergence** | period-1 fixed point or period-2 cycle | `idle_is_fixed` |

The reasoning:

1. **Conservation** holds because `field3` is total: every cell value lands in `{I, N, F}`. The total is preserved cell-wise.
2. **F-monotone** holds because `F` is absorbing in `field3`. Once a cell is `F`, it stays `F` forever.
3. **Active non-increasing** is a corollary: `active = total - F`, and `F` only grows.
4. **Non-negative counts** is structural: counts of distinct symbols are naturals.
5. **Convergence** holds because the trajectory lies in a finite state space (`3^84` possible tensors) and the dynamics are deterministic, so a cycle must form.

---

## Reading the trajectory plot

The plot has six panels.

### Top-left — the diamond and recovered unit

Two clusters in 2D feature space. The four green dots `V_E, V_N, V_W, V_S` are the diamond's vertices. The blue star is the center — the half-step fixed point of reflection. The orange double-arrow is the **recovered unit**, twice the half-step distance from center to `V_E`.

### Top-right — the trajectory in cell-count space (the main plot)

The y-axis is the cell count, capped at 84. Five curves are drawn:

- **grey** at 84: the conserved total (invariant 1)
- **blue** monotone climbing to 54: F-cells (invariant 2)
- **grey-with-squares** monotone falling to 30: active = I+N (invariant 3)
- **green** with triangles: I-cells
- **orange** with V-markers: N-cells

The green and orange curves oscillate in counterphase between epochs 1, 2, 3, … — that is `N · N = I` firing visibly. The system reaches a period-2 cycle by epoch 2.

### Middle-left — per-cell explanations as stacked bars

Each bar is one epoch, height 84. The bar splits into four colors:

- dark green: `id_pass` — identity passed through
- light green: `NN_resolve` — two N's became I
- orange: `diamond_active` — the diamond contributed
- blue: `F_absorb` — F absorbed

Every cell update is exactly one of these four reasons. The bar heights are constant at 84, confirming conservation.

### Middle-right — tensor heatmap snapshots

Four mini-grids show the actual `(axis × op) × inv` tensor at four moments: the identity prior (all green = all I), epoch 1 (orange N's emerging, blue F sweeping the F-axis and Phase row), epoch 2 (N's pairwise cancelled), and the final state. The bottom rows (Phase slot, F-axis) lock to blue immediately — absorption made spatial.

### Bottom-left — the diamond stays consistent

Three diamonds drawn at different epochs overlap. The dataset's geometry doesn't change, so the diamond doesn't drift. Convergence is in **the tensor**, not in the diamond.

### Bottom-middle and bottom-right — the field rules and invariants checklist

The entire algorithm and the five proven invariants checked ✓ on this run.

---

## Why this is explainable

Every cell of `M_out` has a coordinate `(axis, op, inv)` — a triple of named symbolic categories. Every update has exactly one of four reasons drawn from a finite set. Every reason is a single line of the field equation.

You can audit any cell at any epoch by walking back through the trace:

```
M_out[Ax_F, Op_Pos, Inv.F_in] = S_F
  reason: R_F_absorb
  because: tensor_from_diamond(diamond)[Ax_F, Op_Pos, Inv.F_in] = S_F
  because: the F-axis cell is always absorbing (Step 4 rule)
  source: vertex V_E from sample index 47 in the dataset
```

That is a five-step traceback to a specific datapoint, every step a deterministic rule.

Compare to a standard neural net: asking why a weight changed by a specific amount produces an answer involving the chain rule across all upstream neurons, the loss landscape, batch noise, and momentum — opaque even to specialists.

In diamond learning:

- the **dynamics** are five rewrite rules,
- the **state** is a finite labelling of 84 cells,
- the **convergence** is exact equality of dictionaries,
- the **reasons** are a finite set of four named categories,
- the **source** of each cell value is a specific datapoint or a specific field rule.

---

## How to run it

The implementation is in `diamond_learning.py` (the algorithm) and `plot_learning.py` (the visualization). Run:

```bash
python3 diamond_learning.py     # text demo with audit log
python3 plot_learning.py        # produces learning_trajectory.png
```

Verify the proofs in Coq:

```bash
coqc DiamondLearning.v          # the algorithm — zero axioms
coqc LearningPlot.v             # the trajectory invariants — zero axioms
```

Each proof ends with `Print Assumptions ...` showing `Closed under the global context`.

---

## Files

| File | Purpose |
|---|---|
| `DiamondLearning.v` | Coq proof of the algorithm: tensor, composition, explainability |
| `LearningPlot.v` | Coq proof of the five trajectory invariants |
| `diamond_learning.py` | Python implementation of the algorithm |
| `plot_learning.py` | Python visualization producing the trajectory plot |
| `learning_trajectory.png` | The rendered trajectory plot |

The Python code mirrors the Coq definitions exactly: `field3` in Python is the same operator as `field3` in Coq, `tensor_from_diamond` is the same function in both, and the four `CellReason` values are the same enumeration.

---

## Summary

Diamond learning is a complete machine-learning algorithm with these properties:

- **Input and output have the same shape** (a `3 × 4 × 7` tensor), so it composes with itself.
- **The unit is recovered from the data**, not assumed.
- **Five lines of algebra define the entire update rule** — the field equation on `{I, N, F}`.
- **Every cell update has one of four named reasons** drawn from a finite, exhaustive set.
- **Five trajectory invariants are formally proved** in Coq with zero axioms.
- **Convergence happens in finite steps** to a period-1 fixed point or period-2 cycle.
- **Audit is exact**: any cell at any epoch traces back to a specific datapoint and a specific field rule.

The algorithm is not a heuristic, an approximation, or a learned function. It is the symbolic-universe equivalent of "build the metric tensor of the dataset by recovering the unit from a diamond, then compose with the prior."
