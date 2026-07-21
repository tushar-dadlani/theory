# Packages — shared substrate libraries

These directories hold the **reusable cores** that files throughout the tree build on.
They are grouped here (rather than in a step/theme dir) because they are *libraries*,
depended on from many places.

- **`DIM/`** — the "dimension" package: capability, crypto, hashing, complexity,
  reproducibility, consensus, arithmetic and training layers. Self-contained
  (`dim_types` is the root; everything else builds on it).
- **`GHS/`** — the GHS core: `Core`, `RiemannHypothesis`, the `Triple` substrate, and
  `InvolutionEquivalence`.
- **`Stratum/`** — the tower substrate: `TowerConstruction`, `StratumCore`, `StratumTypes`.

## Imports

Every directory in this repo is mapped to the **root logical namespace** in `_CoqProject`
(`-Q <dir> ""`), so each file is imported by its **basename** regardless of where it lives:

```coq
Require Import Triple.             (* packages/GHS/Triple.v *)
Require Import TowerConstruction.  (* packages/Stratum/TowerConstruction.v *)
Require Import dim_types.          (* packages/DIM/dim_types.v *)
```

The theory's earlier dotted conventions (`DIM.*`, `GHS.proven.*`, `Stratum.*`, and
`From MillenniumKappa Require Import foundations.*`) were normalized to these bare
basename imports so the whole repo builds under a single loadpath.
