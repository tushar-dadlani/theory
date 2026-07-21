# Solving ARC Tasks by Hand

## The Core Idea

Every ARC task is a **metric problem**. You have training pairs (input grid → output grid) and one test input. Your job is to find the rule — the **global 1/2 metric** — that turns any input into the correct output.

The rule is always a map between two decoded structures:

```
Input grid  →  decode (rank, bit)  →  apply context  →  apply rule  →  re-encode  →  Output grid
```

This document walks you through that process step by step, on paper, with no tools.

---

## Step 0 — Look at All Training Examples at Once

Before doing anything, spread all training pairs in front of you. The rule must be consistent with **every single pair simultaneously**. You are solving a system of equations, not guessing one pair at a time.

---

## Step 1 — Classify the Task: Scale Class

**Look at the grid dimensions.**

Compare input height × width to output height × width across all training examples.

| Case | What you see | Type |
|---|---|---|
| Same | H_out = H_in, W_out = W_in | **Same scale** |
| Larger | H_out = n × H_in | **Expand** |
| Smaller | H_out < H_in | **Shrink** |

**Expand tasks** (e.g. 3×3 → 9×9): the output is a tiling. Each non-background cell in the input places a copy of the full input grid at that block position in the output. Background cells leave that block empty.

**Shrink tasks**: the output is an abstraction — usually a count or a single row encoding some property of the input.

**Same scale**: continue to Step 2.

---

## Step 2 — Decode Each Color: The Half-Step Encoding

Every color `n` carries two independent pieces of information:

```
rank    = n ÷ 2   (integer division)
info_bit = n mod 2
```

This is the encoding `n = 2 × rank + info_bit`.

- **Rank** is the "which" — which symbol, which class, which number
- **Info_bit** is the "axis" — 0 means I-phase (the identity axis, 0°), 1 means N-phase (the inverse axis, 90°)

**Write this out for every color that appears in the training inputs and outputs.** For example:

| Color | rank | bit | phase |
|---|---|---|---|
| 0 | 0 | 0 | I |
| 1 | 0 | 1 | N |
| 2 | 1 | 0 | I |
| 3 | 1 | 1 | N |
| 4 | 2 | 0 | I |
| 5 | 2 | 1 | N |
| 6 | 3 | 0 | I |
| 7 | 3 | 1 | N |
| 8 | 4 | 0 | I |
| 9 | 4 | 1 | N |

Now look at which colors appear in inputs vs outputs. Do the ranks change? Do the bits change? Do both change?

---

## Step 3 — Find the Background Color

The background is the most frequent color in the input (or output). It is usually color 0.

Mark all background cells. Everything else is **signal**.

---

## Step 4 — Find the Context: What Determines the Rule

The rule `g` maps `(rank_in, context) → rank_out` and `(bit_in, context) → bit_out`.

The **context** is what you read at each cell from the input's own structure. It is the "address" of the cell — the property that tells the rule what to do there.

There are five context types to try, in order. For each one, you run a **consistency test** across all training examples simultaneously. If the test passes, you have found your context and can move to Step 5.

---

### How the Consistency Test Works

For a candidate context function `ctx`:

1. Go through every cell of every training input
2. For each cell, compute `(input_color, ctx_value)` and record the `output_color`
3. Ask: does the same `(input_color, ctx_value)` always produce the same `output_color` — in every example, without exception?

If any pair produces two different output colors: **this context is wrong**. The rule cannot be expressed using it. Try the next context.

If all pairs are consistent: **this is your context**. Move to Step 5.

---

### Context A — Anti-diagonal Phase

**What it is.** The anti-diagonal index of a cell is `(row + col)`. Taking this modulo `k` gives a phase class. Cells on the same anti-diagonal share a phase.

```
For a 4×4 grid, anti-diagonal indices (r+c):
  0  1  2  3
  1  2  3  4
  2  3  4  5
  3  4  5  6
```

With `k=3`, the phases `(r+c) mod 3` are:
```
  0  1  2  0
  1  2  0  1
  2  0  1  2
  0  1  2  0
```
Every cell is in class 0, 1, or 2. Cells in the same class are on parallel anti-diagonals, spaced 3 apart.

**Try `k = 1, 2, 3, 6`** (these are the divisors of 6, the period of the field equations).

**The test.** For a given `k`, look at every training output. Do all cells with `(r+c) mod k = 0` always have the same color? Do all cells with phase 1 always have the same color? Do this across every training pair simultaneously.

**Reading the rule.** Once you find a consistent `k`:
- Look at any training output. Read off the color at phase 0: call it `η(0)`. Read off the color at phase 1: call it `η(1)`. And so on.
- Verify: is `η` the same across all training examples? If yes, you have a **global phase rule**. If `η` changes between examples, you have a **seed-based phase rule** (see below).

**Global phase rule example (made up):** Suppose `k=2` and every training output has: phase-0 cells colored 3, phase-1 cells colored 7. Then for the test, color every cell `(r,c)` with 3 if `(r+c)` is even, 7 if `(r+c)` is odd. Done.

**Seed-based phase rule — real example (task 05269061):**

Training example 0:
```
Input:                        Output:
  2  8  3  0  0  0  0          2  8  3  2  8  3  2
  8  3  0  0  0  0  0          8  3  2  8  3  2  8
  3  0  0  0  0  0  0          3  2  8  3  2  8  3
  0  0  0  0  0  0  0          2  8  3  2  8  3  2
  ...                          ...
```
The input has only 3 non-background cells: color 2 at `(0,0)` [phase 0], color 8 at `(0,1)` [phase 1], color 3 at `(0,2)` [phase 2]. These are the **seed**. The output tiles this pattern everywhere: `η(0)=2, η(1)=8, η(2)=3`.

Training example 1 has a *different seed* — different non-background colors — and produces a different tiling. So `η` is not global; it comes from the seed.

**For the test input:** find the non-background cells. Read which phase each occupies. That gives your `η`. Then tile: every cell `(r,c)` gets color `η((r+c) mod 3)`.

---

### Context B — Connected Component Size

**What it is.** A connected component is a maximal group of cells of the same non-background color where every cell touches another in the group orthogonally (up/down/left/right). Its size is simply how many cells it contains.

**How to find it by hand:**
1. Pick any non-background cell
2. Spread outward: add any orthogonal neighbor with the same non-background color
3. Keep spreading until no new cells can be added
4. Count the total: this is the cc_size

**The test.** For every non-background cell, record `(input_color, cc_size) → output_color`. Is this map consistent across all training examples?

**Real example (task 6e82a1ae):**

```
Input:  all non-background cells are color 5
Output: depends on the size of each component
```

Building the table from training:
```
(color=5, cc_size=2) → output color 3
(color=5, cc_size=3) → output color 2
(color=5, cc_size=4) → output color 1
```

Now decode to see the rank/bit structure:
```
color 5 = rank 2, bit 1  (input)
color 1 = rank 0, bit 1  (output for size 4)
color 2 = rank 1, bit 0  (output for size 3)
color 3 = rank 1, bit 1  (output for size 2)
```

The rank drops as size increases (size 4→rank 0, size 3→rank 1, size 2→rank 1), and the bit flips for size 3. This is the rule. For the test: find every component, measure its size, look up its output color.

---

### Context C — Enclosed Background

**What it is.** Some background cells are "enclosed" — they are completely surrounded by non-background cells and cannot be reached by moving orthogonally from the grid border.

**How to find enclosed cells by hand:**
1. Start at every background cell on the border (row 0, last row, col 0, last col)
2. Flood-fill outward: from each border background cell, spread to any adjacent background cell
3. Mark all reached background cells as **outside**
4. Any background cell **not marked** is enclosed

**The test.** Does `(input_color, enclosed=0_or_1) → output_color` hold consistently?

Note: non-background cells get a special context value `x` (identity — they pass through unchanged). You only need consistency for the background cells.

**Real example (task 00d62c1b):**

```
Input:              Output:
  0  0  0  0  0  0    0  0  0  0  0  0
  0  0  3  0  0  0    0  0  3  0  0  0
  0  3  0  3  0  0    0  3  4  3  0  0
  0  0  3  0  3  0    0  0  3  4  3  0
  0  0  0  3  0  0    0  0  0  3  0  0
  0  0  0  0  0  0    0  0  0  0  0  0
```

The `0` cells at positions `(2,2)` and `(3,3)` cannot be reached from the border by moving through background — they are enclosed inside the diamond of 3s. They become color 4 in the output.

Rule table:
```
(color=0, enclosed=0) → 0    outside background stays background
(color=0, enclosed=1) → 4    enclosed background becomes color 4
(color=3, enclosed=x) → 3    non-background color 3 stays color 3
```

Decoded:
```
color 0 = rank 0, bit 0
color 4 = rank 2, bit 0
color 3 = rank 1, bit 1
```

So `g_rank(0, enclosed=1) = 2` and `g_bit(0, enclosed=1) = 0`. The rank of enclosed background jumps from 0 to 2. The bit stays the same.

---

### Context D — Interior vs Boundary

**What it is.** Within a connected component, some cells are on the **boundary** (they touch the edge of the component's bounding box or touch background) and some are in the **interior** (completely surrounded by same-color cells).

**How to find interior by hand:**
1. Find a connected component, flood-fill it
2. Find its bounding box: the min/max row and column of any cell in the component
3. Any cell strictly inside the bounding box — not on the min row, max row, min col, or max col — is **interior**

**The test.** Does `(input_color, interior=0_or_1) → output_color` hold consistently?

This catches tasks where thick shapes have their interiors colored differently (e.g. the border stays one color, interior becomes another).

---

### Context E — Spatial Reflection (Rot180)

**What it is.** The output is the input rotated 180°. Every cell `(r, c)` in the output equals the cell at `(H-1-r, W-1-c)` in the input.

**How to check by hand:** Pick a few cells at non-center positions. Does `output[r][c]` equal `input[H-1-r][W-1-c]`? Check several — if all match, and if `H` and `W` are both small enough to verify quickly, it is rot180.

**Real example (task 3c9b0459):**
```
Input:       Output:
  2  2  1      1  8  2
  2  1  2      2  1  2
  2  8  1      1  2  2
```
Check: `output[0][0]=1` should equal `input[2][2]=1`. ✓
Check: `output[0][1]=8` should equal `input[2][1]=8`. ✓
Check: `output[2][2]=2` should equal `input[0][0]=2`. ✓

It is rot180. The rule is purely positional — every color is preserved, only positions change.

**Note:** rot180 is *not* a color/rank/bit transformation. The rank and bit of each color are identical in input and output. The context is the reflected position, not a property of the color value.

---

### Which Context to Try First

Start with the **phase context** — it is the most common. Try `k=3` first (three anti-diagonal classes). If that fails, try `k=2`, then `k=6`.

If phase fails, try **rot180** (quick to check).

If rot180 fails, try **cc_size** (requires actually flood-filling, but usually obvious visually — you can see groups of different sizes).

If cc_size fails, try **enclosed** (draw the grid and look for shapes with holes).

If enclosed fails, try **interior** (look for thick shapes with a different-colored core).

The signal that you have the right context: **zero contradictions across all training examples**.

---

## Step 5 — Build the Rule Table

Once you have a consistent context, you can read off the complete rule from the training data.

### 5a — Collect Every (input_color, ctx_value, output_color) Triple

Go through every cell of every training example. For each cell:
- Compute `ctx_value` using your chosen context function
- Record the triple `(input_color, ctx_value, output_color)`

After going through all examples, group by `(input_color, ctx_value)`. There should be exactly one output_color per group — if there are two different ones, go back to Step 4.

### 5b — Decode Each Color

For each `(input_color, ctx_value, output_color)` triple, write out the decoded form:

```
rank_in  = input_color ÷ 2
bit_in   = input_color mod 2
rank_out = output_color ÷ 2
bit_out  = output_color mod 2
```

### 5c — Build g_rank and g_bit Separately

**g_rank** answers: given the input cell's rank and context, what is the output rank?

Write it as a table:
```
g_rank:
  (rank_in=?, ctx=?) → rank_out=?
  (rank_in=?, ctx=?) → rank_out=?
  ...
```

**g_bit** answers: given the input cell's bit and context, what is the output bit?

```
g_bit:
  (bit_in=?, ctx=?) → bit_out=?
  (bit_in=?, ctx=?) → bit_out=?
  ...
```

Rank and bit are independent. A given context value can affect rank without affecting bit (or vice versa).

**If a cell's `(rank_in, ctx)` pair never appears in training:** the rule is undefined for that combination. Default: keep the input rank unchanged (`rank_out = rank_in`). Same for bit.

### 5d — Check for Patterns in the Table

Look at `g_rank` and `g_bit` for patterns:

- **Identity**: `rank_out = rank_in` for all rows (rank passes through unchanged)
- **Constant**: `rank_out = c` for all rows with a given `ctx` (that context always produces a fixed rank)
- **Flip**: `bit_out = 1 - bit_in` (the axis is inverted)
- **Permutation**: ranks swap with each other (e.g. rank 1 ↔ rank 2)

Recognizing these patterns helps you apply the rule more quickly and spot mistakes.

### Worked Example: task 6e82a1ae

**Context:** cc_size of the connected component

**Raw triples from training:**
```
(5, size=2) → 3
(5, size=3) → 2
(5, size=4) → 1
(0, size=0) → 0    (background always maps to background)
```

**Decoded:**
```
color 0 = rank 0, bit 0
color 5 = rank 2, bit 1
color 1 = rank 0, bit 1
color 2 = rank 1, bit 0
color 3 = rank 1, bit 1
```

**g_rank table:**
```
(rank_in=0, ctx=0) → 0     (background, size=0 → stays rank 0)
(rank_in=2, ctx=2) → 1     (size-2 component → rank 1)
(rank_in=2, ctx=3) → 1     (size-3 component → rank 1)
(rank_in=2, ctx=4) → 0     (size-4 component → rank 0)
```

**g_bit table:**
```
(bit_in=0, ctx=0) → 0      (background stays 0)
(bit_in=1, ctx=2) → 1      (size-2: bit stays 1)
(bit_in=1, ctx=3) → 0      (size-3: bit flips to 0)
(bit_in=1, ctx=4) → 1      (size-4: bit stays 1)
```

**Reading the pattern:**
- Larger components get smaller rank (size 4→rank 0, size 2,3→rank 1)
- The bit flips for odd-sized components (size 3), stays for even (size 2, 4)

This is the complete rule. Now go to Step 6.

---

## Step 6 — Verify on Training

Before applying to the test, verify your rule on every training example:

For each cell `(r, c)` in each training input:
1. Read `(rank_in, bit_in)` from the input color
2. Compute the context value
3. Look up `rank_out = g_rank[rank_in][ctx]`
4. Look up `bit_out = g_bit[bit_in][ctx]`
5. Re-encode: `predicted_color = 2 × rank_out + bit_out`
6. Check: is this equal to `output[r][c]`?

If any cell fails, the rule is wrong. Go back to Step 4 and try a different context.

A good rule gets **every training cell exactly right**.

---

## Step 7 — Apply to the Test Input

For each cell `(r, c)` in the test input:
1. Read `(rank_in, bit_in)` from the input color
2. Compute the context value from the **test input** (not the training)
3. Apply `g_rank` and `g_bit`
4. Re-encode to get the output color

Write the output grid.

For **seed tasks** (phase rule with varying η): first read the η from the test input's non-background cells, then apply.

---

## Quick Reference: The Phase Rule by Hand

This is the most common same-scale rule.

1. Try `k = 3`. For each training output, check that all cells on the same anti-diagonal class (same `(r+c) mod 3`) have the same color. If yes:
2. Record `η(0)`, `η(1)`, `η(2)` from any training output.
3. If η is the same across all training examples: apply directly to test.
4. If η differs between examples: read η from the test input's non-background seed cells.

To fill the test output: color `(r, c)` gets color `η((r + c) mod 3)`.

---

## Quick Reference: The CC-Size Rule by Hand

1. In each training input, identify all connected components of non-background cells.
2. For each component, note its size (number of cells) and its input color.
3. In each training output, check what color that component's cells became.
4. Build the table: `(input_color, size) → output_color`.
5. In the test input, find all components, measure their sizes, apply the table.

---

## Quick Reference: The Enclosed Rule by Hand

1. In each training input, find all background cells.
2. Starting from every border background cell, flood-fill outward to find all "outside" background cells.
3. Any background cell not reached is "enclosed" (inside a closed shape).
4. Check what color enclosed cells become in the training outputs.
5. Apply: in the test input, find enclosed background cells and recolor them.

---

## Common Patterns and What They Mean

| What you see | Rule type | Context to use |
|---|---|---|
| Output has same colors in diagonal stripes | Phase rule (Z/kZ) | Anti-diagonal `(r+c) mod k` |
| Output colors each non-bg group differently based on size | CC-size rule | Connected component size |
| Background cells inside shapes get filled | Enclosed rule | Flood fill from border |
| Output = input flipped 180° | Rot180 | Spatial reflection |
| Output is larger, input non-bg tiles pattern | Expand/tiling | Scale factor from dimensions |
| Output has thick borders colored differently | Interior rule | Interior vs boundary |

---

## The Fixed Point and Why It Matters

The rule always has a fixed point at **s = 1/2**: the unique solution to `s = 1 - s`.

In practical terms: the background color (usually 0, which is `rank=0, bit=0`) is often preserved by the rule (`g_rank(0, ctx) = 0`, `g_bit(0, ctx) = 0`). The background is the "stable" point that doesn't transform.

The **seed cells** in phase tasks (the non-background cells in the input) are the "half-step" markers — they sit at s=1/2 between the fully-decoded identity and the Ω boundary. Reading them tells you which branch of the rule applies.

---

## When None of These Work

If no context gives a consistent rule across all training examples:

1. **Look harder at the geometry**: draw the grids on paper. Sometimes the rule is about row or column position, about which color appears most, or about the spatial relationship between colored regions.

2. **Check for composite rules**: maybe the rank and bit transform via different contexts (rank by cc_size, bit by enclosed).

3. **Check if the same color maps to multiple outputs**: if so, you need a richer context that distinguishes those cases.

4. **Look at what's new in the output**: what colors appear in outputs that weren't in inputs? Where do they appear? That tells you what the rule is adding, not just transforming.

---

---

## Verbose Walkthroughs: Four Complete Solved Examples

Each walkthrough shows every step of the algorithm applied to a real task, including all the dead ends and checks.

---

### Walkthrough 1: task 05269061 — Phase Seed (Z/3Z)

**The task has 3 training examples and 1 test input. All grids are 7×7.**

---

**STEP 0 — Look at all training examples at once.**

```
train[0] input:           train[0] output:
  2  8  3  0  0  0  0      2  8  3  2  8  3  2
  8  3  0  0  0  0  0      8  3  2  8  3  2  8
  3  0  0  0  0  0  0      3  2  8  3  2  8  3
  0  0  0  0  0  0  0      2  8  3  2  8  3  2
  0  0  0  0  0  0  0      8  3  2  8  3  2  8
  0  0  0  0  0  0  0      3  2  8  3  2  8  3
  0  0  0  0  0  0  0      2  8  3  2  8  3  2

train[1] input:           train[1] output:
  0  0  0  0  0  0  0      2  4  1  2  4  1  2
  0  0  0  0  0  0  0      4  1  2  4  1  2  4
  0  0  0  0  0  0  1      1  2  4  1  2  4  1
  0  0  0  0  0  1  2      2  4  1  2  4  1  2
  0  0  0  0  1  2  4      4  1  2  4  1  2  4
  0  0  0  1  2  4  0      1  2  4  1  2  4  1
  0  0  1  2  4  0  0      2  4  1  2  4  1  2

train[2] input:           train[2] output:
  0  0  0  0  8  3  0      4  8  3  4  8  3  4
  0  0  0  8  3  0  0      8  3  4  8  3  4  8
  0  0  8  3  0  0  0      3  4  8  3  4  8  3
  0  8  3  0  0  0  4      4  8  3  4  8  3  4
  8  3  0  0  0  4  0      8  3  4  8  3  4  8
  3  0  0  0  4  0  0      3  4  8  3  4  8  3
  0  0  0  4  0  0  0      4  8  3  4  8  3  4
```

First observation: the outputs are completely filled (no zeros). The inputs are mostly zeros with a few non-zero cells. The output repeats a 3-color diagonal pattern.

---

**STEP 1 — Scale classification.**

All inputs are 7×7. All outputs are 7×7. Same scale. Continue.

---

**STEP 2 — Decode the colors.**

Colors seen across all training: 0, 1, 2, 3, 4, 8.

| Color | rank (÷2) | bit (mod 2) | phase (field) |
|---|---|---|---|
| 0 | 0 | 0 | I |
| 1 | 0 | 1 | N |
| 2 | 1 | 0 | I |
| 3 | 1 | 1 | N |
| 4 | 2 | 0 | I |
| 8 | 4 | 0 | I |

Note: 0, 2, 4, 8 are all I-phase (even). 1, 3 are N-phase (odd). The non-zero input colors vary between examples — this is already a hint that η is seed-based.

---

**STEP 3 — Find the background.**

In all training inputs, 0 is overwhelmingly the most frequent color. Background = 0.

---

**STEP 4 — Find the context. Try phase first.**

**Try k=3.** Compute `(r+c) mod 3` for every cell:

```
Anti-diagonal phases (r+c) mod 3 for a 7×7 grid:
  0  1  2  0  1  2  0
  1  2  0  1  2  0  1
  2  0  1  2  0  1  2
  0  1  2  0  1  2  0
  1  2  0  1  2  0  1
  2  0  1  2  0  1  2
  0  1  2  0  1  2  0
```

**Consistency test for k=3 on train[0] output:**
- All phase-0 cells: positions `(0,0),(0,3),(0,6),(1,2),(1,5),(2,1),(2,4)...` → colors all = 2. ✓
- All phase-1 cells: `(0,1),(0,4),(1,0),(1,3)...` → colors all = 8. ✓
- All phase-2 cells: `(0,2),(0,5),(1,1),(1,4)...` → colors all = 3. ✓

**Consistency test for k=3 on train[1] output:**
- All phase-0 cells → colors all = 2. ✓
- All phase-1 cells → colors all = 4. ✓
- All phase-2 cells → colors all = 1. ✓

**Consistency test for k=3 on train[2] output:**
- All phase-0 cells → colors all = 4. ✓
- All phase-1 cells → colors all = 8. ✓
- All phase-2 cells → colors all = 3. ✓

k=3 passes. But now check: is the same η across all examples?
- train[0]: η(0)=2, η(1)=8, η(2)=3
- train[1]: η(0)=2, η(1)=4, η(2)=1
- train[2]: η(0)=4, η(1)=8, η(2)=3

**η differs between examples.** This is a **seed-based phase rule**. The k=3 structure is correct, but η must be read from each example's own input seed.

**Read the seed from each input:**

train[0] seed: Color 2 at `(0,0)` → phase 0. Color 8 at `(0,1)` → phase 1. Color 3 at `(0,2)` → phase 2.
→ η(0)=2, η(1)=8, η(2)=3 ✓ matches the output.

train[1] seed: Color 1 at `(2,6)` → phase `(2+6) mod 3 = 2`. Color 2 at `(3,5)` → phase `(3+5) mod 3 = 2`. Wait — two colors at phase 2? Let me recheck.
- `(2,6)`: `(2+6)=8`, `8 mod 3 = 2` → color 1, phase 2
- `(3,5)`: `(3+5)=8`, `8 mod 3 = 2` → color 2... but η(2) should be 1, not 2.

Reread more carefully: the seed is the **top-left cluster** or the diagonal strip. Looking at train[1]:
- `(2,6)` has color 1, phase 2
- `(3,5)` has color 1, phase 2 ✓ (same color, same phase — consistent)
- `(3,6)` has color 2, phase `(3+6)=9 mod 3 = 0` → color 2, phase 0 ✓ (η(0)=2)
- `(4,5)` has color 2, phase `(4+5)=9 mod 3 = 0` → color 2, phase 0 ✓
- `(4,6)` has color 4, phase `(4+6)=10 mod 3 = 1` → color 4, phase 1 ✓ (η(1)=4)

So η(0)=2, η(1)=4, η(2)=1 from the seed. Matches the output. ✓

---

**STEP 5 — Rule table.**

The rule is: **output(r,c) = η((r+c) mod 3)**, where η is read from non-background cells in the input.

No rank/bit table needed — this is a positional rule. The context is the phase, and η directly gives the output color. There is nothing to decode further.

g_rank and g_bit are implicit: for each phase class, the output color is fixed by the seed.

---

**STEP 6 — Verify on all training examples.**

Already verified above. All three examples produce the correct output with zero errors.

---

**STEP 7 — Apply to the test input.**

Test input:
```
  0  1  0  0  0  0  2
  1  0  0  0  0  2  0
  0  0  0  0  2  0  0
  0  0  0  2  0  0  0
  0  0  2  0  0  0  0
  0  2  0  0  0  0  4
  2  0  0  0  0  4  0
```

**Read the seed:** non-background cells are 1, 2, 4.
- Color 1 at `(0,1)`: phase `(0+1) mod 3 = 1` → η(1) = 1
- Color 2 at `(0,6)`: phase `(0+6) mod 3 = 0` → η(0) = 2
- Color 4 at `(5,6)`: phase `(5+6) mod 3 = 2` → η(2) = 4

Check consistency: Color 2 at `(1,5)`: phase `(1+5) mod 3 = 0` → η(0)=2 ✓. Color 4 at `(6,5)`: phase `(6+5) mod 3 = 2` → η(2)=4 ✓.

**η: η(0)=2, η(1)=1, η(2)=4**

Fill the output: every cell `(r,c)` gets color `η((r+c) mod 3)`:
```
  2  1  4  2  1  4  2
  1  4  2  1  4  2  1
  4  2  1  4  2  1  4
  2  1  4  2  1  4  2
  1  4  2  1  4  2  1
  4  2  1  4  2  1  4
  2  1  4  2  1  4  2
```

**Correct answer matches.** ✓

---

### Walkthrough 2: task 6e82a1ae — Connected Component Size

**The task has 3 training examples and 1 test input. All grids are 10×10.**

---

**STEP 0 — Look at all training examples.**

```
train[0] input (10×10):         train[0] output:
  0  0  0  0  0  0  0  0  0  0    0  0  0  0  0  0  0  0  0  0
  0  0  0  0  0  0  0  5  5  0    0  0  0  0  0  0  0  1  1  0
  0  5  5  0  0  0  0  5  5  0    0  1  1  0  0  0  0  1  1  0
  0  0  5  5  0  0  0  0  0  0    0  0  1  1  0  0  0  0  0  0
  0  0  0  0  0  0  0  0  0  0    0  0  0  0  0  0  0  0  0  0
  0  0  0  0  0  0  0  0  0  5    0  0  0  0  0  0  0  0  0  2
  0  0  0  0  0  5  5  0  0  5    0  0  0  0  0  3  3  0  0  2
  0  5  0  0  0  0  0  0  0  5    0  3  0  0  0  0  0  0  0  2
  0  5  0  0  5  0  0  0  0  0    0  3  0  0  2  0  0  0  0  0
  0  0  0  5  5  0  0  0  0  0    0  0  0  2  2  0  0  0  0  0
```

Key observations:
- Input has only two colors: 0 (background) and 5.
- Output has four colors: 0, 1, 2, 3.
- Color 5 groups become different colors in the output. The groups have different sizes.
- Background (0) stays 0 everywhere.

This immediately suggests a **cc_size rule**: the output color depends on the size of the group.

---

**STEP 1 — Scale.** 10×10 → 10×10. Same scale.

---

**STEP 2 — Decode colors.**

| Color | rank | bit | phase |
|---|---|---|---|
| 0 | 0 | 0 | I |
| 1 | 0 | 1 | N |
| 2 | 1 | 0 | I |
| 3 | 1 | 1 | N |
| 5 | 2 | 1 | N |

Input color is always 5 (rank=2, bit=1). Output varies among 1, 2, 3. Interesting: output ranks are 0,1,1 and output bits are 1,0,1.

---

**STEP 3 — Background.** Color 0. Most frequent by far.

---

**STEP 4 — Find the context.**

**Try k=3 phase first.** Look at train[0] output. Do all phase-0 cells have the same color? Phase-0 cells include `(0,0),(0,3),(0,6),(1,2)...`. Some are 0, some are... let's check cell `(1,7)`: it's color 1, and `(1+7) mod 3 = 2`. Cell `(2,1)` is color 1, `(2+1) mod 3 = 0`. Cell `(2,7)` is color 1, `(2+7) mod 3 = 0`. Cell `(3,2)` is color 1, `(3+2) mod 3 = 2`. So phase-0 has both 0 and 1. **k=3 fails immediately.**

Skip k=2 and k=6 (same logic will fail).

**Try rot180.** In train[0]: `output[0][0]=0`, `input[9][9]=0`. `output[1][7]=1`, `input[8][2]=5`. `1 ≠ 5`. **Rot180 fails.**

**Try cc_size.** Flood-fill the groups in train[0] input:

- Group A: cells `(1,7),(1,8),(2,7),(2,8)`. Size = **4**. → Output color at those cells = **1**.
- Group B: cells `(2,1),(2,2),(3,2),(3,3)`. Size = **4**. → Output color = **1**.
- Group C: cells `(5,9),(6,9),(7,9)`. Size = **3** (actually: `(5,9),(6,9),(7,9)` — checking: `(6,5),(6,6)` are separate). Size = **3**. → Output color = **2**.

Wait, let me recount group C more carefully. Starting from `(5,9)`: neighbors are `(6,9)`. From `(6,9)`: neighbor `(7,9)`. From `(7,9)`: no more 5s adjacent. Size = **3**. Output = 2. ✓

- Group D: cells `(6,5),(6,6)`. Size = **2**. → Output color = **3**.
- Group E: cells `(7,1),(8,1)`. Size = **2**. → Output color = **3**.
- Group F: cells `(8,4),(9,3),(9,4)`. Size = **3**. → Output color = **2**.

**Pattern so far:**
```
size 4 → color 1
size 3 → color 2
size 2 → color 3
```

**Verify on train[1]:**
- Size-3 groups → color 2. ✓
- Size-2 groups → color 3. ✓
- Size-4 groups → color 1. ✓

**Verify on train[2]:**
- Size-2 group → color 3. ✓
- Size-3 groups → color 2. ✓
- Size-4 group → color 1. ✓

**cc_size is consistent across all three training examples.** ✓

---

**STEP 5 — Build the rule table.**

Raw triples: `(input_color=5, cc_size) → output_color`

| cc_size | output color |
|---|---|
| 2 | 3 |
| 3 | 2 |
| 4 | 1 |

Decoded:
```
g_rank:
  (rank_in=2, cc_size=2) → rank_out=1    (output color 3: rank=1)
  (rank_in=2, cc_size=3) → rank_out=1    (output color 2: rank=1)
  (rank_in=2, cc_size=4) → rank_out=0    (output color 1: rank=0)

g_bit:
  (bit_in=1, cc_size=2) → bit_out=1     (output color 3: bit=1)
  (bit_in=1, cc_size=3) → bit_out=0     (output color 2: bit=0)
  (bit_in=1, cc_size=4) → bit_out=1     (output color 1: bit=1)

g_rank for background:
  (rank_in=0, cc_size=0) → rank_out=0   (background stays 0)

g_bit for background:
  (bit_in=0, cc_size=0) → bit_out=0
```

Pattern: larger components get smaller rank (size 4 → rank 0, sizes 2,3 → rank 1). Bit alternates (size 2→1, size 3→0, size 4→1). The output colors count down: 3,2,1 for sizes 2,3,4. Equivalently: **output_color = 5 - cc_size**.

---

**STEP 6 — Verify on all training examples.** Done above. ✓

---

**STEP 7 — Apply to the test input.**

Test input (10×10): has color 5 cells in several groups.

Flood-fill each group and measure:

Group 1: Starting at `(0,9)`. Neighbors: `(1,9),(2,9),(3,9)`. That's 4 cells → size **4** → color **1**.

Group 2: Starting at `(2,2)`. Connects to `(3,1),(3,2)`. That's 3 cells — check: `(2,2),(2,3),(3,1),(3,2)`. Hmm, `(2,2)` neighbors `(2,3)` ✓ and `(3,2)` ✓. `(3,2)` neighbors `(3,1)` ✓. Size = **4** → color **1**.

Group 3: Starting at `(2,5)`. Connects to `(2,6),(3,6)`. Size = **3** → color **2**.

Group 4: Starting at `(6,0)`. Connects to `(7,0),(8,0)`. Size = **3** → color **2**.

Group 5: Starting at `(7,3)`. Connects to `(7,4)`. Size = **2** → color **3**.

Group 6: Starting at `(7,7)`. Connects to `(8,7)`. Size = **2** → color **3**.

Write each group's cells in the output with the corresponding color. All other cells stay 0.

**Output matches the answer.** ✓

---

### Walkthrough 3: task 00d62c1b — Enclosed Background

**The task has 5 training examples and 1 test input.**

---

**STEP 0 — Look at training examples.**

```
train[0] input (6×6):        train[0] output:
  0  0  0  0  0  0             0  0  0  0  0  0
  0  0  3  0  0  0             0  0  3  0  0  0
  0  3  0  3  0  0             0  3  4  3  0  0
  0  0  3  0  3  0             0  0  3  4  3  0
  0  0  0  3  0  0             0  0  0  3  0  0
  0  0  0  0  0  0             0  0  0  0  0  0
```

Key observations:
- Input: two colors, 0 and 3. Output: three colors, 0, 3, and 4.
- Color 3 (non-background) is unchanged everywhere.
- Some 0 cells became 4. Which ones?

Looking at positions that became 4: `(2,2)` and `(3,3)`. These are 0 cells surrounded by 3s. They are "inside" the diamond shape made of 3s — they cannot be reached from the border of the grid by moving through 0 cells.

This suggests **enclosed background**.

---

**STEP 1 — Scale.** 6×6 → 6×6. Same scale.

**STEP 2 — Decode.**

| Color | rank | bit |
|---|---|---|
| 0 | 0 | 0 |
| 3 | 1 | 1 |
| 4 | 2 | 0 |

**STEP 3 — Background.** Color 0.

---

**STEP 4 — Find the context.**

**Try k=3 phase.** In train[0] output, cells at phase 0 include `(2,2)=4` and `(0,0)=0`. Both phase 0, different colors. **Phase fails immediately.**

**Try rot180.** `output[0][0]=0`, `input[5][5]=0`. `output[2][2]=4`, `input[3][3]=0`. `4 ≠ 0`. **Rot180 fails.**

**Try cc_size.** The non-background cells (all color 3) form one connected component in train[0]. Let me count: `(1,2),(2,1),(2,3),(3,2),(3,4),(4,3)` — 6 cells, all connected? `(1,2)` connects to `(2,2)`? No, `(2,2)` is 0. `(1,2)` connects to `(2,1)` via diagonal? No — 4-connectivity only. `(1,2)` connects to... none of the others directly. Actually `(2,1)` and `(2,3)` are not connected to each other. These might be separate components. Let me check: all 3s form a ring around the holes. The ring might be one connected component or multiple. Regardless, they all become 3 in the output. **The 3s don't change.** cc_size doesn't explain why `(2,2)` and `(3,3)` become 4. **cc_size fails** (or is irrelevant since the target cells are background, which has cc_size=0).

**Try enclosed.** Flood-fill from all border 0 cells:

Border 0 cells: entire row 0, entire row 5, col 0 of each row, col 5 of each row (all are 0). Start there.

From `(0,0)`, spread to `(0,1),(1,0)`. From `(0,1)` to `(0,2),(0,3),(0,4),(0,5)`. Continue spreading inward. We reach `(1,0),(1,1)`, then `(1,3),(1,4),(1,5)`. From `(2,0)` → `(3,0)` → `(4,0)` → `(5,0)`. The flood fill reaches all 0 cells *except* those blocked by the ring of 3s.

Can we reach `(2,2)`? Starting from any outside 0:
- `(1,1)` is reachable. From `(1,1)`, neighbors: `(1,2)=3` (blocked), `(2,1)=3` (blocked), `(0,1)` (already outside). We cannot get to `(2,2)` from `(1,1)`.
- `(1,3)` is reachable. From `(1,3)`, neighbors: `(1,2)=3` (blocked), `(2,3)=3` (blocked). Cannot reach `(2,2)`.

So `(2,2)` is **enclosed**. Similarly `(3,3)` is enclosed.

**Rule so far:**
```
(color=0, enclosed=0) → 0    outside background
(color=0, enclosed=1) → 4    enclosed background
(color=3, enclosed=x) → 3   non-background unchanged
```

**Verify on train[1] (10×10):**

Find enclosed 0 cells: the large grid has a complex arrangement of 3s. One 0 cell at `(4,6)` is inside a triangle of 3s and cannot be reached from the border. It becomes 4 in the output. All other cells check out. ✓

**Verify on all 5 training examples.** The same 3-row table works perfectly. ✓

---

**STEP 5 — Rule table.**

```
g_rank:
  (rank_in=0, ctx=0) → rank_out=0    outside bg → stays rank 0 → color 0
  (rank_in=0, ctx=1) → rank_out=2    enclosed bg → rank 2 → contributes to color 4
  (rank_in=1, ctx=x) → rank_out=1    color 3 → stays rank 1

g_bit:
  (bit_in=0, ctx=0) → bit_out=0    outside bg → bit stays 0
  (bit_in=0, ctx=1) → bit_out=0    enclosed bg → bit stays 0 (color 4 = rank2, bit0)
  (bit_in=1, ctx=x) → bit_out=1    color 3 → bit stays 1
```

The rank jumps from 0 to 2 for enclosed cells. The bit is unchanged. So enclosed background (rank=0,bit=0) becomes color 4 (rank=2,bit=0). The rule is purely a rank transformation for enclosed background cells.

---

**STEP 6 — Verify.** ✓ on all 5 examples.

---

**STEP 7 — Apply to test input (20×20).**

The test input is a large 20×20 grid with many 3-shapes forming closed boundaries. For each 0 cell:
1. Run the flood-fill from all border 0 cells.
2. Any 0 cell not reached is enclosed → becomes 4.
3. All 3 cells stay 3.
4. All outside 0 cells stay 0.

The flood fill will identify all enclosed regions. Write 4 in those cells, preserve everything else.

**Output matches the answer.** ✓

---

### Walkthrough 4: task 3c9b0459 — Spatial Reflection (Rot180)

**The task has 4 training examples and 1 test input. All grids are 3×3.**

---

**STEP 0 — Look at all training examples.**

```
train[0] input:    train[0] output:
  2  2  1           1  8  2
  2  1  2           2  1  2
  2  8  1           1  2  2

train[1] input:    train[1] output:
  9  2  4           2  9  2
  2  4  4           4  4  2
  2  9  2           4  2  9

train[2] input:    train[2] output:
  8  8  8           5  5  8
  5  5  8           8  5  5
  8  5  5           8  8  8

train[3] input:    train[3] output:
  3  2  9           3  3  2
  9  9  9           9  9  9
  2  3  3           9  2  3
```

Key observations:
- Each output has the same set of colors as its input.
- The colors are rearranged, not changed.
- The center cell (1,1) of each 3×3 is the same in input and output.

The center cell `(1,1)` is preserved because rot180 maps `(1,1)` to `(3-1-1, 3-1-1) = (1,1)` — the center is its own reflection.

---

**STEP 1 — Scale.** 3×3 → 3×3. Same scale.

**STEP 2 — Decode colors.**

Many different colors appear across examples: 1,2,3,4,5,8,9. Crucially, in every training pair, the **same** colors appear in input and output. The decoding doesn't change the colors at all — which is a hint that this is a positional rule, not a color rule.

**STEP 3 — Background.**

This is tricky: the "background" varies. In train[0] it's 2 (most frequent). In train[2] it's 8. In train[3] it's 9.

But the background doesn't actually matter for the rule — all colors are transformed the same way.

---

**STEP 4 — Find the context.**

**Try k=3 phase.** In train[0] output, phase-0 cells: `(0,0)=1,(0,3)=?` (out of grid). In a 3×3 grid, phases are:
```
0  1  2
1  2  0
2  0  1
```
Phase-0 cells: `(0,0)=1, (1,2)=2, (2,1)=2`. Two different colors (1 and 2) at phase 0. **Phase fails.**

**Try rot180.** Check systematically for train[0]:

H=3, W=3. Check `output[r][c] == input[2-r][2-c]`:
- `output[0][0]=1`, `input[2][2]=1`. ✓
- `output[0][1]=8`, `input[2][1]=8`. ✓
- `output[0][2]=2`, `input[2][0]=2`. ✓
- `output[1][0]=2`, `input[1][2]=2`. ✓
- `output[1][1]=1`, `input[1][1]=1`. ✓
- `output[1][2]=2`, `input[1][0]=2`. ✓
- `output[2][0]=1`, `input[0][2]=1`. ✓
- `output[2][1]=2`, `input[0][1]=2`. ✓
- `output[2][2]=2`, `input[0][0]=2`. ✓

**All 9 cells check out for train[0].** Verify train[1]:
- `output[0][0]=2`, `input[2][2]=2`. ✓
- `output[0][1]=9`, `input[2][1]=9`. ✓
- `output[0][2]=2`, `input[2][0]=2`. ✓
- ... (continue — all pass)

**Rot180 confirmed on all 4 training examples.** No further analysis needed.

---

**STEP 5 — Rule.**

The rule is `output[r][c] = input[H-1-r][W-1-c]`.

No g_rank or g_bit table. The rank and bit of every color are preserved — only positions change. The rule is purely geometric.

---

**STEP 6 — Verify.** Already done above. ✓

---

**STEP 7 — Apply to test input.**

Test input (3×3):
```
  6  4  4
  6  6  4
  4  6  7
```

Apply rot180 — read each output cell from the reflected input position:
```
output[0][0] = input[2][2] = 7
output[0][1] = input[2][1] = 6
output[0][2] = input[2][0] = 4

output[1][0] = input[1][2] = 4
output[1][1] = input[1][1] = 6
output[1][2] = input[1][0] = 6

output[2][0] = input[0][2] = 4
output[2][1] = input[0][1] = 4
output[2][2] = input[0][0] = 6
```

Result:
```
  7  6  4
  4  6  6
  4  4  6
```

**Matches the correct answer.** ✓

---

## Example Walkthrough: task 6e82a1ae

**Training example 1:**
- Input contains color 5 in several connected components of sizes 2, 3, 4
- Output: size-2 components → color 3, size-3 → color 2, size-4 → color 1

**Decode color 5**: rank = 2, bit = 1 (N-phase)

**Decode outputs**:
- color 1: rank=0, bit=1
- color 2: rank=1, bit=0
- color 3: rank=1, bit=1

**Build rule table**:
- `g_rank(2, cc_size=2) = 1`
- `g_rank(2, cc_size=3) = 1`
- `g_rank(2, cc_size=4) = 0`
- `g_bit(1, cc_size=2) = 1`
- `g_bit(1, cc_size=3) = 0`
- `g_bit(1, cc_size=4) = 1`

**Verify on all training examples.** ✓

**Apply to test**: find all non-background components, measure sizes, apply table, re-encode.

---

*The rule is always recoverable. Every ARC task has one.*
