#!/usr/bin/env python3
"""
ARC Three-Class Classifier

Classifies each task example into one of three cascade classes:

  IDENTITY:     pos == 0 across all found dimensions
                Output IS the input under the ring structure
                Spatial task — encoding unchanged

  PENULTIMATE:  pos == period-1 in scalar ring
                Output is one step before ring closes
                Transformation task — one cascade step from completion

  FIRST_STEP:   pos == 1 in spatial ring (row/col/2D)
                Output is one step forward into cascade
                These are the L? / fold tasks

With the classification, also records:
  op_lower:  prime axis encoding of signal transformation
  op_2D:     prime axis encoding of full grid transformation
  fold_dir:  col / row / diag
  period:    ring period at dominant dimension
  fano_line: which Fano line the (op_lower, op_2D) pair sits on

Task-level label = (class, op_lower, op_2D, fold_dir)
Consistency across examples = task is fully determined

Usage:
    python arc_three_class.py <path_to_folder_or_file> [--verbose]
"""

import json, sys, os, glob
from collections import Counter, defaultdict
from fractions import Fraction
from sympy import factorint


# ── cell encoding ─────────────────────────────────────────────────────────────

AXIS_NAMES = {
    0b000:'bg',    0b100:'AND',     0b010:'OR',     0b001:'XOR',
    0b110:'AND+OR',0b101:'AND+XOR', 0b011:'OR+XOR', 0b111:'AND+OR+XOR',
}

def cell_encoding(v):
    if v <= 1: return 0b000
    fi = factorint(v)
    return ((1 if 2 in fi else 0) << 2 |
            (1 if 3 in fi else 0) << 1 |
            (1 if any(p > 3 for p in fi) else 0))

def enc_name(e): return AXIS_NAMES.get(e, f'enc{bin(e)}')

def resolve_op(enc_in, enc_out):
    """XOR of two encodings = resolution operator."""
    return enc_name(enc_in ^ enc_out)

def grid_stats(grid):
    H,W = len(grid),len(grid[0])
    cnt = Counter(grid[r][c] for r in range(H) for c in range(W))
    bg  = cnt.most_common(1)[0][0]
    sig = axis = 0
    for row in grid:
        for v in row:
            e = cell_encoding(v); axis |= e
            if v != bg: sig += 1
    return {'axis':axis,'sig':sig,'total':H*W,'bg':bg,'H':H,'W':W}

def marginal_sig(grid, axis='row'):
    H,W = len(grid),len(grid[0])
    cnt = Counter(grid[r][c] for r in range(H) for c in range(W))
    bg  = cnt.most_common(1)[0][0]
    if axis=='row':
        return [sum(1 for c in range(W) if grid[r][c]!=bg) for r in range(H)]
    return [sum(1 for r in range(H) if grid[r][c]!=bg) for c in range(W)]

def color_histogram(grid):
    H,W = len(grid),len(grid[0])
    cnt = Counter(grid[r][c] for r in range(H) for c in range(W))
    bg  = cnt.most_common(1)[0][0]
    return sorted((v,n) for v,n in cnt.items() if v!=bg)

def grids_equal(A,B):
    if len(A)!=len(B) or len(A[0])!=len(B[0]): return False
    return all(A[r][c]==B[r][c] for r in range(len(A)) for c in range(len(A[0])))

def grid_hash(G):
    return tuple(G[r][c] for r in range(len(G)) for c in range(len(G[0])))


# ── Fano lines ────────────────────────────────────────────────────────────────

FANO_LINES = {
    frozenset(['AND']):           'L_AND',
    frozenset(['OR']):            'L_OR',
    frozenset(['XOR']):           'L_XOR',
    frozenset(['AND','OR']):      'L_AO',
    frozenset(['AND','XOR']):     'L_AX',
    frozenset(['OR','XOR']):      'L_OX',
    frozenset(['AND','OR','XOR']):'L_AOX',
}

def fano_of(op_lo, op_hi):
    """Fano line containing both operators."""
    axes = set()
    for op in [op_lo, op_hi]:
        if 'AND' in op: axes.add('AND')
        if 'OR'  in op: axes.add('OR')
        if 'XOR' in op: axes.add('XOR')
    axes.discard('bg')
    if not axes: return 'L_bg'
    return FANO_LINES.get(frozenset(axes), 'L?')


# ── transforms ────────────────────────────────────────────────────────────────

def col_fold(G):
    H,W=len(G),len(G[0])
    return [[G[r][W-1-c] for c in range(W)] for r in range(H)]

def row_fold(G):
    H,W=len(G),len(G[0])
    return [[G[H-1-r][c] for c in range(W)] for r in range(H)]

def diag_fold(G):
    H,W=len(G),len(G[0])
    if H!=W: return None
    return [[G[c][r] for c in range(W)] for r in range(H)]

def xor_val(A,B):
    return [[A[r][c]^B[r][c] for c in range(len(A[0]))] for r in range(len(A))]

def xor_1d(A,B): return [a^b for a,b in zip(A,B)]
def flip_1d(v):  return list(reversed(v))
def is_zero(G):  return all(G[r][c]==0 for r in range(len(G)) for c in range(len(G[0])))
def is_zero_1d(v): return all(x==0 for x in v)

TRANSFORMS = [('col',col_fold),('row',row_fold),('diag',diag_fold)]


# ── ring computation ──────────────────────────────────────────────────────────

def scalar_ring(v, max_steps=32):
    """Gray-code XOR cascade on scalar. Returns (positions→values) list."""
    ring = [v]; seen = {v:0}; cur = v
    for _ in range(max_steps):
        nxt = cur ^ (cur >> 1)
        if nxt in seen or nxt == 0:
            ring.append(nxt); break
        seen[nxt] = len(ring)
        ring.append(nxt); cur = nxt
    return ring

def ring_1d(vec, max_steps=32):
    """1D XOR cascade. Returns list of vectors."""
    ring=[vec]; hashes={tuple(vec):0}; cur=vec
    for _ in range(max_steps):
        nxt=xor_1d(cur,flip_1d(cur)); h=tuple(nxt)
        if h in hashes or is_zero_1d(nxt):
            ring.append(nxt); break
        hashes[h]=len(ring); ring.append(nxt); cur=nxt
    return ring

def ring_2d(G, tfn, max_steps=32):
    """2D XOR cascade. Returns list of grids."""
    ring=[G]; hashes={grid_hash(G):0}; cur=G
    for _ in range(max_steps):
        T=tfn(cur)
        if T is None: return ring
        nxt=xor_val(cur,T); h=grid_hash(nxt)
        if h in hashes or is_zero(nxt):
            ring.append(nxt); break
        hashes[h]=len(ring); ring.append(nxt); cur=nxt
    return ring


# ── three-class classification ────────────────────────────────────────────────

CLASSES = ['IDENTITY', 'PENULTIMATE', 'FIRST_STEP', 'OTHER']

def classify_pos(pos, period):
    """Classify a (pos, period) pair into one of the three classes."""
    if pos is None or period is None or period == 0:
        return None
    if pos == 0:
        return 'IDENTITY'
    if pos == period - 1:
        return 'PENULTIMATE'
    if pos == 1:
        return 'FIRST_STEP'
    return f'OTHER_{pos}/{period}'

def find_pos_in_ring_vals(ring_vals, target):
    """Find position of target in a list of scalar values."""
    for i,v in enumerate(ring_vals):
        if v == target: return i
    return None

def find_pos_in_ring_1d_sig(ring_1d_list, target_sig):
    """Find position where 1D ring has matching signal count."""
    for i,v in enumerate(ring_1d_list):
        sig = sum(1 for x in v if x!=0)
        if sig == target_sig: return i
    return None

def find_pos_in_ring_2d_sig(ring_2d_list, target_sig):
    """Find position where 2D ring has matching signal count."""
    for i,G in enumerate(ring_2d_list):
        st = grid_stats(G)
        if st['sig'] == target_sig: return i
    return None


# ── solve one example ─────────────────────────────────────────────────────────

def solve_example(grid_in, grid_out):
    if not grid_in or not grid_out: return None

    Hi,Wi = len(grid_in), len(grid_in[0])
    st_in  = grid_stats(grid_in)
    st_out = grid_stats(grid_out)
    sig_in,  sig_out  = st_in['sig'],  st_out['sig']
    axis_in, axis_out = st_in['axis'], st_out['axis']

    # resolution operators
    op_lower = enc_name(cell_encoding(sig_in) ^ cell_encoding(sig_out))
    op_2d    = resolve_op(axis_in, axis_out)
    fano     = fano_of(op_lower, op_2d)

    # ── scalar ring ───────────────────────────────────────────────────────────
    sc_ring  = scalar_ring(sig_in)
    sc_pos   = find_pos_in_ring_vals(sc_ring, sig_out)
    sc_per   = len(sc_ring)
    sc_cls   = classify_pos(sc_pos, sc_per)

    # ── row ring ──────────────────────────────────────────────────────────────
    row_in   = marginal_sig(grid_in,  'row')
    row_out_sig = sum(marginal_sig(grid_out, 'row'))
    row_ring = ring_1d(row_in)
    row_pos  = find_pos_in_ring_1d_sig(row_ring, row_out_sig)
    row_per  = len(row_ring)
    row_cls  = classify_pos(row_pos, row_per)

    # ── col ring ──────────────────────────────────────────────────────────────
    col_in   = marginal_sig(grid_in,  'col')
    col_out_sig = sum(marginal_sig(grid_out, 'col'))
    col_ring = ring_1d(col_in)
    col_pos  = find_pos_in_ring_1d_sig(col_ring, col_out_sig)
    col_per  = len(col_ring)
    col_cls  = classify_pos(col_pos, col_per)

    # ── 2D ring ───────────────────────────────────────────────────────────────
    best_2d = {'pos':None,'per':None,'cls':None,'fold':None}
    for fold_name, tfn in TRANSFORMS:
        if fold_name=='diag' and Hi!=Wi: continue
        r2d   = ring_2d(grid_in, tfn)
        pos2d = find_pos_in_ring_2d_sig(r2d, sig_out)
        per2d = len(r2d)
        cls2d = classify_pos(pos2d, per2d)
        if pos2d is not None:
            if best_2d['pos'] is None or \
               cls2d in ('IDENTITY','PENULTIMATE','FIRST_STEP'):
                best_2d = {'pos':pos2d,'per':per2d,
                           'cls':cls2d,'fold':fold_name}
            if cls2d in ('IDENTITY','PENULTIMATE'): break

    # ── dominant class ────────────────────────────────────────────────────────
    # priority: PENULTIMATE > IDENTITY > FIRST_STEP > OTHER
    all_classes = [sc_cls, row_cls, col_cls, best_2d['cls']]
    all_classes = [c for c in all_classes if c]

    def class_priority(c):
        if c == 'PENULTIMATE': return 0
        if c == 'IDENTITY':    return 1
        if c == 'FIRST_STEP':  return 2
        return 3

    dom_cls = min(all_classes, key=class_priority) if all_classes else 'UNKNOWN'

    # dominant period (from most informative dimension)
    dom_per = sc_per  # scalar always has a period

    return {
        'cls':      dom_cls,
        'op_lower': op_lower,
        'op_2d':    op_2d,
        'fano':     fano,
        'fold':     best_2d['fold'] or 'col',
        'sc':       {'pos':sc_pos,  'per':sc_per,  'cls':sc_cls},
        'row':      {'pos':row_pos, 'per':row_per, 'cls':row_cls},
        'col':      {'pos':col_pos, 'per':col_per, 'cls':col_cls},
        '2d':       best_2d,
        'label':    (dom_cls, op_lower, op_2d, best_2d['fold'] or 'col'),
    }


# ── task analysis ─────────────────────────────────────────────────────────────

def analyze_task(path):
    with open(path) as f:
        task = json.load(f)

    filename = os.path.basename(path)
    examples = task.get("train",[])
    n        = len(examples)

    ex_results = [solve_example(ex.get("input"), ex.get("output"))
                  for ex in examples]

    n_solved = sum(1 for r in ex_results if r)

    # task-level label
    labels   = Counter(r['label'] for r in ex_results if r)
    classes  = Counter(r['cls']   for r in ex_results if r)
    op_los   = Counter(r['op_lower'] for r in ex_results if r)
    op_2ds   = Counter(r['op_2d']    for r in ex_results if r)
    fanos    = Counter(r['fano']     for r in ex_results if r)
    folds    = Counter(r['fold']     for r in ex_results if r)

    dom_label  = labels.most_common(1)[0][0]  if labels  else None
    dom_cls    = classes.most_common(1)[0][0] if classes else 'UNKNOWN'
    dom_fano   = fanos.most_common(1)[0][0]   if fanos   else '?'

    lbl_consistent  = len(labels)   == 1
    cls_consistent  = len(classes)  == 1
    op_lo_consistent= len(op_los)   == 1
    op_2d_consistent= len(op_2ds)   == 1

    free_dims = sum([
        not cls_consistent,
        not op_lo_consistent,
        not op_2d_consistent,
        len(folds) > 1,
    ])

    return {
        "file":            filename,
        "n":               n,
        "n_solved":        n_solved,
        "dom_label":       dom_label,
        "dom_cls":         dom_cls,
        "dom_fano":        dom_fano,
        "label_consistent":lbl_consistent,
        "cls_consistent":  cls_consistent,
        "free_dims":       free_dims,
        "classes":         classes,
        "op_los":          op_los,
        "op_2ds":          op_2ds,
        "fanos":           fanos,
        "folds":           folds,
        "ex_results":      ex_results,
    }


# ── printing ──────────────────────────────────────────────────────────────────

def print_task(r, verbose=False):
    lc = "L✓" if r["label_consistent"] else "L✗"
    lbl = str(r["dom_label"]) if r["dom_label"] else "?"
    print(f"  {r['file']:<30} n={r['n']}  "
          f"cls={r['dom_cls']:<12}  "
          f"fano={r['dom_fano']:<8}  "
          f"free={r['free_dims']}  {lc}")
    if verbose:
        for i,res in enumerate(r["ex_results"]):
            if res:
                print(f"    ex{i}  cls={res['cls']:<12}  "
                      f"op_lo={res['op_lower']:<12}  "
                      f"op_2d={res['op_2d']:<12}  "
                      f"fano={res['fano']:<8}  "
                      f"fold={res['fold']}")
                print(f"         sc=({res['sc']['pos']}/{res['sc']['per']},{res['sc']['cls']})  "
                      f"row=({res['row']['pos']}/{res['row']['per']},{res['row']['cls']})  "
                      f"col=({res['col']['pos']}/{res['col']['per']},{res['col']['cls']})  "
                      f"2D=({res['2d']['pos']}/{res['2d']['per']},{res['2d']['cls']})")


def print_stats(results):
    total = len(results)
    if not total: print("No results."); return

    s_lc  = sum(1 for r in results if r["label_consistent"])
    s_cc  = sum(1 for r in results if r["cls_consistent"])

    print(f"\n{'='*60}")
    print(f"Tasks: {total}")
    print(f"  Label consistent:    {s_lc:>5} ({s_lc/total*100:.1f}%)")
    print(f"  Class consistent:    {s_cc:>5} ({s_cc/total*100:.1f}%)")
    print()

    # three-class distribution
    print("Three-class distribution:")
    cls_c = Counter()
    for r in results: cls_c += r["classes"]
    total_ex = sum(cls_c.values())
    for cls in CLASSES + ['UNKNOWN']:
        cnt = cls_c.get(cls, 0)
        bar = "█" * (cnt*30//max(total_ex,1))
        print(f"  {cls:<15} {cnt:>6} ({cnt/max(total_ex,1)*100:.1f}%)  {bar}")
    print()

    # class at task level
    print("Dominant class per task:")
    task_cls_c = Counter(r["dom_cls"] for r in results)
    for cls, cnt in task_cls_c.most_common():
        print(f"  {cls:<15} {cnt:>5} ({cnt/total*100:.1f}%)")
    print()

    # Fano line distribution per class
    print("Fano line by class:")
    cf_c = Counter((r["dom_cls"], r["dom_fano"]) for r in results)
    for (cls, fano), cnt in cf_c.most_common(20):
        print(f"  {cls:<15} {fano:<10} {cnt:>4}")
    print()

    # op_lower × op_2D per class
    print("op_lower × op_2D by class (top 15):")
    cop_c = Counter()
    for r in results:
        for res in r["ex_results"]:
            if res:
                cop_c[(res['cls'], res['op_lower'], res['op_2d'])] += 1
    for (cls, lo, hi), cnt in cop_c.most_common(15):
        print(f"  {cls:<15} {lo:<15} × {hi:<15} {cnt:>5}")
    print()

    # free dims distribution
    print("Free dimensions by class:")
    fd_c = Counter((r["dom_cls"], r["free_dims"]) for r in results)
    for (cls,fd), cnt in fd_c.most_common(15):
        print(f"  {cls:<15} free={fd}  {cnt:>5}")
    print()

    # free dims by n
    print("Free dims by n:")
    by_n = defaultdict(list)
    for r in results: by_n[r["n"]].append(r)
    print(f"  {'n':>3}" + "".join(f"  free={i}" for i in range(5)))
    for n in sorted(by_n):
        g = by_n[n]
        fd_c2 = Counter(r["free_dims"] for r in g)
        row   = f"  {n:>3}"
        for i in range(5):
            row += f"  {fd_c2.get(i,0):>6}"
        print(row)
    print()

    # top labels
    print("Top task labels (cls, op_lower, op_2D, fold):")
    lbl_c = Counter(str(r["dom_label"]) for r in results
                    if r["dom_label"] and r["free_dims"]==0)
    for lbl, cnt in lbl_c.most_common(20):
        print(f"  {cnt:>4}  {lbl}")
    print()

    # class × fold
    print("Class × fold direction:")
    fld_c = Counter((r["dom_cls"], r["folds"].most_common(1)[0][0]
                     if r["folds"] else '?')
                    for r in results)
    for (cls,fold), cnt in fld_c.most_common(12):
        print(f"  {cls:<15} {fold:<8} {cnt:>5}")


# ── main ──────────────────────────────────────────────────────────────────────

def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__); sys.exit(0)

    verbose = "--verbose" in args or "-v" in args
    paths   = [a for a in args if not a.startswith("--")]

    json_files = []
    for p in paths:
        if os.path.isdir(p):
            json_files.extend(sorted(glob.glob(os.path.join(p,"*.json"))))
        elif os.path.isfile(p):
            json_files.append(p)

    if not json_files:
        print("No JSON files found."); sys.exit(1)

    results = []
    for path in json_files:
        try:
            r = analyze_task(path)
            results.append(r)
            print_task(r, verbose)
        except Exception as e:
            print(f"Error {path}: {e}", file=sys.stderr)

    print_stats(results)

if __name__ == "__main__":
    main()
