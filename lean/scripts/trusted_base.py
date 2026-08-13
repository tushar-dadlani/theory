#!/usr/bin/env python3
"""Emit the project's trusted base: the exact transitive mathlib closure it relies on.

mathlib in this toolchain uses the Lean module system, so imports appear both as
`import Mathlib.X` and as `public import Mathlib.X` after a `module` line. Both are parsed.
`Mathlib/Analysis/Normed/Algebra/Exponential.lean` contains a literal `import Mathlib` inside
a docstring code block; naive scanners conclude everything depends on all of mathlib, so
comments are stripped first.
"""
import re, sys, pathlib, collections

ROOT = pathlib.Path(__file__).resolve().parent.parent
ML = ROOT / ".lake/packages/mathlib"

BANNED = re.compile(
    r'^Mathlib$'
    r'|^Mathlib\.NumberTheory\.LSeries\.'
    r'|^Mathlib\.NumberTheory\.Harmonic\.ZetaAsymp$'
    r'|^Mathlib\.NumberTheory\.EulerProduct\.DirichletLSeries$'
    r'|^Mathlib\.NumberTheory\.ModularForms\.JacobiTheta'
    r'|^Mathlib\.Analysis\.SpecialFunctions\.Gaussian\.PoissonSummation$'
    r'|^Mathlib\.Analysis\.SpecialFunctions\.Gamma\.Deligne$'
    r'|^Mathlib\.NumberTheory\.(Chebyshev|PrimeCounting)$')

IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)', re.M)

def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2
        elif src.startswith("-/", i) and depth:
            depth -= 1; i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i); j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        else:
            out.append(src[i]); i += 1
    return "".join(out)

def imports_of(path):
    try:
        return IMPORT.findall(strip_comments(path.read_text(encoding="utf-8")))
    except OSError:
        return []

def module_path(mod):
    return ML / (mod.replace(".", "/") + ".lean")

# direct mathlib imports of our own sources
direct = set()
for f in sorted((ROOT / "TDLean").rglob("*.lean")) + [ROOT / "TDLean.lean"]:
    for m in imports_of(f):
        if m.split(".")[0] == "Mathlib":
            direct.add(m)

# transitive closure
seen, queue = set(), collections.deque(direct)
while queue:
    m = queue.popleft()
    if m in seen:
        continue
    seen.add(m)
    p = module_path(m)
    if p.exists():
        for d in imports_of(p):
            if d.split(".")[0] == "Mathlib" and d not in seen:
                queue.append(d)

violations = sorted(m for m in seen if BANNED.match(m))

print(f"direct mathlib imports : {len(direct)}")
print(f"transitive closure     : {len(seen)} modules")
print(f"banned modules in closure: {len(violations)}")
for v in violations:
    print("  VIOLATION:", v)
print()
print("Direct imports:")
for m in sorted(direct):
    print("  " + m)
sys.exit(1 if violations else 0)
