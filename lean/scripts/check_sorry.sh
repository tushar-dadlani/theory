#!/usr/bin/env bash
# Syntactic ban-list over PROJECT sources only (never .lake/).
#
# This is the cheap layer. The real gate is TDLean/Audit.lean, whose `#guard_msgs in
# #print axioms` blocks fail the build if `sorryAx` reaches any audited theorem. This
# script catches what `#print axioms` cannot see (opaque, unsafe, @[implemented_by],
# banned imports) and gives a fast answer without a build.
#
# Comments and docstrings are stripped before matching -- otherwise prose *about* `sorry`
# (of which this project has plenty) trips the gate.
set -uo pipefail
cd "$(dirname "$0")/.."

python3 - "$@" <<'PY'
import re, sys, pathlib

BAD = [
    (r'(?<![A-Za-z_.])sorry(?![A-Za-z_])',      'sorry'),
    (r'(?<![A-Za-z_.])native_decide(?![A-Za-z_])', 'native_decide'),
    (r'^\s*axiom\s',                            'axiom declaration'),
    (r'^\s*opaque\s',                           'opaque'),
    (r'(?<![A-Za-z_.])unsafe\s',                'unsafe'),
    (r'@\[implemented_by',                      '@[implemented_by]'),
]

BANNED_IMPORTS = re.compile(
    r'^import\s+Mathlib$'
    r'|^import\s+Mathlib\.NumberTheory\.LSeries\.(RiemannZeta|HurwitzZeta|Nonvanishing|AbstractFuncEq)'
    r'|^import\s+Mathlib\.NumberTheory\.ModularForms\.JacobiTheta'
    r'|^import\s+Mathlib\.Analysis\.SpecialFunctions\.Gaussian\.PoissonSummation'
    r'|^import\s+Mathlib\.Analysis\.SpecialFunctions\.Gamma\.Deligne'
    r'|^import\s+Mathlib\.NumberTheory\.(Chebyshev|PrimeCounting)')

def strip_comments(src: str) -> str:
    """Blank out /- ... -/ blocks (incl. /-- docstrings) and -- line comments,
    preserving line structure so reported line numbers stay correct."""
    out, i, depth = [], 0, 0
    n = len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif src.startswith('-/', i) and depth:
            depth -= 1; out.append('  '); i += 2
        elif depth:
            out.append('\n' if src[i] == '\n' else ' '); i += 1
        elif src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        else:
            out.append(src[i]); i += 1
    return ''.join(out)

fail = False
files = sorted(pathlib.Path('.').glob('TDLean.lean')) + \
        sorted(pathlib.Path('TDLean').rglob('*.lean'))

for f in files:
    raw = f.read_text()
    code = strip_comments(raw)
    lines = code.split('\n')
    raw_lines = raw.split('\n')
    in_audit = 'Audit' in f.parts or f.name == 'Audit.lean'
    for k, line in enumerate(lines, 1):
        for pat, label in BAD:
            if re.search(pat, line):
                print(f'{f}:{k}: banned construct ({label}): {raw_lines[k-1].strip()}')
                fail = True
        # banned imports may appear ONLY under TDLean/Audit/
        if BANNED_IMPORTS.search(line) and not in_audit:
            print(f'{f}:{k}: banned import outside TDLean/Audit/: {raw_lines[k-1].strip()}')
            fail = True

if fail:
    print('FAIL: see LEDGER.md section 1 for the ban list')
    sys.exit(1)
print(f'OK: {len(files)} files clean -- no sorry / axiom / native_decide / opaque / unsafe,')
print('    and no banned imports outside TDLean/Audit/')
PY
