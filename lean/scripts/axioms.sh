#!/usr/bin/env bash
# Ad-hoc single-theorem axiom query, without rebuilding the audit file.
# usage: scripts/axioms.sh TDLean.Newman.trunc_winding
set -euo pipefail
cd "$(dirname "$0")/.."
printf 'import TDLean\n#print axioms %s\n' "$1" | lake env lean --stdin
