#!/bin/bash
# run_rederive.sh -- independent counterexample sweep for IRIS Conjecture 6.1.
# Written from scratch 2026-06-11 (does not use problems/p0-iris/code/*).
#
# Usage: ./run_rederive.sh <plantri_binary> <outdir> [nmin] [nmax]
#
# For each n, generates ALL simple planar triangulations on n vertices with
# plantri's DEFAULT class (-c3m3: 3-connected plane triangulation; dual is a
# simple 3-connected plane cubic graph = graph of a simple 3-polytope, by
# Steinitz), in ascii (-a) format, and pipes them through rederive_filter.
# Exact invocation: plantri -a <n>
set -euo pipefail

PLANTRI=$1
OUT=$2
NMIN=${3:-8}
NMAX=${4:-16}

DIR="$(cd "$(dirname "$0")" && pwd)"
gcc -O3 -o "$OUT/rederive_filter" "$DIR/rederive_filter.c"

LOG="$OUT/counts.log"
: > "$LOG"
echo "plantri version/source: plantri58.tar.gz from https://users.cecs.anu.edu.au/~bdm/plantri/" >> "$LOG"
echo "invocation per n: plantri -a <n> | rederive_filter" >> "$LOG"
echo "violation test: S>=3 and 20*p6 < 39 + 10*p3 - 5*p5 - 20*S (pk = # degree-k vertices of triangulation = # k-gonal faces of dual polytope)" >> "$LOG"
echo "" >> "$LOG"

for n in $(seq "$NMIN" "$NMAX"); do
    echo "=== n=$n (triangulation vertices = polytope faces) ===" | tee -a "$LOG"
    "$PLANTRI" -a "$n" 2>"$OUT/plantri_n$n.stderr" \
        | "$OUT/rederive_filter" > "$OUT/violations_n$n.txt" 2>"$OUT/filter_n$n.stderr"
    cat "$OUT/plantri_n$n.stderr" | tee -a "$LOG"
    cat "$OUT/filter_n$n.stderr"  | tee -a "$LOG"
done
echo "DONE" | tee -a "$LOG"
