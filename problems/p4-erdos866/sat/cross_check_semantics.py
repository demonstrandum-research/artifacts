"""End-to-end semantic cross-check of the archived upper-bound claims on
tiny cells, fully independent of the SAT/CEGAR/CNF pipeline.

For each chosen small cell (variant, k, n, M) this script enumerates ALL
subsets A of {1..2n} of size M+1 and, for each, brute-forces the existence of
a configuration directly from the frozen definition (PROBLEM.md section 3):
k pairwise-distinct integers b_1..b_k (all >= 1 for variant h; arbitrary in
[2-2n, 2n-1] for variant g, which is a complete range: at most one b_i is
non-positive, every positive b_i is <= 2n-1, and the non-positive one is
>= 1-(2n-1)) with every pairwise sum in A.

If every size-(M+1) subset has a configuration, the cell's upper half
("no config-free A of size M+1") is confirmed by exhaustive enumeration —
no SAT solver, no clause tuples, no cardinality encoding, no shared oracle
code (find_configs is NOT used here).
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CELLS = os.path.join(HERE, "..", "..", "..", "lab", "data", "cells")


def has_config_bruteforce(A, n, k, variant):
    As = frozenset(A)
    N = 2 * n
    lo = 1 if variant == "h" else 2 - N
    hi = N - 1
    rng = range(lo, hi + 1)

    def extend(chosen):
        if len(chosen) == k:
            return True
        start = chosen[-1] + 1 if chosen else lo
        for b in range(start, hi + 1):
            ok = True
            for c in chosen:
                if (b + c) not in As:
                    ok = False
                    break
            if ok and extend(chosen + [b]):
                return True
        return False

    return extend([])


def check_cell(cell_id):
    with open(os.path.join(CELLS, cell_id + ".json"), encoding="utf-8") as f:
        rec = json.load(f)
    n, k, variant, M = rec["n"], rec["k"], rec["variant"], rec["M"]
    N = 2 * n
    total = 0
    for A in itertools.combinations(range(1, N + 1), M + 1):
        total += 1
        if not has_config_bruteforce(A, n, k, variant):
            print(f"FAIL {cell_id}: config-free A of size {M+1} exists: {A}")
            return False
    print(f"ok   {cell_id}: all {total} subsets of size {M+1} of [1,{N}] "
          f"have a ({variant},{k})-configuration  -> M <= {M} confirmed "
          f"by exhaustion")
    return True


if __name__ == "__main__":
    cells = sys.argv[1:] or ["g3_n004", "g4_n004", "g5_n005",
                             "h3_n004", "h4_n005", "h5_n005"]
    bad = [c for c in cells if not check_cell(c)]
    sys.exit(1 if bad else 0)
