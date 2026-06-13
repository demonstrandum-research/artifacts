#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Mutation tests for checker_g143.py: every targeted corruption of the
certificate must be REJECTED. A checker that never rejects proves nothing.
"""
import copy
import json
import subprocess
import sys
import tempfile
import os

BASE = json.load(open("certificate_g143.json", encoding="utf-8"))


def run_checker(cert):
    fd, path = tempfile.mkstemp(suffix=".json", dir=".")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(cert, fh)
        proc = subprocess.run([sys.executable, "checker_g143.py", path],
                              capture_output=True, text=True, timeout=900)
        accepted = (proc.returncode == 0
                    and "CHECKER VERDICT: ACCEPT" in proc.stdout)
        return accepted, proc.stdout
    finally:
        os.unlink(path)


def single(inst):
    c = copy.deepcopy(BASE)
    c["instances"] = [inst]
    return c


def dumbbell_inst(name):
    for i in BASE["instances"]:
        if name in i["name"]:
            return copy.deepcopy(i)
    raise KeyError(name)


MUTS = []

# M1: claim a violation for a graph that satisfies the conjecture: D(10,5,10).
from checker_g143 import dumbbell_edges, adjacency_from_edges, bfs_wiener
from fractions import Fraction
n, edges = dumbbell_edges(10, 5, 10)
A = adjacency_from_edges(n, edges)
m = len(edges); W = bfs_wiener(A)
MUTS.append(("M1 false claim: D(10,5,10) said to violate both", single({
    "name": "M1", "family": "dumbbell", "t1": 10, "p": 5, "t2": 10,
    "n": n, "m": m, "W": W, "k": 4,
    "edges": [list(e) for e in edges],
    "rhs_n2": str(Fraction(m * n * n, 2 * W)),
    "rhs_pairs": str(Fraction(m * n * (n - 1), 2 * W)),
    "violates": ["n2", "pairs"]})))

# M2: D(6,12,19) claimed to violate the strict n2 convention (it does not).
i = dumbbell_inst("6,12,19")
i["violates"] = ["n2", "pairs"]
MUTS.append(("M2 overclaim: D(6,12,19) said to violate n2", single(i)))

# M3: drop a path edge (disconnects the graph; also breaks canonical form).
i = dumbbell_inst("7,12,20")
i["edges"] = [e for e in i["edges"] if tuple(e) != [7, 8] and e != [7, 8]]
i["m"] -= 1
MUTS.append(("M3 missing path edge (disconnected)", single(i)))

# M4: corrupt Wiener index by 1.
i = dumbbell_inst("7,12,20")
i["W"] += 1
MUTS.append(("M4 Wiener index off by one", single(i)))

# M5: corrupt positive-eigenvalue count.
i = dumbbell_inst("7,12,20")
i["k"] += 1
MUTS.append(("M5 k off by one", single(i)))

# M6: corrupt claimed RHS fraction.
i = dumbbell_inst("7,12,20")
i["rhs_n2"] = "10646/311"
MUTS.append(("M6 corrupted rhs_n2", single(i)))

# M7: absurd claimed margin lower bound.
i = dumbbell_inst("7,12,20")
i["margin_n2_lower"] = "100"
MUTS.append(("M7 inflated claimed margin bound", single(i)))

# M8: non-canonical relabeling of edges (family fields kept).
i = dumbbell_inst("7,12,20")
perm = list(range(i["n"]))
perm[0], perm[1] = perm[1], perm[0]
perm[7], perm[20] = perm[20], perm[7]
i["edges"] = [[perm[u], perm[v]] for u, v in i["edges"]]
MUTS.append(("M8 relabeled edges vs canonical dumbbell", single(i)))

# M9: swap one clique edge for a chord on the path (same m, different graph).
i = dumbbell_inst("7,12,20")
ed = [tuple(e) for e in i["edges"]]
ed.remove((1, 2))
ed.append((8, 10))
i["edges"] = [list(e) for e in ed]
MUTS.append(("M9 edge swapped (clique edge -> path chord)", single(i)))

# M10: wrong t1/t2 metadata for a correct edge list.
i = dumbbell_inst("7,12,20")
i["t1"], i["t2"] = 8, 19
MUTS.append(("M10 family metadata mismatched", single(i)))


def main():
    print("positive control: pristine certificate must ACCEPT")
    ok, out = run_checker(BASE)
    print("  pristine -> %s" % ("ACCEPT" if ok else "REJECT"))
    if not ok:
        print(out)
        sys.exit(1)
    all_good = True
    for name, cert in MUTS:
        ok, out = run_checker(cert)
        verdict = "ACCEPT" if ok else "REJECT"
        good = not ok
        all_good &= good
        print("  %-55s -> %s %s" % (name, verdict,
                                    "(expected REJECT)" if good else
                                    "*** MUTATION SURVIVED ***"))
    print("MUTATION TESTS: %s" % ("ALL KILLED" if all_good else "FAILURE"))
    sys.exit(0 if all_good else 1)


if __name__ == "__main__":
    main()
