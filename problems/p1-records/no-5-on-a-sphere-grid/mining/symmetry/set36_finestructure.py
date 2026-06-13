#!/usr/bin/env python3
"""Fine structure of the 36-set's 18 pair directions: parity census, central-plane
saturation, line/circle usage, and comparison against pool baselines."""
import json, os, sys
from collections import Counter
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, "..", ".."))
S36 = sl.load_json_set(os.path.join(BASE, "certificates", "record36_centralsym.json"))
pool = sl.load_jsonl_sets(os.path.join(BASE, "runs", "central-symmetric", "main-run", "pool_34.jsonl"))

us = []
Sf = set(S36)
for p in Sf:
    q = tuple(12 - c for c in p)
    if p < q:
        us.append(tuple(p[i] - 6 for i in range(3)))
assert len(us) == 18

# parity census of u
par = Counter(tuple(c % 2 for c in u) for u in us)
print("u parity census (36-set):", dict(par))
pool_par = Counter()
nsym = 0
for S in pool[:1000]:
    core = sl.sym_core(S)
    if len(core) != len(S):
        continue
    nsym += 1
    for p in set(S):
        q = tuple(12 - c for c in p)
        if p < q:
            pool_par[tuple((p[i] - 6) % 2 for i in range(3))] += 1
print("u parity census (pool, frac):", {k: round(v / sum(pool_par.values()), 3) for k, v in pool_par.items()})

# distinct |u|^2 mod small numbers
for m in (3, 4, 5, 8, 13):
    print(f"r2 mod {m} census:", dict(Counter(sum(c*c for c in u) % m for u in us)))

# central-plane saturation: every 2 pairs span a central plane with exactly 4 pts.
# count how many GRID cells lie on each such plane (room that must stay empty)
def plane_cells(u1, u2):
    nvec = (u1[1]*u2[2] - u1[2]*u2[1], u1[2]*u2[0] - u1[0]*u2[2], u1[0]*u2[1] - u1[1]*u2[0])
    if nvec == (0, 0, 0):
        return None
    cnt = 0
    for x in range(-6, 7):
        for y in range(-6, 7):
            for z in range(-6, 7):
                if nvec[0]*x + nvec[1]*y + nvec[2]*z == 0:
                    cnt += 1
    return cnt
cells = []
for u1, u2 in combinations(us, 2):
    c = plane_cells(u1, u2)
    cells.append(c)
cells = np.array(cells)
print(f"\ncentral planes spanned by pair-pairs: {len(cells)}; grid cells on plane: "
      f"min {cells.min()}, median {np.median(cells)}, max {cells.max()}")
# baseline: random pairs of directions
rng = np.random.default_rng(0)
rc = []
allu = [(x, y, z) for x in range(-6, 7) for y in range(-6, 7) for z in range(-6, 7) if (x, y, z) != (0, 0, 0)]
for _ in range(153):
    i, j = rng.integers(0, len(allu), 2)
    c = plane_cells(allu[i], allu[j])
    if c:
        rc.append(c)
rc = np.array(rc)
print(f"random-direction baseline: min {rc.min()}, median {np.median(rc)}, max {rc.max()}")

# 3-points-per-line usage: max collinear count in 36-set
from math import gcd
def max_collinear(S):
    S = sorted(S)
    best = 0
    for i, p in enumerate(S):
        dirs = Counter()
        for q in S[i+1:]:
            d = tuple(q[k] - p[k] for k in range(3))
            g = gcd(gcd(abs(d[0]), abs(d[1])), abs(d[2]))
            dirs[tuple(c // g for c in d)] += 1
        if dirs:
            best = max(best, 1 + max(dirs.values()))
    return best
print("max collinear in 36-set:", max_collinear(S36))

# min |det| margin of 36-set and where the tightest 5-subsets sit
d = sl.all_dets(S36)
idx = sl.combos5(36)
tight = np.flatnonzero(np.abs(d) <= 4)
print(f"min|det|={np.abs(d).min()}, #5-subsets with |det|<=4: {len(tight)}")

# how many central planes contain exactly 4 set points (saturated) vs could a 5th pair fit
# (sanity: no central plane may contain 6 set points)
from collections import defaultdict
planes = Counter()
for u1, u2 in combinations(us, 2):
    nvec = (u1[1]*u2[2] - u1[2]*u2[1], u1[2]*u2[0] - u1[0]*u2[2], u1[0]*u2[1] - u1[1]*u2[0])
    g = gcd(gcd(abs(nvec[0]), abs(nvec[1])), abs(nvec[2]))
    nv = tuple(c // g for c in nvec)
    nv = max(nv, tuple(-c for c in nv))
    planes[nv] += 1
print("central-plane multiplicity (should be all 1 => 153 distinct):",
      dict(Counter(planes.values())))
