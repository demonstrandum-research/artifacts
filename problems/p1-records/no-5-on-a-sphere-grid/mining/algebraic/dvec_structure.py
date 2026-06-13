#!/usr/bin/env python3
"""d-vector algebra of the centrally symmetric 36-set.

Derivation (verified symbolically below by brute force over random integer instances):
For a centrally symmetric set S = {c +/- d_i}, translate to center 0. A 5-subset with
TWO full pairs {+-d_i, +-d_j} and one extra point e_k (= +-d_k) has lifted determinant
    det5 = +-4 * (N_i - N_j) * det3[d_i, d_j, d_k],   N = |d|^2.
Hence validity of any symmetric set with >= 3 pairs REQUIRES
  (C1) all pair-norms N_i distinct          (else 4 cocircular points block everything)
  (C2) every triple {d_i,d_j,d_k} linearly independent over Q
       (no 3 directions coplanar with the center).

This script:
 1. verifies the det5 factorization numerically on random data;
 2. checks C1, C2 on the record-36 d-vectors;
 3. reduces the 18 directions mod 13 -> PG(2,13): distinctness, collinear triples
    (an arc in PG(2,13) has <= 14 points, so >= 15 pairs FORCES mod-13 collinearity);
 4. checks even/odd monomial rank split explaining the 4 vanishing quartics;
 5. Sidon-type stats on the norm set; misc d-vector stats.
"""
import json, os, random
from itertools import combinations
from collections import Counter

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"

def det3(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))

def det5_lifted(points):
    """5x5 det with rows (x,y,z,|p|^2,1) via 4x4 differences."""
    L = [(x, y, z, x*x+y*y+z*z) for (x, y, z) in points]
    p = L[0]
    (a0,a1,a2,a3),(b0,b1,b2,b3),(c0,c1,c2,c3),(d0,d1,d2,d3) = \
        [tuple(L[i][k]-p[k] for k in range(4)) for i in range(1, 5)]
    return ((a0*b1-a1*b0)*(c2*d3-c3*d2) - (a0*b2-a2*b0)*(c1*d3-c3*d1)
          + (a0*b3-a3*b0)*(c1*d2-c2*d1) + (a1*b2-a2*b1)*(c0*d3-c3*d0)
          - (a1*b3-a3*b1)*(c0*d2-c2*d0) + (a2*b3-a3*b2)*(c0*d1-c1*d0))

out = {}

# ---- 1. verify factorization on random instances ----
random.seed(1)
ok = True
for trial in range(2000):
    di = tuple(random.randint(-9, 9) for _ in range(3))
    dj = tuple(random.randint(-9, 9) for _ in range(3))
    dk = tuple(random.randint(-9, 9) for _ in range(3))
    pts = [di, tuple(-v for v in di), dj, tuple(-v for v in dj), dk]
    if len(set(pts)) < 5:
        continue
    Ni = sum(v*v for v in di); Nj = sum(v*v for v in dj)
    lhs = det5_lifted(pts)
    rhs = 4 * (Nj - Ni) * det3(di, dj, dk)
    if abs(lhs) != abs(rhs):
        ok = False
        out["factorization_counterexample"] = {"di": di, "dj": dj, "dk": dk,
                                               "lhs": lhs, "rhs": rhs}
        break
out["factorization_2pair_verified_2000_random"] = ok

cert = json.load(open(os.path.join(BASE, "certificates", "record36_centralsym.json")))
pts = sorted(tuple(p) for p in cert)
S = set(pts)
ds = sorted(tuple(p[k]-6 for k in range(3)) for p in pts
            if p > tuple(12-p[k] for k in range(3)))
out["n_pairs"] = len(ds)

# ---- 2. C1 / C2 ----
norms = [d[0]**2+d[1]**2+d[2]**2 for d in ds]
out["C1_all_norms_distinct"] = len(set(norms)) == len(norms)
dep = [(i, j, k) for i, j, k in combinations(range(len(ds)), 3)
       if det3(ds[i], ds[j], ds[k]) == 0]
out["C2_dependent_triples_over_Q"] = len(dep)
par = [(i, j) for i, j in combinations(range(len(ds)), 2)
       if det3(ds[i], ds[j], (1, 0, 0)) == 0 and det3(ds[i], ds[j], (0, 1, 0)) == 0
       and det3(ds[i], ds[j], (0, 0, 1)) == 0]
out["parallel_direction_pairs"] = len(par)

# ---- 3. directions in PG(2,13) ----
P = 13
def proj_normalize(v, p):
    v = tuple(x % p for x in v)
    for x in v:
        if x % p:
            inv = pow(x, p-2, p)
            return tuple((inv*y) % p for y in v)
    return None
projs = [proj_normalize(d, P) for d in ds]
out["directions_distinct_mod13"] = len(set(projs)) == len(projs)
coll13 = [(i, j, k) for i, j, k in combinations(range(len(ds)), 3)
          if det3(ds[i], ds[j], ds[k]) % P == 0]
out["collinear_triples_mod13"] = len(coll13)
out["collinear_triples_mod13_expected_generic"] = round(len(list(combinations(range(18),3)))/13, 1)
out["arc_bound_note"] = "max arc in PG(2,13) = 14 < 18 pairs, so some mod-13 collinear triple is unavoidable"
# max sub-arc mod 13 (greedy from each start)
best = 0
idx = list(range(len(ds)))
for st in range(len(ds)):
    order = idx[st:] + idx[:st]
    sub = []
    for i in order:
        if all(det3(ds[i], ds[j], ds[k]) % P for j, k in combinations(sub, 2)):
            sub.append(i)
    best = max(best, len(sub))
out["greedy_max_subarc_directions_mod13"] = best

# ---- 4. even/odd rank split for quartics about the center ----
def monomials_deg(nvars, maxdeg):
    outm = []
    def rec(prefix, remaining, left):
        if remaining == 0:
            outm.append(tuple(prefix)); return
        for e in range(left + 1):
            rec(prefix + [e], remaining - 1, left - e)
    rec([], nvars, maxdeg)
    return outm

def rank_Q(rows):
    from math import gcd
    M = [list(r) for r in rows]
    m, n = len(M), len(M[0])
    rank, r = 0, 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(r+1, m):
            if M[i][c]:
                f1, f2 = M[r][c], M[i][c]
                M[i] = [f1*M[i][j] - f2*M[r][j] for j in range(n)]
                g = 0
                for v in M[i]:
                    g = gcd(g, v)
                if g > 1:
                    M[i] = [v//g for v in M[i]]
        r += 1; rank += 1
        if r == m:
            break
    return rank

monos = monomials_deg(3, 4)
even = [m for m in monos if sum(m) % 2 == 0]
odd = [m for m in monos if sum(m) % 2 == 1]
def evalm(point, ex):
    v = 1
    for xi, e in zip(point, ex):
        v *= xi**e
    return v
rows_even = [[evalm(d, m) for m in even] for d in ds]
rows_odd = [[evalm(d, m) for m in odd] for d in ds]
out["even_monomials_deg4"] = len(even)
out["odd_monomials_deg4"] = len(odd)
out["rank_even_on_18_dvecs"] = rank_Q(rows_even)
out["rank_odd_on_18_dvecs"] = rank_Q(rows_odd)
out["explains_deg4_deficiency"] = (rank_Q(rows_even) + rank_Q(rows_odd) == 31)

# ---- 5. norm-set arithmetic ----
out["norms"] = sorted(norms)
sums = Counter(norms[i]+norms[j] for i, j in combinations(range(len(norms)), 2))
diffs = Counter(abs(norms[i]-norms[j]) for i, j in combinations(range(len(norms)), 2))
out["norm_pair_sums_max_multiplicity"] = max(sums.values())
out["norm_pair_diffs_max_multiplicity"] = max(diffs.values())
out["norms_mod13"] = sorted(n % 13 for n in norms)
out["norms_mod8"] = sorted(n % 8 for n in norms)   # sums of 3 squares: norm != 4^a(8b+7)
out["dot_products_distinct"] = None
dots = Counter(sum(a*b for a, b in zip(ds[i], ds[j])) for i, j in combinations(range(len(ds)), 2))
out["dot_products_max_multiplicity"] = max(dots.values())
out["dot_products_n_values"] = len(dots)

# coordinate-sum structure of d-vectors
out["d_coord_sums"] = sorted(sum(d) for d in ds)
out["d_coord_sums_mod13"] = sorted(sum(d) % 13 for d in ds)

print(json.dumps(out, indent=1, default=str))
