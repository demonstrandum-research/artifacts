#!/usr/bin/env python3
"""Census of all C(36,5)=376992 lifted dets of the record 36-set.

Questions:
 - is there a small prime p with NO det divisible by p (a 'one-prime certificate'
   that would signal an F_p-algebraic construction route)?
 - zero counts mod each prime p <= 97 vs generic expectation n5/p;
 - distribution of |det|: min, percentiles; gcd of all dets;
 - sign balance and smallest dets' 5-subset pair-types (how many full antipodal
   pairs the tightest 5-subsets contain).
"""
import json
import numpy as np
from itertools import combinations
from collections import Counter

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"
pts = sorted(tuple(p) for p in json.load(open(BASE + r"\certificates\record36_centralsym.json")))
P = np.array(pts, dtype=np.int64)
L = np.concatenate([P, (P*P).sum(1, keepdims=True)], axis=1)

c5 = np.array(list(combinations(range(36), 5)), dtype=np.int32)
P0 = L[c5[:, 0]]
A = L[c5[:, 1]] - P0; B = L[c5[:, 2]] - P0; C = L[c5[:, 3]] - P0; D = L[c5[:, 4]] - P0
a0,a1,a2,a3 = A[:,0],A[:,1],A[:,2],A[:,3]
b0,b1,b2,b3 = B[:,0],B[:,1],B[:,2],B[:,3]
c0,c1,c2,c3 = C[:,0],C[:,1],C[:,2],C[:,3]
d0,d1,d2,d3 = D[:,0],D[:,1],D[:,2],D[:,3]
det = ((a0*b1-a1*b0)*(c2*d3-c3*d2) - (a0*b2-a2*b0)*(c1*d3-c3*d1)
     + (a0*b3-a3*b0)*(c1*d2-c2*d1) + (a1*b2-a2*b1)*(c0*d3-c3*d0)
     - (a1*b3-a3*b1)*(c0*d2-c2*d0) + (a2*b3-a3*b2)*(c0*d1-c1*d0))

out = {"n5": len(det), "min_abs": int(np.abs(det).min()), "max_abs": int(np.abs(det).max())}
primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
modz = {}
for p in primes:
    z = int((det % p == 0).sum())
    modz[p] = {"zeros": z, "expected": round(len(det)/p, 1), "ratio": round(z/(len(det)/p), 3)}
out["zeros_mod_p"] = modz
out["any_prime_clean"] = [p for p in primes if modz[p]["zeros"] == 0]

g = np.gcd.reduce(det)
out["gcd_all_dets"] = int(abs(g))
out["sign_balance"] = {"pos": int((det > 0).sum()), "neg": int((det < 0).sum())}
ab = np.abs(det)
out["percentiles_abs"] = {q: int(np.percentile(ab, q)) for q in (1, 5, 25, 50, 75, 95, 99)}
out["n_abs_le_10"] = int((ab <= 10).sum())

# pair-type of the tightest 5-subsets
mirror = {i: pts.index(tuple(12 - v for v in pts[i])) for i in range(36)}
def pairtype(idx):
    s = set(int(v) for v in idx)
    return sum(1 for i in s if mirror[i] in s) // 2
order = np.argsort(ab)
tight = Counter(pairtype(c5[i]) for i in order[:200])
out["pairtype_of_200_tightest"] = dict(sorted(tight.items()))
allty = Counter(pairtype(c5[i]) for i in range(0, len(c5), 37))  # sample for baseline
out["pairtype_sample_baseline"] = dict(sorted(allty.items()))
# parity: dets even/odd
out["dets_even"] = int((det % 2 == 0).sum())

print(json.dumps(out, indent=1))
