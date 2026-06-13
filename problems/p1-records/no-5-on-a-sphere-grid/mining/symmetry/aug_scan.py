#!/usr/bin/env python3
"""Asymmetric augmentation scan: for a sample of fully-symmetric 34-sets from
the pool, find ALL addable single cells p (exact: S+p valid <=> every 4-subset
cofactor dot with L(p) is nonzero). For each addable p, also test S+p+antip(p)
(-> 36, 18 pairs) and exhaustive second-point addability of S+p (-> any 36).

Usage: python aug_scan.py [K_sample] [seed]
Writes aug_scan.json (+ aug_found_35/36 JSON certificate files if found).
"""
import json, os, sys, random
from collections import Counter
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, "..", ".."))
MR = os.path.join(BASE, "runs", "central-symmetric", "main-run")

K = int(sys.argv[1]) if len(sys.argv) > 1 else 300
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 7

def det4_batch(D):
    """(N,4,4) int64 -> (N,) exact dets (formula identical to symlib.det5_batch core)."""
    a0, a1, a2, a3 = D[:, 0, 0], D[:, 0, 1], D[:, 0, 2], D[:, 0, 3]
    b0, b1, b2, b3 = D[:, 1, 0], D[:, 1, 1], D[:, 1, 2], D[:, 1, 3]
    c0, c1, c2, c3 = D[:, 2, 0], D[:, 2, 1], D[:, 2, 2], D[:, 2, 3]
    d0, d1, d2, d3 = D[:, 3, 0], D[:, 3, 1], D[:, 3, 2], D[:, 3, 3]
    return ((a0*b1 - a1*b0) * (c2*d3 - c3*d2) - (a0*b2 - a2*b0) * (c1*d3 - c3*d1)
          + (a0*b3 - a3*b0) * (c1*d2 - c2*d1) + (a1*b2 - a2*b1) * (c0*d3 - c3*d0)
          - (a1*b3 - a3*b1) * (c0*d2 - c2*d0) + (a2*b3 - a3*b2) * (c0*d1 - c1*d0))

def lift5(P):
    P = np.asarray(P, np.int64)
    return np.concatenate([P, (P * P).sum(1, keepdims=True),
                           np.ones((len(P), 1), np.int64)], axis=1)

def cofactor_matrix(S):
    """(C(m,4),5) cofactor vectors: det5(quad + p) = C @ lift5(p)."""
    L = lift5(S)                                   # (m,5)
    m = len(S)
    idx = np.array(list(combinations(range(m), 4)), np.int64)
    Q = L[idx]                                     # (q,4,5)
    cols = []
    for j in range(5):
        keep = [k for k in range(5) if k != j]
        cols.append(((-1) ** j) * det4_batch(Q[:, :, keep]))
    # det5 = sum_j (-1)^{4+j} p_j M_j = sum_j (-1)^j M_j p_j
    return np.stack(cols, axis=1)                  # (q,5)

ALL = [(x, y, z) for x in range(13) for y in range(13) for z in range(13)]
ALL_L = lift5(ALL)                                 # (2197,5)

pool = sl.load_jsonl_sets(os.path.join(MR, "pool_34.jsonl"))
sym = [S for S in pool if len(sl.sym_core(S)) == len(S) and len(S) == 34]
rng = random.Random(SEED)
sample = rng.sample(range(len(sym)), min(K, len(sym)))

res = {"K": len(sample), "addable_hist": Counter(), "n_sets_extendable": 0,
       "found35": 0, "found36": 0, "center_addable": 0}
found35_sets, found36_sets = [], []

for si, i in enumerate(sample):
    S = sym[i]
    Sf = set(S)
    C = cofactor_matrix(S)                         # (46376,5)
    addable = []
    for lo in range(0, len(ALL), 256):
        chunk = ALL_L[lo:lo + 256]                 # (c,5)
        dots = C @ chunk.T                         # (46376,c) int64
        ok = ~(dots == 0).any(axis=0)
        for k in np.flatnonzero(ok):
            p = ALL[lo + k]
            if p not in Sf:
                addable.append(p)
    res["addable_hist"][len(addable)] += 1
    if addable:
        res["n_sets_extendable"] += 1
        for p in addable:
            S35 = S + [p]
            assert sl.is_valid(S35)
            res["found35"] += 1
            if len(found35_sets) < 20:
                found35_sets.append(sorted(S35))
            if p == (6, 6, 6):
                res["center_addable"] += 1
            q = tuple(12 - c for c in p)
            if q not in Sf and q != p and sl.is_valid_with_new(S35, [q]):
                res["found36"] += 1
                found36_sets.append(sorted(S35 + [q]))
            # exhaustive second point (any cell), only if first succeeded cheaply
        # full second-point scan for the first addable point only (cost control)
        p = addable[0]
        S35 = S + [p]
        C2 = cofactor_matrix(S35)
        for lo in range(0, len(ALL), 256):
            chunk = ALL_L[lo:lo + 256]
            dots = C2 @ chunk.T
            ok = ~(dots == 0).any(axis=0)
            for k in np.flatnonzero(ok):
                p2 = ALL[lo + k]
                if p2 not in Sf and p2 != p:
                    S36 = S35 + [p2]
                    if sl.is_valid(S36):
                        res["found36"] += 1
                        found36_sets.append(sorted(S36))
    if (si + 1) % 25 == 0:
        print(json.dumps({"done": si + 1, "extendable": res["n_sets_extendable"],
                          "f35": res["found35"], "f36": res["found36"]}), flush=True)

res["addable_hist"] = {str(k): v for k, v in sorted(res["addable_hist"].items())}
json.dump(res, open(os.path.join(HERE, "aug_scan.json"), "w"), indent=1)
if found35_sets:
    json.dump(found35_sets, open(os.path.join(HERE, "aug_found_35.json"), "w"))
if found36_sets:
    json.dump(found36_sets, open(os.path.join(HERE, "aug_found_36.json"), "w"))
print(json.dumps(res, indent=1))
print("written aug_scan.json")
