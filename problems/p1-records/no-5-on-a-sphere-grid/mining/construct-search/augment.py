#!/usr/bin/env python3
"""Greedy asymmetric point-augmentation of a valid set inside a (possibly
larger) cube {0..n-1}^3, over all translation offsets that keep it in-grid.

Exact int64 numpy. A cell p is addable to valid S iff det5(Q,p) != 0 for
every 4-subset Q of S, i.e. all cofactor dot products nonzero (a valid set
with >= 5 points has no rank-degenerate quads, so no zero-cofactor trap).
After each accepted point, cofactors are recomputed and the scan repeats
until saturation.  Every output is re-verified by code/check_cert.py logic.

Usage: python augment.py points.json n_target [maxsets]
  (points.json may be a single JSON list of points, or a .jsonl pool)
"""
import sys, json, os, importlib.util
import numpy as np
from itertools import combinations

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"
spec = importlib.util.spec_from_file_location("check_cert", os.path.join(BASE, "code", "check_cert.py"))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)

def det4_batch(R):
    a, b, c, d = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
    return ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(c[:,2]*d[:,3]-c[:,3]*d[:,2])
          - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(c[:,1]*d[:,3]-c[:,3]*d[:,1])
          + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(c[:,1]*d[:,2]-c[:,2]*d[:,1])
          + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(c[:,0]*d[:,3]-c[:,3]*d[:,0])
          - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(c[:,0]*d[:,2]-c[:,2]*d[:,0])
          + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(c[:,0]*d[:,1]-c[:,1]*d[:,0]))

def lift(P):
    P = np.asarray(P, np.int64)
    return np.concatenate([P, (P * P).sum(1, keepdims=True),
                           np.ones((len(P), 1), np.int64)], axis=1)

def cofactors(L):
    k = len(L)
    idx = np.array(list(combinations(range(k), 4)), np.int32)
    Q = L[idx]
    cols = np.arange(5)
    out = np.zeros((len(idx), 5), np.int64)
    for j in range(5):
        out[:, j] = ((-1) ** j) * det4_batch(Q[:, :, cols != j])
    return out

def saturate(pts, n, CL):
    """greedy add addable cells until none; returns (pts, n_added)."""
    pts = [tuple(p) for p in pts]
    added = 0
    while True:
        L = lift(pts)
        CF = cofactors(L)
        dots = CF @ CL.T                       # (quads, cells)
        ok = ~(dots == 0).any(axis=0)
        occ = set(pts)
        cand = [i for i in np.nonzero(ok)[0] if tuple(CL[i, :3]) not in occ]
        if not cand:
            return pts, added
        # prefer the cell blocking fewest future... simple: first candidate
        pts.append(tuple(int(v) for v in CL[cand[0], :3]))
        added += 1

def main():
    src, n = sys.argv[1], int(sys.argv[2])
    maxsets = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
    raw = open(src).read().strip()
    sets = ([json.loads(l) for l in raw.splitlines() if l.strip()]
            if src.endswith(".jsonl") else [json.loads(raw)])
    sets = sets[:maxsets]
    cells = [(x, y, z) for x in range(n) for y in range(n) for z in range(n)]
    CL = lift(cells)
    best = None
    for si, pts in enumerate(sets):
        pts = [tuple(p) for p in pts]
        lo = [min(p[i] for p in pts) for i in range(3)]
        hi = [max(p[i] for p in pts) for i in range(3)]
        offs = [(a, b, c)
                for a in range(-lo[0], n - hi[0])
                for b in range(-lo[1], n - hi[1])
                for c in range(-lo[2], n - hi[2])]
        for off in offs:
            t = [(p[0] + off[0], p[1] + off[1], p[2] + off[2]) for p in pts]
            out, added = saturate(t, n, CL)
            if added > 0:
                ok, why = cc.check([list(p) for p in out], n)
                tag = "VALID" if ok else f"INVALID {why}"
                print(json.dumps({"set": si, "off": off, "m0": len(pts),
                                  "m": len(out), "check": tag}), flush=True)
                assert ok
                if best is None or len(out) > best[0]:
                    best = (len(out), out)
        if si % 20 == 0:
            print(json.dumps({"progress": si, "of": len(sets),
                              "best": best[0] if best else None}), flush=True)
    if best:
        fn = os.path.join(BASE, "mining", "construct-search",
                          f"aug_n{n}_m{best[0]}.json")
        json.dump(sorted(map(list, best[1])), open(fn, "w"))
        print(f"BEST m={best[0]} -> {fn}")
    else:
        print("no augmentation found anywhere")

if __name__ == "__main__":
    main()
