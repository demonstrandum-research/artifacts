#!/usr/bin/env python3
"""Deterministic symmetric greedy: how large a valid set does a parameter-free
ordering rule reach (no randomness, no search)?

Orderings over orbit representatives d (one per +/- pair):
  desc_norm / asc_norm : by |d|^2
  corner_first         : by -(|x|+|y|+|z|), then lex
  lex                  : lexicographic
  norm_mod13           : by (|d|^2 mod 13, |d|^2)
  odd_first            : all-odd-coordinate d first (parity heuristics), then desc norm
Greedy accepts a pair iff exact validity is preserved (same machinery as
general_n_sym_greedy: cofactor blocking + pair-internal det5s + C1 shell filter).
"""
import sys, json
import numpy as np
from itertools import combinations

sys.path.insert(0, r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid\mining\algebraic")

def run_n(n):
    m = (n - 1) // 2
    c = np.array([m, m, m], dtype=np.int64)
    ds = [(x, y, z) for x in range(-m, m+1) for y in range(-m, m+1)
          for z in range(-m, m+1) if (x, y, z) > (-x, -y, -z)]
    D = np.array(ds, np.int64)
    NORM = (D*D).sum(1)
    P1 = D + c; P2 = -D + c
    def liftrow(P):
        return np.concatenate([P, (P*P).sum(1, keepdims=True),
                               np.ones((len(P), 1), np.int64)], axis=1)
    L1, L2 = liftrow(P1), liftrow(P2)

    def cofactors(L):
        k = len(L)
        if k < 4:
            return np.zeros((0, 5), np.int64)
        idx = np.array(list(combinations(range(k), 4)), np.int32)
        Q = L[idx]
        cols = np.arange(5)
        out = np.zeros((len(idx), 5), np.int64)
        for j in range(5):
            s = Q[:, :, cols != j]
            a, b, cc, d = s[:,0], s[:,1], s[:,2], s[:,3]
            det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(cc[:,2]*d[:,3]-cc[:,3]*d[:,2])
                 - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(cc[:,1]*d[:,3]-cc[:,3]*d[:,1])
                 + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(cc[:,1]*d[:,2]-cc[:,2]*d[:,1])
                 + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(cc[:,0]*d[:,3]-cc[:,3]*d[:,0])
                 - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(cc[:,0]*d[:,2]-cc[:,2]*d[:,0])
                 + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(cc[:,0]*d[:,1]-cc[:,1]*d[:,0]))
            out[:, j] = ((-1)**j) * det
        return out

    def pair_ok(Lmem, l1, l2):
        k = len(Lmem)
        if k < 3:
            if k == 2:
                cf = cofactors(np.stack([Lmem[0], Lmem[1], l1, l2]))
                return bool((cf != 0).any())
            return True
        idx = np.array(list(combinations(range(k), 3)), np.int32)
        T = Lmem[idx]
        rows = np.concatenate([T, np.broadcast_to(l1, (len(idx),1,5)),
                               np.broadcast_to(l2, (len(idx),1,5))], axis=1)
        R = rows[:, 1:, :4] - rows[:, :1, :4]
        a, b, cc, d = R[:,0], R[:,1], R[:,2], R[:,3]
        det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(cc[:,2]*d[:,3]-cc[:,3]*d[:,2])
             - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(cc[:,1]*d[:,3]-cc[:,3]*d[:,1])
             + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(cc[:,1]*d[:,2]-cc[:,2]*d[:,1])
             + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(cc[:,0]*d[:,3]-cc[:,3]*d[:,0])
             - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(cc[:,0]*d[:,2]-cc[:,2]*d[:,0])
             + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(cc[:,0]*d[:,1]-cc[:,1]*d[:,0]))
        return not (det == 0).any()

    def greedy(order):
        used = set()
        Lmem = np.zeros((0, 5), np.int64)
        CF = np.zeros((0, 5), np.int64)
        sel = []
        for i in order:
            nv = int(NORM[i])
            if nv in used:
                continue
            l1, l2 = L1[i], L2[i]
            if len(CF) and ((CF @ l1 == 0).any() or (CF @ l2 == 0).any()):
                continue
            if not pair_ok(Lmem, l1, l2):
                continue
            sel.append(i); used.add(nv)
            Lmem = np.concatenate([Lmem, l1[None], l2[None]])
            CF = cofactors(Lmem)
        return sel

    nd = len(ds)
    orders = {
        "desc_norm": sorted(range(nd), key=lambda i: (-NORM[i], ds[i])),
        "asc_norm": sorted(range(nd), key=lambda i: (NORM[i], ds[i])),
        "corner_first": sorted(range(nd), key=lambda i: (-(abs(ds[i][0])+abs(ds[i][1])+abs(ds[i][2])), ds[i])),
        "lex": list(range(nd)),
        "norm_mod13": sorted(range(nd), key=lambda i: (NORM[i] % 13, NORM[i], ds[i])),
        "odd_first_desc": sorted(range(nd), key=lambda i: (0 if (ds[i][0]%2 and ds[i][1]%2 and ds[i][2]%2) else 1, -NORM[i], ds[i])),
    }
    res = {}
    for name, o in orders.items():
        sel = greedy(o)
        res[name] = {"pairs": len(sel), "points": 2*len(sel)}
    return res

if __name__ == "__main__":
    out = {}
    for n in (13, 15):
        out[str(n)] = run_n(n)
    print(json.dumps(out, indent=1))
