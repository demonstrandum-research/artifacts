#!/usr/bin/env python3
"""General-n centrally-symmetric pair greedy + light ILS (numpy, exact int64).

Construction algorithm 'SYM(n)' for odd n (center c = ((n-1)/2,)*3):
  pick antipodal pairs c +/- d, enforcing
    - C1: all pair-norms |d|^2 distinct (exact pruning; rectangle = 4-cocircular)
    - full exact validity via cofactor blocking (every 5-subset with 1 new point)
      and pair-internal dets (every 5-subset with both new points).
Greedy fill to saturation; ruin-and-rebuild ILS on pairs within a time budget.

Validity logic (complete):
  5-subsets of S u {p,q}:  all old -> valid by induction;
  exactly one new -> cofactor dot c_Q . (L(new),1) != 0 for all quads Q in S;
  both new -> det5({x,y,z,p,q}) != 0 for all triples in S (also catches
  degenerate quads {x,y,p,q} and {x,y,z,p} as soon as |S| >= 3).

Usage: python general_n_sym_greedy.py n seconds [seed]
Writes best set to sym_best_n{n}.json and prints progress JSON lines.
"""
import sys, json, time, random
import numpy as np
from itertools import combinations

def run(n, budget, seed=1):
    assert n % 2 == 1
    m = (n - 1) // 2
    c = np.array([m, m, m], dtype=np.int64)
    rng = random.Random(seed)

    # orbit representatives: d-vectors, one per +/- pair, excluding 0
    ds = []
    for x in range(-m, m + 1):
        for y in range(-m, m + 1):
            for z in range(-m, m + 1):
                if (x, y, z) > (-x, -y, -z):
                    ds.append((x, y, z))
    D = np.array(ds, dtype=np.int64)                      # (nd,3)
    NORM = (D * D).sum(axis=1)                            # |d|^2
    P1 = D + c                                            # point c+d
    P2 = -D + c                                           # point c-d
    L1 = np.concatenate([P1, (P1 * P1).sum(1, keepdims=True),
                         np.ones((len(D), 1), np.int64)], axis=1)  # (nd,5)
    L2 = np.concatenate([P2, (P2 * P2).sum(1, keepdims=True),
                         np.ones((len(D), 1), np.int64)], axis=1)

    def lift_pts(P):
        P = np.asarray(P, np.int64)
        return np.concatenate([P, (P * P).sum(1, keepdims=True),
                               np.ones((len(P), 1), np.int64)], axis=1)

    def cofactors(L):
        """cofactor vectors of all 4-subsets of rows of L (k,5) -> (C(k,4),5)"""
        k = len(L)
        if k < 4:
            return np.zeros((0, 5), np.int64)
        idx = np.array(list(combinations(range(k), 4)), np.int32)
        Q = L[idx]                                        # (q,4,5)
        cols = np.arange(5)
        out = np.zeros((len(idx), 5), np.int64)
        for j in range(5):
            sub = Q[:, :, cols != j]                      # (q,4,4)
            a, b, cc, d = sub[:, 0], sub[:, 1], sub[:, 2], sub[:, 3]
            det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(cc[:,2]*d[:,3]-cc[:,3]*d[:,2])
                 - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(cc[:,1]*d[:,3]-cc[:,3]*d[:,1])
                 + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(cc[:,1]*d[:,2]-cc[:,2]*d[:,1])
                 + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(cc[:,0]*d[:,3]-cc[:,3]*d[:,0])
                 - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(cc[:,0]*d[:,2]-cc[:,2]*d[:,0])
                 + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(cc[:,0]*d[:,1]-cc[:,1]*d[:,0]))
            out[:, j] = ((-1) ** j) * det
        return out

    def det5_pair_ok(Lmem, l1, l2):
        """all det5 over triples of members + both new points nonzero"""
        k = len(Lmem)
        if k < 3:
            if k == 2:
                # reject only a fully rank-degenerate quad (all 5 cofactors zero):
                # it would block every future point (zero cofactor vector).
                M = np.stack([Lmem[0], Lmem[1], l1, l2])
                cf = cofactors(M)
                return bool((cf != 0).any())
            return True
        idx = np.array(list(combinations(range(k), 3)), np.int32)
        T = Lmem[idx]                                     # (t,3,5)
        rows = np.concatenate([T, np.broadcast_to(l1, (len(idx), 1, 5)),
                               np.broadcast_to(l2, (len(idx), 1, 5))], axis=1)  # (t,5,5)
        # 5x5 det exactly: subtract row0, drop last col (ones), 4x4 det
        R = rows[:, 1:, :4] - rows[:, :1, :4]
        a, b, cc, d = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
        det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(cc[:,2]*d[:,3]-cc[:,3]*d[:,2])
             - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(cc[:,1]*d[:,3]-cc[:,3]*d[:,1])
             + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(cc[:,1]*d[:,2]-cc[:,2]*d[:,1])
             + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(cc[:,0]*d[:,3]-cc[:,3]*d[:,0])
             - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(cc[:,0]*d[:,2]-cc[:,2]*d[:,0])
             + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(cc[:,0]*d[:,1]-cc[:,1]*d[:,0]))
        return not (det == 0).any()

    def build(start_pairs, tabu=frozenset()):
        """greedy fill from given pair-index list; returns pair index list"""
        sel = list(start_pairs)
        used_norm = set(int(NORM[i]) for i in sel)
        pts = []
        for i in sel:
            pts.append(L1[i]); pts.append(L2[i])
        Lmem = np.array(pts, np.int64).reshape(-1, 5)
        CF = cofactors(Lmem)
        order = [i for i in range(len(D)) if i not in sel and i not in tabu]
        rng.shuffle(order)
        for i in order:
            if int(NORM[i]) in used_norm:
                continue
            l1, l2 = L1[i], L2[i]
            if len(CF):
                if (CF @ l1 == 0).any() or (CF @ l2 == 0).any():
                    continue
            if not det5_pair_ok(Lmem, l1, l2):
                continue
            # accept
            sel.append(i)
            used_norm.add(int(NORM[i]))
            Lmem = np.concatenate([Lmem, l1[None], l2[None]], axis=0)
            CF = cofactors(Lmem)   # full recompute (simple; fine at this scale)
        return sel

    t0 = time.time()
    best = []
    cur = build([])
    if len(cur) > len(best):
        best = list(cur)
    it = 0
    while time.time() - t0 < budget:
        it += 1
        r = rng.choice([1, 1, 2, 2, 3])
        if len(cur) <= r:
            cur = build([])
        else:
            removed = rng.sample(cur, r)
            keep = [i for i in cur if i not in removed]
            cand = build(keep, tabu=frozenset(removed))
            cand = build(cand)
            if len(cand) >= len(cur):
                cur = cand
        if len(cur) > len(best):
            best = list(cur)
            print(json.dumps({"t": round(time.time()-t0, 1), "iter": it,
                              "pairs": len(best), "points": 2*len(best)}), flush=True)
        if it % 50 == 0:
            print(json.dumps({"t": round(time.time()-t0, 1), "iter": it,
                              "cur_pairs": len(cur), "best_pairs": len(best)}), flush=True)
    pts = []
    for i in best:
        pts.append([int(v) for v in P1[i]])
        pts.append([int(v) for v in P2[i]])
    fn = rf"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid\mining\algebraic\sym_best_n{n}_s{seed}.json"
    json.dump(sorted(pts), open(fn, "w"))
    print(json.dumps({"final_pairs": len(best), "final_points": 2*len(best),
                      "n": n, "file": fn}), flush=True)

if __name__ == "__main__":
    n = int(sys.argv[1]); budget = float(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    run(n, budget, seed)
