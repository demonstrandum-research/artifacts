#!/usr/bin/env python3
"""V4_coord structured-template search (mining hypothesis H3), EVEN n.

Template: S is a union of orbits of the coordinate-rotation Klein group
  V4 = {id, Rx, Ry, Rz},  Rx(p) = (p_x, n-1-p_y, n-1-p_z), etc.
For even n the action is fixed-point-free, every orbit has size exactly 4,
all four points share the scaled shell sum_i (2 p_i - (n-1))^2, and in
centered doubled coordinates D = 2p - (n-1) every coordinate is odd, so the
orbit is never coplanar (det3 of the direction triple = -16 xyz != 0 in
suitable form) and never rank-degenerate.  One orbit exactly saturates its
shell (4 cospherical points about the center c); hence ALL orbits must
occupy pairwise distinct shells (a 5th point on an orbit's c-sphere is an
instant violation).  36 points = 9 orbits, 40 = 10 orbits.

Validity of S u O for a candidate orbit O = {o1..o4} over members M
(|M| = 4k), checked EXACTLY in int64 numpy:
  stage 1: shell(O) unused           (lossless: equal shells => 5-cospherical)
  stage 2: CF @ lift(o_i) != 0 for every member 4-subset cofactor vector CF
           (covers every 5-subset with exactly 1 new point, and any
            degenerate member quad blocks everything automatically)
  stage 3: det5({x,y,z,oi},oj) != 0 over member triples, all 6 new pairs
           (covers every 5-subset with exactly 2 new points)
           + zero-cofactor rejection of quads {x,y,oi,oj}
  stage 4: det5({x,y,oi,oj},ok) != 0 over member pairs, all 4 new triples
           (5-subsets with 3 new) + zero-cofactor rejection of {x,oi,oj,ok}
  stage 5: det5(O, x) != 0 for every member x (5-subsets with 4 new)
Together with induction on |S| this covers every 5-subset and every
rank-degenerate quadruple.  Final sets are re-verified externally by
code/check_cert.py (exact, independent).

Usage: python v4search.py n seconds [seed]
"""
import sys, json, time, random
import numpy as np
from itertools import combinations

def lift(P):
    P = np.asarray(P, np.int64)
    return np.concatenate([P, (P * P).sum(1, keepdims=True),
                           np.ones((len(P), 1), np.int64)], axis=1)

def det4_batch(R):
    """R: (t,4,4) int64 -> (t,) exact dets."""
    a, b, c, d = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
    return ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(c[:,2]*d[:,3]-c[:,3]*d[:,2])
          - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(c[:,1]*d[:,3]-c[:,3]*d[:,1])
          + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(c[:,1]*d[:,2]-c[:,2]*d[:,1])
          + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(c[:,0]*d[:,3]-c[:,3]*d[:,0])
          - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(c[:,0]*d[:,2]-c[:,2]*d[:,0])
          + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(c[:,0]*d[:,1]-c[:,1]*d[:,0]))

def det5_rows(rows5):
    """rows5: (t,5,5) lifted rows -> exact det via difference reduction."""
    R = rows5[:, 1:, :4] - rows5[:, :1, :4]
    return det4_batch(R)

def cofactors(L):
    """cofactor vectors of all 4-subsets of rows of L (k,5) -> (q,5)."""
    k = len(L)
    if k < 4:
        return np.zeros((0, 5), np.int64)
    idx = np.array(list(combinations(range(k), 4)), np.int32)
    Q = L[idx]
    cols = np.arange(5)
    out = np.zeros((len(idx), 5), np.int64)
    for j in range(5):
        out[:, j] = ((-1) ** j) * det4_batch(Q[:, :, cols != j])
    return out

def cof_quad_batch(rows4):
    """rows4: (t,4,5) -> (t,5) cofactor vectors (for zero-vector rejection)."""
    t = len(rows4)
    cols = np.arange(5)
    out = np.zeros((t, 5), np.int64)
    for j in range(5):
        out[:, j] = ((-1) ** j) * det4_batch(rows4[:, :, cols != j])
    return out

def run(n, budget, seed=1):
    assert n % 2 == 0
    rng = random.Random(seed)
    nm1 = n - 1

    def rx(p): return (p[0], nm1 - p[1], nm1 - p[2])
    def ry(p): return (nm1 - p[0], p[1], nm1 - p[2])
    def rz(p): return (nm1 - p[0], nm1 - p[1], p[2])

    seen = set()
    orbits = []   # list of 4-point tuples
    for x in range(n):
        for y in range(n):
            for z in range(n):
                p = (x, y, z)
                if p in seen:
                    continue
                orb = (p, rx(p), ry(p), rz(p))
                assert len(set(orb)) == 4
                seen.update(orb)
                orbits.append(orb)
    NO = len(orbits)
    OP = np.array(orbits, np.int64)                     # (NO,4,3)
    OL = np.zeros((NO, 4, 5), np.int64)
    for i in range(NO):
        OL[i] = lift(OP[i])
    D2 = 2 * OP[:, 0, :] - nm1
    SHELL = (D2 * D2).sum(1)                            # scaled shell, orbit-invariant
    # sanity: shell is constant on the orbit
    for i in (0, NO // 2, NO - 1):
        Dall = 2 * OP[i] - nm1
        nrm = (Dall * Dall).sum(1)
        assert int(nrm.max()) == int(nrm.min())

    pair_idx = list(combinations(range(4), 2))
    tri_idx = list(combinations(range(4), 3))

    def orbit_ok(Lmem, CF, ol):
        """exact validity of S u O; Lmem (m,5) members, ol (4,5) new lifted."""
        m = len(Lmem)
        # stage 2: one new point  (also blocks on degenerate member quads)
        if len(CF) and (CF @ ol.T == 0).any():
            return False
        # stage 5 + orbit quad itself
        oc = cof_quad_batch(ol[None])
        if (oc == 0).all():
            return False
        if m >= 1:
            rows = np.concatenate([np.broadcast_to(ol, (m, 4, 5)),
                                   Lmem[:, None, :]], axis=1)
            if (det5_rows(rows) == 0).any():
                return False
        # stage 3: two new points
        if m >= 2:
            pidx = np.array(list(combinations(range(m), 2)), np.int32)
            P2 = Lmem[pidx]                              # (q,2,5)
            for (i, j) in pair_idx:
                rows4 = np.concatenate([P2, np.broadcast_to(ol[i], (len(pidx), 1, 5)),
                                        np.broadcast_to(ol[j], (len(pidx), 1, 5))], axis=1)
                if (cof_quad_batch(rows4) == 0).all(axis=1).any():
                    return False
        if m >= 3:
            tidx = np.array(list(combinations(range(m), 3)), np.int32)
            T = Lmem[tidx]                               # (t,3,5)
            for (i, j) in pair_idx:
                rows = np.concatenate([T, np.broadcast_to(ol[i], (len(tidx), 1, 5)),
                                       np.broadcast_to(ol[j], (len(tidx), 1, 5))], axis=1)
                if (det5_rows(rows) == 0).any():
                    return False
        # stage 4: three new points
        if m >= 1:
            for (i, j, k) in tri_idx:
                rows4 = np.concatenate([Lmem[:, None, :],
                                        np.broadcast_to(ol[[i, j, k]], (m, 3, 5))], axis=1)
                if (cof_quad_batch(rows4) == 0).all(axis=1).any():
                    return False
        if m >= 2:
            pidx = np.array(list(combinations(range(m), 2)), np.int32)
            P2 = Lmem[pidx]
            for (i, j, k) in tri_idx:
                rows = np.concatenate([P2, np.broadcast_to(ol[[i, j, k]],
                                                           (len(pidx), 3, 5))], axis=1)
                if (det5_rows(rows) == 0).any():
                    return False
        return True

    def build(start, tabu=frozenset()):
        sel = list(start)
        used = set(int(SHELL[i]) for i in sel)
        Lmem = OL[sel].reshape(-1, 5) if sel else np.zeros((0, 5), np.int64)
        CF = cofactors(Lmem)
        order = [i for i in range(NO) if i not in sel and i not in tabu]
        rng.shuffle(order)
        for i in order:
            if int(SHELL[i]) in used:
                continue
            if orbit_ok(Lmem, CF, OL[i]):
                sel.append(i)
                used.add(int(SHELL[i]))
                Lmem = np.concatenate([Lmem, OL[i]], axis=0)
                CF = cofactors(Lmem)
        return sel

    t0 = time.time()
    cur = build([])
    best = list(cur)
    it = 0
    while time.time() - t0 < budget:
        it += 1
        r = rng.choice([1, 1, 1, 2])
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
            print(json.dumps({"t": round(time.time() - t0, 1), "iter": it,
                              "orbits": len(best), "points": 4 * len(best)}), flush=True)
        if it % 25 == 0:
            print(json.dumps({"t": round(time.time() - t0, 1), "iter": it,
                              "cur": len(cur), "best": len(best)}), flush=True)
    pts = sorted(tuple(int(v) for v in q) for i in best for q in OP[i])
    fn = (r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"
          r"\mining\construct-search\v4_best_n%d_s%d.json" % (n, seed))
    json.dump([list(p) for p in pts], open(fn, "w"))
    print(json.dumps({"final_orbits": len(best), "final_points": 4 * len(best),
                      "n": n, "file": fn}), flush=True)

if __name__ == "__main__":
    n = int(sys.argv[1]); budget = float(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    run(n, budget, seed)
