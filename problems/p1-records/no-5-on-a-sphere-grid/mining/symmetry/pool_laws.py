#!/usr/bin/env python3
"""Pair-level LAWS of centrally-symmetric valid sets, verified exactly on the
36-record and the full symmetric 34-pool, plus a sufficiency measurement.

Laws (proved synthetically, n-independent; verified here on data):
  L1 (distinct shells / rectangle law): pairs +-u, +-v with |u|^2=|v|^2 form a
     rectangle (they lie on the central plane span(u,v) AND the central sphere
     r^2=|u|^2, hence on a circle) -> 4 cocircular points block EVERY 5th point.
     So in any valid centrally-symmetric set with >=5 points, all pair-norms
     are DISTINCT: at most one antipodal pair per central shell.
  L2 (no parallel pairs): u || v would put 4 points on a central line.
  L3 (no 3 coplanar pair-dirs): det[u,v,w]=0 puts 6 points on a central plane.
  COROLLARY (orbit-inequivalence): every isometry of the cube preserves |u|^2,
     so by L1 no two pairs of a valid symmetric set can lie in the same orbit
     of the 48-element point group (or of O(3)): large symmetric sets are
     forced to be unions of pairwise-INEQUIVALENT C2-orbits, never unions of
     few orbits of a bigger group.

Sufficiency probe: how far are L1-L3 from the full no-5 condition? Sample
random m-pair configurations satisfying L1-L3 and exact-check full validity;
also greedy-with-laws-only then exact check.
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

out = {}

def u_reps(S, n=13):
    c2 = n - 1
    Sf = set(S)
    reps = []
    for p in Sf:
        q = tuple(c2 - c for c in p)
        if q in Sf and p < q:
            reps.append(tuple(2 * p[i] - c2 for i in range(3)))  # 2u to stay integral
    return reps

def law_check(us):
    """Return dict of violations of L1, L2, L3 for a list of (doubled) u-vectors."""
    v1 = v2 = v3 = 0
    norms = [sum(c * c for c in u) for u in us]
    v1 = len(norms) - len(set(norms))
    for (i, u), (j, v) in combinations(enumerate(us), 2):
        # parallel iff cross product zero
        cx = (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
        if cx == (0, 0, 0):
            v2 += 1
    for a, b, c in combinations(us, 3):
        det = (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
             + a[2]*(b[0]*c[1]-b[1]*c[0]))
        if det == 0:
            v3 += 1
    return {"L1_dup_norms": v1, "L2_parallel": v2, "L3_coplanar_triples": v3}

# ---------- verify on the 36-set
S36 = sl.load_json_set(os.path.join(BASE, "certificates", "record36_centralsym.json"))
u36 = u_reps(S36)
assert len(u36) == 18
r = law_check(u36)
print("36-set law violations:", r)
out["laws_36"] = r

# ---------- verify on full symmetric pool
pool = sl.load_jsonl_sets(os.path.join(MR, "pool_34.jsonl"))
viol = Counter()
nsym = 0
for S in pool:
    us = u_reps(S)
    if 2 * len(us) != len(S):
        continue
    nsym += 1
    r = law_check(us)
    for k, v in r.items():
        if v:
            viol[k] += 1
print(f"symmetric pool sets checked: {nsym}; sets violating any law: {dict(viol)}")
out["pool_checked"] = nsym
out["pool_violations"] = dict(viol)

# B3-orbit-inequivalence corollary on data: pairs of pairs equivalent under B3
equiv = 0
for S in pool[:500]:
    us = u_reps(S)
    if 2 * len(us) != len(S):
        continue
    canon = [min(tuple(sorted((abs(a), abs(b), abs(c)))) for _ in [0]) or None for (a, b, c) in us]
    # two u's are B3-equivalent iff sorted absolute coordinate multisets agree
    cs = [tuple(sorted(map(abs, u))) for u in us]
    equiv += len(cs) - len(set(cs))
print(f"B3-equivalent pair-direction collisions in first 500 pool sets: {equiv}")
out["pool_B3equiv_collisions_first500"] = equiv
cs36 = [tuple(sorted(map(abs, u))) for u in u36]
out["set36_B3equiv_collisions"] = len(cs36) - len(set(cs36))
print(f"36-set B3-equivalent pair collisions: {out['set36_B3equiv_collisions']}")

# ---------- sufficiency probe at n=13: random law-satisfying m-pair configs
def pairs_to_points(us, n=13):
    c = (n - 1) // 2
    pts = []
    for u in us:
        uu = tuple(v // 2 for v in u)
        pts.append(tuple(c + uu[i] for i in range(3)))
        pts.append(tuple(c - uu[i] for i in range(3)))
    return pts

rng = random.Random(20260612)
allu = [(2*x, 2*y, 2*z) for x in range(-6, 7) for y in range(-6, 7) for z in range(-6, 7)
        if (x, y, z) > (-x, -y, -z)]

def sample_lawful(m):
    """Rejection-sample m pair-dirs satisfying L1 (distinct norms) and L2; then
    check L3; retry until lawful."""
    while True:
        cand = rng.sample(allu, m)
        norms = [sum(c*c for c in u) for u in cand]
        if len(set(norms)) != m:
            continue
        r = law_check(cand)
        if r["L2_parallel"] == 0 and r["L3_coplanar_triples"] == 0:
            return cand

for m in (10, 13, 15, 17):
    trials = 120
    nvalid = 0
    viol_counts = []
    for _ in range(trials):
        us = sample_lawful(m)
        pts = pairs_to_points(us)
        d = sl.all_dets(pts)
        nz = int((d == 0).sum())
        if nz == 0:
            nvalid += 1
        viol_counts.append(nz)
    vc = np.array(viol_counts)
    print(f"m={m}: lawful-random configs fully valid {nvalid}/{trials}; "
          f"violating 5-subsets per config: median {np.median(vc)}, mean {vc.mean():.1f}, max {vc.max()}")
    out[f"lawful_random_m{m}"] = {"trials": trials, "valid": nvalid,
                                  "viol_median": float(np.median(vc)), "viol_mean": float(vc.mean())}

# ---------- greedy with laws-only vs greedy with full check (5 seeds each)
def greedy(mode, seed):
    r = random.Random(seed)
    order = allu[:]
    r.shuffle(order)
    chosen = []
    norms = set()
    pts = []
    for u in order:
        nu = sum(c*c for c in u)
        if nu in norms:
            continue
        ok = True
        for v in chosen:
            cx = (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
            if cx == (0, 0, 0):
                ok = False; break
        if not ok:
            continue
        for v, w in combinations(chosen, 2):
            det = (u[0]*(v[1]*w[2]-v[2]*w[1]) - u[1]*(v[0]*w[2]-v[2]*w[0])
                 + u[2]*(v[0]*w[1]-v[1]*w[0]))
            if det == 0:
                ok = False; break
        if not ok:
            continue
        if mode == "full":
            new = pairs_to_points([u])
            if len(pts) + 2 >= 5 and not sl.is_valid_with_new(pts, new):
                continue
            pts = pts + new
        chosen.append(u)
        norms.add(nu)
    if mode == "laws":
        pts = pairs_to_points(chosen)
        d = sl.all_dets(pts)
        return len(chosen), int((d == 0).sum())
    return len(chosen), 0

for mode in ("laws", "full"):
    res = [greedy(mode, s) for s in range(5)]
    print(f"greedy[{mode}]: (pairs, violating-5-subsets) per seed: {res}")
    out[f"greedy_{mode}"] = res

json.dump(out, open(os.path.join(HERE, "pool_laws.json"), "w"), indent=1)
print("written pool_laws.json")
