#!/usr/bin/env python3
"""Nested growth: embed a centrally-symmetric record set for grid n centered,
and add new antipodal pairs available in the larger grid n+2 (new shell ring).
Tests the hypothesis C(n+2) >= C(n) + 2k by pure augmentation (core untouched).

Stage 1: S36 (n=13) -> n=15. Stage 2: best n=15 -> n=17 (also tries the
algebraic team's sym_best_n15 as an alternative core if present).

All checks exact int64 (overflow bound: n=17 -> diffs<=16, lifted<=768,
|det| <= 24*16^3*768 < 2^37, int64-safe).

Usage: python nested_growth.py [budget_seconds_per_stage]
Writes nested_growth.json and nested_best_n{15,17}.json.
"""
import json, os, sys, time, random
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, "..", ".."))
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 240.0

def embed(S, dn=1):
    return [tuple(c + dn for c in p) for p in S]

def candidates(S, n):
    """All u (pair dirs, canonical sign) whose pair c+-u is disjoint from S."""
    c = (n - 1) // 2
    Sf = set(S)
    out = []
    for x in range(-c, c + 1):
        for y in range(-c, c + 1):
            for z in range(-c, c + 1):
                u = (x, y, z)
                if u <= (-x, -y, -z):
                    continue
                p = (c + x, c + y, c + z)
                q = (c - x, c - y, c - z)
                if p in Sf or q in Sf:
                    continue
                out.append(u)
    return out

def pair_pts(u, n):
    c = (n - 1) // 2
    return [tuple(c + u[i] for i in range(3)), tuple(c - u[i] for i in range(3))]

def grow(S0, n, budget, seed=0, label=""):
    rng = random.Random(seed)
    t0 = time.time()
    cands = candidates(S0, n)
    # singly-addable pairs (exact)
    oks = []
    for u in cands:
        if sl.is_valid_with_new(S0, pair_pts(u, n)):
            oks.append(u)
    print(f"[{label}] singly-addable pairs: {len(oks)} of {len(cands)} candidates "
          f"({time.time()-t0:.1f}s)", flush=True)

    # greedy + ruin-rebuild ILS over the addable candidates
    best = []
    def rebuild(seedlist):
        S = S0[:]
        added = []
        for u in seedlist:
            pp = pair_pts(u, n)
            if any(p in set(S) for p in pp):
                continue
            if sl.is_valid_with_new(S, pp):
                S = S + pp
                added.append(u)
        order = oks[:]
        rng.shuffle(order)
        for u in order:
            if u in added:
                continue
            pp = pair_pts(u, n)
            if any(p in set(S) for p in pp):
                continue
            if sl.is_valid_with_new(S, pp):
                S = S + pp
                added.append(u)
        return S, added

    cur_added = []
    while time.time() - t0 < budget:
        if best and rng.random() < 0.7:
            keep = list(best)
            rng.shuffle(keep)
            keep = keep[:max(0, len(keep) - rng.randrange(1, 3))]
            S, added = rebuild(keep)
        else:
            S, added = rebuild([])
        if len(added) > len(best):
            best = added
            print(f"[{label}] pairs added: {len(best)} -> size {len(S0) + 2*len(best)} "
                  f"({time.time()-t0:.1f}s)", flush=True)
    Sbest = S0[:]
    for u in best:
        Sbest += pair_pts(u, n)
    assert sl.is_valid(Sbest)
    # final single-point scan (odd augmentation)
    singles = []
    for x in range(n):
        for y in range(n):
            for z in range(n):
                p = (x, y, z)
                if p in set(Sbest):
                    continue
                if sl.is_valid_with_new(Sbest, [p]):
                    singles.append(p)
    return Sbest, best, oks, singles

out = {}

# ---------------- stage 1: 36-set (n=13) -> n=15
S36 = sl.load_json_set(os.path.join(BASE, "certificates", "record36_centralsym.json"))
S0 = embed(S36, 1)
S15, added15, oks15, singles15 = grow(S0, 15, BUDGET, seed=1, label="13->15")
print(f"13->15: +{len(added15)} pairs => {len(S15)} points; singles addable after: {len(singles15)}")
out["stage13to15"] = {"singly_addable_pairs": len(oks15), "pairs_added": len(added15),
                      "final_size": len(S15), "added_dirs": [list(u) for u in added15],
                      "singles_after": [list(p) for p in singles15]}
json.dump(sorted(S15), open(os.path.join(HERE, "nested_best_n15.json"), "w"))

# ---------------- stage 2: best n=15 -> n=17
alt = os.path.join(BASE, "mining", "algebraic", "sym_best_n15_s1.json")
cores = [("nested15", S15)]
if os.path.exists(alt):
    Salt = sl.load_json_set(alt)
    cores.append(("algebraic15", Salt))
best17 = None
for name, core in cores:
    S0 = embed(core, 1)
    S17, added17, oks17, singles17 = grow(S0, 17, BUDGET, seed=2, label=f"{name}->17")
    print(f"{name}->17: +{len(added17)} pairs => {len(S17)} points; singles: {len(singles17)}")
    out[f"stage_{name}_to17"] = {"core_size": len(core), "singly_addable_pairs": len(oks17),
                                 "pairs_added": len(added17), "final_size": len(S17),
                                 "singles_after": [list(p) for p in singles17]}
    if best17 is None or len(S17) > len(best17):
        best17 = S17
json.dump(sorted(best17), open(os.path.join(HERE, "nested_best_n17.json"), "w"))

json.dump(out, open(os.path.join(HERE, "nested_growth.json"), "w"), indent=1)
print("written nested_growth.json")
