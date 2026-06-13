#!/usr/bin/env python3
"""Hybrid: freeze the best cone-template core, complete over the FULL e-vector
pool (many greedy orders + core-preserving ILS).  Measures how far an explicit
algebraic core can be pushed by generic completion.

Usage: python hybrid_complete.py res_file budget [seed]
"""
import sys, os, json, time, random
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import (set_idle_priority, evec_box, SymPoolSearch,
                     verify_and_save, OUT)

def main():
    set_idle_priority()
    res = json.load(open(sys.argv[1]))
    budget = float(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    n = res["n"]
    core = [tuple(e) for e in res["evecs"]]
    pool = evec_box(n)
    S = SymPoolSearch(n, pool, seed=seed)
    emap = {tuple(int(v) for v in S.E[i]): i for i in range(len(S.E))}
    core_idx = [emap[e] for e in core]
    t0 = time.time()
    cur = S.build(core_idx)
    best = list(cur)
    it = 0
    while time.time() - t0 < budget:
        it += 1
        non_core = [i for i in cur if i not in core_idx]
        r = S.rng.choice([1, 1, 2, 2, 3])
        if len(non_core) <= r:
            cur = S.build(core_idx)
        else:
            removed = S.rng.sample(non_core, r)
            keep = [i for i in cur if i not in removed]
            cand = S.build(keep, tabu=frozenset(removed))
            cand = S.build(cand)
            if len(cand) >= len(cur):
                cur = cand
        if len(cur) > len(best):
            best = list(cur)
    pts = S.points(best)
    ok, info = verify_and_save(n, pts, f"hybrid_{res['template']}")
    print(json.dumps({"n": n, "template": res["template"], "core_pairs": len(core),
                      "total_pairs": len(best), "points": len(pts),
                      "verified": ok, "iters": it, "file": str(info)}))

if __name__ == "__main__":
    main()
