#!/usr/bin/env python3
"""Worker: run one (n, template, budget, seed) combo; write result JSON.

Usage: python run_template.py n template budget seed
Writes res_{template}_n{n}_s{seed}.json and (if valid) the best point set.
"""
import sys, os, json, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import (set_idle_priority, make_pool, template_pred, SymPoolSearch,
                     verify_and_save, OUT)

def main():
    set_idle_priority()
    n = int(sys.argv[1]); template = sys.argv[2]
    budget = float(sys.argv[3]); seed = int(sys.argv[4])
    pred = template_pred(template)
    pool = make_pool(n, pred)
    res = {"n": n, "template": template, "seed": seed, "budget": budget,
           "pool_size": len(pool)}
    if len(pool) < 3:
        res["pairs"] = 0
    else:
        t0 = time.time()
        S = SymPoolSearch(n, pool, seed=seed)
        best, iters = S.ils(budget)
        pts = S.points(best)
        ok, info = verify_and_save(n, pts, f"set_{template}")
        res.update({"pairs": len(best), "points": len(pts), "iters": iters,
                    "elapsed": round(time.time() - t0, 1),
                    "verified": ok, "file_or_reason": str(info),
                    "evecs": [[int(v) for v in S.E[i]] for i in sorted(best)]})
        # structure stats: distinct projective directions mod p (if template has p)
        digits = "".join(c for c in template if c.isdigit())
        if digits:
            p = int(digits)
            def projn(e):
                e = tuple(int(v) % p for v in e)
                for v in e:
                    if v % p:
                        inv = pow(v, p - 2, p)
                        return tuple((inv * w) % p for w in e)
                return ("zero",)
            projs = set(projn(S.E[i]) for i in best)
            res["p"] = p
            res["distinct_proj_dirs_mod_p"] = len(projs)
    fn = os.path.join(OUT, f"res_{template}_n{n}_s{seed}.json")
    json.dump(res, open(fn, "w"), indent=1)
    print(json.dumps({k: res.get(k) for k in
                      ("n", "template", "pool_size", "pairs", "points",
                       "verified", "distinct_proj_dirs_mod_p", "iters")}))

if __name__ == "__main__":
    main()
