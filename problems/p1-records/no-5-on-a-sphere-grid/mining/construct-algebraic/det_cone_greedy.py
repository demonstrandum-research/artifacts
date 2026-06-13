#!/usr/bin/env python3
"""DETERMINISTIC construction CG(n; Q, p, order):

  pool  = { canonical e-vectors e in box(n) : Q(e) == 0 mod p }   (or 'full')
  order = canonical sort key (no randomness)
  selection = exact greedy: accept e iff full validity is preserved
              (incremental cofactor blocking + pair-internal det5, C1 norm filter)

Output: a valid centrally-symmetric set, reproducible from (n, Q, p, order) alone.

Usage: python det_cone_greedy.py [n ...]
"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import (set_idle_priority, make_pool, template_pred, SymPoolSearch,
                     verify_and_save, OUT)

ORDERS = {
    "desc_norm":      lambda e: (-(e[0]**2+e[1]**2+e[2]**2), e),
    "asc_norm":       lambda e: ((e[0]**2+e[1]**2+e[2]**2), e),
    "corner_first":   lambda e: (-(abs(e[0])+abs(e[1])+abs(e[2])), e),
    "lex":            lambda e: e,
    "odd_first_desc": lambda e: (0 if all(abs(v) % 2 for v in e) else 1,
                                 -(e[0]**2+e[1]**2+e[2]**2), e),
}

TEMPLATES = ["full", "ver7", "ver11", "ver13", "hyp7", "hyp11",
             "union_ver_hyp7", "union_ver_hyp11", "union_ver_hyp13",
             "union_ver_vera_verb7", "union_ver_vera_verb11",
             "union_ver_vera_verb13"]

def main():
    set_idle_priority()
    ns = [int(a) for a in sys.argv[1:]] or [11, 12, 13, 14, 15, 16, 17]
    results = {}
    for n in ns:
        results[n] = {}
        for tmpl in TEMPLATES:
            pool = make_pool(n, template_pred(tmpl))
            if len(pool) < 3:
                continue
            S = SymPoolSearch(n, pool, seed=0)
            evs = [tuple(int(v) for v in S.E[i]) for i in range(len(S.E))]
            best = None
            for oname, key in ORDERS.items():
                order = sorted(range(len(evs)), key=lambda i: key(evs[i]))
                sel = S.build([], order=order)
                pts = S.points(sel)
                ok, info = (True, None)
                if best is None or len(pts) > best["points"]:
                    ok, info = verify_and_save(n, pts, f"det_{tmpl}_{oname}")
                    best = {"order": oname, "points": len(pts), "verified": ok,
                            "file": str(info)}
                results[n][f"{tmpl}/{oname}"] = len(pts)
            results[n][f"{tmpl}/BEST"] = best
            print(json.dumps({"n": n, "template": tmpl, "best": best}), flush=True)
    json.dump(results, open(os.path.join(OUT, "det_cone_greedy_results.json"), "w"),
              indent=1, default=str)

if __name__ == "__main__":
    main()
