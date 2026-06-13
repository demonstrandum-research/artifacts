#!/usr/bin/env python3
"""Deterministic formula family CONIC(p; k, c):

    d_t = centered lift of  c * t^k * (1, t, t^2)  mod p,   t in T subset F_p*,
    S(n) = { center +/- d_t },  n >= p odd (works embedded for n >= p).

For odd n = p this is "one lift per projective conic point, monomially rescaled".
Guarantees (proof-grade, all p, k, c, T):
  * directions are pairwise non-parallel and no 3 coplanar over Z
    (det3 = c^3 (t1 t2 t3)^k * Vandermonde(t1,t2,t3) != 0 mod p),
  so given distinct norms, ALL (2,2,1) 5-subsets are nonzero by the
  factorization lemma.  The (2,1,1,1)/(1^5) classes are exact-checked.

This script: for each (k, c) finds a large valid T by exhaustive-greedy +
pairwise-deepening (pool <= p-1 elements, ILS with many restarts), exactly.
Outputs the best (k, c, T) per n with verification.

Usage: python formula_family.py n [budget_per_config=6]
"""
import sys, os, json, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import set_idle_priority, SymPoolSearch, verify_and_save, OUT


def centered(v, p):
    v %= p
    return v - p if v > (p - 1) // 2 else v


def family_evecs(n, p, k, c):
    """candidate (t, e-vector) list; e = 2*lift for odd n (d-vector doubled).
    Only valid for odd n with (p-1)/2 <= (n-1)/2 i.e. p <= n."""
    m = (n - 1) // 2
    out = []
    for t in range(1, p):
        s = (c * pow(t, k, p)) % p
        d = (centered(s, p), centered(s * t, p), centered(s * t * t, p))
        if d == (0, 0, 0) or max(abs(x) for x in d) > m:
            continue
        e = tuple(2 * x for x in d)
        if e < tuple(-x for x in e):
            e = tuple(-x for x in e)
        out.append((t, e))
    return out


def main():
    set_idle_priority()
    n = int(sys.argv[1])
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 6.0
    assert n % 2 == 1
    primes = [p for p in (5, 7, 11, 13, 17) if p <= n]
    best_overall = None
    results = []
    for p in primes:
        for k in range(p - 1):
            for c in range(1, (p - 1) // 2 + 1):
                cand = family_evecs(n, p, k, c)
                # dedupe e-vectors (different t can give same +/- class)
                seen, evecs, ts = set(), [], []
                for t, e in cand:
                    if e in seen:
                        continue
                    seen.add(e); evecs.append(e); ts.append(t)
                if len(evecs) < 3:
                    continue
                S = SymPoolSearch(n, evecs, seed=1)
                sel, _ = S.ils(budget)
                # map back: S.E sorted; recover t per selected evec
                emap = {tuple(int(v) for v in S.E[i]): i for i in range(len(S.E))}
                tsel = sorted(ts[j] for j in range(len(evecs))
                              if emap[evecs[j]] in set(sel))
                pts = S.points(sel)
                rec = {"n": n, "p": p, "k": k, "c": c, "pairs": len(sel),
                       "points": len(pts), "T": tsel,
                       "pool": len(evecs)}
                results.append(rec)
                if best_overall is None or len(pts) > best_overall["points"]:
                    ok, info = verify_and_save(n, pts, f"formula_p{p}k{k}c{c}")
                    rec["verified"] = ok
                    rec["file"] = str(info)
                    best_overall = rec
                    print(json.dumps(rec), flush=True)
    results.sort(key=lambda r: -r["points"])
    json.dump({"n": n, "best": best_overall, "top20": results[:20]},
              open(os.path.join(OUT, f"formula_sweep_n{n}.json"), "w"), indent=1)
    print(json.dumps({"n": n, "BEST": best_overall}), flush=True)


if __name__ == "__main__":
    main()
