#!/usr/bin/env python3
"""Central-inversion symmetric pair greedy + ILS for EVEN n (half-integral
center c = ((n-1)/2)^3; the map p -> (n-1)-p is still a grid involution with
NO fixed cell, so every orbit has size exactly 2 — arguably cleaner than odd n).
All pair laws (L1 distinct |2u|^2, L2/L3 general position) carry over verbatim
with doubled vectors d = 2p - (n-1)(1,1,1) (odd integer coords).

Usage: python even_n_sym.py n budget_seconds [seed]
Writes even_sym_best_n{n}.json + progress lines.
"""
import json, os, sys, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl

HERE = os.path.dirname(os.path.abspath(__file__))
n = int(sys.argv[1]) if len(sys.argv) > 1 else 14
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 240.0
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 1

c2 = n - 1  # 2*center
def mate(p):
    return (c2 - p[0], c2 - p[1], c2 - p[2])

# pair reps: p with p > mate(p) lexicographically
reps = [(x, y, z) for x in range(n) for y in range(n) for z in range(n)
        if (x, y, z) > (c2 - x, c2 - y, c2 - z)]
rng = random.Random(SEED)

def d2(p):
    return sum((2 * p[i] - c2) ** 2 for i in range(3))

def rebuild(keep, best_order_hint=None):
    S = []
    used = []
    norms = set()
    for p in keep:
        nm = d2(p)
        if nm in norms:
            continue
        pp = [p, mate(p)]
        if len(S) + 2 < 5 or sl.is_valid_with_new(S, pp):
            S += pp
            used.append(p)
            norms.add(nm)
    order = reps[:]
    rng.shuffle(order)
    for p in order:
        if p in used:
            continue
        nm = d2(p)
        if nm in norms:
            continue
        pp = [p, mate(p)]
        if len(S) + 2 < 5:
            if sl.is_valid(S + pp):
                S += pp; used.append(p); norms.add(nm)
        elif sl.is_valid_with_new(S, pp):
            S += pp; used.append(p); norms.add(nm)
    return S, used

t0 = time.time()
best, bestS = [], []
it = 0
while time.time() - t0 < BUDGET:
    it += 1
    if best and rng.random() < 0.7:
        keep = list(best)
        rng.shuffle(keep)
        keep = keep[:max(0, len(keep) - rng.randrange(1, 4))]
        S, used = rebuild(keep)
    else:
        S, used = rebuild([])
    if len(used) > len(best):
        best, bestS = used, S
        print(json.dumps({"t": round(time.time() - t0, 1), "iter": it,
                          "pairs": len(best), "points": len(bestS)}), flush=True)
assert sl.is_valid(bestS)
json.dump(sorted(bestS), open(os.path.join(HERE, f"even_sym_best_n{n}.json"), "w"))
print(json.dumps({"final_pairs": len(best), "final_points": len(bestS), "n": n,
                  "iters": it}))
