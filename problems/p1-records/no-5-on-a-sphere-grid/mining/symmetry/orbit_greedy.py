#!/usr/bin/env python3
"""Time-budgeted greedy+ILS over H-orbits, exact validity, for each admissible
symmetry group H. Measures the empirical max valid-set size per group at n=13
(and a generalization probe for <-I> at n=15).

Usage: python orbit_greedy.py [budget_seconds_per_group]
Writes orbit_greedy_results.json.
"""
import json, os, sys, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 90.0

RZ   = ((0, 1, 2), (-1, -1, 1))    # 180 about z-axis through center
RX   = ((0, 1, 2), (1, -1, -1))
RY   = ((0, 1, 2), (-1, 1, -1))
R110 = ((1, 0, 2), (1, 1, -1))     # 180 about (1,1,0) face diagonal
R1m10= ((1, 0, 2), (-1, -1, -1))
S4Z  = ((1, 0, 2), (1, -1, -1))    # rotoreflection about z (this is -R90z up to choice)

GROUPS = {
    "trivial":   [sl.IDENT],
    "C2_negI":   [sl.IDENT, sl.NEG_I],
    "C2_rot180z":[sl.IDENT, RZ],
    "C2_rot180_110": [sl.IDENT, R110],
    "V4_coord":  [sl.IDENT, RX, RY, RZ],
    "V4_mixed":  [sl.IDENT, RZ, R110, R1m10],
    "C4_S4z":    None,  # closure of S4Z computed below
}

def closure(gens):
    elems = {sl.IDENT}
    frontier = list(gens)
    while frontier:
        new = []
        for a in list(elems) + frontier:
            for b in frontier:
                c = sl.g_compose(a, b)
                if c not in elems:
                    elems.add(c)
                    new.append(c)
        frontier = new
    return sorted(elems)

GROUPS["C4_S4z"] = closure([S4Z])
assert len(GROUPS["C4_S4z"]) == 4, GROUPS["C4_S4z"]
# sanity: every element admissible
for name, H in GROUPS.items():
    for g in H:
        assert sl.element_type(g) in {"I", "-I", "rot180", "S4"}, (name, g, sl.element_type(g))

def orbits_of(H, n=13):
    seen, orbs = set(), []
    for x in range(n):
        for y in range(n):
            for z in range(n):
                p = (x, y, z)
                if p in seen:
                    continue
                o = sorted({sl.apply_g(g, p, n) for g in H})
                seen.update(o)
                orbs.append(o)
    return orbs

def shell4(p, n):
    c2 = n - 1
    return sum((2 * p[i] - c2) ** 2 for i in range(3))

def greedy_run(orbs, n, rng):
    """One randomized greedy pass. Central-sphere cap-4 prefilter + exact check."""
    order = list(range(len(orbs)))
    rng.shuffle(order)
    S = []
    shell_count = {}
    used = []
    for oi in order:
        o = orbs[oi]
        sh = shell4(o[0], n)
        if shell_count.get(sh, 0) + len(o) > 4:
            continue
        if len(S) + len(o) >= 5 and not sl.is_valid_with_new(S, o):
            continue
        if len(S) + len(o) < 5:
            # tiny sets: validate directly (duplicates etc.)
            if not sl.is_valid(S + o):
                continue
        S = S + o
        shell_count[sh] = shell_count.get(sh, 0) + len(o)
        used.append(oi)
    return S, used

def ils(name, H, n=13, budget=BUDGET, seed=0):
    rng = random.Random(hash((name, seed)) & 0xffffffff)
    orbs = orbits_of(H, n)
    t0 = time.time()
    bestS, best_used = [], []
    restarts = 0
    while time.time() - t0 < budget:
        if bestS and rng.random() < 0.7:
            # ruin & rebuild: drop a few orbits from the incumbent, re-greedy
            keep = list(best_used)
            rng.shuffle(keep)
            k = rng.randrange(1, max(2, len(keep) // 3))
            keep = keep[:-k]
            S = []
            shell_count = {}
            ok = True
            for oi in keep:
                o = orbs[oi]
                S = S + o
                sh = shell4(o[0], n)
                shell_count[sh] = shell_count.get(sh, 0) + len(o)
            order = list(range(len(orbs)))
            rng.shuffle(order)
            used = list(keep)
            for oi in order:
                if oi in used:
                    continue
                o = orbs[oi]
                sh = shell4(o[0], n)
                if shell_count.get(sh, 0) + len(o) > 4:
                    continue
                if len(S) + len(o) >= 5:
                    if not sl.is_valid_with_new(S, o):
                        continue
                elif not sl.is_valid(S + o):
                    continue
                S = S + o
                shell_count[sh] = shell_count.get(sh, 0) + len(o)
                used.append(oi)
        else:
            S, used = greedy_run(orbs, n, rng)
        restarts += 1
        if len(S) > len(bestS):
            bestS, best_used = S, used
    assert sl.is_valid(bestS)
    # double-check symmetry of result
    st = sl.stabilizer(bestS, n) if n == 13 else None
    return {"group": name, "n": n, "best_size": len(bestS), "n_orbits": len(orbs),
            "restarts": restarts,
            "stab_order_check": (len(st) if st is not None else None),
            "best_set": sorted(bestS)}

results = []
for name, H in GROUPS.items():
    r = ils(name, H, n=13, budget=BUDGET)
    print(f"n=13 {name:>14}: best {r['best_size']:>2}  (orbits {r['n_orbits']}, "
          f"restarts {r['restarts']}, stab order of best {r['stab_order_check']})", flush=True)
    results.append(r)

# generalization probe: central symmetry at n=15 (same budget)
r = ils("C2_negI", GROUPS["C2_negI"], n=15, budget=BUDGET, seed=1)
print(f"n=15 {'C2_negI':>14}: best {r['best_size']:>2}  (orbits {r['n_orbits']}, restarts {r['restarts']})", flush=True)
results.append(r)
r = ils("trivial", GROUPS["trivial"], n=15, budget=BUDGET, seed=1)
print(f"n=15 {'trivial':>14}: best {r['best_size']:>2}  (orbits {r['n_orbits']}, restarts {r['restarts']})", flush=True)
results.append(r)

with open(os.path.join(HERE, "orbit_greedy_results.json"), "w") as f:
    json.dump(results, f, indent=1)
print("written orbit_greedy_results.json")
