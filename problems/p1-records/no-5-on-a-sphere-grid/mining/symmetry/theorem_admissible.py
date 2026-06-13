#!/usr/bin/env python3
"""Which subgroups of B3 (acting about the center) can stabilize a LARGE valid set?

Geometric claims (verified exactly here over many integer points, plus the
clean synthetic arguments noted in comments):

 T1 (mirror): for any reflection m and any two points p,q with nondegenerate
    orbit-pairs, the quad {p,mp,q,mq} has lifted-diff rank <= 2 (two parallel
    chords => isosceles trapezoid => concyclic or collinear). Such a quad
    blocks EVERY fifth point => a valid set with >=5 points has at most one
    nondegenerate mirror pair => mirror-symmetric valid sets have <= 6 points
    (<=4 on the fixed plane + 1 pair).

 T2 (rot90): a size-4 orbit lies on a circle (centered on the axis) =>
    rank <= 2 => blocks everything => C4-rotation-symmetric valid sets <= 4.

 T3 (rot120): two size-3 orbits lie on two coaxial circles; any two coaxial
    circles in distinct parallel planes lie on a common sphere (solve
    r1^2+(h-h1)^2 = r2^2+(h-h2)^2 for the center height h) => 6 points on a
    sphere => all C(6,5) 5-subsets singular => C3-symmetric valid sets <= 6.

 T4 (S6): a single size-6 orbit = two antipodal triangles on coaxial circles
    of EQUAL radius at heights +-h => on a common central sphere => invalid;
    also <g> contains rot120 => bound 6 anyway.

 T5 (-I, rot180, S4 rotoreflection): NOT forced (generic orbits create no
    blocking quad and no singular 5-subset) — verified by exhibiting random
    valid unions.

 Consequence: for |S| >= 7, every non-identity stabilizer element is one of
 {-I} u {9 rot180} u {6 S4}. Enumerate all subgroups of B3 contained in that
 set: the maximal ones are computed below.
"""
import os, sys, random
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

rng = random.Random(20260612)

def lifted_diff_rank(quad):
    """Exact rank over Q of the 3 lifted diffs of a 4-point set."""
    L = [sl.lift(p) for p in quad]
    M = [[L[i][k] - L[0][k] for k in range(4)] for i in range(1, 4)]
    from fractions import Fraction
    A = [[Fraction(v) for v in r] for r in M]
    rank = 0
    for col in range(4):
        piv = next((r for r in range(rank, 3) if A[r][col] != 0), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        for r in range(3):
            if r != rank and A[r][col] != 0:
                f = A[r][col] / A[rank][col]
                A[r] = [A[r][c] - f * A[rank][c] for c in range(4)]
        rank += 1
    return rank

def orbit(g, p, n=13):
    o, q = [], tuple(p)
    while True:
        o.append(q)
        q = sl.apply_g(g, q, n)
        if q == o[0]:
            return sorted(set(o))

def rand_pt():
    return tuple(rng.randrange(13) for _ in range(3))

types = {}
for g in sl.B3:
    types.setdefault(sl.element_type(g), []).append(g)
print("element type census:", {k: len(v) for k, v in types.items()})

TRIALS = 400
report = {}

# T1: mirrors — two nondegenerate orbit-pairs always rank<=2
for t in ("mirror",):
    forced = 0; tested = 0
    for g in types[t]:
        for _ in range(TRIALS // len(types[t]) + 1):
            p, q = rand_pt(), rand_pt()
            op, oq = orbit(g, p), orbit(g, q)
            if len(op) != 2 or len(oq) != 2 or set(op) & set(oq):
                continue
            tested += 1
            if lifted_diff_rank(op + oq) <= 2:
                forced += 1
    report[t] = (forced, tested)
    print(f"T1 mirror: blocking quad in {forced}/{tested} random 2-pair unions (claim: all)")

# T2: rot90 — size-4 orbit always rank<=2
forced = tested = 0
for g in types["rot90"]:
    for _ in range(TRIALS // 6 + 1):
        o = orbit(g, rand_pt())
        if len(o) != 4:
            continue
        tested += 1
        if lifted_diff_rank(o) <= 2:
            forced += 1
print(f"T2 rot90: orbit-quad rank<=2 in {forced}/{tested} (claim: all)")
report["rot90"] = (forced, tested)

# T3: rot120 — two size-3 orbits => some singular 5-subset (in fact all)
forced = tested = 0
for g in types["rot120"]:
    for _ in range(TRIALS // 8 + 1):
        o1, o2 = orbit(g, rand_pt()), orbit(g, rand_pt())
        if len(o1) != 3 or len(o2) != 3 or set(o1) & set(o2):
            continue
        tested += 1
        if not sl.is_valid(o1 + o2):
            forced += 1
print(f"T3 rot120: union of two 3-orbits invalid in {forced}/{tested} (claim: all)")
report["rot120"] = (forced, tested)

# T4: S6 — single size-6 orbit invalid
forced = tested = 0
for g in types["S6"]:
    for _ in range(TRIALS // 8 + 1):
        o = orbit(g, rand_pt())
        if len(o) != 6:
            continue
        tested += 1
        if not sl.is_valid(o):
            forced += 1
print(f"T4 S6: size-6 orbit invalid in {forced}/{tested} (claim: all)")
report["S6"] = (forced, tested)

# T5: -I / rot180 / S4 NOT forced: find a valid union of 3 generic orbits
for t in ("-I", "rot180", "S4"):
    ok = 0; tried = 0
    for g in types[t]:
        for _ in range(40):
            pts = []
            for _ in range(3):
                o = orbit(g, rand_pt())
                pts += o
            if len(set(pts)) != len(pts):
                continue
            tried += 1
            if sl.is_valid(pts):
                ok += 1
    print(f"T5 {t}: valid 3-orbit unions exist: {ok}/{tried} random trials valid")
    report[t] = (ok, tried)

# ---- enumerate ALL subgroups of B3, flag admissible (elements only I/-I/rot180/S4)
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
    return frozenset(elems)

subgroups = {frozenset([sl.IDENT])}
for g1 in sl.B3:
    subgroups.add(closure([g1]))
for g1 in sl.B3:
    for g2 in sl.B3:
        subgroups.add(closure([g1, g2]))
# triples to be safe (B3 small; cap work)
sub_list = list(subgroups)
for H in sub_list:
    for g in sl.B3:
        subgroups.add(closure(list(H) + [g]))
print(f"\ntotal subgroups found: {len(subgroups)}")

ADM = {"I", "-I", "rot180", "S4"}
admissible = [H for H in subgroups if all(sl.element_type(g) in ADM for g in H)]
admissible.sort(key=len)
from collections import Counter
print("admissible subgroup order histogram:", Counter(len(H) for H in admissible))
maximal = [H for H in admissible
           if not any(H < K for K in admissible)]
print(f"maximal admissible subgroups: {len(maximal)}")
for H in sorted(maximal, key=lambda h: (len(h), sorted(map(str, h)))):
    desc = Counter(sl.element_type(g) for g in H)
    # name the axes involved
    print(f"  order {len(H)}: {dict(desc)} | elements: {sorted((sl.element_type(g), g) for g in H if g != sl.IDENT)}")

import json
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "admissible_groups.json"), "w") as f:
    json.dump({"forced_checks": report,
               "n_subgroups": len(subgroups),
               "admissible_orders": sorted(len(H) for H in admissible),
               "maximal": [[[list(g[0]), list(g[1])] for g in H] for H in maximal]}, f, indent=1)
print("written admissible_groups.json")
