#!/usr/bin/env python3
"""Symmetry analysis of the headline certificates (36-set, seven 35s, 34s).

Outputs JSON findings to certs_analysis.json and human-readable stdout.
"""
import json, os, sys
from collections import Counter
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

BASE = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
CERT = os.path.join(BASE, "certificates")

named = {
    "record36_centralsym": os.path.join(CERT, "record36_centralsym.json"),
    "record35_baseline": os.path.join(CERT, "record35_baseline.json"),
    **{f"record35_blockerrepair_{i}": os.path.join(CERT, f"record35_blockerrepair_{i}.json")
       for i in range(1, 7)},
    "candidate34_centralsym": os.path.join(CERT, "candidate34_central-symmetric.txt"),
    "candidate34_f13": os.path.join(CERT, "candidate34_finite-field-f13.txt"),
    "candidate34_baseline": os.path.join(CERT, "candidate34_baseline-ils.txt"),
}
# published 33 (n=12) for contrast, if present
rec_path = os.path.join(BASE, "data", "records.json")

out = {}
for name, path in named.items():
    if not os.path.exists(path):
        continue
    S = sl.load_json_set(path)
    res = {"size": len(S), "valid": sl.is_valid(S)}
    stab = sl.stabilizer(S)
    res["stab_order"] = len(stab)
    res["stab_types"] = sorted(sl.element_type(g) for g in stab)
    # near-symmetry: best overlap |g(S) ^ S| over non-identity g in B3 (about center)
    Sf = frozenset(S)
    near = []
    for g in sl.B3:
        if g == sl.IDENT:
            continue
        ov = len(sl.apply_g_set(g, Sf) & Sf)
        near.append((ov, sl.element_type(g)))
    near.sort(reverse=True)
    res["near_sym_top5"] = near[:5]
    # best inversion center over ALL centers (translation-relaxed central symmetry)
    inv = sl.inversion_scores(S)
    best_c = max(inv.items(), key=lambda kv: (kv[1], kv[0]))
    res["best_inversion"] = {"two_c": best_c[0], "sym_core_size": best_c[1]}
    # shells about the true center
    sh = sl.shells(S)
    res["shell_values_4r2"] = sorted(Counter(sh).items())
    res["distinct_shells"] = len(set(sh))
    # mod-13 structure: how many 5-subset dets are ==0 mod 13 (vs generic)
    d = sl.all_dets(S)
    res["n_5subsets"] = int(d.size)
    res["dets_zero_mod13"] = int((d % 13 == 0).sum())
    res["expected_generic_mod13"] = round(d.size / 13, 1)
    res["min_abs_det"] = int(np.abs(d).min())
    # parity classes (mod 2)
    res["parity_classes"] = sorted(Counter(tuple(c % 2 for c in p) for p in S).items())
    # layer profile per axis
    res["layers"] = [sorted(Counter(p[i] for p in S).values(), reverse=True) for i in range(3)]
    out[name] = res
    print(f"=== {name}: size={res['size']} valid={res['valid']} "
          f"stab={res['stab_order']}{res['stab_types']} "
          f"best_inv_core={res['best_inversion']['sym_core_size']}@{res['best_inversion']['two_c']} "
          f"shells={res['distinct_shells']} z13={res['dets_zero_mod13']}/{res['n_5subsets']} "
          f"(generic {res['expected_generic_mod13']})")
    print(f"    near-sym top5 (overlap,type): {res['near_sym_top5']}")

# ---- cross-relations among certs
sets = {k: frozenset(sl.load_json_set(p)) for k, p in named.items() if os.path.exists(p)}
S36 = sets["record36_centralsym"]
rel = {}
for name, S in sets.items():
    if name == "record36_centralsym":
        continue
    # raw intersection and best intersection over the 48 images of S
    best = max(len(sl.apply_g_set(g, S) & S36) for g in sl.B3)
    rel[name] = {"raw_overlap_with_36": len(S & S36), "best_overlap_with_36_over_B3": best}
out["overlap_with_36"] = rel
print("\n--- overlap with the 36-set (raw / best over B3):")
for k, v in rel.items():
    print(f"  {k}: {v['raw_overlap_with_36']} / {v['best_overlap_with_36_over_B3']}")

# pairwise equivalence among 35s
names35 = [k for k in sets if k.startswith("record35")]
eq = []
for a, b in combinations(names35, 2):
    Ca, Cb = sl.canonical_form(sets[a]), sl.canonical_form(sets[b])
    ov = max(len(sl.apply_g_set(g, sets[a]) & sets[b]) for g in sl.B3)
    eq.append({"pair": [a, b], "equivalent": Ca == Cb, "best_overlap": ov})
out["pairs35"] = eq
print("\n--- 35-vs-35 best overlaps:", [(e["pair"][0][-1] + e["pair"][1][-1], e["best_overlap"]) for e in eq])

# ---- detailed look at the 36-set's 18 antipodal pairs
S36l = sorted(S36)
reps = [p for p in S36l if tuple(12 - c for c in p) > p or tuple(12 - c for c in p) == p]
reps = [p for p in S36l if p < tuple(12 - c for c in p)]
pairs = [(p, tuple(12 - c for c in p)) for p in reps]
assert len(pairs) == 18 and all(q in S36 for _, q in pairs)
detail = []
for p, q in pairs:
    u = tuple(p[i] - 6 for i in range(3))
    detail.append({"rep": p, "u": u, "r2": sum(c * c for c in u),
                   "norm_mod13": sum(c * c for c in p) % 13})
detail.sort(key=lambda d: d["r2"])
out["pairs36"] = detail
print("\n--- 36-set antipodal pairs (centered reps, sorted by r^2):")
for d in detail:
    print(f"  u={d['u']}  r2={d['r2']}  |p|^2 mod13={d['norm_mod13']}")
r2s = [d["r2"] for d in detail]
print("r2 multiset:", sorted(r2s), "distinct:", len(set(r2s)))

# how many shells are available at all? (u in {-6..6}^3, r2 = sum of 3 squares <= 108)
avail = sorted({a*a + b*b + c*c for a in range(7) for b in range(7) for c in range(7)})
out["available_shells"] = {"count": len(avail), "max": max(avail)}
print(f"available shells r2 (n=13): {len(avail)} values, used {len(set(r2s))}")

# quadric / cubic / quartic fits through all 36 points, over Q (exact, via fractions)
from fractions import Fraction
def monomials(p, deg):
    x, y, z = p
    mons = []
    for i in range(deg + 1):
        for j in range(deg + 1 - i):
            for k in range(deg + 1 - i - j):
                mons.append(x**i * y**j * z**k)
    return mons

def kernel_dim_exact(pts, deg, mod=None):
    rows = [monomials(p, deg) for p in pts]
    ncols = len(rows[0])
    if mod is None:
        A = [[Fraction(v) for v in r] for r in rows]
    else:
        A = [[v % mod for v in r] for r in rows]
    # gaussian elimination
    rank, rpos = 0, 0
    nrows = len(A)
    for col in range(ncols):
        piv = None
        for r in range(rank, nrows):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        inv = (pow(A[rank][col], -1, mod) if mod else Fraction(1) / A[rank][col])
        A[rank] = [v * inv % mod if mod else v * inv for v in A[rank]]
        for r in range(nrows):
            if r != rank and A[r][col] != 0:
                f = A[r][col]
                A[r] = [(A[r][c] - f * A[rank][c]) % mod if mod else A[r][c] - f * A[rank][c]
                        for c in range(ncols)]
        rank += 1
    return ncols - rank

fits = {}
for deg in (2, 3, 4):
    cen = [tuple(c - 6 for c in p) for p in S36l]
    fits[f"deg{deg}_overQ_kernel"] = kernel_dim_exact(cen, deg)
    fits[f"deg{deg}_modF13_kernel"] = kernel_dim_exact([tuple(c % 13 for c in p) for p in S36l], deg, mod=13)
    nmon = len(monomials((1, 1, 1), deg))
    fits[f"deg{deg}_nmonomials"] = nmon
out["vanishing_polys_36"] = fits
print("\n--- polynomials vanishing on all 36 points:", fits)

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "certs_analysis.json"), "w") as f:
    json.dump(out, f, indent=1, default=str)
print("\nwritten certs_analysis.json")
