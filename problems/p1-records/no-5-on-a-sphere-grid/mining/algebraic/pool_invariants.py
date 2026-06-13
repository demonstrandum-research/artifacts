#!/usr/bin/env python3
"""Invariant mining across ALL large valid sets vs random-greedy valid sets.

Sources:
  - 4126 centrally-symmetric 34-sets   (runs/central-symmetric/main-run/pool_34.jsonl)
  - asymmetric 33/34/35s               (runs/baseline-ils/main/found_sets_*.jsonl)
  - record 36 + seven 35s              (certificates/)
  - baseline: random greedy valid sets (generated here, exact integer checks)

Cheap invariants for every set; expensive (mod-13 det census) for a sample.
Outputs JSON. numpy int64 exact (dets bounded << 2^63).
"""
import json, os, glob, random
import numpy as np
from itertools import combinations
from collections import Counter
from math import comb

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"
rng = random.Random(20260612)

def lift_np(P):
    P = np.asarray(P, dtype=np.int64)
    w = (P * P).sum(axis=1, keepdims=True)
    return np.concatenate([P, w], axis=1)

def det4_rows(A, B, C, D):
    """vectorized 4x4 dets, rows A,B,C,D shape (m,4)"""
    a0,a1,a2,a3 = A[:,0],A[:,1],A[:,2],A[:,3]
    b0,b1,b2,b3 = B[:,0],B[:,1],B[:,2],B[:,3]
    c0,c1,c2,c3 = C[:,0],C[:,1],C[:,2],C[:,3]
    d0,d1,d2,d3 = D[:,0],D[:,1],D[:,2],D[:,3]
    return ((a0*b1-a1*b0)*(c2*d3-c3*d2) - (a0*b2-a2*b0)*(c1*d3-c3*d1)
          + (a0*b3-a3*b0)*(c1*d2-c2*d1) + (a1*b2-a2*b1)*(c0*d3-c3*d0)
          - (a1*b3-a3*b1)*(c0*d2-c2*d0) + (a2*b3-a3*b2)*(c0*d1-c1*d0))

def det3_rows(A, B, C):
    a0,a1,a2 = A[:,0],A[:,1],A[:,2]
    b0,b1,b2 = B[:,0],B[:,1],B[:,2]
    c0,c1,c2 = C[:,0],C[:,1],C[:,2]
    return a0*(b1*c2-b2*c1) - a1*(b0*c2-b2*c0) + a2*(b0*c1-b1*c0)

COMB_CACHE = {}
def combs(m, k):
    key = (m, k)
    if key not in COMB_CACHE:
        COMB_CACHE[key] = np.array(list(combinations(range(m), k)), dtype=np.int32)
    return COMB_CACHE[key]

def cheap_invariants(pts):
    m = len(pts)
    P = np.array(sorted(pts), dtype=np.int64)
    inv = {"m": m}
    Sset = set(map(tuple, P.tolist()))
    pairs = sum(1 for p in Sset if tuple(12-v for v in p) in Sset and p < tuple(12-v for v in p))
    inv["sym_pairs_666"] = pairs
    for i, ax in enumerate("xyz"):
        cnt = Counter(int(v) for v in P[:, i])
        prof = sorted(cnt.values(), reverse=True)
        inv[f"prof_{ax}"] = prof
    inv["max_layer"] = max(max(inv[f"prof_{ax}"]) for ax in "xyz")
    inv["n4_layers"] = sum(inv[f"prof_{ax}"].count(4) for ax in "xyz")
    inv["empty_layers"] = sum(13 - len(inv[f"prof_{ax}"]) for ax in "xyz")
    inv["surface"] = int(np.any((P == 0) | (P == 12), axis=1).sum())
    par = Counter(tuple(int(v) % 2 for v in row) for row in P)
    inv["parity_sorted"] = sorted(par.values(), reverse=True)
    inv["parity_classes_used"] = len(par)
    # collinear triples & coplanar quadruples
    c3 = combs(m, 3)
    A = P[c3[:,0]]; B = P[c3[:,1]]; C = P[c3[:,2]]
    cross_zero = (det3_rows(B-A, C-A, np.ones_like(A)) * 0)  # placeholder not used
    u = B - A; v = C - A
    cr = np.stack([u[:,1]*v[:,2]-u[:,2]*v[:,1], u[:,2]*v[:,0]-u[:,0]*v[:,2],
                   u[:,0]*v[:,1]-u[:,1]*v[:,0]], axis=1)
    inv["collinear_triples"] = int((np.abs(cr).sum(axis=1) == 0).sum())
    c4 = combs(m, 4)
    A = P[c4[:,0]]; B = P[c4[:,1]]; C = P[c4[:,2]]; D = P[c4[:,3]]
    d3 = det3_rows(B-A, C-A, D-A)
    inv["coplanar_quads"] = int((d3 == 0).sum())
    inv["coplanar_per_1k_quads"] = round(1000.0 * inv["coplanar_quads"] / len(c4), 2)
    return inv

def mod13_census(pts):
    m = len(pts)
    L = lift_np(np.array(sorted(pts), dtype=np.int64))
    c5 = combs(m, 5)
    z13 = 0; n5 = len(c5)
    # batch to limit memory
    B = 400000
    minabs = None
    for s in range(0, n5, B):
        cc = c5[s:s+B]
        P0 = L[cc[:,0]]
        d = det4_rows(L[cc[:,1]]-P0, L[cc[:,2]]-P0, L[cc[:,3]]-P0, L[cc[:,4]]-P0)
        z13 += int((d % 13 == 0).sum())
        mn = int(np.abs(d).min())
        minabs = mn if minabs is None else min(minabs, mn)
    return {"n5": n5, "zero_mod13": z13, "ratio_vs_generic": round(z13/(n5/13.0), 3),
            "min_abs_det": minabs}

# ---------- random greedy valid set generator (exact) ----------
GRID = np.array([(x, y, z) for x in range(13) for y in range(13) for z in range(13)],
                dtype=np.int64)

def greedy_random():
    order = list(range(len(GRID)))
    rng.shuffle(order)
    S = []
    L = []
    for gi in order:
        p = GRID[gi]
        lp = (int(p[0]), int(p[1]), int(p[2]), int(p[0])**2+int(p[1])**2+int(p[2])**2)
        m = len(S)
        if m >= 4:
            Larr = np.array(L, dtype=np.int64)
            lparr = np.array(lp, dtype=np.int64)
            c4 = combs(m, 4)
            A = Larr[c4[:,0]]-lparr; B = Larr[c4[:,1]]-lparr
            C = Larr[c4[:,2]]-lparr; D = Larr[c4[:,3]]-lparr
            d = det4_rows(A, B, C, D)
            if (d == 0).any():
                continue
        elif m == 4:
            pass
        S.append((int(p[0]), int(p[1]), int(p[2])))
        L.append(lp)
    return S

def main():
    out = {}
    # ---- load pools ----
    pool34 = []
    with open(os.path.join(BASE, "runs", "central-symmetric", "main-run", "pool_34.jsonl")) as f:
        for line in f:
            line = line.strip()
            if line:
                pool34.append([tuple(p) for p in json.loads(line)])
    out["n_pool34"] = len(pool34)

    ils = []
    for fn in glob.glob(os.path.join(BASE, "runs", "baseline-ils", "main", "found_sets_*.jsonl")):
        with open(fn) as f:
            for line in f:
                line = line.strip()
                if line:
                    rec = json.loads(line)
                    ptsl = rec["points"] if isinstance(rec, dict) and "points" in rec else rec
                    ils.append([tuple(p) for p in ptsl])
    out["n_ils_sets"] = len(ils)
    out["ils_sizes"] = dict(Counter(len(s) for s in ils))

    cert36 = [tuple(p) for p in json.load(open(os.path.join(BASE, "certificates", "record36_centralsym.json")))]

    # ---- cheap invariants over full symmetric pool ----
    aggr = {"max_layer": Counter(), "n4_layers": Counter(), "empty_layers": Counter(),
            "surface": Counter(), "parity_classes_used": Counter(),
            "collinear_triples": Counter(), "coplanar_quads": []}
    dvec_freq = Counter()
    norm_freq = Counter()
    normset_hash = Counter()
    for ptsl in pool34:
        inv = cheap_invariants(ptsl)
        for k in ("max_layer", "n4_layers", "empty_layers", "surface",
                  "parity_classes_used", "collinear_triples"):
            aggr[k][inv[k]] += 1
        aggr["coplanar_quads"].append(inv["coplanar_quads"])
        Sset = set(ptsl)
        ds = sorted(tuple(p[k]-6 for k in range(3)) for p in Sset
                    if p > tuple(12-p[k] for k in range(3)) and tuple(12-v for v in p) in Sset)
        for d in ds:
            dvec_freq[d] += 1
            norm_freq[d[0]**2+d[1]**2+d[2]**2] += 1
        normset_hash[tuple(sorted(d[0]**2+d[1]**2+d[2]**2 for d in ds))] += 1
    cq = np.array(aggr["coplanar_quads"])
    out["pool34"] = {
        "max_layer_distribution": dict(aggr["max_layer"]),
        "n4_layers_distribution": dict(sorted(aggr["n4_layers"].items())),
        "empty_layers_distribution": dict(sorted(aggr["empty_layers"].items())),
        "surface_distribution": dict(sorted(aggr["surface"].items())),
        "parity_classes_used": dict(sorted(aggr["parity_classes_used"].items())),
        "collinear_triples_distribution": dict(sorted(aggr["collinear_triples"].items())),
        "coplanar_quads": {"min": int(cq.min()), "max": int(cq.max()),
                           "mean": round(float(cq.mean()), 1), "median": float(np.median(cq))},
        "n_distinct_dvectors_used": len(dvec_freq),
        "top20_dvectors": dvec_freq.most_common(20),
        "bottom_norms": sorted(norm_freq.items())[:15],
        "top_norms": sorted(norm_freq.items(), key=lambda kv: -kv[1])[:15],
        "n_distinct_norm_multisets": len(normset_hash),
        "most_common_norm_multiset": normset_hash.most_common(1)[0],
    }
    # norms present in EVERY pool set?
    always = [nv for nv, ct in norm_freq.items() if ct >= len(pool34)]
    # careful: a norm could repeat? no — C1 forces distinct norms per set, so ct<=n_pool
    out["pool34"]["norms_present_in_every_set"] = always
    out["pool34"]["n_norms_seen"] = len(norm_freq)

    # overlap of pool sets with the 36-set
    s36 = set(cert36)
    ov = np.array([len(s36 & set(p)) for p in pool34])
    out["pool34"]["overlap_with_36"] = {"min": int(ov.min()), "max": int(ov.max()),
                                        "mean": round(float(ov.mean()), 1)}

    # ---- ILS asymmetric sets (use the largest unique ones) ----
    uniq = {}
    for s in ils:
        uniq[tuple(sorted(s))] = len(s)
    ils_u = [list(k) for k, v in sorted(uniq.items(), key=lambda kv: -kv[1])]
    big = [s for s in ils_u if len(s) >= 33][:300]
    out["n_ils_unique_ge33"] = len(big)
    inv_list = [cheap_invariants(s) for s in big]
    out["ils_ge33"] = {
        "max_layer_distribution": dict(Counter(i["max_layer"] for i in inv_list)),
        "surface_mean": round(float(np.mean([i["surface"] for i in inv_list])), 1),
        "sym_pairs_666_distribution": dict(sorted(Counter(i["sym_pairs_666"] for i in inv_list).items())),
        "collinear_triples_distribution": dict(sorted(Counter(i["collinear_triples"] for i in inv_list).items())),
        "coplanar_per_1k_mean": round(float(np.mean([i["coplanar_per_1k_quads"] for i in inv_list])), 2),
    }

    # ---- random greedy baseline ----
    greedy = [greedy_random() for _ in range(40)]
    ginv = [cheap_invariants(s) for s in greedy]
    out["greedy_baseline"] = {
        "sizes": sorted(len(s) for s in greedy),
        "max_layer_distribution": dict(Counter(i["max_layer"] for i in ginv)),
        "surface_mean": round(float(np.mean([i["surface"] for i in ginv])), 1),
        "coplanar_per_1k_mean": round(float(np.mean([i["coplanar_per_1k_quads"] for i in ginv])), 2),
        "collinear_mean": round(float(np.mean([i["collinear_triples"] for i in ginv])), 2),
        "parity_classes_used": dict(Counter(i["parity_classes_used"] for i in ginv)),
        "sym_pairs_666_mean": round(float(np.mean([i["sym_pairs_666"] for i in ginv])), 2),
    }
    # per-1k coplanar for record sets
    out["record36_coplanar_per_1k"] = cheap_invariants(cert36)["coplanar_per_1k_quads"]

    # ---- mod-13 det census on samples ----
    sample = rng.sample(pool34, 80)
    rats = []
    minds = []
    for s in sample:
        c = mod13_census(s)
        rats.append(c["ratio_vs_generic"]); minds.append(c["min_abs_det"])
    out["mod13_census_pool34_sample80"] = {
        "ratio_mean": round(float(np.mean(rats)), 3),
        "ratio_min": min(rats), "ratio_max": max(rats),
        "min_abs_det_distribution": dict(sorted(Counter(minds).items())),
    }
    gr_big = [s for s in greedy if len(s) >= 25][:30]
    rats_g = [mod13_census(s)["ratio_vs_generic"] for s in gr_big]
    out["mod13_census_greedy"] = {"ratio_mean": round(float(np.mean(rats_g)), 3),
                                  "ratio_min": min(rats_g), "ratio_max": max(rats_g)}
    print(json.dumps(out, indent=1, default=str))

if __name__ == "__main__":
    main()
