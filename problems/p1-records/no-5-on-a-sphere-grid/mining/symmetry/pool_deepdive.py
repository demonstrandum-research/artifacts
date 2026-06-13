#!/usr/bin/env python3
"""Deep-dive on the symmetric 34-pool: pair-direction statistics, shell
decompositions, the 28 non-symmetric entries, and class structure."""
import json, os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, "..", ".."))
MR = os.path.join(BASE, "runs", "central-symmetric", "main-run")

pool = sl.load_jsonl_sets(os.path.join(MR, "pool_34.jsonl"))
S36 = sl.load_json_set(os.path.join(BASE, "certificates", "record36_centralsym.json"))

def u_reps(S):
    """Canonical pair directions u (centered), for fully symmetric sets."""
    Sf = set(S)
    reps = []
    for p in Sf:
        q = tuple(12 - c for c in p)
        if q in Sf and p < q:
            reps.append(tuple(p[i] - 6 for i in range(3)))
    return reps

# ---- the 28 non-fully-symmetric pool entries
odd = [S for S in pool if len(sl.sym_core(S)) != len(S)]
print(f"non-fully-symmetric pool entries: {len(odd)}")
for S in odd[:6]:
    core = sl.sym_core(S)
    print(f"  size {len(S)} core {len(core)} extras {sorted(set(S)-set(core))[:4]}")

# ---- u-direction popularity across the pool
freq = Counter()
nsym = 0
for S in pool:
    if len(sl.sym_core(S)) != len(S):
        continue
    nsym += 1
    for u in u_reps(S):
        # canonicalize sign: lexicographically positive
        cu = max(u, tuple(-c for c in u))
        freq[cu] += 1
print(f"\nfully symmetric sets used: {nsym}; distinct pair directions used: {len(freq)} "
      f"of {(13**3 - 1)//2} possible")
top = freq.most_common(25)
print("top-25 pair directions (u, count):")
for u, c in top:
    r2 = sum(x * x for x in u)
    print(f"  u={u} r2={r2}: {c}")

u36 = [max(u, tuple(-c for c in u)) for u in u_reps(S36)]
ranks = {u: i for i, (u, _) in enumerate(freq.most_common())}
print("\n36-set pair ranks in pool popularity (rank/total {}):".format(len(freq)))
print(sorted(ranks.get(u, -1) for u in u36))

# ---- never-used pair directions: structured?
allu = set()
for x in range(-6, 7):
    for y in range(-6, 7):
        for z in range(-6, 7):
            u = (x, y, z)
            if u == (0, 0, 0):
                continue
            cu = max(u, tuple(-c for c in u))
            allu.add(cu)
never = sorted(u for u in allu if freq[u] == 0)
print(f"\npair directions never used in pool: {len(never)} of {len(allu)}")
# classify by type: axis (two zero coords), face diag (|a|=|b|, 0), body diag |a|=|b|=|c|,
# in-coordinate-plane (one zero), generic
def utype(u):
    a = sorted(map(abs, u))
    nz = sum(1 for c in u if c == 0)
    if nz == 2:
        return "axis"
    if nz == 1:
        if a[1] == a[2]:
            return "facediag"
        return "coordplane"
    if a[0] == a[1] == a[2]:
        return "bodydiag"
    if a[1] == a[2] or a[0] == a[1]:
        return "partial-equal"
    return "generic"
tn = Counter(utype(u) for u in never)
ta = Counter(utype(u) for u in allu)
print("never-used by type (never/all):", {k: (tn.get(k, 0), ta[k]) for k in ta})
nv_small = [u for u in never if max(abs(c) for c in u) <= 3]
print("never-used with all |coords|<=3:", nv_small)

# shells of never-used vs used
sh_never = Counter(sum(c * c for c in u) for u in never)
print("never-used shell histogram (r2: count):", dict(sorted(sh_never.items())))

# ---- per-set direction-type profile (36-set vs pool average)
def type_profile(us):
    return Counter(utype(u) for u in us)
print("\n36-set direction-type profile:", dict(type_profile(u36)))
agg = Counter()
for S in pool[:500]:
    if len(sl.sym_core(S)) == len(S):
        agg += type_profile([max(u, tuple(-c for c in u)) for u in u_reps(S)])
tot = sum(agg.values())
print("pool(500) direction-type profile (fraction):",
      {k: round(v / tot, 3) for k, v in agg.items()})
alltot = sum(ta.values())
print("all-u baseline type fractions:", {k: round(v / alltot, 3) for k, v in ta.items()})

# ---- class sizes (B3 classes) of pool
canon = Counter()
for S in pool:
    canon[sl.canonical_form(S)] += 1
sizes = Counter(canon.values())
print(f"\nB3 class multiplicity histogram (copies-per-class: nclasses): {dict(sorted(sizes.items()))}")

# ---- 36-subset containment: how many pool 34s are subsets of the 36-set?
S36f = frozenset(S36)
sub = sum(1 for S in pool if frozenset(S) <= S36f)
print(f"pool 34-sets that are subsets of the 36-set: {sub} (max possible C(18,1)=18 sym ones)")

json.dump({"top_pair_dirs": [[list(u), c] for u, c in top],
           "never_used_count": len(never), "never_by_type": {k: [tn.get(k, 0), ta[k]] for k in ta},
           "ranks36": sorted(ranks.get(u, -1) for u in u36)},
          open(os.path.join(HERE, "pool_deepdive.json"), "w"), indent=1)
print("written pool_deepdive.json")
