#!/usr/bin/env python3
"""Addable-cell scan: is each headline certificate maximal in {0..12}^3?
Also: for the 36-set, symmetric-pair addability (could a 19th pair ever fit
after deletions? quick 1-pair-out/1-pair-in scan)."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, "..", ".."))
CERT = os.path.join(BASE, "certificates")

names = ["record36_centralsym.json", "record35_baseline.json"] + \
        [f"record35_blockerrepair_{i}.json" for i in range(1, 7)]

def addable_cells(S):
    Sf = set(S)
    out = []
    for x in range(13):
        for y in range(13):
            for z in range(13):
                p = (x, y, z)
                if p in Sf:
                    continue
                if sl.is_valid_with_new(S, [p]):
                    out.append(p)
    return out

res = {}
for nm in names:
    S = sl.load_json_set(os.path.join(CERT, nm))
    ad = addable_cells(S)
    res[nm] = {"size": len(S), "addable": ad}
    print(f"{nm}: size {len(S)}, addable cells: {len(ad)} {ad[:5]}")

# symmetric move scan on the 36-set: remove pair i, try all other pairs
S36 = sl.load_json_set(os.path.join(CERT, "record36_centralsym.json"))
Sf = set(S36)
pairs = []
for p in sorted(Sf):
    q = tuple(12 - c for c in p)
    if p < q:
        pairs.append((p, q))
allu = [(x, y, z) for x in range(13) for y in range(13) for z in range(13)]
swap_found = []
for i, (p0, q0) in enumerate(pairs):
    S = [p for p in S36 if p not in (p0, q0)]
    Sset = set(S)
    for p in allu:
        q = tuple(12 - c for c in p)
        if p >= q or p in Sset or q in Sset:
            continue
        if (p, q) == (p0, q0):
            continue
        if sl.is_valid_with_new(S, [p, q]):
            swap_found.append({"out": [p0, q0], "in": [p, q]})
print(f"\n1-pair-out/1-pair-in alternatives for the 36-set: {len(swap_found)}")
for s in swap_found[:10]:
    print("  ", s)
res["pair_swaps_36"] = swap_found

json.dump(res, open(os.path.join(HERE, "maximality_scan.json"), "w"), indent=1, default=str)
print("written maximality_scan.json")
