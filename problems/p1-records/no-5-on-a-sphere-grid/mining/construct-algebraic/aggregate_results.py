#!/usr/bin/env python3
"""Final aggregation: best verified set per n per category -> RESULTS.json."""
import os, re, json, glob, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import exact_check, OUT

def main():
    best = {}
    for fn in glob.glob(os.path.join(OUT, "*.json")):
        base = os.path.basename(fn)
        m = re.match(r"^(det_|formula_|hybrid_|set_|CC_best_).*?_?n(\d+)_m(\d+)\.json$", base)
        if not m:
            continue
        n = int(m.group(2))
        pts = json.load(open(fn))
        cat = ("deterministic_CC" if base.startswith(("det_", "CC_best_")) else
               "formula" if base.startswith("formula_") else
               "full_ILS" if base.startswith(("set_full", "hybrid_")) and "full" in base else
               "hybrid" if base.startswith("hybrid_") else
               "full_ILS" if base.startswith("set_full") else "cone_ILS")
        ok, why = exact_check(pts, n)
        assert ok, (base, why)
        key = (n, cat)
        if key not in best or len(pts) > best[key][1]:
            best[key] = (base, len(pts))
    table = {}
    for (n, cat), (f, m) in sorted(best.items()):
        table.setdefault(n, {})[cat] = {"m": m, "file": f}
    json.dump(table, open(os.path.join(OUT, "RESULTS.json"), "w"), indent=1)
    hdr = ["n", "determ_CC", "cone_ILS", "hybrid", "full_ILS", "formula"]
    print("\t".join(hdr))
    for n in sorted(table):
        row = [str(n)]
        for cat in ("deterministic_CC", "cone_ILS", "hybrid", "full_ILS", "formula"):
            row.append(str(table[n].get(cat, {}).get("m", "-")))
        print("\t".join(row))

if __name__ == "__main__":
    main()
