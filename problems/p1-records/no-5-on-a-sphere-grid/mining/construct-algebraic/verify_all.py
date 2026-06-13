#!/usr/bin/env python3
"""Independently re-verify every saved point-set JSON in this directory with the
exact checker; emit MANIFEST.json with per-file status and the best set per n
per category (deterministic / cone-ILS / full-ILS / formula / hybrid).
"""
import os, re, json, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import exact_check, OUT

CATS = [("det_", "deterministic"), ("formula_", "formula"),
        ("hybrid_", "hybrid"), ("set_full", "full_ILS"), ("set_", "cone_ILS")]

def category(fn):
    for pref, cat in CATS:
        if fn.startswith(pref):
            return cat
    return "other"

def main():
    manifest = []
    for fn in sorted(os.listdir(OUT)):
        m = re.match(r"^(det_|formula_|hybrid_|set_).*_n(\d+)_m(\d+)\.json$", fn)
        if not m:
            continue
        n, mm = int(m.group(2)), int(m.group(3))
        pts = json.load(open(os.path.join(OUT, fn)))
        ok, why = exact_check(pts, n)
        manifest.append({"file": fn, "n": n, "m": len(pts), "category": category(fn),
                         "valid": ok, **({} if ok else {"reason": str(why)})})
        assert len(pts) == mm
    best = {}
    for r in manifest:
        if not r["valid"]:
            continue
        key = (r["n"], r["category"])
        if key not in best or r["m"] > best[key]["m"]:
            best[key] = r
    summary = {f"n{n}_{cat}": v["m"] for (n, cat), v in sorted(best.items())}
    out = {"n_files": len(manifest),
           "n_valid": sum(r["valid"] for r in manifest),
           "n_invalid": sum(not r["valid"] for r in manifest),
           "best_by_n_and_category": {f"{k[0]}|{k[1]}": v["file"] for k, v in sorted(best.items())},
           "best_sizes": summary,
           "files": manifest}
    json.dump(out, open(os.path.join(OUT, "MANIFEST.json"), "w"), indent=1)
    print(json.dumps({"n_files": out["n_files"], "n_valid": out["n_valid"],
                      "n_invalid": out["n_invalid"], "best_sizes": summary}, indent=1))

if __name__ == "__main__":
    main()
