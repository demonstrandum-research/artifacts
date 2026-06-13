#!/usr/bin/env python3
"""Harvest + exact-verify the construct-search runs.

For each candidate file, re-verifies with the EXACT independent checker
(code/check_cert.py, pure-int), records structural diagnostics (central
symmetry, distinct scaled shells, V4 closure), keeps the best per n in
cert_n{n}_m{m}.json, and writes RESULTS.json.
"""
import json, os, sys, importlib.util

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"
CS = os.path.join(BASE, "mining", "construct-search")
spec = importlib.util.spec_from_file_location("check_cert", os.path.join(BASE, "code", "check_cert.py"))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)

def diag(pts, n):
    s = set(map(tuple, pts))
    nm1 = n - 1
    cs = all((nm1 - x, nm1 - y, nm1 - z) in s for (x, y, z) in s)
    shells = {}
    for (x, y, z) in s:
        sh = (2 * x - nm1) ** 2 + (2 * y - nm1) ** 2 + (2 * z - nm1) ** 2
        shells[sh] = shells.get(sh, 0) + 1
    v4 = all(all(q in s for q in [(x, nm1 - y, nm1 - z), (nm1 - x, y, nm1 - z),
                                  (nm1 - x, nm1 - y, z)]) for (x, y, z) in s)
    return {"centrally_symmetric": cs, "v4_closed": v4,
            "n_shells": len(shells), "max_per_shell": max(shells.values()),
            "shell_occupancies": sorted(shells.values(), reverse=True)[:6]}

def main():
    cands = []  # (n, path, tag)
    for n in (14, 15, 16, 17):
        d = os.path.join(CS, "runs", f"main_n{n}")
        for f, tag in (("best_sym.json", "sym"), ("best_total.json", "total")):
            p = os.path.join(d, f)
            if os.path.exists(p):
                cands.append((n, p, f"ILS-{tag}"))
        for f in os.listdir(d) if os.path.isdir(d) else []:
            if f.startswith("FOUND") and f.endswith(".json"):
                cands.append((n, os.path.join(d, f), "ILS-found"))
    for n in (14, 16):
        p = os.path.join(CS, f"v4_best_n{n}_s7.json")
        if os.path.exists(p):
            cands.append((n, p, "V4-template"))
    # prior mining baselines
    for n, p, tag in ((15, os.path.join(BASE, "mining", "algebraic", "sym_best_n15_s1.json"), "prior-python"),
                      (17, os.path.join(BASE, "mining", "algebraic", "sym_best_n17_s1.json"), "prior-python"),
                      (14, os.path.join(BASE, "mining", "symmetry", "even_sym_best_n14.json"), "prior-python")):
        if os.path.exists(p):
            cands.append((n, p, tag))

    best = {}
    rows = []
    for n, p, tag in cands:
        pts = json.load(open(p))
        ok, why = cc.check(pts, n)
        row = {"n": n, "file": p.replace(BASE, "."), "tag": tag, "m": len(pts),
               "valid": ok}
        if ok:
            row.update(diag(pts, n))
            if n not in best or len(pts) > best[n][0]:
                best[n] = (len(pts), pts, p, tag)
        else:
            row["why"] = str(why)[:120]
        rows.append(row)
        print(json.dumps(row))

    summary = {}
    for n, (m, pts, src, tag) in sorted(best.items()):
        out = os.path.join(CS, f"cert_n{n}_m{m}.json")
        json.dump(sorted(map(list, map(tuple, pts))), open(out, "w"))
        ok2, _ = cc.check(json.load(open(out)), n)
        assert ok2
        summary[n] = {"m": m, "cert": os.path.basename(out), "source": src.replace(BASE, "."),
                      "tag": tag, **diag(pts, n)}
        print(f"BEST n={n}: m={m} ({tag}) -> {out}")
    json.dump({"results": rows, "best": summary}, open(os.path.join(CS, "RESULTS.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
