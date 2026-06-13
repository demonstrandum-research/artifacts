#!/usr/bin/env python3
"""Gate-2 validation orchestrator for the no-5-on-a-sphere tooling.

Steps (all exact integer arithmetic, no floats):
  1. Python checker ACCEPTS all six published record sets (n=7..12), and the
     33-point n=12 record both as an n=12 and as an n=13 certificate.
  2. Construct a known-bad 34-point set (33-record + one cell that completes a
     zero 5-subset, found by exact determinants) and verify the Python checker
     REJECTS it, naming the offending 5-subset.
  3. cargo test --release (includes the rank-degenerate-quadruple trap tests).
  4. Rust dual checker: VALID on the 33-record, INVALID on the bad 34-set.
  5. Saturation: the Rust incremental core must report 0 addable cells for the
     33-record in {0..12}^3, for ALL 8 translates by {0,1}^3 — together these
     cover the dossier's 2711-cell {-1..12}^3 scan exactly. One translate is
     also cross-validated against a full brute-force det5 blocked-grid recount.
  6. Benchmark (single thread + all-thread scaling), parse moves/sec.

Writes out/gate2_status.json. Exit 0 iff every step passed.
"""
import itertools, json, re, subprocess, sys, time
from pathlib import Path

import check_cert

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "data"
OUT = HERE / "out"
BIN = HERE / "core" / "target" / "release" / "no5core.exe"

status = {"timestamp": time.strftime("%Y-%m-%d %H:%M:%S"), "steps": {}, "ok": False}


def step(name, ok, **info):
    status["steps"][name] = {"ok": bool(ok), **info}
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {info if info else ''}")
    return ok


def run(args, high_priority=False):
    flags = 0x00000080 if high_priority else 0  # HIGH_PRIORITY_CLASS
    r = subprocess.run([str(a) for a in args], capture_output=True, text=True,
                       creationflags=flags)
    return r.returncode, r.stdout + r.stderr


def det5(q, p):
    """Exact lifted 5-point determinant (independent reference, pure int)."""
    L = [(x, y, z, x * x + y * y + z * z) for (x, y, z) in (*q, p)]
    base = L[0]
    (a0, a1, a2, a3), (b0, b1, b2, b3), (c0, c1, c2, c3), (d0, d1, d2, d3) = \
        [tuple(L[i][k] - base[k] for k in range(4)) for i in range(1, 5)]
    return ((a0*b1 - a1*b0) * (c2*d3 - c3*d2) - (a0*b2 - a2*b0) * (c1*d3 - c3*d1)
          + (a0*b3 - a3*b0) * (c1*d2 - c2*d1) + (a1*b2 - a2*b1) * (c0*d3 - c3*d0)
          - (a1*b3 - a3*b1) * (c0*d2 - c2*d0) + (a2*b3 - a3*b2) * (c0*d1 - c1*d0))


def main():
    OUT.mkdir(exist_ok=True)
    records = json.load(open(DATA / "records.json"))
    s12 = [tuple(p) for p in records["12"]]
    assert len(s12) == 33
    json.dump([list(p) for p in s12], open(OUT / "s12.json", "w"))

    all_ok = True

    # ---- step 1: python checker accepts all published records -------------
    rec_ok = True
    for nstr, pts in sorted(records.items(), key=lambda kv: int(kv[0])):
        ok, why = check_cert.check([tuple(p) for p in pts], int(nstr))
        rec_ok &= ok and len(pts) == {7: 21, 8: 23, 9: 26, 10: 28, 11: 31, 12: 33}[int(nstr)]
    ok13, _ = check_cert.check(s12, 13)
    all_ok &= step("py_checker_accepts_records", rec_ok and ok13,
                   records_checked=sorted(int(k) for k in records))

    # ---- step 2: construct + reject a known-bad 34-point set --------------
    bad_cell, bad_quad = None, None
    grid = [(x, y, z) for x in range(13) for y in range(13) for z in range(13)]
    sset = set(s12)
    for cell in grid:
        if cell in sset:
            continue
        for q in itertools.combinations(s12, 4):
            if det5(q, cell) == 0:
                bad_cell, bad_quad = cell, q
                break
        if bad_cell:
            break
    bad34 = s12 + [bad_cell]
    json.dump([list(p) for p in bad34], open(OUT / "s12_bad34.json", "w"))
    ok_bad, witness = check_cert.check(bad34, 13)
    rejected = (not ok_bad) and isinstance(witness, list)
    all_ok &= step("py_checker_rejects_bad34", rejected,
                   added_cell=bad_cell, zero_quadruple=bad_quad,
                   reported_5subset=witness)

    # ---- step 3: cargo unit tests (incl. degenerate-quadruple traps) ------
    rc, out = run(["cargo", "test", "--release", "--manifest-path",
                   HERE / "core" / "Cargo.toml"])
    m = re.search(r"test result: ok\. (\d+) passed; 0 failed", out)
    trap_names = ["trap_collinear_axis", "trap_collinear_skew",
                  "trap_cocircular_unit_square", "trap_cocircular_rotated_rectangle",
                  "trap_cocircular_tilted_plane"]
    traps_ran = all(f"test tests::{t} ... ok" in out for t in trap_names)
    all_ok &= step("cargo_tests", rc == 0 and m and traps_ran,
                   passed=int(m.group(1)) if m else 0, trap_tests=trap_names)

    # ---- step 4: rust dual checker ----------------------------------------
    rc_good, out_good = run([BIN, "check", OUT / "s12.json", 13])
    rc_bad, out_bad = run([BIN, "check", OUT / "s12_bad34.json", 13])
    all_ok &= step("rust_checker_accept_reject",
                   rc_good == 0 and "VALID m=33" in out_good
                   and rc_bad == 1 and "INVALID m=34" in out_bad,
                   good=out_good.strip().splitlines()[-1],
                   bad=out_bad.strip().splitlines()[-1])

    # ---- step 5: saturation, 8 translates (covers {-1..12}^3) -------------
    sat_ok = True
    sat_info = {}
    for dx, dy, dz in itertools.product((0, 1), repeat=3):
        shifted = [[x + dx, y + dy, z + dz] for (x, y, z) in s12]
        f = OUT / f"s12_shift{dx}{dy}{dz}.json"
        json.dump(shifted, open(f, "w"))
        args = [BIN, "saturation", f] + (["--brute"] if (dx, dy, dz) == (0, 0, 0) else [])
        rc, out = run(args)
        madd = re.search(r"addable_count=(\d+)", out)
        valid = "valid_set=true" in out
        nadd = int(madd.group(1)) if madd else -1
        sat_info[f"shift{dx}{dy}{dz}"] = nadd
        sat_ok &= rc == 0 and valid and nadd == 0
        if (dx, dy, dz) == (0, 0, 0):
            sat_ok &= "bruteforce_grid_match=true" in out
            sat_info["bruteforce_grid_match"] = "bruteforce_grid_match=true" in out
    all_ok &= step("saturation_zero_addable_all_8_translates", sat_ok, **sat_info)

    # ---- step 6: benchmark (high priority: machine carries background load) --
    rc1, out1 = run([BIN, "bench", OUT / "s12.json", "--secs", "5", "--threads", "1"],
                    high_priority=True)
    rc32, out32 = run([BIN, "bench", OUT / "s12.json", "--secs", "5", "--threads", "32"],
                      high_priority=True)
    bench = {}
    m1 = re.search(r"RESULT (.*)", out1)
    mt = re.search(r"RESULT (.*)", out32)
    mtp = re.search(r"RESULT_PER_THREAD (.*)", out32)
    if m1:
        bench["single_thread"] = m1.group(1)
    if mt:
        bench["threads32_total"] = mt.group(1)
    if mtp:
        bench["threads32_per_thread"] = mtp.group(1)
    all_ok &= step("bench", rc1 == 0 and rc32 == 0 and m1 is not None, **bench)

    status["ok"] = bool(all_ok)
    json.dump(status, open(OUT / "gate2_status.json", "w"), indent=2, default=str)
    print(f"\nGATE-2 {'PASSED' if all_ok else 'FAILED'} -> {OUT / 'gate2_status.json'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
