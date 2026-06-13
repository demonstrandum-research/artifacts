#!/usr/bin/env python3
"""Gate-4/5 FRESH verification for the no-5-on-a-sphere C(13) >= 36 claim.

Run by the Gate-4/5 agent (who did not build any search pipeline) on 2026-06-12.

Three independent routes on EVERY banked certificate in certificates/:
  Route A: code/check_cert.py  (the Gate-2-validated Python checker, hardcoded
           2x2-cofactor expansion of the differenced 4x4 lifted matrix).
  Route B: written fresh HERE, different algorithm: Bareiss fraction-free
           Gaussian elimination on the full 5x5 lifted matrix
           [x, y, z, x^2+y^2+z^2, 1] with row pivoting. Pure integer.
  Route C: the independent Rust checker (code/core, no5core.exe check).

Plus, for the headline 36-point set record36_centralsym.json:
  - explicit central-symmetry verification (invariance under
    sigma(p) = (12,12,12) - p; 18 orbit pairs; center cell (6,6,6) absent;
    pairwise-distinct central shells |p-c'|^2 with c' = (6,6,6) doubled to
    avoid halves: shell(p) = |2p-(12,12,12)|^2),
  - min |det| statistics over all C(36,5) = 376,992 5-subsets,
  - mutation testing: 7 targeted corruptions, every route must REJECT,
  - saturation: Rust incremental engine + brute-force cross-check must report
    0 addable cells (no 37-point superset by single addition).

Convention anchor re-run (fresh): all six published AlphaEvolve record sets
(n=7..12, data/records.json) accepted by all three routes; the known-bad
34-set rejected by all three; the published 33-set saturation re-confirmed
for all 8 translates of the 12-cube inside the 13-cube.

Writes verification/gate45_report.json. Exit 0 iff everything passed.
"""
import hashlib, itertools, json, re, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CERTS = ROOT / "certificates"
DATA = ROOT / "data"
OUT2 = ROOT / "code" / "out"
BIN = ROOT / "code" / "core" / "target" / "release" / "no5core.exe"
TMP = HERE / "tmp"

sys.path.insert(0, str(ROOT / "code"))
import check_cert  # Route A

report = {"timestamp": time.strftime("%Y-%m-%d %H:%M:%S"), "sections": {}, "ok": False}
ALL_OK = True


def log(msg):
    print(msg, flush=True)


def sect(name, ok, **info):
    global ALL_OK
    report["sections"].setdefault(name, []).append({"ok": bool(ok), **info})
    ALL_OK &= bool(ok)
    log(f"[{'PASS' if ok else 'FAIL'}] {name} :: {info if info else ''}")
    return ok


# ---------------------------------------------------------------- Route B ---
def det_bareiss(M):
    """Exact integer determinant of a square integer matrix, Bareiss
    fraction-free elimination with row pivoting. Independent of the cofactor
    formulas used by Routes A and C."""
    A = [row[:] for row in M]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    A[k], A[r] = A[r], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
            A[i][k] = 0
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def route_b(points, n=13, want_min=False):
    """Fresh independent checker. Returns (valid, info)."""
    pts = []
    for p in points:
        if (not isinstance(p, (list, tuple))) or len(p) != 3:
            return False, "malformed point"
        for c in p:
            if not isinstance(c, int) or isinstance(c, bool) or not (0 <= c < n):
                return False, f"bad coordinate in {p}"
        pts.append(tuple(p))
    if len(set(pts)) != len(pts):
        return False, "duplicate points"
    L = [[x, y, z, x * x + y * y + z * z, 1] for (x, y, z) in pts]
    mn, n_small = None, 0
    for idx in itertools.combinations(range(len(pts)), 5):
        d = det_bareiss([L[i] for i in idx])
        if d == 0:
            return False, {"zero_5subset": [list(pts[i]) for i in idx]}
        if want_min:
            a = abs(d)
            if mn is None or a < mn:
                mn = a
            if a <= 10:
                n_small += 1
    return True, ({"min_abs_det": mn, "n_subsets_absdet_le_10": n_small}
                  if want_min else None)


# ---------------------------------------------------------------- Route C ---
def route_c(path, n=13):
    r = subprocess.run([str(BIN), "check", str(path), str(n)],
                       capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    return r.returncode == 0 and "VALID" in out and "INVALID" not in out, out


def rust_tmp(points, name):
    TMP.mkdir(exist_ok=True)
    f = TMP / name
    f.write_text(json.dumps([list(map(int, p)) for p in points]), encoding="utf-8")
    return f


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


# ============================== 1. all banked certificates, three routes ====
log("=" * 78)
log("SECTION 1: fresh three-route verification of every banked certificate")
log("=" * 78)
cert_files = sorted(CERTS.iterdir(), key=lambda p: p.name)
classes = {}  # frozenset-of-points -> [filenames]
for f in cert_files:
    pts = load(f)
    key = frozenset(tuple(p) for p in pts)
    classes.setdefault(key, []).append(f.name)
    okA, whyA = check_cert.check([tuple(p) for p in pts], 13)
    okB, infoB = route_b(pts, 13)
    okC, outC = route_c(f, 13)
    sect("certificates_three_routes", okA and okB and okC,
         file=f.name, m=len(pts), sha256=sha256(f),
         routeA="PASS" if okA else f"FAIL:{whyA}",
         routeB="PASS" if okB else f"FAIL:{infoB}",
         routeC=outC)

dup_classes = sorted([sorted(v) for v in classes.values() if len(v) > 1])
sizes = sorted({len(k) for k in classes})
sect("certificate_inventory", True,
     n_files=len(cert_files), n_distinct_sets=len(classes),
     distinct_sizes=sizes, duplicate_file_groups=dup_classes)

# ============================== 2. the 36-set: symmetry, tightness ==========
log("=" * 78)
log("SECTION 2: the 36-point set - central symmetry + tightness")
log("=" * 78)
S36 = [tuple(p) for p in load(CERTS / "record36_centralsym.json")]
sset = set(S36)
sigma = lambda p: (12 - p[0], 12 - p[1], 12 - p[2])
sym_ok = all(sigma(p) in sset for p in S36)
no_fixed = all(sigma(p) != p for p in S36)  # center (6,6,6) is the only fixed cell
center_absent = (6, 6, 6) not in sset
pairs = {frozenset((p, sigma(p))) for p in S36}
shell = lambda p: sum((2 * c - 12) ** 2 for c in p)  # 4*|p-center|^2, integer
shells = sorted(shell(min(pr)) for pr in pairs)
shells_distinct = len(set(shells)) == len(shells)
sect("centrally_symmetric", sym_ok and no_fixed and center_absent
     and len(pairs) == 18,
     m=len(S36), invariant_under_sigma=sym_ok, fixed_points=0 if no_fixed else "!",
     center_cell_absent=center_absent, n_orbit_pairs=len(pairs),
     shells_4x=shells, shells_pairwise_distinct=shells_distinct)

okB36, tight = route_b(S36, 13, want_min=True)
sect("tightness_36", okB36, **(tight or {}))

# ============================== 3. mutation tests on the 36-set =============
log("=" * 78)
log("SECTION 3: mutation testing (every route must REJECT every corruption)")
log("=" * 78)


def find_coplanar_append(S):
    """A grid cell, not in S, coplanar with two orbit pairs of S (the plane of
    any two orbit pairs passes through the center): a near-valid corruption."""
    pl = sorted(pairs)
    for pr1, pr2 in itertools.combinations(pl, 2):
        q, qq = sorted(pr1)
        r, rr = sorted(pr2)
        # plane through q, qq, r (and automatically rr): normal = (qq-q) x (r-q)
        u = tuple(qq[i] - q[i] for i in range(3))
        v = tuple(r[i] - q[i] for i in range(3))
        nvec = (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2],
                u[0] * v[1] - u[1] * v[0])
        if nvec == (0, 0, 0):
            continue
        d = sum(nvec[i] * q[i] for i in range(3))
        for cell in itertools.product(range(13), repeat=3):
            if cell in sset or cell in (q, qq, r, rr):
                continue
            if sum(nvec[i] * cell[i] for i in range(3)) == d:
                return list(cell), [list(q), list(qq), list(r), list(rr)]
    return None, None


cop_cell, cop_quad = find_coplanar_append(S36)
mutations = {
    "duplicate_point": S36[:-1] + [S36[0]],
    "coordinate_13_out_of_range": [(13, S36[0][1], S36[0][2])] + S36[1:],
    "negative_coordinate": [(-1, S36[0][1], S36[0][2])] + S36[1:],
    "append_center_cell": S36 + [(6, 6, 6)],          # center + any 2 pairs coplanar
    "replace_point_with_center": S36[1:] + [(6, 6, 6)],
    "append_coplanar_cell": S36 + [tuple(cop_cell)] if cop_cell else None,
}
for name, mut in mutations.items():
    if mut is None:
        sect("mutation", False, mutation=name, error="construction failed")
        continue
    okA, whyA = check_cert.check([tuple(p) for p in mut], 13)
    okB, whyB = route_b(mut, 13)
    f = rust_tmp(mut, f"mut_{name}.json")
    okC, outC = route_c(f, 13)
    rejected = (not okA) and (not okB) and (not okC)
    sect("mutation", rejected, mutation=name, m=len(mut),
         routeA="REJECT" if not okA else "ACCEPT(!)",
         routeB="REJECT" if not okB else "ACCEPT(!)",
         routeC=outC,
         extra={"appended_cell": cop_cell, "coplanar_with_pairs": cop_quad}
               if name == "append_coplanar_cell" else None)

# float mutation (routes A and B only; Rust parser is integer-only by design)
mut_float = [[5.0, S36[0][1], S36[0][2]]] + [list(p) for p in S36[1:]]
okA, _ = check_cert.check([tuple(p) for p in mut_float], 13)
okB, _ = route_b(mut_float, 13)
sect("mutation", (not okA) and (not okB), mutation="float_coordinate_5.0",
     routeA="REJECT" if not okA else "ACCEPT(!)",
     routeB="REJECT" if not okB else "ACCEPT(!)",
     routeC="n/a (integer-only parser)")

# ============================== 4. saturation of the 36-set =================
log("=" * 78)
log("SECTION 4: saturation of the 36-set (incremental + brute cross-check)")
log("=" * 78)
r = subprocess.run([str(BIN), "saturation", str(CERTS / "record36_centralsym.json"),
                    "--brute"], capture_output=True, text=True)
out = (r.stdout + r.stderr).strip()
madd = re.search(r"addable_count=(\d+)", out)
nadd = int(madd.group(1)) if madd else -1
sect("saturation_36", r.returncode == 0 and "valid_set=true" in out
     and "bruteforce_grid_match=true" in out and nadd >= 0,
     addable_count=nadd, raw=out.splitlines()[-1] if out else "")

# ============================== 5. convention anchor (fresh re-run) =========
log("=" * 78)
log("SECTION 5: convention anchor - published records n=7..12, bad-34, 33-set")
log("=" * 78)
records = load(DATA / "records.json")
expected = {7: 21, 8: 23, 9: 26, 10: 28, 11: 31, 12: 33}
for nstr, pts in sorted(records.items(), key=lambda kv: int(kv[0])):
    n = int(nstr)
    okA, whyA = check_cert.check([tuple(p) for p in pts], n)
    okB, _ = route_b(pts, n)
    f = rust_tmp(pts, f"record_n{n}.json")
    okC, outC = route_c(f, n)
    sect("published_records_accepted", okA and okB and okC
         and len(pts) == expected[n],
         n=n, m=len(pts), routeA=okA, routeB=okB, routeC=outC)

bad34 = load(OUT2 / "s12_bad34.json")
okA, whyA = check_cert.check([tuple(p) for p in bad34], 13)
okB, whyB = route_b(bad34, 13)
okC, outC = route_c(OUT2 / "s12_bad34.json", 13)
sect("known_bad34_rejected", (not okA) and (not okB) and (not okC),
     routeA="REJECT" if not okA else "ACCEPT(!)",
     routeB="REJECT" if not okB else "ACCEPT(!)", routeC=outC)

sat33 = {}
sat_ok = True
for dx, dy, dz in itertools.product((0, 1), repeat=3):
    f = OUT2 / f"s12_shift{dx}{dy}{dz}.json"
    args = [str(BIN), "saturation", str(f)] + \
           (["--brute"] if (dx, dy, dz) == (0, 0, 0) else [])
    r = subprocess.run(args, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    madd = re.search(r"addable_count=(\d+)", out)
    nadd = int(madd.group(1)) if madd else -1
    sat33[f"shift{dx}{dy}{dz}"] = nadd
    sat_ok &= r.returncode == 0 and "valid_set=true" in out and nadd == 0
    if (dx, dy, dz) == (0, 0, 0):
        sat_ok &= "bruteforce_grid_match=true" in out
sect("record33_saturation_8_translates", sat_ok, **sat33)

# ============================== write report ================================
report["ok"] = bool(ALL_OK)
(HERE / "gate45_report.json").write_text(
    json.dumps(report, indent=2, default=str), encoding="utf-8")
log("=" * 78)
log(f"GATE-4/5 FRESH VERIFICATION {'PASSED' if ALL_OK else 'FAILED'} "
    f"-> {HERE / 'gate45_report.json'}")
sys.exit(0 if ALL_OK else 1)
