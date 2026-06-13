# -*- coding: utf-8 -*-
"""Hostile-referee recomputation for papers/no5sphere-record/note.tex.

Independent implementation (5x5 permutation expansion for the headline check;
vectorized 4x4 integer expansion for the saturation scans). Parses the point
set and Table 1 straight out of note.tex, so the *paper itself* is the object
being verified, not the bundle.
"""
import hashlib
import itertools
import json
import math
import os
import re
import sys
import time
from datetime import datetime

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
TEX = os.path.join(HERE, "note.tex")
BUNDLE = os.path.normpath(os.path.join(
    HERE, "..", "..", "problems", "p1-records", "no-5-on-a-sphere-grid"))

report = {}
def rep(key, val):
    report[key] = val
    print(f"{key}: {val}")

src = open(TEX, encoding="utf-8").read()

# ---------------------------------------------------------------- parse tex
# 1. machine-readable verbatim list (first verbatim block containing [[)
blocks = re.findall(r"\\begin{verbatim}(.*?)\\end{verbatim}", src, re.S)
listblock = next(b for b in blocks if b.strip().startswith("[["))
S = [tuple(p) for p in json.loads(listblock.strip().replace("\n", ""))]
rep("tex_list_n_points", len(S))
rep("tex_list_distinct", len(set(S)) == len(S))
rep("tex_list_in_range", all(len(p) == 3 and all(0 <= c <= 12 for c in p) for p in S))
rep("tex_list_sorted", S == sorted(S))

# 2. Table 1 rows: "1 & $(3,5,7)$ & $(9,7,5)$ & 44 & 10 & ..."
rowre = re.compile(
    r"(\d+)\s*&\s*\$\((\d+),(\d+),(\d+)\)\$\s*&\s*\$\((\d+),(\d+),(\d+)\)\$\s*&\s*(\d+)")
pairs = {}
for m in rowre.finditer(src):
    idx = int(m.group(1))
    p = tuple(int(m.group(i)) for i in (2, 3, 4))
    sp = tuple(int(m.group(i)) for i in (5, 6, 7))
    pairs[idx] = (p, sp, int(m.group(8)))
rep("table_rows_found", len(pairs))
assert len(pairs) == 18 and set(pairs) == set(range(1, 19))

ok_sigma = all(tuple(12 - c for c in p) == sp for (p, sp, _) in pairs.values())
rep("table_sigma_correct", ok_sigma)
ok_rho = all(sum((2 * c - 12) ** 2 for c in p) == d for (p, sp, d) in pairs.values())
rep("table_4rho2_correct", ok_rho)
dvals = [pairs[i][2] for i in range(1, 19)]
rep("table_4rho2_sorted_ascending", dvals == sorted(dvals))
rep("table_4rho2_pairwise_distinct", len(set(dvals)) == 18)
union = sorted({pt for (p, sp, _) in pairs.values() for pt in (p, sp)})
rep("table_union_equals_list", union == sorted(S))

# ------------------------------------------------- headline determinant scan
def det5_perm(rows):
    """5x5 integer determinant by full permutation expansion (independent)."""
    tot = 0
    for perm in PERMS5:
        sgn, idxs = perm
        prod = 1
        for r, c in enumerate(idxs):
            prod *= rows[r][c]
        tot += sgn * prod
    return tot

def perm_sign(p):
    s = 1
    p = list(p)
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s

PERMS5 = [(perm_sign(p), p) for p in itertools.permutations(range(5))]

L5 = [(x, y, z, x * x + y * y + z * z, 1) for (x, y, z) in S]
t0 = time.time()
mind = None
maxd = 0
small = 0   # |det| <= 10
zeros = 0
count = 0
for combo in itertools.combinations(range(36), 5):
    d = det5_perm([L5[i] for i in combo])
    count += 1
    a = abs(d)
    if a == 0:
        zeros += 1
    else:
        mind = a if mind is None else min(mind, a)
        maxd = max(maxd, a)
    if a <= 10:
        small += 1
rep("subsets_total", count)
rep("subsets_expected_376992", count == 376992 == math.comb(36, 5))
rep("zero_dets", zeros)
rep("min_abs_det", mind)
rep("max_abs_det", maxd)
rep("count_absdet_le_10", small)
rep("headline_scan_secs", round(time.time() - t0, 1))

# ------------------------------------------------------------- structure
prof = {ax: [sum(1 for p in S if p[ax] == v) for v in range(13)] for ax in range(3)}
rep("profile_x", prof[0])
rep("profile_y", prof[1])
rep("profile_z", prof[2])
claim = {0: [4,3,2,3,2,3,2,3,2,3,2,3,4],
         1: [4,3,1,3,3,2,4,2,3,3,1,3,4],
         2: [4,3,4,2,2,3,0,3,2,2,4,3,4]}
rep("profiles_match_tex", all(prof[a] == claim[a] for a in range(3)))
rep("profiles_palindromic", all(prof[a] == prof[a][::-1] for a in range(3)))
rep("max_layer_count", max(max(prof[a]) for a in range(3)))
surf = sum(1 for p in S if any(c in (0, 12) for c in p))
rep("surface_points", surf)
center_absent = (6, 6, 6) not in S
rep("center_absent", center_absent)

# ------------------------------------------------- vectorized 4x4 det engine
def dets4_for_cell(L4, quads, u):
    """All dets of rows L4[quad]-lift(u) for each quad (vectorized, int64)."""
    D = L4[quads] - np.array(u, dtype=np.int64)   # (nq,4,4)
    a, b, c, d = D[:, 0, :], D[:, 1, :], D[:, 2, :], D[:, 3, :]
    def m2(p, q, i, j):
        return p[:, i] * q[:, j] - p[:, j] * q[:, i]
    return (m2(a, b, 0, 1) * m2(c, d, 2, 3)
            - m2(a, b, 0, 2) * m2(c, d, 1, 3)
            + m2(a, b, 0, 3) * m2(c, d, 1, 2)
            + m2(a, b, 1, 2) * m2(c, d, 0, 3)
            - m2(a, b, 1, 3) * m2(c, d, 0, 2)
            + m2(a, b, 2, 3) * m2(c, d, 0, 1))

def lift4(pts):
    return np.array([(x, y, z, x * x + y * y + z * z) for (x, y, z) in pts],
                    dtype=np.int64)

def addable_cells(pts, n=13):
    """Cells u of {0..n-1}^3 \\ pts such that pts+{u} is still valid."""
    L4 = lift4(pts)
    m = len(pts)
    quads = np.array(list(itertools.combinations(range(m), 4)), dtype=np.int64)
    members = set(map(tuple, pts))
    good = []
    for u in itertools.product(range(n), repeat=3):
        if u in members:
            continue
        lu = (u[0], u[1], u[2], u[0]**2 + u[1]**2 + u[2]**2)
        if not np.all(dets4_for_cell(L4, quads, lu)):
            continue
        good.append(u)
    return good

# cross-check engine vs permanent expansion on the 36-set (random spot checks)
rng = np.random.default_rng(0)
L4S = lift4(S)
for _ in range(2000):
    ix = sorted(rng.choice(36, size=5, replace=False).tolist())
    d5 = det5_perm([L5[i] for i in ix])
    quad = np.array([ix[:4]])
    u = S[ix[4]]
    d4 = dets4_for_cell(L4S, quad, (u[0], u[1], u[2], u[0]**2+u[1]**2+u[2]**2))[0]
    assert abs(d5) == abs(int(d4)), (ix, d5, d4)
rep("engine_crosscheck_2000_random_5subsets", "OK (|det5| == |det4diff|)")

t0 = time.time()
add36 = addable_cells(S)
rep("saturation_36_addable_cells", len(add36))
rep("saturation_scan_secs", round(time.time() - t0, 1))

# ------------------------------------------------- validity of a generic set
def is_valid(pts):
    """Exact validity via the vectorized engine: for every point as 'cell',
    no zero det against quads of the others; plus full 5-subset coverage."""
    m = len(pts)
    L4 = lift4(pts)
    quads = np.array(list(itertools.combinations(range(m), 4)), dtype=np.int64)
    # every 5-subset {q1..q4, u}: iterate u over points, quads over others
    for ui in range(m):
        others = [i for i in range(m) if i != ui]
        oq = np.array(list(itertools.combinations(others, 4)), dtype=np.int64)
        u = pts[ui]
        lu = (u[0], u[1], u[2], u[0]**2 + u[1]**2 + u[2]**2)
        if not np.all(dets4_for_cell(L4, oq, lu)):
            return False
    return True

# -------------------------------------------- official records + bad 34 set
records = json.load(open(os.path.join(BUNDLE, "data", "records.json")))
sizes = {}
for k, v in sorted(records.items()):
    pts = [tuple(p) for p in v]
    nn = int(re.sub(r"\D", "", k))
    val = is_valid(pts)
    sizes[nn] = (len(pts), val)
rep("official_record_sizes_and_validity", sizes)
rep("official_sizes_match_note",
    [sizes[n][0] for n in (7, 8, 9, 10, 11, 12)] == [21, 23, 26, 28, 31, 33]
    and all(sizes[n][1] for n in (7, 8, 9, 10, 11, 12)))

bad34 = [tuple(p) for p in json.load(open(os.path.join(BUNDLE, "code", "out", "s12_bad34.json")))]
rep("bad34_rejected", not is_valid(bad34))

# min |det| over the published 33-set (edge-of-degeneracy claim for n<=12)
s12 = [tuple(p) for p in records[sorted(records.keys())[-1]] ] if False else None
rec12 = [tuple(p) for p in records[[k for k in records if "12" in k][0]]]
L12 = [(x, y, z, x*x+y*y+z*z, 1) for (x, y, z) in rec12]
m12 = None
for combo in itertools.combinations(range(len(rec12)), 5):
    d = abs(det5_perm([L12[i] for i in combo]))
    assert d != 0
    m12 = d if m12 is None else min(m12, d)
rep("record12_min_abs_det", m12)

# ------------------------- saturation of the 33-set: all 8 translates
t0 = time.time()
sat = {}
for shift in itertools.product((0, 1), repeat=3):
    shifted = [tuple(c + s for c, s in zip(p, shift)) for p in rec12]
    assert all(0 <= c <= 12 for p in shifted for c in p)
    sat["shift" + "".join(map(str, shift))] = len(addable_cells(shifted))
rep("record33_translate_addable_cells", sat)
rep("record33_all_translates_saturated", all(v == 0 for v in sat.values()))
rep("translate_scan_secs", round(time.time() - t0, 1))

# ----------------------------------------------------- mutation testing (mine)
def mutated_ok(pts):
    """True iff a checker with range+distinct+int guards would ACCEPT."""
    if len(set(map(tuple, map(tuple, pts)))) != len(pts):
        return False
    for p in pts:
        if len(p) != 3 or any(not isinstance(c, int) or not 0 <= c < 13 for c in p):
            return False
    return is_valid([tuple(p) for p in pts])

Slist = [list(p) for p in S]
muts = {
    "duplicate_point": Slist[:-1] + [Slist[0]],
    "coord_13": [[13, Slist[0][1], Slist[0][2]]] + Slist[1:],
    "coord_negative": [[-1, Slist[0][1], Slist[0][2]]] + Slist[1:],
    "coord_float": [[float(Slist[0][0]), Slist[0][1], Slist[0][2]]] + Slist[1:],
    "append_center": Slist + [[6, 6, 6]],
    "replace_with_center": Slist[1:] + [[6, 6, 6]],
    "append_coplanar_cell_1_8_0": Slist + [[1, 8, 0]],
}
mut_res = {k: (not mutated_ok(v)) for k, v in muts.items()}
rep("mutations_all_rejected", mut_res)

# (1,8,0) must be in range and complete a *coplanar* zero 5-subset
u = (1, 8, 0)
lu = (1, 8, 0, 1 + 64 + 0)
quads = np.array(list(itertools.combinations(range(36), 4)), dtype=np.int64)
dz = dets4_for_cell(L4S, quads, lu)
zq = [tuple(S[i] for i in quads[j]) for j in np.nonzero(dz == 0)[0]]
rep("cell_1_8_0_zero_quads", zq)

# ------------------------------------------------------------ file identities
def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

cert = os.path.join(BUNDLE, "certificates", "record36_centralsym.json")
found = os.path.join(BUNDLE, "runs", "central-symmetric", "main-run", "FOUND36_sym.json")
cand = os.path.join(BUNDLE, "certificates", "candidate36_central-symmetric.txt")
rep("cert_sha256", sha(cert))
rep("cert_sha_matches_note",
    sha(cert) == "333d36ece36e3d845cd2f5bb26e5460f78d881c00418c92cae8bd5215ab0629a")
rep("cert_byteident_FOUND36", sha(found) == sha(cert))
rep("cert_byteident_candidate36", sha(cand) == sha(cert))
cert_pts = sorted(tuple(p) for p in json.load(open(cert)))
rep("cert_points_equal_tex_list", cert_pts == sorted(S))

# ----------------------------------------- quoted code verbatim + line count
code_block = next(b for b in blocks if "def check(points" in b)
code_lines = code_block.strip("\n").split("\n")
rep("tex_code_line_count", len(code_lines))
real = open(os.path.join(BUNDLE, "code", "check_cert.py"), encoding="utf-8").read().split("\n")
# locate the same span in check_cert.py
start = real.index("import sys, json")
span = real[start:start + len(code_lines)]
rep("tex_code_verbatim_match", span == code_lines)

# --------------------------------------------------------- small arithmetic
rep("comb_36_5", math.comb(36, 5))
rep("bound_24_12cubed_432", 24 * 12**3 * 432)
rep("bound_lt_2_25", 24 * 12**3 * 432 < 2**25)
rep("grid_cells_2197", 13**3)
rep("trivial_upper", 4 * 13)
rep("dozens_of_35s_total", 20 + 30 + 47 + 1)

# --------------------------------------------------------------- timestamps
def ts(epoch):
    return datetime.fromtimestamp(epoch).strftime("%Y-%m-%d %H:%M:%S")

stamps = {
    "centralsym_smoke_updated(found34 ~4s before)": ts(1781234100),
    "baseline_smoke_start": ts(1781234232),
    "baseline_smoke_34_t53.8": ts(1781234232 + 54),
    "baseline_main_start": ts(1781234790),
    "baseline_main_34_t47.2": ts(1781234790 + 47),
    "baseline_main_35_t538.2": ts(1781234790 + 538),
    "centralsym_main_updated(36 found at 840.9s)": ts(1781238559),
    "f13_seeded_start": ts(1781238186),
    "blockerrepair_last_update": ts(1781238598),
}
for k, v in stamps.items():
    rep("epoch_" + k, v)

print()
print("REFEREE RECOMPUTE COMPLETE")
json.dump(report, open(os.path.join(HERE, "referee_recompute_report.json"), "w"), indent=1, default=str)
