"""Literature-lens analysis: growth-law fits for C(n) + template-compatibility stats.

Outputs mining/literature/fit_results.json and prints a report.
"""
import json, math, itertools, random, os
from fractions import Fraction

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # .../no-5-on-a-sphere-grid/mining
ROOT = os.path.dirname(BASE)
CERT = os.path.join(ROOT, "certificates")
POOL34 = os.path.join(ROOT, "runs", "central-symmetric", "main-run", "pool_34.jsonl")

# ---------------- 1. Growth fits ----------------
# Known best lower bounds: PatternBoost (n=3..6), AlphaEvolve (7..12), ours (13).
ns = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
cs = [8, 11, 14, 18, 21, 23, 26, 28, 31, 33, 36]

def linfit(xs, ys):
    n = len(xs)
    sx, sy = sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    a = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    b = (sy - a * sx) / n
    resid = [y - (a * x + b) for x, y in zip(xs, ys)]
    sse = sum(r * r for r in resid)
    return a, b, sse, resid

def powfit(xs, ys):
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    a, b, sse, _ = linfit(lx, ly)
    return a, math.exp(b), sse  # y = c * x^alpha, alpha=a, c=e^b

results = {}
for label, lo in [("all_n3_13", 0), ("record_regime_n7_13", 4)]:
    xs, ys = ns[lo:], cs[lo:]
    a, b, sse, resid = linfit(xs, ys)
    alpha, c, _ = powfit(xs, ys)
    results[label] = {
        "linear": {"slope": round(a, 4), "intercept": round(b, 4),
                   "pred14": round(a * 14 + b, 2), "pred15": round(a * 15 + b, 2),
                   "max_abs_resid": round(max(abs(r) for r in resid), 3)},
        "power": {"alpha": round(alpha, 4), "c": round(c, 4),
                  "pred14": round(c * 14 ** alpha, 2), "pred15": round(c * 15 ** alpha, 2)},
    }
diffs = [cs[i + 1] - cs[i] for i in range(len(cs) - 1)]
results["diffs"] = diffs
results["density_ratios"] = {n: round(c / n, 3) for n, c in zip(ns, cs)}

# ---------------- 2. Structure of record36 ----------------
with open(os.path.join(CERT, "record36_centralsym.json")) as f:
    S36 = [tuple(p) for p in json.load(f)]
assert len(S36) == 36 and len(set(S36)) == 36

def lift(p):
    x, y, z = p
    return (x, y, z, x * x + y * y + z * z)

def det4(rows):
    # exact 4x4 determinant by cofactor on first row, with 3x3 cofactors
    def det3(m):
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
    d = 0
    for j in range(4):
        minor = [[rows[i][k] for k in range(4) if k != j] for i in range(1, 4)]
        d += (-1) ** j * rows[0][j] * det3(minor)
    return d

st = {}
# central symmetry about (6,6,6)
sset = set(S36)
st["centrally_symmetric"] = all((12 - x, 12 - y, 12 - z) in sset for (x, y, z) in S36)
# layer profiles
for ax in range(3):
    prof = [0] * 13
    for p in S36:
        prof[p[ax]] += 1
    st[f"layer_profile_axis{ax}"] = prof

# collinear triples and plane saturation
def collinear(p, q, r):
    ux, uy, uz = q[0] - p[0], q[1] - p[1], q[2] - p[2]
    vx, vy, vz = r[0] - p[0], r[1] - p[1], r[2] - p[2]
    return (uy * vz - uz * vy == 0) and (uz * vx - ux * vz == 0) and (ux * vy - uy * vx == 0)

def plane_stats(S):
    """Return (#collinear triples, dict plane->count restricted to planes with >=4 pts)."""
    from math import gcd
    coll = 0
    planes = {}
    n = len(S)
    for i, j, k in itertools.combinations(range(n), 3):
        p, q, r = S[i], S[j], S[k]
        ux, uy, uz = q[0] - p[0], q[1] - p[1], q[2] - p[2]
        vx, vy, vz = r[0] - p[0], r[1] - p[1], r[2] - p[2]
        nx, ny, nz = uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx
        if nx == 0 and ny == 0 and nz == 0:
            coll += 1
            continue
        g = gcd(gcd(abs(nx), abs(ny)), abs(nz))
        nx, ny, nz = nx // g, ny // g, nz // g
        if (nx, ny, nz) < (0, 0, 0) or (nx < 0) or (nx == 0 and ny < 0) or (nx == 0 and ny == 0 and nz < 0):
            nx, ny, nz = -nx, -ny, -nz
        off = nx * p[0] + ny * p[1] + nz * p[2]
        planes.setdefault((nx, ny, nz, off), set()).update((i, j, k))
    plane_sizes = {}
    for key, pts in planes.items():
        if len(pts) >= 4:
            plane_sizes[key] = len(pts)
    return coll, plane_sizes

coll36, planes36 = plane_stats(S36)
st["collinear_triples"] = coll36
from collections import Counter
psizes = Counter(planes36.values())
st["planes_with_4pts"] = psizes.get(4, 0)
st["planes_with_5plus"] = sum(v for k, v in psizes.items() if k >= 5)  # must be 0
st["max_points_on_a_plane"] = max(psizes) if psizes else 3

# mod-13 cap test: count 5-subsets with lifted det == 0 mod 13
L = [lift(p) for p in S36]
zero_mod13 = 0
total5 = 0
for c in itertools.combinations(range(36), 5):
    p0 = L[c[0]]
    rows = [[L[c[i]][k] - p0[k] for k in range(4)] for i in range(1, 5)]
    total5 += 1
    if det4(rows) % 13 == 0:
        zero_mod13 += 1
st["five_subsets_total"] = total5
st["five_subsets_det_zero_mod13"] = zero_mod13
st["is_F13_cap"] = (zero_mod13 == 0)

# quadric rank over Q and over F_13: monomials [1,x,y,z,x2,y2,z2,xy,xz,yz]
def monrow(p):
    x, y, z = p
    return [1, x, y, z, x * x, y * y, z * z, x * y, x * z, y * z]

def rank_modp(rows, p):
    m = [[v % p for v in r] for r in rows]
    rank, ncols = 0, len(m[0])
    for col in range(ncols):
        piv = next((r for r in range(rank, len(m)) if m[r][col] % p != 0), None)
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        inv = pow(m[rank][col], p - 2, p)
        m[rank] = [(v * inv) % p for v in m[rank]]
        for r in range(len(m)):
            if r != rank and m[r][col]:
                f = m[r][col]
                m[r] = [(m[r][k] - f * m[rank][k]) % p for k in range(ncols)]
        rank += 1
    return rank

def rank_q(rows):
    m = [[Fraction(v) for v in r] for r in rows]
    rank, ncols = 0, len(m[0])
    for col in range(ncols):
        piv = next((r for r in range(rank, len(m)) if m[r][col] != 0), None)
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        m[rank] = [v / m[rank][col] for v in m[rank]]
        for r in range(len(m)):
            if r != rank and m[r][col] != 0:
                f = m[r][col]
                m[r] = [m[r][k] - f * m[rank][k] for k in range(ncols)]
        rank += 1
    return rank

mon = [monrow(p) for p in S36]
st["quadric_monomial_rank_Q"] = rank_q(mon)        # 10 => no common quadric over Q
st["quadric_monomial_rank_F13"] = rank_modp(mon, 13)  # 10 => no common quadric mod 13
# cubic monomials mod 13 (20 monomials) - lies on a cubic surface iff rank < 20
def cubrow(p):
    x, y, z = p
    out = []
    for i in range(4):
        for j in range(4 - i):
            for k in range(4 - i - j):
                out.append((x ** i) * (y ** j) * (z ** k) % 13)
    return out
cub = [cubrow(p) for p in S36]
st["cubic_monomial_rank_F13"] = rank_modp(cub, 13)  # 20 => not on any cubic surface mod 13
st["n_cubic_monomials"] = len(cub[0])

# distinct coordinate values per axis (single-curve image over F13 would have <=14 points)
st["points_vs_single_curve_cap"] = {"points": 36, "max_per_curve_over_F13": 14}

results["record36_structure"] = st

# ---------------- 3. Pool-level stats (sample) ----------------
random.seed(0)
pool = []
with open(POOL34) as f:
    for line in f:
        line = line.strip()
        if line:
            pool.append([tuple(p) for p in json.loads(line)])
sample = random.sample(pool, min(150, len(pool)))
sym_cnt, coll_list, p4_list = 0, [], []
for S in sample:
    ss = set(S)
    if all((12 - x, 12 - y, 12 - z) in ss for (x, y, z) in S):
        sym_cnt += 1
    coll, plane_sizes = plane_stats(S)
    coll_list.append(coll)
    p4_list.append(sum(1 for v in plane_sizes.values() if v == 4))
results["pool34_sample"] = {
    "pool_size": len(pool), "sample": len(sample),
    "frac_centrally_symmetric": sym_cnt / len(sample),
    "collinear_triples_mean": sum(coll_list) / len(coll_list),
    "planes4_mean": sum(p4_list) / len(p4_list),
    "planes4_min": min(p4_list), "planes4_max": max(p4_list),
}

# mod-13 cap test across sample: how close are 34-sets to F13 caps?
zfrac = []
for S in sample[:40]:
    Ls = [lift(p) for p in S]
    z = 0
    t = 0
    for c in itertools.combinations(range(len(S)), 5):
        p0 = Ls[c[0]]
        rows = [[Ls[c[i]][k] - p0[k] for k in range(4)] for i in range(1, 5)]
        t += 1
        if det4(rows) % 13 == 0:
            z += 1
    zfrac.append(z / t)
results["pool34_mod13_zero_frac"] = {
    "mean": sum(zfrac) / len(zfrac), "min": min(zfrac), "max": max(zfrac), "n_sets": len(zfrac),
}

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fit_results.json")
with open(out, "w") as f:
    json.dump(results, f, indent=1)
print(json.dumps(results, indent=1))
