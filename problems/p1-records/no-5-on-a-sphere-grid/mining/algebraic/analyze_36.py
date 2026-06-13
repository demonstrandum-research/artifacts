#!/usr/bin/env python3
"""Deep algebraic structure probe of the 36-point record set (and the seven 35s).

All arithmetic exact (int / GF(p) elimination). Outputs JSON to stdout.

Probes:
  A. central symmetry / d-vector structure about c=(6,6,6)
  B. vanishing ideal: ranks of monomial evaluation matrices deg<=1..4 over Q and F_13
     (also in lifted (x,y,z,w)-space, deg<=2, where w = x^2+y^2+z^2)
  C. layer profiles, parity classes, surface counts
  D. mod-13 norm/sum distributions; det distribution mod 13
  E. cube-symmetry stabilizer (48 isometries fixing the center)
  F. lines with 3 collinear points; coplanar 4-subsets count
"""
import json, os, sys
from itertools import combinations
from collections import Counter
from math import comb

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"

def lift(p):
    x, y, z = p
    return (x, y, z, x*x + y*y + z*z)

def det5(L, idx):
    p = L[idx[0]]
    (a0,a1,a2,a3),(b0,b1,b2,b3),(c0,c1,c2,c3),(d0,d1,d2,d3) = \
        [tuple(L[i][k]-p[k] for k in range(4)) for i in idx[1:]]
    return ((a0*b1-a1*b0)*(c2*d3-c3*d2) - (a0*b2-a2*b0)*(c1*d3-c3*d1)
          + (a0*b3-a3*b0)*(c1*d2-c2*d1) + (a1*b2-a2*b1)*(c0*d3-c3*d0)
          - (a1*b3-a3*b1)*(c0*d2-c2*d0) + (a2*b3-a3*b2)*(c0*d1-c1*d0))

# ---------- exact rank over Q (fraction-free) and over GF(p) ----------
def rank_Q(rows):
    """Exact rank of integer matrix over Q via fraction-free elimination."""
    M = [list(r) for r in rows]
    m, n = len(M), len(M[0])
    rank, r = 0, 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(r + 1, m):
            if M[i][c]:
                f1, f2 = M[r][c], M[i][c]
                M[i] = [f1 * M[i][j] - f2 * M[r][j] for j in range(n)]
                from math import gcd
                g = 0
                for v in M[i]:
                    g = gcd(g, v)
                if g > 1:
                    M[i] = [v // g for v in M[i]]
        r += 1
        rank += 1
        if r == m:
            break
    return rank

def rank_modp(rows, p):
    M = [[v % p for v in r] for r in rows]
    m, n = len(M), len(M[0])
    rank, r = 0, 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(m):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(n)]
        r += 1
        rank += 1
        if r == m:
            break
    return rank

def monomials_deg(nvars, maxdeg):
    """exponent tuples with total degree <= maxdeg"""
    out = []
    def rec(prefix, remaining, left):
        if remaining == 0:
            out.append(tuple(prefix))
            return
        for e in range(left + 1):
            rec(prefix + [e], remaining - 1, left - e)
    rec([], nvars, maxdeg)
    return out

def eval_monos(pts, monos):
    rows = []
    for p in pts:
        row = []
        for ex in monos:
            v = 1
            for xi, e in zip(p, ex):
                v *= xi ** e
            row.append(v)
        rows.append(row)
    return rows

def analyze(pts, name, full_dets=True):
    R = {"name": name, "size": len(pts)}
    c2 = (12, 12, 12)  # 2*center
    S = set(pts)
    pairs = sum(1 for p in pts if tuple(c2[k]-p[k] for k in range(3)) in S and p < tuple(c2[k]-p[k] for k in range(3)))
    fixed = sum(1 for p in pts if tuple(c2[k]-p[k] for k in range(3)) == p)
    R["antipodal_pairs_about_666"] = pairs
    R["fixed_center_points"] = fixed

    # d-vectors (only meaningful if perfectly symmetric)
    if 2 * pairs + fixed == len(pts):
        ds = sorted(tuple(p[k]-6 for k in range(3)) for p in pts
                    if p > tuple(c2[k]-p[k] for k in range(3)))
        R["d_vectors"] = ds
        R["d_norms"] = sorted(d[0]**2+d[1]**2+d[2]**2 for d in ds)
        R["d_norms_mod13"] = sorted((d[0]**2+d[1]**2+d[2]**2) % 13 for d in ds)
        R["d_norm_counter"] = dict(Counter(d[0]**2+d[1]**2+d[2]**2 for d in ds))

    # vanishing ideal ranks
    ideal = {}
    for deg in (1, 2, 3, 4):
        monos = monomials_deg(3, deg)
        rows = eval_monos(pts, monos)
        nm = len(monos)
        rq = rank_Q(rows)
        r13 = rank_modp(rows, 13)
        ideal[f"deg{deg}"] = {"n_monomials": nm, "rank_Q": rq, "indep_forms_vanishing_Q": nm - rq,
                              "rank_F13": r13, "forms_vanishing_F13": nm - r13}
    # lifted space deg<=2 (15 monomials in x,y,z,w); w=x^2+y^2+z^2 gives 1 guaranteed relation
    lpts = [lift(p) for p in pts]
    monos4 = monomials_deg(4, 2)
    rows4 = eval_monos(lpts, monos4)
    ideal["lifted_deg2"] = {"n_monomials": len(monos4),
                            "rank_Q": rank_Q(rows4),
                            "rank_F13": rank_modp(rows4, 13),
                            "note": "1 relation (w - x^2-y^2-z^2) guaranteed; deficiency beyond rank 14 is structure"}
    R["vanishing"] = ideal

    # layer profiles
    R["layer_profiles"] = {ax: sorted(Counter(p[i] for p in pts).values(), reverse=True)
                           for i, ax in enumerate("xyz")}
    R["layers_used"] = {ax: len(set(p[i] for p in pts)) for i, ax in enumerate("xyz")}
    R["parity_classes"] = sorted(Counter(tuple(v % 2 for v in p) for p in pts).values(), reverse=True)
    R["surface_points"] = sum(1 for p in pts if any(v in (0, 12) for v in p))
    R["norm_mod13_distribution"] = dict(sorted(Counter((p[0]**2+p[1]**2+p[2]**2) % 13 for p in pts).items()))
    R["sum_mod13_distribution"] = dict(sorted(Counter((p[0]+p[1]+p[2]) % 13 for p in pts).items()))

    # cube-symmetry stabilizer about center (48 elements)
    import itertools as it
    stab = []
    for perm in it.permutations(range(3)):
        for signs in it.product((1, -1), repeat=3):
            def img(p, perm=perm, signs=signs):
                d = tuple(p[k]-6 for k in range(3))
                d2 = tuple(signs[k]*d[perm[k]] for k in range(3))
                return tuple(d2[k]+6 for k in range(3))
            if all(img(p) in S for p in pts):
                stab.append((perm, signs))
    R["cube_stabilizer_order"] = len(stab)
    R["cube_stabilizer"] = [[list(p), list(s)] for p, s in stab]

    # collinear triples / lines with 3 points
    coll = 0
    for a, b, cc in combinations(pts, 3):
        u = tuple(b[k]-a[k] for k in range(3)); v = tuple(cc[k]-a[k] for k in range(3))
        cross = (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
        if cross == (0, 0, 0):
            coll += 1
    R["collinear_triples"] = coll

    # coplanar quadruples (legal but structural)
    cop = 0
    for q in combinations(range(len(pts)), 4):
        a = pts[q[0]]
        u = [tuple(pts[i][k]-a[k] for k in range(3)) for i in q[1:]]
        det = (u[0][0]*(u[1][1]*u[2][2]-u[1][2]*u[2][1])
             - u[0][1]*(u[1][0]*u[2][2]-u[1][2]*u[2][0])
             + u[0][2]*(u[1][0]*u[2][1]-u[1][1]*u[2][0]))
        if det == 0:
            cop += 1
    R["coplanar_quadruples"] = cop

    if full_dets:
        L = lpts
        n5 = 0; z13 = 0; z169 = 0; mind = None
        absdets = Counter()
        for idx in combinations(range(len(pts)), 5):
            d = det5(L, idx)
            n5 += 1
            ad = abs(d)
            if mind is None or ad < mind:
                mind = ad
            if d % 13 == 0:
                z13 += 1
                if d % 169 == 0:
                    z169 += 1
        R["dets"] = {"n_5subsets": n5, "min_abs_det": mind,
                     "zero_mod13": z13, "expected_mod13": round(n5/13, 1),
                     "zero_mod169": z169, "expected_mod169": round(n5/169, 1)}
    return R

def main():
    out = []
    cert = json.load(open(os.path.join(BASE, "certificates", "record36_centralsym.json")))
    pts36 = sorted(tuple(p) for p in cert)
    out.append(analyze(pts36, "record36_centralsym"))
    # the 35s
    import glob
    for f in sorted(glob.glob(os.path.join(BASE, "certificates", "record35_*.json"))):
        pts = sorted(tuple(p) for p in json.load(open(f)))
        out.append(analyze(pts, os.path.basename(f), full_dets=False))
    print(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
