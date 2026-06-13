#!/usr/bin/env python3
"""Exact integer certificate checker for the no-5-on-a-sphere grid problem (AlphaEvolve 6.60).

A point set S in {0..n-1}^3 is VALID iff every 5-subset {p1..p5} has nonzero determinant
of the 4x4 integer matrix with rows L(p_i)-L(p_1), i=2..5, where L(p)=(x,y,z,x^2+y^2+z^2).
Pure integer arithmetic only (max |det| < 2^25 for n=13); no floats anywhere.

Usage: python check_cert.py points.json [n]   # points.json = JSON list of [x,y,z]; default n=13
Exit code 0 = VALID, 1 = INVALID.
"""
import sys, json
from itertools import combinations

def check(points, n=13):
    """Return (True, None) if valid, else (False, reason-or-offending-5-subset)."""
    pts = [tuple(p) for p in points]
    if len(set(pts)) != len(pts):
        return False, "duplicate points"
    if any(len(p) != 3 or any(not isinstance(c, int) or not 0 <= c < n for c in p) for p in pts):
        return False, "non-integer or out-of-range coordinate"
    L = [(x, y, z, x * x + y * y + z * z) for (x, y, z) in pts]
    for idx in combinations(range(len(pts)), 5):
        p = L[idx[0]]
        (a0, a1, a2, a3), (b0, b1, b2, b3), (c0, c1, c2, c3), (d0, d1, d2, d3) = \
            [tuple(L[i][k] - p[k] for k in range(4)) for i in idx[1:]]
        det = ((a0*b1 - a1*b0) * (c2*d3 - c3*d2) - (a0*b2 - a2*b0) * (c1*d3 - c3*d1)
             + (a0*b3 - a3*b0) * (c1*d2 - c2*d1) + (a1*b2 - a2*b1) * (c0*d3 - c3*d0)
             - (a1*b3 - a3*b1) * (c0*d2 - c2*d0) + (a2*b3 - a3*b2) * (c0*d1 - c1*d0))
        if det == 0:
            return False, [pts[i] for i in idx]
    return True, None

if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        pts = json.load(f)
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    ok, why = check(pts, n)
    print(f"VALID m={len(pts)} n={n}" if ok else f"INVALID m={len(pts)} n={n}: {why}")
    sys.exit(0 if ok else 1)
