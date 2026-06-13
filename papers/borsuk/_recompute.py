# _recompute.py — independent exact-arithmetic recomputation of every number
# quoted in note.tex (witnesses A, B, C for the disproof of Conjecture 3 of
# arXiv:2508.20009).  Pure Python 3 standard library; Fractions everywhere on
# the accept path.  Run:  python _recompute.py   -> expect "ALL CHECKS PASS".
#
# Sources being cross-checked:
#   problems/p3-moonshot/borsuk/lean/Borsuk/*.lean   (witness A, formalized)
#   problems/p3-moonshot/gate0-results.json          (witnesses B, C, vetted)
from fractions import Fraction
from itertools import combinations
from math import gcd

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        ok = False

# ---------------------------------------------------------------- Witness A
SA = [(0, 0), (1, 0), (0, 1), (3, 5)]

# A1: all 6 pairwise differences primitive
diffs = [(q[0]-p[0], q[1]-p[1]) for p, q in combinations(SA, 2)]
check("A1: |SA| = 4, six pairwise differences", len(SA) == 4 and len(diffs) == 6)
check("A2: all six differences primitive (gcd = 1)",
      all(gcd(abs(dx), abs(dy)) == 1 for dx, dy in diffs))
# and therefore the segment-lattice-point count gcd+1 = 2 for each pair, so
# diam_Z(SA) = 1 and beta_Z(SA) = |SA| = 4 = 2^2 (singleton-parts argument).

# A3: the H-representation of conv(SA):  x>=0, y>=0, 5x-2y<=5, 3y-4x<=3
HS_A = [(1, 0, 0, +1),   # +x >= 0   encoded (a,b,c,sense): a*x+b*y >= c if sense=+1
        (0, 1, 0, +1),   # +y >= 0
        (5, -2, 5, -1),  # 5x-2y <= 5
        (-4, 3, 3, -1)]  # 3y-4x <= 3
def in_halfspaces(p, hs):
    x, y = p
    for a, b, c, s in hs:
        v = a*x + b*y
        if s == +1 and not (v >= c): return False
        if s == -1 and not (v <= c): return False
    return True
check("A3: all four points of SA satisfy the four halfspaces",
      all(in_halfspaces(p, HS_A) for p in SA))
# each inequality is tight on exactly the claimed edge pair => genuine edges
def tight_set(hs, pts):
    a, b, c, s = hs
    return sorted(p for p in pts if a*p[0] + b*p[1] == c)
check("A4: x=0 tight exactly on {(0,0),(0,1)}",
      tight_set(HS_A[0], SA) == [(0, 0), (0, 1)])
check("A5: y=0 tight exactly on {(0,0),(1,0)}",
      tight_set(HS_A[1], SA) == [(0, 0), (1, 0)])
check("A6: 5x-2y=5 tight exactly on {(1,0),(3,5)}",
      tight_set(HS_A[2], SA) == [(1, 0), (3, 5)])
check("A7: 3y-4x=3 tight exactly on {(0,1),(3,5)}",
      tight_set(HS_A[3], SA) == [(0, 1), (3, 5)])

# A8: integer points of the halfspace intersection = the 7 claimed points
HULL7 = [(0, 0), (1, 0), (0, 1), (1, 1), (1, 2), (2, 3), (3, 5)]
enum = sorted(p for x in range(-10, 21) for y in range(-10, 21)
              if in_halfspaces(p := (x, y), HS_A))
# (box is generous: halfspaces force 0<=x<=3, 0<=y<=5 -- re-derive:)
check("A8a: halfspaces imply 0<=x<=3, 0<=y<=5 on the enumeration box",
      all(0 <= x <= 3 and 0 <= y <= 5 for x, y in enum))
check("A8b: integer points of H-representation = the 7 listed points",
      enum == sorted(HULL7))

# A9: every one of the 7 points is a convex combination of SA over Q (exact),
#     so H-polytope = conv(SA) on lattice points.  Certificates from
#     HullSeven.lean: (1,1)=2/5*(0,0)+2/5*(1,0)+1/5*(3,5);
#     (1,2)=1/3*(0,0)+1/3*(0,1)+1/3*(3,5); (2,3)=1/5*(0,0)+1/5*(1,0)+3/5*(3,5).
certs = {
    (1, 1): [(Fraction(2, 5), (0, 0)), (Fraction(2, 5), (1, 0)), (Fraction(1, 5), (3, 5))],
    (1, 2): [(Fraction(1, 3), (0, 0)), (Fraction(1, 3), (0, 1)), (Fraction(1, 3), (3, 5))],
    (2, 3): [(Fraction(1, 5), (0, 0)), (Fraction(1, 5), (1, 0)), (Fraction(3, 5), (3, 5))],
}
def conv_ok(target, cert):
    if any(l < 0 for l, _ in cert): return False
    if sum(l for l, _ in cert) != 1: return False
    sx = sum(l * Fraction(p[0]) for l, p in cert)
    sy = sum(l * Fraction(p[1]) for l, p in cert)
    return (sx, sy) == (Fraction(target[0]), Fraction(target[1]))
check("A9: exact convex-combination certificates for (1,1),(1,2),(2,3)",
      all(conv_ok(t, c) for t, c in certs.items()))
# the other four of HULL7 are points of SA themselves:
check("A10: remaining 4 of the 7 points are points of SA",
      set(HULL7) - set(certs) == set(SA))

# A11: 7 is not a perfect square, and |[0,m]^2 cap Z^2| = (m+1)^2
check("A11: (m+1)^2 != 7 for 0<=m<=10 and (m+1)^2 monotone past 7",
      all((m+1)**2 != 7 for m in range(11)) and 2**2 == 4 < 7 < 9 == 3**2)

# ---------------------------------------------------------------- Witness B
T = [(0, 1), (1, 0), (1, 1), (2, 2)]
diffsB = [(q[0]-p[0], q[1]-p[1]) for p, q in combinations(T, 2)]
check("B1: all six differences of T primitive",
      all(gcd(abs(dx), abs(dy)) == 1 for dx, dy in diffsB))

# B2: hull of T is the triangle with vertices (0,1),(1,0),(2,2); (1,1) interior.
# Triangle halfplanes (computed from the three edges, integer normal forms):
#   edge (0,1)-(1,0): x + y >= 1 ;  edge (1,0)-(2,2): 2x - y <= 2 ;
#   edge (2,2)-(0,1): x - 2y >= -2  i.e. 2y - x <= 2.
HS_B = [(1, 1, 1, +1), (2, -1, 2, -1), (-1, 2, 2, -1)]
check("B2a: all of T satisfies the triangle halfplanes",
      all(in_halfspaces(p, HS_B) for p in T))
check("B2b: (1,1) strictly interior (all three inequalities strict)",
      all((a*1 + b*1 > c) if s == +1 else (a*1 + b*1 < c) for a, b, c, s in HS_B))
enumB = sorted(p for x in range(-5, 8) for y in range(-5, 8)
               if in_halfspaces(p := (x, y), HS_B))
check("B3: conv(T) cap Z^2 = T (full lattice set witness)", enumB == sorted(T))
# vertices of the hull: a point of T is a vertex iff it is NOT a convex comb of
# the others; (1,1) = 1/2*(0,1) + ... check: (1,1) = ((0,1)+(2,2)+(1,0))/3
check("B4: (1,1) = centroid of the other three (so hull has 3 vertices)",
      conv_ok((1, 1), [(Fraction(1, 3), (0, 1)), (Fraction(1, 3), (1, 0)),
                       (Fraction(1, 3), (2, 2))]))
# shoelace area of triangle (0,1),(1,0),(2,2)
v0, v1, v2 = (0, 1), (1, 0), (2, 2)
area2 = abs((v1[0]-v0[0])*(v2[1]-v0[1]) - (v2[0]-v0[0])*(v1[1]-v0[1]))
check("B5: area of conv(T) = 3/2", Fraction(area2, 2) == Fraction(3, 2))
check("B6: lattice count 4 forces m=1 ((m+1)^2=4); [0,1]^2 has area 1 != 3/2",
      (1+1)**2 == 4 and Fraction(1) != Fraction(3, 2))

# ---------------------------------------------------------------- Witness C
C = [(0, 2, 2), (1, 0, 1), (1, 1, 2), (1, 2, 2),
     (2, 1, 1), (2, 1, 2), (2, 2, 1), (3, 1, 3)]
check("C1: |C| = 8 and all 28 pairwise differences primitive",
      len(C) == 8 and all(
          gcd(gcd(abs(q[0]-p[0]), abs(q[1]-p[1])), abs(q[2]-p[2])) == 1
          for p, q in combinations(C, 2)))

# C2: exact H-representation of conv(C): every plane through 3 affinely
# independent points of C that supports C (all 8 points on one side).
def cross(u, v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def sub(p, q): return (p[0]-q[0], p[1]-q[1], p[2]-q[2])
def dot(u, v): return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]
facets = set()
for p, q, r in combinations(C, 3):
    n = cross(sub(q, p), sub(r, p))
    if n == (0, 0, 0):
        continue
    g = gcd(gcd(abs(n[0]), abs(n[1])), abs(n[2]))
    n = (n[0]//g, n[1]//g, n[2]//g)
    c0 = dot(n, p)
    vals = [dot(n, s) for s in C]
    if all(v <= c0 for v in vals):
        facets.add((n, c0))            # n.x <= c0 supports C
    elif all(v >= c0 for v in vals):
        facets.add(((-n[0], -n[1], -n[2]), -c0))
facets = sorted(facets)
check("C2a: supporting planes found (hull is full-dimensional)", len(facets) >= 4)
def in_hullC(p):
    return all(dot(n, p) <= c0 for n, c0 in facets)
check("C2b: all 8 points of C inside all supporting halfspaces",
      all(in_hullC(p) for p in C))
xs = [p[0] for p in C]; ys = [p[1] for p in C]; zs = [p[2] for p in C]
enumC = sorted(p for x in range(min(xs), max(xs)+1)
               for y in range(min(ys), max(ys)+1)
               for z in range(min(zs), max(zs)+1)
               if in_hullC(p := (x, y, z)))
# NOTE (soundness of the enumeration): if conv(C) is full-dimensional, every
# facet of conv(C) is the hull of the points of C lying on it, hence its plane
# is spanned by some affinely independent triple of points of C; so every facet
# inequality of conv(C) occurs among `facets`, and the intersection of the
# collected halfspaces is exactly conv(C) (it contains conv(C) since each is
# supporting, and is contained in the facet intersection = conv(C)).  The box
# restriction is sound because conv(C) lies in the coordinate bounding box of
# C (coordinates of convex combinations are bounded by the min/max).
# Verify full-dimensionality: rank of {p - C[0] : p in C} is 3.
fulldim = any(
    dot(sub(p, C[0]), cross(sub(q, C[0]), sub(r, C[0]))) != 0
    for p, q, r in combinations(C[1:], 3))
check("C2c: conv(C) is full-dimensional (some 4 points affinely independent)",
      fulldim)
check("C3: conv(C) cap Z^3 = C (full lattice set witness, 8 points)",
      enumC == sorted(C))

# C4: exact volume of conv(C) = 5/2 -- pure integer arithmetic throughout.
# Cone from the polytope point b = C[0] over every facet: the cones over the
# facets of a convex polytope, apexed at any point of the polytope, cover it
# with pairwise measure-zero overlaps (facets through b give degenerate,
# zero-volume cones), so vol = (1/6) * sum over facets of |det| over a fan
# triangulation of each facet polygon.  Each facet polygon is recovered in
# exact integer arithmetic: project the facet's points to 2D by dropping the
# coordinate where the facet normal is largest (injective on the facet plane),
# take the 2D convex hull by Andrew's monotone chain (integer cross products),
# and fan-triangulate the hull cycle.
def hull2d(pts):
    """Andrew monotone chain; integer arithmetic; returns CCW hull cycle."""
    pts = sorted(set(pts))
    if len(pts) <= 2:
        return pts
    def cr(o, a, q):
        return (a[0]-o[0])*(q[1]-o[1]) - (a[1]-o[1])*(q[0]-o[0])
    lo, up = [], []
    for p in pts:
        while len(lo) >= 2 and cr(lo[-2], lo[-1], p) <= 0:
            lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(up) >= 2 and cr(up[-2], up[-1], p) <= 0:
            up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]

b = C[0]
vol6 = 0
for n, c0 in facets:
    F = [p for p in C if dot(n, p) == c0]
    if len(F) < 3:
        continue
    k = max(range(3), key=lambda i: abs(n[i]))   # drop coordinate k
    ij = [i for i in range(3) if i != k]
    proj = {}
    for p in F:
        proj[(p[ij[0]], p[ij[1]])] = p           # injective: n[k] != 0
    cyc = hull2d(list(proj))
    P3 = [proj[q] for q in cyc]
    for i in range(1, len(P3)-1):
        d6 = dot(sub(P3[0], b), cross(sub(P3[i], b), sub(P3[i+1], b)))
        vol6 += abs(d6)
check("C4: volume of conv(C) = 5/2 (exact integer arithmetic)",
      Fraction(vol6, 6) == Fraction(5, 2))

# C5: pair-sum coincidence invariant.
# I(S) := #{ {{p,q},{r,s}} : unordered pairs of DISTINCT points, {p,q} != {r,s},
#            p+q = r+s }, an invariant of injective affine maps x -> Ax+t
# (A invertible: p+q=r+s <=> (Ap+t)+(Aq+t)=(Ar+t)+(As+t)).
def pair_sum_invariant(S):
    pairs = list(combinations(S, 2))
    sums = {}
    for p, q in pairs:
        s = (p[0]+q[0], p[1]+q[1], p[2]+q[2])
        sums[s] = sums.get(s, 0) + 1
    return sum(k*(k-1)//2 for k in sums.values())
cube8 = [(x, y, z) for x in (0, 1) for y in (0, 1) for z in (0, 1)]
iC, icube = pair_sum_invariant(C), pair_sum_invariant(cube8)
check(f"C5: pair-sum invariant: C -> {iC} (=2), {{0,1}}^3 -> {icube} (=12)",
      iC == 2 and icube == 12)

# C6: cube lattice counts in d=3: m=0 -> 1, m=1 -> 8, m>=2 -> >= 27 > 8
check("C6: (m+1)^3 = 1, 8, 27, ... so only m=1 matches count 8",
      (0+1)**3 == 1 and (1+1)**3 == 8 and (2+1)**3 == 27 and
      all((m+1)**3 > 8 for m in range(2, 12)))

print()
print("ALL CHECKS PASS" if ok else "SOME CHECKS FAILED")
raise SystemExit(0 if ok else 1)
