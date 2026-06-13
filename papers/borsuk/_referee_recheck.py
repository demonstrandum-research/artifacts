# _referee_recheck.py — hostile-referee INDEPENDENT recomputation of every
# number in papers/borsuk/note.tex.  Written 2026-06-12 by the referee agent,
# deliberately using DIFFERENT algorithms from _recompute.py:
#   * hull membership via exact Caratheodory (barycentric solves over Fraction),
#     not via H-representations;
#   * the H-representations of the note are then checked against that
#     ground truth;
#   * vertices identified by the "not in hull of the others" criterion;
#   * 3D volume by signed-tetrahedra over a divergence-style surface sum
#     derived from an independently computed facet list;
#   * full pair-sum census printed, not just the count.
# Pure stdlib.  Exits 0 iff every check passes.
from fractions import Fraction as F
from itertools import combinations
from math import gcd

fails = []
def chk(name, cond, extra=""):
    print(("PASS " if cond else "FAIL ") + name + (("  " + extra) if extra else ""))
    if not cond:
        fails.append(name)

# ---------------------------------------------------------------- helpers
def solve(M, rhs):
    """Exact Gaussian elimination; M list of rows; returns solution or None."""
    n = len(M); m = len(M[0])
    A = [[F(x) for x in row] + [F(rhs[i])] for i, row in enumerate(M)]
    piv = []
    r = 0
    for c in range(m):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        A[r] = [v / A[r][c] for v in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                A[i] = [a - A[i][c] * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == n:
            break
    # consistency
    for i in range(r, n):
        if A[i][m] != 0:
            return None
    x = [F(0)] * m
    for i, c in enumerate(piv):
        x[c] = A[i][m]
    return x

def in_hull(p, pts, dim):
    """Exact: is p in conv(pts)?  Caratheodory: some (dim+1)-subset works."""
    for sub in combinations(pts, dim + 1):
        # solve sum l_i v_i = p, sum l_i = 1, l_i >= 0
        M = [[v[k] for v in sub] for k in range(dim)] + [[1] * (dim + 1)]
        rhs = list(p) + [1]
        lam = solve(M, rhs)
        if lam is not None and all(l >= 0 for l in lam):
            # verify (solve() may return a least-squares-like artifact never,
            # but re-verify anyway: exact substitution)
            okc = all(sum(l * v[k] for l, v in zip(lam, sub)) == p[k]
                      for k in range(dim)) and sum(lam) == 1
            if okc:
                return True
    return False

def gcd_all(*xs):
    g = 0
    for x in xs:
        g = gcd(g, abs(x))
    return g

# ================================================================ WITNESS A
SA = [(0, 0), (1, 0), (0, 1), (3, 5)]
dA = [tuple(q[i] - p[i] for i in range(2)) for p, q in combinations(SA, 2)]
chk("A-1  six pairwise differences of S_A", len(dA) == 6)
chk("A-2  differences are exactly {(1,0),(0,1),(3,5),(-1,1),(2,5),(3,4)}",
    sorted(dA) == sorted([(1, 0), (0, 1), (3, 5), (-1, 1), (2, 5), (3, 4)]))
chk("A-3  all six primitive", all(gcd_all(*v) == 1 for v in dA))

# ground truth lattice points of conv(SA): exact Caratheodory over a box
boxA = [(x, y) for x in range(-3, 7) for y in range(-3, 9)]
hullA_pts = sorted(p for p in boxA if in_hull(p, SA, 2))
chk("A-4  conv(S_A) has exactly 7 lattice points (independent Caratheodory)",
    len(hullA_pts) == 7, str(hullA_pts))
chk("A-5  they are the 7 listed in the note",
    hullA_pts == sorted([(0, 0), (1, 0), (0, 1), (1, 1), (1, 2), (2, 3), (3, 5)]))
# the box is generous: every point of conv(SA) has 0<=x<=3, 0<=y<=5 (coord
# bounds of SA), so the box [-3,6]x[-3,8] certainly contains all of them.
chk("A-6  coordinate bounds of S_A: 0<=x<=3, 0<=y<=5",
    min(p[0] for p in SA) == 0 and max(p[0] for p in SA) == 3 and
    min(p[1] for p in SA) == 0 and max(p[1] for p in SA) == 5)

# now check the note's H-representation against this ground truth
def QA(p):
    x, y = p
    return x >= 0 and y >= 0 and 5 * x - 2 * y <= 5 and 3 * y - 4 * x <= 3
chk("A-7  note's Q (x>=0, y>=0, 5x-2y<=5, 3y-4x<=3) agrees with ground truth "
    "on the whole test box",
    all(QA(p) == (p in hullA_pts) for p in boxA))
chk("A-8  all 16 point/halfplane evaluations hold", all(QA(p) for p in SA))
tight = lambda f, c: sorted(p for p in SA if f(p) == c)
chk("A-9  edge incidences as claimed",
    tight(lambda p: p[0], 0) == [(0, 0), (0, 1)] and
    tight(lambda p: p[1], 0) == [(0, 0), (1, 0)] and
    tight(lambda p: 5 * p[0] - 2 * p[1], 5) == [(1, 0), (3, 5)] and
    tight(lambda p: 3 * p[1] - 4 * p[0], 3) == [(0, 1), (3, 5)])
# the note's case chase: 15x-15 <= 6y <= 8x+6  =>  x <= 3
chk("A-10 implication 5x-2y<=5 & 3y-4x<=3 => 15x-15<=6y<=8x+6 => 7x<=21",
    all((15 * x - 15 <= 6 * y <= 8 * x + 6)
        for x in range(0, 4) for y in range(0, 6)
        if 5 * x - 2 * y <= 5 and 3 * y - 4 * x <= 3) and (15 * 4 - 15 > 8 * 4 + 6))
# convex-combination certificates quoted in the note
chk("A-11 (1,1)=2/5(0,0)+2/5(1,0)+1/5(3,5)",
    (F(2,5)*0 + F(2,5)*1 + F(1,5)*3, F(2,5)*0 + F(2,5)*0 + F(1,5)*5) == (1, 1)
    and F(2,5)+F(2,5)+F(1,5) == 1)
chk("A-12 (1,2)=1/3[(0,0)+(0,1)+(3,5)]",
    (F(1,3)*(0+0+3), F(1,3)*(0+1+5)) == (1, 2))
chk("A-13 (2,3)=1/5(0,0)+1/5(1,0)+3/5(3,5)",
    (F(1,5)*0 + F(1,5)*1 + F(3,5)*3, F(1,5)*0 + F(1,5)*0 + F(3,5)*5) == (2, 3)
    and F(1,5)+F(1,5)+F(3,5) == 1)
chk("A-14 7 is not a perfect square; 2^2=4<7<9=3^2",
    all((m + 1) ** 2 != 7 for m in range(100)) and 4 < 7 < 9)
chk("A-15 S_A omits exactly (1,1),(1,2),(2,3) from its hull's lattice points",
    sorted(set(hullA_pts) - set(SA)) == [(1, 1), (1, 2), (2, 3)])

# ================================================================ WITNESS T
T = [(0, 1), (1, 0), (1, 1), (2, 2)]
dT = [tuple(q[i] - p[i] for i in range(2)) for p, q in combinations(T, 2)]
chk("T-1  six differences exactly {(1,-1),(1,0),(2,1),(0,1),(1,2),(1,1)}",
    sorted(dT) == sorted([(1, -1), (1, 0), (2, 1), (0, 1), (1, 2), (1, 1)]))
chk("T-2  all primitive", all(gcd_all(*v) == 1 for v in dT))
boxT = [(x, y) for x in range(-4, 7) for y in range(-4, 7)]
hullT_pts = sorted(p for p in boxT if in_hull(p, T, 2))
chk("T-3  conv(T) cap Z^2 = T (independent Caratheodory)",
    hullT_pts == sorted(T), str(hullT_pts))
chk("T-4  (1,1) is the centroid of the other three",
    (F(0+1+2, 3), F(1+0+2, 3)) == (1, 1))
# vertices: p is a vertex of conv(T) iff p not in conv(T \ {p})
verts = [p for p in T if not in_hull(p, [q for q in T if q != p], 2)]
chk("T-5  vertex set of conv(T) is {(0,1),(1,0),(2,2)} (3 vertices)",
    sorted(verts) == sorted([(0, 1), (1, 0), (2, 2)]))
(x1, y1), (x2, y2), (x3, y3) = (0, 1), (1, 0), (2, 2)
areaT = F(abs(x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2)), 2)
chk("T-6  area of conv(T) = 3/2 (shoelace)", areaT == F(3, 2))
def QT(p):
    x, y = p
    return x + y >= 1 and 2 * x - y <= 2 and 2 * y - x <= 2
chk("T-7  note's triangle H-representation agrees with ground truth on box",
    all(QT(p) == (p in hullT_pts) for p in boxT))
chk("T-8  each T-point satisfies, centroid strictly",
    all(QT(p) for p in T) and 1 + 1 > 1 and 2 * 1 - 1 < 2 and 2 * 1 - 1 < 2)
chk("T-9  note's x-chase: 2nd+3rd ineqs give 4x-4<=2+x i.e. x<=2; "
    "x<=-1 impossible",
    all(not (2 * x - y <= 2 and 2 * y - x <= 2 and x + y >= 1)
        for x in range(-30, 0) for y in range(-40, 40)) and
    all(not (2 * 3 - y <= 2 and 2 * y - 3 <= 2) for y in range(-40, 40)))
chk("T-10 count 4 forces m=1; area 3/2 != 1 = area([0,1]^2); 3 != 4 vertices",
    (1 + 1) ** 2 == 4 and (0 + 1) ** 2 == 1 and (2 + 1) ** 2 == 9 and
    areaT != 1 and len(verts) == 3)

# ================================================================ WITNESS C
C = [(0, 2, 2), (1, 0, 1), (1, 1, 2), (1, 2, 2),
     (2, 1, 1), (2, 1, 2), (2, 2, 1), (3, 1, 3)]
dC = [tuple(q[i] - p[i] for i in range(3)) for p, q in combinations(C, 2)]
chk("C-1  |C| = 8, 28 pairwise differences, all primitive",
    len(C) == 8 and len(dC) == 28 and all(gcd_all(*v) == 1 for v in dC))
chk("C-2  bounding box of C is [0,3]x[0,2]x[1,3]",
    (min(p[0] for p in C), max(p[0] for p in C)) == (0, 3) and
    (min(p[1] for p in C), max(p[1] for p in C)) == (0, 2) and
    (min(p[2] for p in C), max(p[2] for p in C)) == (1, 3))
boxC = [(x, y, z) for x in range(0, 4) for y in range(0, 3) for z in range(1, 4)]
hullC_pts = sorted(p for p in boxC if in_hull(p, C, 3))
chk("C-3  conv(C) cap Z^3 = C (independent Caratheodory over the box)",
    hullC_pts == sorted(C), str(hullC_pts))
# full-dimensionality
def det3(u, v, w):
    return (u[0] * (v[1] * w[2] - v[2] * w[1])
            - u[1] * (v[0] * w[2] - v[2] * w[0])
            + u[2] * (v[0] * w[1] - v[1] * w[0]))
sub3 = lambda p, q: (p[0] - q[0], p[1] - q[1], p[2] - q[2])
chk("C-4  conv(C) full-dimensional",
    any(det3(sub3(q, p), sub3(r, p), sub3(s, p)) != 0
        for p, q, r, s in combinations(C, 4)))
# vertices of conv(C)
vertsC = [p for p in C if not in_hull(p, [q for q in C if q != p], 3)]
print("      (info) vertices of conv(C):", sorted(vertsC))
# independent facet derivation + volume via divergence-style surface sum:
# facets = supporting planes through affinely independent triples
facets = set()
for p, q, r in combinations(C, 3):
    n = (
        (q[1]-p[1])*(r[2]-p[2]) - (q[2]-p[2])*(r[1]-p[1]),
        (q[2]-p[2])*(r[0]-p[0]) - (q[0]-p[0])*(r[2]-p[2]),
        (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0]),
    )
    if n == (0, 0, 0):
        continue
    g = gcd_all(*n)
    n = tuple(v // g for v in n)
    c0 = sum(a * b for a, b in zip(n, p))
    vals = [sum(a * b for a, b in zip(n, s)) for s in C]
    if max(vals) <= c0:
        facets.add((n, c0))
    if min(vals) >= c0:
        facets.add((tuple(-v for v in n), -c0))
facets = sorted(facets)
print("      (info) %d facet planes:" % len(facets), facets)
# cross-check the facet H-representation against the Caratheodory ground truth
def inH(p):
    return all(sum(a * b for a, b in zip(n, p)) <= c0 for n, c0 in facets)
chk("C-5  facet H-representation agrees with Caratheodory ground truth on box",
    all(inH(p) == (p in hullC_pts) for p in boxC))
# volume via divergence theorem: vol = (1/3) sum_F (n.x_F / |n|) * area(F)
# done exactly: vol = (1/6) * sum_F sum_{triangles (a,b,c) of F} det(a,b,c)
# where the triangle is oriented with outward normal n.  (For the tetra
# decomposition w.r.t. the ORIGIN; signs handled by orientation.)
vol6 = 0
for n, c0 in facets:
    Fpts = [p for p in C if sum(a * b for a, b in zip(n, p)) == c0]
    assert len(Fpts) >= 3
    # order the facet polygon: project out the largest |n| coordinate, sort
    # around the centroid by exact cross-product comparisons (convex position)
    k = max(range(3), key=lambda i: abs(n[i]))
    ij = [i for i in range(3) if i != k]
    P2 = [(p[ij[0]], p[ij[1]]) for p in Fpts]
    cx = (sum(F(p[0]) for p in P2) / len(P2), sum(F(p[1]) for p in P2) / len(P2))
    import functools
    def half(a):
        return (a[0] - cx[0], a[1] - cx[1])
    def cmp_ang(a, b):
        ax, ay = half(a); bx, by = half(b)
        ha = (ay, -ax) < (0, 0)   # half-plane split: angle >= pi
        hb = (by, -bx) < (0, 0)
        if ha != hb:
            return -1 if not ha else 1
        cr = ax * by - ay * bx
        return -1 if cr > 0 else (1 if cr < 0 else 0)
    order = sorted(range(len(Fpts)), key=functools.cmp_to_key(
        lambda i, j: cmp_ang(P2[i], P2[j])))
    poly = [Fpts[i] for i in order]
    # orient consistently with outward normal n, then sum signed tetra dets
    s = 0
    for i in range(1, len(poly) - 1):
        s += det3(poly[0], poly[i], poly[i + 1])
    # orientation: the polygon's own normal (from first nondegenerate triple)
    nn = None
    for i in range(1, len(poly) - 1):
        cand = (
            (poly[i][1]-poly[0][1])*(poly[i+1][2]-poly[0][2]) - (poly[i][2]-poly[0][2])*(poly[i+1][1]-poly[0][1]),
            (poly[i][2]-poly[0][2])*(poly[i+1][0]-poly[0][0]) - (poly[i][0]-poly[0][0])*(poly[i+1][2]-poly[0][2]),
            (poly[i][0]-poly[0][0])*(poly[i+1][1]-poly[0][1]) - (poly[i][1]-poly[0][1])*(poly[i+1][0]-poly[0][0]),
        )
        if cand != (0, 0, 0):
            nn = cand
            break
    dotn = sum(a * b for a, b in zip(nn, n))
    assert dotn != 0
    if dotn < 0:
        s = -s
    vol6 += s
volC = F(vol6, 6)
chk("C-6  vol(conv(C)) = 5/2 (divergence-theorem signed sum, exact)",
    volC == F(5, 2), "got " + str(volC))
# pair-sum census
def census(S):
    sums = {}
    for p, q in combinations(S, 2):
        s = tuple(a + b for a, b in zip(p, q))
        sums.setdefault(s, []).append((p, q))
    co = {s: v for s, v in sums.items() if len(v) > 1}
    N = sum(len(v) * (len(v) - 1) // 2 for v in co.values())
    return N, co
NC, coC = census(C)
cube = [(x, y, z) for x in (0, 1) for y in (0, 1) for z in (0, 1)]
Ncube, cocube = census(cube)
print("      (info) coinciding sums in C:", coC)
chk("C-7  N(C) = 2", NC == 2, "N(C)=%d" % NC)
chk("C-8  the two coincidences are exactly the displayed ones",
    sorted(coC.keys()) == [(2, 3, 4), (3, 3, 3)] and
    sorted(coC[(2, 3, 4)]) == sorted([((0, 2, 2), (2, 1, 2)), ((1, 1, 2), (1, 2, 2))]) and
    sorted(coC[(3, 3, 3)]) == sorted([((1, 1, 2), (2, 2, 1)), ((1, 2, 2), (2, 1, 1))]))
chk("C-9  N({0,1}^3) = 12", Ncube == 12, "N=%d" % Ncube)
# decomposition claimed in the note: 6 among antipodal pairs (sum (1,1,1)),
# plus one per facet (6 facets)
chk("C-10 cube census: sum (1,1,1) has 4 pairs (C(4,2)=6); 6 face-centers "
    "with 2 pairs each; nothing else",
    len(cocube.get((1, 1, 1), [])) == 4 and
    sorted(len(v) for v in cocube.values()) == [2, 2, 2, 2, 2, 2, 4])
chk("C-11 (m+1)^3: m=0 -> 1, m=1 -> 8, m>=2 -> >=27",
    1 ** 3 == 1 and 2 ** 3 == 8 and 3 ** 3 == 27 and
    all((m + 1) ** 3 > 8 for m in range(2, 30)))
chk("C-12 N invariance sanity: affine image of C under a unimodular map has "
    "the same census",
    census([(p[0] + 2 * p[1] - p[2] + 3, p[1] + p[2] - 1, p[0] + p[1] + p[2])
            for p in C])[0] == NC)

print()
if fails:
    print("REFEREE RECHECK: %d FAILURE(S): %s" % (len(fails), fails))
    raise SystemExit(1)
print("REFEREE RECHECK: ALL CHECKS PASS")
raise SystemExit(0)
