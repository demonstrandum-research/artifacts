#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gate-4 clean-room checker for the refutation of Graffiti Conjecture 143
("Written on the Wall", S. Fajtlowicz):

    143. variance of positive eigenvalues <= size / average distance.

Conventions verified (both standard readings of "average distance"):
  * variance  = population variance of the multiset of strictly positive
                adjacency eigenvalues (Graffiti: statistical invariants are
                random variables on uniform sample spaces).
  * size      = m = number of edges.
  * average distance, reading N2    : mean of the n^2 ordered-pair distance
                matrix entries incl. diagonal  = 2W/n^2
                (formalization used by Roucairol-Cazenave, ECAI 2025 code).
  * average distance, reading PAIRS : mean over distinct vertex pairs
                = 2W/(n(n-1))  (Aouchiche-Hansen convention).
  RHS_N2 = m*n^2/(2W)  >  RHS_PAIRS = m*n(n-1)/(2W).
  A certified violation of BOTH readings kills the conjecture under either.

This checker was written from scratch for Gate-4 verification (no code shared
with the discovery pipeline). It verifies every instance by TWO independent
exact routes and accepts only if both certify the claimed strict inequality:

  Route A ("sympy"): integer characteristic polynomial of the full adjacency
      matrix via sympy's charpoly; exact real-root isolation with
      multiplicities via Poly.intervals; rational interval arithmetic for
      the variance of positive roots.

  Route B ("stdlib"): pure-stdlib (fractions, integers) re-derivation:
      own Berkowitz characteristic polynomial of the full matrix; equitable-
      partition quotient matrix of the dumbbell (size p+4) with own Berkowitz;
      certified polynomial identity  charA(x) == charB(x) * (x+1)^(t1+t2-4);
      own Yun squarefree decomposition + Sturm chains + bisection isolation
      of the positive roots of charB; rational interval arithmetic.

Internal consistency demands (any failure => REJECT):
  - Route A and Route B produce the identical integer charpoly.
  - charpoly coefficient checks: coeff[x^(n-1)] == 0 (trace), coeff[x^(n-2)]
    == -m (sum over pairs of eigenvalue products).
  - number of real roots (with multiplicity) == n  (A symmetric).
  - both routes agree on k (number of positive eigenvalues, w/ multiplicity)
    and their variance intervals intersect.
  - graph is connected (BFS); W, m, n match the certificate.
  - certificate's claimed exact RHS fractions match recomputation.
  - the strict inequalities  var_lo > RHS  hold for every convention the
    certificate claims to violate, in BOTH routes.
  - for every convention the certificate does NOT claim to violate, the
    certified enclosure lies strictly below the RHS (var_hi < RHS) in BOTH
    routes, i.e. the non-violation is certified as well (assertion added
    2026-06-12 while preparing the research note; it covers the "dash"
    entries of the note's Table 1).

Usage:  python checker_g143.py certificate.json
Exit code 0 and final line "CHECKER VERDICT: ACCEPT" iff all instances verify.
"""

import json
import sys
from fractions import Fraction
from itertools import combinations

# Windows consoles often default to cp1252; the certificate contains "≤".
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

# ----------------------------------------------------------------------------
# Graph utilities (pure stdlib, exact integers)
# ----------------------------------------------------------------------------

def adjacency_from_edges(n, edges):
    A = [[0] * n for _ in range(n)]
    seen = set()
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError("bad edge (%r,%r)" % (u, v))
        key = (min(u, v), max(u, v))
        if key in seen:
            raise ValueError("duplicate edge %r" % (key,))
        seen.add(key)
        A[u][v] = A[v][u] = 1
    return A


def bfs_wiener(A):
    """Wiener index (sum of distances over unordered pairs); None if disconnected."""
    n = len(A)
    nbrs = [[j for j in range(n) if A[i][j]] for i in range(n)]
    total = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        frontier = [s]
        while frontier:
            nxt = []
            for u in frontier:
                for v in nbrs[u]:
                    if dist[v] < 0:
                        dist[v] = dist[u] + 1
                        nxt.append(v)
            frontier = nxt
        if any(d < 0 for d in dist):
            return None
        total += sum(dist)
    assert total % 2 == 0
    return total // 2


def dumbbell_edges(t1, p, t2):
    """Canonical dumbbell: clique K_t1 on {0..t1-1}, path internal vertices
    {t1..t1+p-1}, clique K_t2 on {t1+p..n-1}; chain 0 - t1 - ... - (t1+p-1) - (t1+p)."""
    n = t1 + p + t2
    edges = []
    edges += [(i, j) for i, j in combinations(range(t1), 2)]
    edges += [(i, j) for i, j in combinations(range(t1 + p, n), 2)]
    chain = [0] + list(range(t1, t1 + p)) + [t1 + p]
    edges += [(a, b) for a, b in zip(chain, chain[1:])]
    return n, edges

# ----------------------------------------------------------------------------
# Polynomial helpers over QQ (coeff lists, highest degree first)
# ----------------------------------------------------------------------------

def poly_trim(c):
    if not c:
        return [0]
    i = 0
    while i < len(c) - 1 and c[i] == 0:
        i += 1
    return c[i:]


def poly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def poly_eval(c, x):
    acc = Fraction(0)
    for co in c:
        acc = acc * x + co
    return acc


def poly_deriv(c):
    d = len(c) - 1
    return [co * (d - i) for i, co in enumerate(c[:-1])] or [0]


def poly_divmod(a, b):
    """Long division over Fractions. Returns (q, r) with a == q*b + r."""
    a = poly_trim([Fraction(x) for x in a])
    b = poly_trim([Fraction(x) for x in b])
    if b == [0]:
        raise ZeroDivisionError
    if len(a) < len(b) or a == [0]:
        return [Fraction(0)], a
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    r = a[:]
    while len(r) >= len(b) and r != [Fraction(0)] and poly_trim(r) != [0]:
        shift = len(r) - len(b)
        coef = r[0] / b[0]
        q[len(q) - 1 - shift] = coef
        r = [r[i] - coef * b[i] for i in range(len(b))] + r[len(b):]
        assert r[0] == 0
        r = poly_trim(r[1:])
    return poly_trim(q), poly_trim(r)


def poly_monic(c):
    c = poly_trim([Fraction(x) for x in c])
    if c == [0]:
        return c
    lead = c[0]
    return [x / lead for x in c]


def poly_gcd(a, b):
    a = poly_monic(a)
    b = poly_monic(b)
    while poly_trim(b) != [0]:
        _, r = poly_divmod(a, b)
        a, b = b, poly_monic(r)
    return poly_monic(a)


def yun_squarefree(f):
    """Yun's algorithm. Returns list of (factor, multiplicity), factors monic
    squarefree pairwise coprime, product of factor^mult == monic(f)."""
    f = poly_monic(f)
    if len(f) - 1 == 0:
        return []
    fp = poly_deriv(f)
    a = poly_gcd(f, fp)
    if len(a) - 1 == 0:
        return [(f, 1)]
    b, r = poly_divmod(f, a)
    assert poly_trim(r) == [0]
    c, r = poly_divmod(fp, a)
    assert poly_trim(r) == [0]
    # d = c - b'
    bp = poly_deriv(b)
    L = max(len(c), len(bp))
    cc = [Fraction(0)] * (L - len(c)) + list(map(Fraction, c))
    bb = [Fraction(0)] * (L - len(bp)) + list(map(Fraction, bp))
    d = poly_trim([x - y for x, y in zip(cc, bb)])
    out = []
    i = 1
    while True:
        if len(b) - 1 == 0:
            break
        g = poly_gcd(b, d)
        if len(g) - 1 > 0:
            out.append((g, i))
        b_new, r = poly_divmod(b, g)
        assert poly_trim(r) == [0]
        c_new, r = poly_divmod(d, g)
        assert poly_trim(r) == [0]
        bp = poly_deriv(b_new)
        L = max(len(c_new), len(bp))
        cc = [Fraction(0)] * (L - len(c_new)) + list(map(Fraction, c_new))
        bb = [Fraction(0)] * (L - len(bp)) + list(map(Fraction, bp))
        d = poly_trim([x - y for x, y in zip(cc, bb)])
        b = b_new
        i += 1
    # verify decomposition
    prod = [Fraction(1)]
    for g, mult in out:
        for _ in range(mult):
            prod = poly_mul(prod, g)
    fm = poly_monic(f)
    assert len(prod) == len(fm) and prod == fm, \
        "Yun decomposition failed verification"
    return out

# ----------------------------------------------------------------------------
# Berkowitz characteristic polynomial (own implementation, integer arithmetic)
# returns coefficients of det(xI - M), highest first, integers.
# ----------------------------------------------------------------------------

def berkowitz_charpoly(M):
    n = len(M)
    if n == 0:
        return [1]
    poly = [1, -M[0][0]]
    for i in range(1, n):
        # leading principal submatrix A = M[:i][:i], row R = M[i][:i],
        # column C = M[:i][i], corner a = M[i][i]
        a = M[i][i]
        R = M[i][:i]
        C = [M[r][i] for r in range(i)]
        # T-column: [1, -a, -R.C, -R.A.C, -R.A^2.C, ..., -R.A^(i-2).C]
        t = [1, -a]
        if i >= 1:
            w = C[:]  # A^0 . C
            t.append(-sum(R[r] * w[r] for r in range(i)))
            for _ in range(i - 1):
                w = [sum(M[r][s] * w[s] for s in range(i)) for r in range(i)]
                t.append(-sum(R[r] * w[r] for r in range(i)))
        # poly_new[k] = sum_j t[j]*poly[k-j]
        newp = [0] * (i + 2)
        for k in range(i + 2):
            s = 0
            for j in range(len(t)):
                if 0 <= k - j < len(poly):
                    s += t[j] * poly[k - j]
            newp[k] = s
        poly = newp
    return poly

# ----------------------------------------------------------------------------
# Sturm chains and certified positive-root isolation (stdlib route)
# ----------------------------------------------------------------------------

def sturm_chain(f):
    f = poly_monic(f)
    chain = [f, poly_monic(poly_deriv(f))]
    while poly_trim(chain[-1]) != [0] and len(chain[-1]) > 1:
        _, r = poly_divmod(chain[-2], chain[-1])
        r = poly_trim(r)
        if r == [0]:
            break
        chain.append(poly_monic([-x for x in r]))
    return chain


def sturm_sign_changes(chain, x):
    signs = []
    for f in chain:
        v = poly_eval(f, x)
        if v != 0:
            signs.append(1 if v > 0 else -1)
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def sturm_count(chain, a, b):
    """Number of distinct real roots in (a, b]."""
    return sturm_sign_changes(chain, a) - sturm_sign_changes(chain, b)


def cauchy_bound(f):
    f = poly_monic(f)
    if len(f) == 1:
        return Fraction(1)
    return 1 + max(abs(c) for c in f[1:])


def isolate_positive_roots(f):
    """f squarefree (monic, Fractions). Returns list of (lo, hi) Fractions,
    0 < lo <= root <= hi, one per distinct positive root, certified by Sturm.
    Requires f(0) != 0."""
    assert poly_eval(f, Fraction(0)) != 0, "f(0)==0 not allowed here"
    chain = sturm_chain(f)
    U = cauchy_bound(f)
    total = sturm_count(chain, Fraction(0), U)
    intervals = []
    stack = [(Fraction(0), U)]
    while stack:
        lo, hi = stack.pop()
        cnt = sturm_count(chain, lo, hi)   # roots in (lo, hi]
        if cnt == 0:
            continue
        if cnt == 1:
            intervals.append((lo, hi))
            continue
        mid = None
        for num, den in ((1, 2), (1, 3), (2, 5), (3, 7), (4, 9), (5, 11)):
            cand = lo + (hi - lo) * Fraction(num, den)
            if poly_eval(f, cand) != 0:
                mid = cand
                break
        assert mid is not None, "could not find non-root split point"
        stack.append((lo, mid))
        stack.append((mid, hi))
    assert len(intervals) == total, "isolation lost roots"
    return sorted(intervals)


def refine_interval(f, lo, hi, eps):
    """Bisection refinement of an isolating interval for a simple root of f.
    Maintains certification: sign(f(lo)) * sign(f(hi)) < 0 (or exact point)."""
    if lo == hi:
        return lo, hi
    flo = poly_eval(f, lo)
    fhi = poly_eval(f, hi)
    assert flo != 0, "left endpoint of isolating (lo,hi] cannot be a root"
    if fhi == 0:
        return hi, hi
    assert (flo > 0) != (fhi > 0), "interval endpoints do not bracket a sign change"
    while hi - lo > eps:
        mid = (lo + hi) / 2
        fm = poly_eval(f, mid)
        if fm == 0:
            return mid, mid
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi, fhi = mid, fm
    return lo, hi

# ----------------------------------------------------------------------------
# Variance interval from certified positive-root intervals
# ----------------------------------------------------------------------------

def variance_interval(root_intervals):
    """root_intervals: list of (lo, hi, mult) with 0 <= lo <= root <= hi.
    Returns (var_lo, var_hi, k) -- certified bounds on the population variance
    of the multiset of positive roots."""
    k = sum(mult for _, _, mult in root_intervals)
    s1_lo = sum(lo * mult for lo, _, mult in root_intervals)
    s1_hi = sum(hi * mult for _, hi, mult in root_intervals)
    s2_lo = sum(lo * lo * mult for lo, _, mult in root_intervals)
    s2_hi = sum(hi * hi * mult for _, hi, mult in root_intervals)
    assert s1_lo >= 0
    var_lo = Fraction(s2_lo, k) - Fraction(s1_hi * s1_hi, k * k)
    var_hi = Fraction(s2_hi, k) - Fraction(s1_lo * s1_lo, k * k)
    return var_lo, var_hi, k

# ----------------------------------------------------------------------------
# Route B: pure-stdlib verification of one instance
# ----------------------------------------------------------------------------

EPS = Fraction(1, 2 ** 70)


def route_b(A, family=None):
    """Returns dict with charpoly (ints), k, var_lo, var_hi."""
    n = len(A)
    charA = berkowitz_charpoly(A)
    assert len(charA) == n + 1 and charA[0] == 1
    m = sum(A[i][j] for i in range(n) for j in range(i))
    # coefficient sanity: trace 0, e2 = -m
    assert charA[1] == 0, "coeff x^(n-1) != 0 (trace)"
    assert charA[2] == -m, "coeff x^(n-2) != -m"

    work_poly = charA
    extra_neg1 = 0
    if family is not None:
        t1, p, t2 = family
        nf, ef = dumbbell_edges(t1, p, t2)
        assert nf == n
        # quotient (equitable partition divisor) matrix, classes:
        # [a1, c1others(t1-1), v_1..v_p, a2, c2others(t2-1)]
        q = p + 4
        B = [[0] * q for _ in range(q)]
        # indices: 0=a1, 1=c1, 2..p+1 = v_1..v_p, p+2=a2, p+3=c2
        B[0][1] = t1 - 1
        B[1][0] = 1
        B[1][1] = t1 - 2
        B[p + 2][p + 3] = t2 - 1
        B[p + 3][p + 2] = 1
        B[p + 3][p + 3] = t2 - 2
        chain = [0] + list(range(2, p + 2)) + [p + 2]
        for a_, b_ in zip(chain, chain[1:]):
            B[a_][b_] += 1
            B[b_][a_] += 1
        charB = berkowitz_charpoly(B)
        e = (t1 - 2) + (t2 - 2)
        # identity charA == charB * (x+1)^e   (exact integer polynomial identity)
        rhs = charB[:]
        for _ in range(e):
            rhs = poly_mul(rhs, [1, 1])
        assert len(charA) == len(rhs) and charA == rhs, \
            "quotient identity charA != charB*(x+1)^e"
        # (x+1)^e contributes only eigenvalue -1 (negative): the positive
        # spectrum of A equals the positive root multiset of charB.
        work_poly = charB

    # strip zero roots from work_poly
    wp = [Fraction(c) for c in work_poly]
    nzero = 0
    while wp[-1] == 0:
        wp = wp[:-1]
        nzero += 1
    # squarefree decomposition with multiplicities
    sqf = yun_squarefree(wp)
    roots = []
    for g, mult in sqf:
        assert poly_eval(g, Fraction(0)) != 0
        for lo, hi in isolate_positive_roots(g):
            lo, hi = refine_interval(g, lo, hi, EPS)
            assert lo > 0 or lo == hi, "refined interval still touches 0"
            if lo == 0:
                raise AssertionError("cannot certify strict positivity")
            roots.append((lo, hi, mult))
    var_lo, var_hi, k = variance_interval(roots)
    return {"charpoly": charA, "k": k, "var_lo": var_lo, "var_hi": var_hi}

# ----------------------------------------------------------------------------
# Route A: sympy verification of one instance
# ----------------------------------------------------------------------------

def route_a(A):
    import sympy
    from sympy import Matrix, Poly, Rational, Symbol
    x = Symbol('x')
    n = len(A)
    M = Matrix(A)
    cp = M.charpoly(x)            # Berkowitz/DomainMatrix, exact over ZZ
    coeffs = [int(c) for c in cp.all_coeffs()]
    assert len(coeffs) == n + 1 and coeffs[0] == 1
    # strip exact zero roots
    nzero = 0
    while coeffs[-1] == 0:
        coeffs = coeffs[:-1]
        nzero += 1
    P = Poly(coeffs, x, domain='QQ')
    eps = Rational(1, 2) ** 70
    ivs = P.intervals(eps=eps, sqf=False)   # real-root isolation w/ multiplicity
    total_real = sum(mult for (_a, _b), mult in ivs)
    assert total_real + nzero == n, "not all eigenvalues real?!  charpoly wrong"
    roots = []
    k = 0
    for (a, b), mult in ivs:
        a = Fraction(int(a.p), int(a.q))
        b = Fraction(int(b.p), int(b.q))
        assert not (a <= 0 <= b), \
            "isolating interval touches 0 at eps=2^-70 (0 was stripped)"
        if b < 0:
            continue
        # strictly positive root
        assert a > 0
        roots.append((a, b, mult))
        k += mult
    var_lo, var_hi, k2 = variance_interval(roots)
    assert k2 == k
    return {"charpoly": [int(c) for c in cp.all_coeffs()],
            "k": k, "var_lo": var_lo, "var_hi": var_hi}

# ----------------------------------------------------------------------------
# Per-instance verification
# ----------------------------------------------------------------------------

def check_instance(inst):
    name = inst.get("name", "?")
    n = inst["n"]
    edges = [tuple(e) for e in inst["edges"]]
    A = adjacency_from_edges(n, edges)
    m = len(edges)
    assert m == inst["m"], "m mismatch"

    family = None
    if inst.get("family") == "dumbbell":
        t1, p, t2 = inst["t1"], inst["p"], inst["t2"]
        nf, ef = dumbbell_edges(t1, p, t2)
        assert nf == n and sorted(map(tuple, ef)) == sorted(
            (min(u, v), max(u, v)) for u, v in edges), \
            "edge list is not the canonical dumbbell"
        family = (t1, p, t2)

    W = bfs_wiener(A)
    assert W is not None, "graph disconnected"
    assert W == inst["W"], "Wiener index mismatch"

    rhs_n2 = Fraction(m * n * n, 2 * W)
    rhs_pairs = Fraction(m * n * (n - 1), 2 * W)
    assert rhs_n2 == Fraction(inst["rhs_n2"]), "rhs_n2 mismatch"
    assert rhs_pairs == Fraction(inst["rhs_pairs"]), "rhs_pairs mismatch"

    rb = route_b(A, family)
    ra = route_a(A)
    assert ra["charpoly"] == rb["charpoly"], "charpoly mismatch between routes"
    assert ra["k"] == rb["k"] == inst["k"], "positive-eigenvalue count mismatch"
    # intervals must intersect
    lo = max(ra["var_lo"], rb["var_lo"])
    hi = min(ra["var_hi"], rb["var_hi"])
    assert lo <= hi, "route variance intervals disjoint"

    claims = inst["violates"]  # list among ["n2","pairs"]
    results = {}
    for conv, rhs in (("n2", rhs_n2), ("pairs", rhs_pairs)):
        margin_lo_a = ra["var_lo"] - rhs
        margin_lo_b = rb["var_lo"] - rhs
        ok = (margin_lo_a > 0) and (margin_lo_b > 0)
        results[conv] = (ok, min(margin_lo_a, margin_lo_b))
        if conv in claims:
            assert ok, "claimed violation of '%s' NOT certified (margin_lo=%s)" % (
                conv, float(min(margin_lo_a, margin_lo_b)))
        else:
            # the certificate does not claim this reading: certify the
            # NON-violation as well -- both routes' certified upper bounds
            # must lie strictly below the right-hand side. (Added 2026-06-12.)
            margin_hi_a = ra["var_hi"] - rhs
            margin_hi_b = rb["var_hi"] - rhs
            assert (margin_hi_a < 0) and (margin_hi_b < 0), \
                "unclaimed reading '%s' NOT certified non-violated " \
                "(margin_hi=%s)" % (conv, float(max(margin_hi_a, margin_hi_b)))
    # cross-check claimed certified margin lower bounds, if present
    for conv in claims:
        key = "margin_%s_lower" % conv
        if key in inst:
            claimed = Fraction(inst[key])
            actual = results[conv][1]
            assert actual >= claimed, "certified margin below claimed bound"

    print("  [PASS] %s : n=%d m=%d W=%d k=%d" % (name, n, m, W, ra["k"]))
    print("         var_pos in [%.12f, %.12f]  (certified width %.2e)" % (
        float(lo), float(hi), float(hi - lo)))
    for conv, rhs in (("n2", rhs_n2), ("pairs", rhs_pairs)):
        ok, mg = results[conv]
        tag = "VIOLATED" if ok else "certified NOT violated"
        print("         RHS_%s = %s = %.12f   margin_lo = %+.12f  -> %s" % (
            conv, rhs, float(rhs), float(mg), tag))
    return True


def main():
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    with open(sys.argv[1], "r", encoding="utf-8") as fh:
        cert = json.load(fh)
    print("Certificate: %s" % cert.get("title", "?"))
    print("Conjecture : %s" % cert.get("conjecture_verbatim", "?"))
    ok = True
    for inst in cert["instances"]:
        try:
            check_instance(inst)
        except AssertionError as e:
            print("  [FAIL] %s : %s" % (inst.get("name", "?"), e))
            ok = False
        except Exception as e:
            print("  [FAIL] %s : unexpected error %r" % (inst.get("name", "?"), e))
            ok = False
    print("CHECKER VERDICT: %s" % ("ACCEPT" if ok else "REJECT"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
