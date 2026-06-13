#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Clean-room Gate-4 checker for the claimed refutation of Graffiti Conjecture 154
("Written on the Wall", Fajtlowicz, c. 1988):

    "154. deviation of eigenvalues <= n / average distance."

(verbatim from wow-july2004.pdf, decoded; eigenvalues = adjacency matrix per the
WoW preamble).

Operational readings checked
----------------------------
"deviation" (std-dev reading, the one under which the kill is claimed):
    population standard deviation of the n adjacency eigenvalues
      = sqrt( (1/n) sum lambda_i^2  -  ((1/n) sum lambda_i)^2 )
      = sqrt( 2m/n )            [exact: tr A = 0, tr A^2 = 2m]
"average distance", two conventions:
    (DP)  distinct-pairs:  l = 2W / (n(n-1))   => RHS n/l = n^2 (n-1) / (2W)
    (N2)  all n^2 entries: l = 2W / n^2        => RHS n/l = n^3 / (2W)
          (this is what Roucairol-Cazenave's code uses: mean over the full
           distance matrix including the zero diagonal)

Violation conditions in PURE INTEGER arithmetic (square both sides; all
quantities positive):
    sqrt(2m/n) > n^2 (n-1)/(2W)   <=>   8 m W^2 > n^5 (n-1)^2     (DP)
    sqrt(2m/n) > n^3/(2W)         <=>   8 m W^2 > n^7             (N2)

MAD reading (claimed NOT violated -- verified here too):
    mean absolute deviation = (1/n) sum |lambda_i - mean| = (1/n) sum |lambda_i|
      = energy(G)/n            [mean = 0]
    Checked three independent ways:
      (1) float64 numpy eigenvalues (sanity),
      (2) mpmath dps=60 eigenvalues with explicit sign-separation margins,
      (3) EXACT: Koolen-Moulton bound E <= 2m/n + sqrt((n-1)(2m - (2m/n)^2))
          compared against n^2/l in exact rational arithmetic, and
      (4) EXACT: Sturm-certified rational enclosure of energy via the
          equitable-quotient characteristic polynomial (degree p+2).

Counterexample object (rebuilt from the construction DESCRIPTION; no code
reuse from the discovery scripts):
    lollipop(t, p): vertices 0..t-1 form a clique K_t; vertices t..t+p-1 form
    a path; one extra edge joins clique vertex 0 to path vertex t.
    n = t+p, m = t(t-1)/2 + p.

Claimed instances re-verified:
    lollipop(72,72): n=144  -- violates BOTH conventions
    lollipop(50,70): n=120  -- violates BOTH conventions (smallest found, both)
    lollipop(48,70): n=118  -- violates DP only, NOT N2 (smallest found, DP)
Plus an exhaustive integer scan of all lollipops with n <= 130 confirming
those are the minimal violating lollipops, and mutation self-tests.

Pure-stdlib for the kill itself; numpy/mpmath/sympy only for the spectral
cross-checks of the side claims.
"""

import sys
from fractions import Fraction
from math import isqrt

sys.stdout.reconfigure(encoding="utf-8", errors="backslashreplace")

FAILURES = []


def check(label, cond):
    tag = "PASS" if cond else "FAIL"
    print(f"  [{tag}] {label}")
    if not cond:
        FAILURES.append(label)
    return cond


# ---------------------------------------------------------------------------
# Graph construction and exact invariants (stdlib only)
# ---------------------------------------------------------------------------

def lollipop_edges(t, p):
    """Edge list of lollipop(t,p). Clique on 0..t-1, path on t..t+p-1,
    bridge edge (0, t)."""
    E = [(i, j) for i in range(t) for j in range(i + 1, t)]
    if p > 0:
        E.append((0, t))
        E += [(t + i, t + i + 1) for i in range(p - 1)]
    return E


def adjacency_lists(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def bfs_all_pairs_wiener(n, adj):
    """Exact Wiener index (sum of distances over unordered distinct pairs)
    by BFS from every vertex. Raises if disconnected."""
    from collections import deque
    total = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1
                    q.append(w)
        if min(dist) < 0:
            raise ValueError("graph disconnected")
        total += sum(dist)
    assert total % 2 == 0
    return total // 2


def wiener_closed_form(t, p):
    """Independently derived closed form for W(lollipop(t,p)):
       clique pairs: C(t,2) * 1
       clique<->path: sum_{k=1..p} [ k  (vertex 0 to k-th path vertex)
                                    + (t-1)(k+1) (each other clique vertex) ]
       path pairs: sum_{1<=i<j<=p} (j-i) = C(p+1,3)
    """
    W = t * (t - 1) // 2
    W += sum(k + (t - 1) * (k + 1) for k in range(1, p + 1))
    W += (p + 1) * p * (p - 1) // 6
    return W


# ---------------------------------------------------------------------------
# Std-dev reading: pure integer violation check
# ---------------------------------------------------------------------------

def stddev_violation_margins(t, p, W=None):
    """Return (n, m, W, lhs, rhs_dp, rhs_n2) for the squared/cleared
    comparison 8 m W^2  vs  n^5 (n-1)^2  and  n^7 (all integers)."""
    n = t + p
    m = t * (t - 1) // 2 + p
    if W is None:
        W = wiener_closed_form(t, p)
    lhs = 8 * m * W * W
    return n, m, W, lhs, n ** 5 * (n - 1) ** 2, n ** 7


# ---------------------------------------------------------------------------
# MAD reading helpers
# ---------------------------------------------------------------------------

def frac_lt_sqrt(q, x):
    """Exact test: is Fraction q < sqrt(x) for Fraction x >= 0?"""
    if q < 0:
        return True
    return q * q < x


def koolen_moulton_mad_check(n, m, W):
    """EXACT rational check that the Koolen-Moulton upper bound on graph
    energy E(G) <= 2m/n + sqrt((n-1)(2m-(2m/n)^2))   [valid when 2m >= n]
    stays strictly below n^2/l for BOTH average-distance conventions.
    Returns (ok_dp, ok_n2). A True is a PROOF of MAD non-violation
    (given the published KM theorem); False is merely inconclusive."""
    assert 2 * m >= n
    d = Fraction(2 * m, n)
    radicand = (n - 1) * (2 * m - d * d)        # exact rational >= 0
    out = []
    for rhs in (Fraction(n ** 3 * (n - 1), 2 * W),   # n^2 / l_DP
                Fraction(n ** 4, 2 * W)):            # n^2 / l_N2
        gap = rhs - d
        # KM < rhs  <=>  sqrt(radicand) < gap  <=>  gap > 0 and radicand < gap^2
        out.append(gap > 0 and radicand < gap * gap)
    return tuple(out)


def quotient_matrix(t, p):
    """Equitable-partition quotient of lollipop(t,p).
    Classes: 0 = clique vertex 0 (attachment), 1 = other t-1 clique vertices,
    2..p+1 = path vertices individually.  Size (p+2) x (p+2), integer."""
    k = p + 2
    B = [[0] * k for _ in range(k)]
    B[0][1] = t - 1
    B[1][0] = 1
    B[1][1] = t - 2
    if p > 0:
        B[0][2] = 1
        B[2][0] = 1
        for i in range(p - 1):
            B[2 + i][3 + i] = 1
            B[3 + i][2 + i] = 1
    return B


def verify_equitable(n, adj, classes):
    """Integer check that `classes` (list of vertex lists) is an equitable
    partition: every vertex in class i has the same number of neighbours in
    class j, for all i,j. Returns the (integer) quotient matrix or None."""
    idx = {}
    for ci, cl in enumerate(classes):
        for v in cl:
            idx[v] = ci
    k = len(classes)
    Q = None
    for ci, cl in enumerate(classes):
        rows = []
        for v in cl:
            cnt = [0] * k
            for w in adj[v]:
                cnt[idx[w]] += 1
            rows.append(cnt)
        if any(r != rows[0] for r in rows):
            return None
        if Q is None:
            Q = [[0] * k for _ in range(k)]
        Q[ci] = rows[0]
    return Q


def sturm_energy_enclosure(t, p, eps_bits=60):
    """EXACT route: rational enclosure [lo, hi] of energy(lollipop(t,p)).
    spec(A) = roots(charpoly(B)) UNION {-1}^(t-2) where B is the equitable
    quotient (verified by caller via trace identities + equitability +
    explicit -1 eigenvvectors). Uses sympy integer charpoly + isolating
    intervals refined by exact bisection."""
    import sympy as sp
    B = sp.Matrix(quotient_matrix(t, p))
    x = sp.Symbol('x')
    cp = B.charpoly(x)                      # Berkowitz, exact integers
    poly = sp.Poly(cp.as_expr(), x)
    deg = poly.degree()
    assert deg == p + 2
    # isolating intervals for all real roots, refined to width 2^-eps_bits
    ivs = poly.intervals(eps=sp.Rational(1, 2 ** eps_bits), sqf=False)
    nreal = sum(mult for (_, mult) in ivs)
    assert nreal == deg, f"charpoly(B) must have all {deg} roots real, got {nreal}"
    lo = hi = Fraction(t - 2)               # the (t-2) eigenvalues equal to -1
    for (a, b), mult in ivs:
        a = Fraction(int(sp.numer(a)), int(sp.denom(a)))
        b = Fraction(int(sp.numer(b)), int(sp.denom(b)))
        if a >= 0:
            alo, ahi = a, b
        elif b <= 0:
            alo, ahi = -b, -a
        else:
            alo, ahi = Fraction(0), max(-a, b)
        lo += mult * alo
        hi += mult * ahi
    return lo, hi, poly


# ---------------------------------------------------------------------------
# Spectral cross-checks (numpy float64 + mpmath high precision)
# ---------------------------------------------------------------------------

def spectral_crosscheck(t, p, dps=60):
    """Build the actual adjacency matrix; confirm the exact identities
    sum(lambda)=0, sum(lambda^2)=2m numerically; return high-precision energy."""
    import numpy as np
    import mpmath as mp
    n = t + p
    E = lollipop_edges(t, p)
    A = np.zeros((n, n))
    for u, v in E:
        A[u, v] = A[v, u] = 1.0
    ev = np.linalg.eigvalsh(A)
    s1, s2 = float(ev.sum()), float((ev ** 2).sum())
    m = len(E)
    ok_id = abs(s1) < 1e-9 and abs(s2 - 2 * m) < 1e-6
    energy_f64 = float(np.abs(ev).sum())

    mp.mp.dps = dps
    Am = mp.matrix(n, n)
    for u, v in E:
        Am[u, v] = Am[v, u] = mp.mpf(1)
    evm = mp.mp.eigsy(Am, eigvals_only=True)
    energy_mp = sum(abs(e) for e in evm)
    s1m = sum(evm)
    s2m = sum(e * e for e in evm)
    ok_idm = abs(s1m) < mp.mpf(10) ** (-(dps - 15)) and \
             abs(s2m - 2 * m) < mp.mpf(10) ** (-(dps - 15))
    return ok_id, ok_idm, energy_f64, energy_mp, ev


# ---------------------------------------------------------------------------
# Main verification
# ---------------------------------------------------------------------------

def verify_instance(t, p, expect_dp, expect_n2, do_spectral=True):
    print(f"\n=== lollipop(t={t}, p={p}) ===")
    n = t + p
    E = lollipop_edges(t, p)
    adj = adjacency_lists(n, E)
    m = len(E)
    check(f"n = {n}", n == t + p)
    check(f"m = {m} = t(t-1)/2 + p", m == t * (t - 1) // 2 + p)
    degs = sorted(len(a) for a in adj)
    check("degree sequence sane (path end deg 1, clique deg >= t-1)",
          degs[0] == 1 and degs[-1] == t)
    W_bfs = bfs_all_pairs_wiener(n, adj)          # also proves connectivity
    W_cf = wiener_closed_form(t, p)
    check(f"W (BFS) = {W_bfs} == closed form {W_cf}", W_bfs == W_cf)

    _, _, _, lhs, rhs_dp, rhs_n2 = stddev_violation_margins(t, p, W_bfs)
    print(f"    8mW^2          = {lhs}")
    print(f"    n^5(n-1)^2 (DP)= {rhs_dp}   margin = {lhs - rhs_dp}")
    print(f"    n^7        (N2)= {rhs_n2}   margin = {lhs - rhs_n2}")
    check(f"std-dev violates DP convention is {expect_dp}",
          (lhs > rhs_dp) == expect_dp)
    check(f"std-dev violates N2 convention is {expect_n2}",
          (lhs > rhs_n2) == expect_n2)

    # exact std dev and RHS as decimals, for the record
    import mpmath as mp
    mp.mp.dps = 30
    sd = mp.sqrt(mp.mpf(2 * m) / n)
    rdp = mp.mpf(n ** 2 * (n - 1)) / (2 * W_bfs)
    rn2 = mp.mpf(n ** 3) / (2 * W_bfs)
    print(f"    stddev = sqrt(2m/n) = {mp.nstr(sd, 15)}; "
          f"n/l_DP = {mp.nstr(rdp, 15)}; n/l_N2 = {mp.nstr(rn2, 15)}")

    if not do_spectral:
        return

    # ---- spectral cross-checks + MAD reading ----
    ok_id, ok_idm, e64, emp, ev = spectral_crosscheck(t, p)
    check("float64: tr(A)=0 and tr(A^2)=2m reproduced by actual eigenvalues", ok_id)
    check("mpmath dps=60: same identities at high precision", ok_idm)
    check(f"energy float64 {e64:.6f} vs mpmath agree to 1e-6",
          abs(e64 - float(emp)) < 1e-6)

    mad = emp / n
    import mpmath as mp2
    rdp60 = mp2.mpf(n ** 2 * (n - 1)) / (2 * W_bfs)
    rn260 = mp2.mpf(n ** 3) / (2 * W_bfs)
    print(f"    MAD = energy/n = {mp2.nstr(mad, 20)} "
          f"(energy = {mp2.nstr(emp, 20)})")
    print(f"    sign-separation: n/l_DP - MAD = {mp2.nstr(rdp60 - mad, 10)}; "
          f"n/l_N2 - MAD = {mp2.nstr(rn260 - mad, 10)}")
    check("MAD reading NOT violated (DP), high precision", mad < rdp60)
    check("MAD reading NOT violated (N2), high precision", mad < rn260)

    km_dp, km_n2 = koolen_moulton_mad_check(n, m, W_bfs)
    check("EXACT (Koolen-Moulton, rational): MAD non-violation proven, DP", km_dp)
    check("EXACT (Koolen-Moulton, rational): MAD non-violation proven, N2", km_n2)

    # ---- exact Sturm route via equitable quotient ----
    classes = [[0], list(range(1, t)), *[[t + i] for i in range(p)]]
    Q = verify_equitable(n, adj, classes)
    check("partition {v0}|{other clique}|path singletons is equitable", Q is not None)
    check("quotient matrix matches analytic construction",
          Q == quotient_matrix(t, p))
    # explicit -1 eigenvectors: x = e_1 - e_j (clique-others), j = 2..t-1
    okm1 = True
    for j in range(2, t):
        xv = [0] * n
        xv[1], xv[j] = 1, -1
        Ax = [sum(xv[w] for w in adj[u]) for u in range(n)]
        if Ax != [-v for v in xv]:
            okm1 = False
            break
    check(f"explicit verification: -1 eigenvalue with {t-2} independent "
          f"difference eigenvectors", okm1)
    lo, hi, poly = sturm_energy_enclosure(t, p)
    co = poly.all_coeffs()
    # trace identities certifying spec(A) = roots(B) u {-1}^(t-2):
    trB = quotient_matrix(t, p)
    trace_B = sum(trB[i][i] for i in range(len(trB)))
    trace_B2 = sum(trB[i][j] * trB[j][i]
                   for i in range(len(trB)) for j in range(len(trB)))
    check(f"trace identity: tr(B) + (t-2)(-1) = 0 = tr(A)",
          trace_B - (t - 2) == 0)
    check(f"trace identity: tr(B^2) + (t-2) = 2m = tr(A^2)",
          trace_B2 + (t - 2) == 2 * m)
    check(f"charpoly(B) has integer coefficients, degree {p+2} "
          f"(all-{p+2}-roots-real is asserted inside sturm_energy_enclosure)",
          all(isinstance(c, (int,)) or c.is_integer for c in co))
    print(f"    EXACT energy enclosure: [{float(lo):.12f}, {float(hi):.12f}] "
          f"(width {float(hi-lo):.2e})")
    check("exact enclosure consistent with mpmath energy",
          lo <= Fraction(str(emp)) if False else
          (float(lo) - 1e-9 <= float(emp) <= float(hi) + 1e-9))
    rhs_dp_frac = Fraction(n ** 3 * (n - 1), 2 * W_bfs)   # n^2/l_DP
    rhs_n2_frac = Fraction(n ** 4, 2 * W_bfs)             # n^2/l_N2
    check("EXACT (Sturm enclosure): energy_hi < n^2/l_DP  => MAD not violated (DP)",
          hi < rhs_dp_frac)
    check("EXACT (Sturm enclosure): energy_hi < n^2/l_N2  => MAD not violated (N2)",
          hi < rhs_n2_frac)
    # cross-check numpy spectrum against the certified multiset
    import numpy as np
    import sympy as sp
    roots = []
    for (a, b), mult in poly.intervals(eps=sp.Rational(1, 2 ** 40), sqf=False):
        mid = (Fraction(int(sp.numer(a)), int(sp.denom(a))) +
               Fraction(int(sp.numer(b)), int(sp.denom(b)))) / 2
        roots += [float(mid)] * mult
    certified = np.sort(np.array(roots + [-1.0] * (t - 2)))
    check("numpy spectrum == certified multiset roots(B) u {-1}^(t-2) (1e-8)",
          bool(np.max(np.abs(certified - np.sort(ev))) < 1e-8))


def scan_lollipops(nmax=130):
    """Exhaustive integer scan over all lollipops with 3 <= t, 1 <= p,
    n = t+p <= nmax. Returns sorted list of violators (n, t, p, dp, n2)."""
    out = []
    for n in range(4, nmax + 1):
        for t in range(3, n):
            p = n - t
            _, m, W, lhs, rdp, rn2 = stddev_violation_margins(t, p)
            dp, n2 = lhs > rdp, lhs > rn2
            if dp or n2:
                out.append((n, t, p, dp, n2))
    return out


def mutation_tests():
    """The checker must REJECT corrupted claims."""
    print("\n=== mutation self-tests (all must be rejected) ===")
    muts = [
        ("lollipop(47,70) n=117 claimed to violate DP",
         lambda: stddev_violation_margins(47, 70)[3] >
                 stddev_violation_margins(47, 70)[4]),
        ("lollipop(48,70) claimed to violate N2 (it must not)",
         lambda: stddev_violation_margins(48, 70)[3] >
                 stddev_violation_margins(48, 70)[5]),
        ("lollipop(72,72) with W corrupted by -1 still gives same margin",
         lambda: 8 * 2628 * (259080 - 1) ** 2 == 8 * 2628 * 259080 ** 2),
        ("path-only graph P_144 (t=2 degenerate) violates DP",
         lambda: stddev_violation_margins(2, 142)[3] >
                 stddev_violation_margins(2, 142)[4]),
        ("clique-only K_144 violates DP",
         lambda: stddev_violation_margins(144, 0)[3] >
                 stddev_violation_margins(144, 0)[4]),
        ("wrong closed form W+1 matches BFS at (72,72)",
         lambda: wiener_closed_form(72, 72) + 1 ==
                 bfs_all_pairs_wiener(144, adjacency_lists(
                     144, lollipop_edges(72, 72)))),
    ]
    for label, f in muts:
        rejected = not f()
        check(f"mutation rejected: {label}", rejected)


def main():
    print("Graffiti Conjecture 154 -- clean-room Gate-4 verification")
    print("Statement (WoW July 2004, decoded, verbatim): "
          "'154. deviation of eigenvalues <= n / average distance.'")

    # The three claimed instances
    verify_instance(72, 72, expect_dp=True, expect_n2=True, do_spectral=True)
    verify_instance(50, 70, expect_dp=True, expect_n2=True, do_spectral=True)
    verify_instance(48, 70, expect_dp=True, expect_n2=False, do_spectral=True)

    # specific margins from the claim record
    print("\n=== claim-record exact numbers ===")
    _, m, W, lhs, rdp, rn2 = stddev_violation_margins(72, 72)
    check("(72,72): m=2628", m == 2628)
    check("(72,72): W=259080", W == 259080)
    check("(72,72): 8mW^2 = 1411182313113600", lhs == 1411182313113600)
    check("(72,72): n^5(n-1)^2 = 1266148181016576", rdp == 1266148181016576)
    check("(72,72): n^7 = 1283918464548864", rn2 == 1283918464548864)
    _, _, _, lhs48, _, rn248 = stddev_violation_margins(48, 70)
    print(f"    (48,70): n^7 - 8mW^2 = {rn248 - lhs48}  (~5.1e12 claimed)")
    check("(48,70): N2 shortfall about 5.1e12",
          4.9e12 < (rn248 - lhs48) < 5.3e12)

    # exhaustive lollipop scan
    print("\n=== exhaustive lollipop scan n <= 130 ===")
    v = scan_lollipops(130)
    dp_only = [x for x in v if x[3]]
    both = [x for x in v if x[3] and x[4]]
    n2v = [x for x in v if x[4]]
    print(f"    violators found (any convention): {len(v)}")
    print(f"    first few: {v[:8]}")
    at118 = sorted(x[:3] for x in dp_only if x[0] == 118)
    at120 = sorted(x[:3] for x in both if x[0] == 120)
    print(f"    all DP violators at n=118: {at118}")
    print(f"    all both-convention violators at n=120: {at120}")
    check("minimal n for a DP-violating lollipop is 118, and (48,70) is one "
          "of them (claim said 'smallest found'; NOT unique: see list above)",
          min(x[0] for x in dp_only) == 118 and (118, 48, 70) in at118)
    check("minimal n for a both-conventions lollipop is 120, and (50,70) is "
          "one of them (NOT unique: see list above)",
          min(x[0] for x in both) == 120 and (120, 50, 70) in at120)
    check("no lollipop with n <= 117 violates either convention",
          all(x[0] >= 118 for x in v))
    check("every N2 violator also violates DP (n^7 > n^5(n-1)^2)",
          all(x[3] for x in n2v))

    mutation_tests()

    print("\n" + "=" * 70)
    if FAILURES:
        print(f"OVERALL: FAIL ({len(FAILURES)} failures)")
        for f in FAILURES:
            print("  -", f)
        sys.exit(1)
    print("OVERALL: ALL CHECKS PASS -- Conjecture 154 (std-dev reading) is "
          "REFUTED by lollipop(48,70)/(50,70)/(72,72); MAD reading NOT "
          "violated by these instances (proven exactly).")


if __name__ == "__main__":
    main()
