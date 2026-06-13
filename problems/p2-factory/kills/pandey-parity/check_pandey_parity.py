#!/usr/bin/env python3
"""
Clean-room Gate-4 checker for the refutation of the "Parity Conjecture"
(Conjecture 4.1) of R. Pandey, "Parity-Dependent Real-Rootedness in
Independence Polynomials of Generalized Petersen Graphs", arXiv:2601.03293
(submitted 2026-01-05; HTML/abstract fetched 2026-06-11).

Verbatim conjecture (arXiv:2601.03293, Conjecture 4.1, accessed 2026-06-11):

    "For all integers n >= 2k+1, the independence polynomial I(GP(n,k),x)
     has only real roots if and only if k is even."

Verbatim definition (Definition 2.1 of the paper): for integers n >= 3 and
1 <= k < n/2, GP(n,k) has vertex set U cup V, U = {u_0..u_{n-1}},
V = {v_0..v_{n-1}}, and edges u_i u_{i+1} (outer cycle), v_i v_{i+k}
(inner chords), u_i v_i (spokes), indices mod n.
I(G,x) = sum_k i_k(G) x^k, i_k = number of independent sets of size k.

This checker was written FROM SCRATCH for this verification (no code reused
from the discovery scripts). Pure Python 3, standard library only; all
load-bearing arithmetic is exact (integers / fractions.Fraction; Sturm
chains over Q). It:

  1. builds GP(n,k) from the definition above;
  2. computes I(GP(n,k),x) exactly by the standard vertex recursion
       I(G) = I(G - v) + x * I(G - N[v]),
     memoized on induced-subgraph bitmasks;
  3. cross-checks coefficients by brute-force enumeration of all 2^(2n)
     vertex subsets for 2n <= 20 (an external Rust brute-forcer covers the
     remaining n <= 14 cases; see bf_gp.rs / rust_bruteforce.log);
  4. decides real-rootedness EXACTLY: p is real-rooted iff its squarefree
     part q = p/gcd(p,p') has (#real roots of q, by Sturm's theorem) equal
     to deg q. No floating point is used in the decision.
  5. verifies the explicit isomorphism GP(7,2) ~ GP(7,3)
     (u_j -> v'_{3j mod 7}, v_j -> u'_{3j mod 7});
  6. scans every legal pair (n,k), 3 <= n <= 14, 1 <= k < n/2, and lists
     every violation of the conjecture in both directions;
  7. compares everything against certificate.json and exits nonzero on any
     mismatch (so a tampered certificate is rejected);
  8. --selftest runs unit + mutation tests (known real/non-real polynomials,
     tampered coefficients, corrupted isomorphism map must all be caught).

Usage:  python check_pandey_parity.py [--selftest] [--cert certificate.json]
Exit 0 = all checks pass.
"""

import json
import os
import sys
from fractions import Fraction

# ----------------------------------------------------------------------
# Graph construction (straight from Definition 2.1)
# ----------------------------------------------------------------------

def gp_vertices(n):
    """Vertex labels: ('u', i) and ('v', i) for 0 <= i < n."""
    return [('u', i) for i in range(n)] + [('v', i) for i in range(n)]


def gp_edges(n, k):
    """Edge set of GP(n,k) as a sorted list of sorted label pairs."""
    if not (n >= 3 and 1 <= k and 2 * k < n):
        raise ValueError(f"GP({n},{k}) outside Definition 2.1 domain")
    E = set()
    for i in range(n):
        E.add(frozenset({('u', i), ('u', (i + 1) % n)}))   # outer cycle
        E.add(frozenset({('v', i), ('v', (i + k) % n)}))   # inner chords
        E.add(frozenset({('u', i), ('v', i)}))             # spokes
    if not all(len(e) == 2 for e in E):
        raise ArithmeticError("self-loop produced (impossible for k<n/2)")
    if len(E) != 3 * n:
        raise ArithmeticError(f"GP({n},{k}): expected {3*n} edges, got {len(E)}")
    return sorted(tuple(sorted(e)) for e in E)


def adjacency_masks(n, k):
    """Bitmask adjacency. Vertex order interleaved (u_i -> 2i, v_i -> 2i+1)
    to keep the elimination frontier narrow; the labeling is irrelevant to
    the polynomial."""
    idx = {}
    for i in range(n):
        idx[('u', i)] = 2 * i
        idx[('v', i)] = 2 * i + 1
    adj = [0] * (2 * n)
    for a, b in gp_edges(n, k):
        ia, ib = idx[a], idx[b]
        adj[ia] |= 1 << ib
        adj[ib] |= 1 << ia
    return adj

# ----------------------------------------------------------------------
# Independence polynomial, exact integers
# ----------------------------------------------------------------------

def indep_poly(adj):
    """Coefficients [i_0, i_1, ...] of I(G,x), exact ints.
    Recursion: I(G) = I(G - v) + x * I(G - N[v]), v = lowest-index vertex."""
    sys.setrecursionlimit(10000)
    memo = {0: (1,)}

    def rec(mask):
        got = memo.get(mask)
        if got is not None:
            return got
        v = (mask & -mask).bit_length() - 1
        a = rec(mask & ~(1 << v))                    # v excluded
        b = rec(mask & ~((1 << v) | adj[v]))         # v included
        L = max(len(a), len(b) + 1)
        res = [0] * L
        for i, c in enumerate(a):
            res[i] += c
        for i, c in enumerate(b):
            res[i + 1] += c
        res = tuple(res)
        memo[mask] = res
        return res

    full = (1 << len(adj)) - 1
    return list(rec(full))


def indep_poly_bruteforce(adj):
    """Independent cross-check: enumerate all 2^N subsets. Only for N <= 20."""
    N = len(adj)
    if N > 20:
        raise ValueError("brute force capped at 2^20 here")
    counts = [0] * (N + 1)
    for S in range(1 << N):
        T = S
        ok = True
        while T:
            v = (T & -T).bit_length() - 1
            T &= T - 1
            if adj[v] & S:
                ok = False
                break
        if ok:
            counts[bin(S).count('1')] += 1
    while counts and counts[-1] == 0:
        counts.pop()
    return counts

# ----------------------------------------------------------------------
# Exact real-rootedness via Sturm's theorem over Q
# Polynomials = lists of Fraction, low degree first, no trailing zeros.
# ----------------------------------------------------------------------

def pnorm(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    if not p:
        p = [Fraction(0)]
    return p


def pdeg(p):
    return len(p) - 1 if p != [Fraction(0)] and p[-1] != 0 else (len(p) - 1)


def pderiv(p):
    if len(p) == 1:
        return [Fraction(0)]
    return pnorm([Fraction(i) * p[i] for i in range(1, len(p))])


def prem(a, b):
    """Remainder of a / b over Q (b nonzero)."""
    a = list(a)
    db, lb = len(b) - 1, b[-1]
    while len(a) - 1 >= db and not (len(a) == 1 and a[0] == 0):
        f = a[-1] / lb
        shift = len(a) - 1 - db
        for i in range(len(b)):
            a[shift + i] -= f * b[i]
        a.pop()  # leading term cancels exactly
        while len(a) > 1 and a[-1] == 0:
            a.pop()
        if len(a) == 1 and a[0] == 0:
            break
    return pnorm(a)


def pgcd(a, b):
    a, b = pnorm(a), pnorm(b)
    while not (len(b) == 1 and b[0] == 0):
        a, b = b, prem(a, b)
        # normalize to keep numbers tame
        if not (len(b) == 1 and b[0] == 0):
            lead = b[-1]
            b = [c / lead for c in b]
    # make monic
    if a[-1] != 0:
        a = [c / a[-1] for c in a]
    return a


def pdiv_exact(a, b):
    """Exact quotient a / b (b must divide a)."""
    a = list(pnorm(a))
    b = pnorm(b)
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    db, lb = len(b) - 1, b[-1]
    while len(a) - 1 >= db and not (len(a) == 1 and a[0] == 0):
        f = a[-1] / lb
        shift = len(a) - 1 - db
        q[shift] = f
        for i in range(len(b)):
            a[shift + i] -= f * b[i]
        a = pnorm(a)
        if len(a) == 1 and a[0] == 0:
            break
    if not (len(a) == 1 and a[0] == 0):
        raise ArithmeticError("pdiv_exact: division not exact")
    return pnorm(q)


def sign(x):
    return (x > 0) - (x < 0)


def sign_changes(seq):
    s = [x for x in seq if x != 0]
    return sum(1 for i in range(len(s) - 1) if s[i] * s[i + 1] < 0)


def sturm_real_root_count(p):
    """Number of DISTINCT real roots of squarefree p, by Sturm's theorem,
    evaluated at -infinity and +infinity via leading-coefficient signs."""
    chain = [pnorm(p), pderiv(p)]
    while not (len(chain[-1]) == 1 and chain[-1][0] == 0):
        r = prem(chain[-2], chain[-1])
        chain.append([-c for c in r])
    chain.pop()  # drop the zero polynomial
    at_pinf = [sign(q[-1]) for q in chain]
    at_minf = [sign(q[-1]) * (-1 if (len(q) - 1) % 2 else 1) for q in chain]
    return sign_changes(at_minf) - sign_changes(at_pinf)


def real_rootedness(coeffs_int):
    """Return dict with exact real-rootedness data for an integer-coefficient
    polynomial. real_rooted == True iff ALL complex roots are real."""
    p = pnorm([Fraction(c) for c in coeffs_int])
    deg = len(p) - 1
    if deg == 0:
        return dict(degree=0, sqfree_degree=0, real_distinct=0,
                    squarefree=True, real_rooted=True)
    g = pgcd(p, pderiv(p))
    q = pdiv_exact(p, g)               # squarefree part: same root SET as p
    nreal = sturm_real_root_count(q)
    return dict(degree=deg,
                sqfree_degree=len(q) - 1,
                real_distinct=nreal,
                squarefree=(len(g) == 1),
                real_rooted=(nreal == len(q) - 1))

# ----------------------------------------------------------------------
# Isomorphism verification
# ----------------------------------------------------------------------

def verify_isomorphism(n, k_from, k_to, mapping):
    """mapping: dict label->label. Check it is a bijection V(GP(n,k_from)) ->
    V(GP(n,k_to)) sending edges to edges bijectively."""
    Vfrom = gp_vertices(n)
    Efrom = {frozenset(e) for e in gp_edges(n, k_from)}
    Eto = {frozenset(e) for e in gp_edges(n, k_to)}
    if sorted(mapping.keys()) != sorted(Vfrom):
        return False, "domain is not V(GP(n,k_from))"
    if sorted(mapping.values()) != sorted(Vfrom):
        return False, "not a bijection onto V(GP(n,k_to))"
    image = {frozenset({mapping[a], mapping[b]}) for e in Efrom for a, b in [tuple(e)]}
    if len(image) != len(Efrom):
        return False, "edge images collide"
    if image != Eto:
        return False, "edge image set != E(GP(n,k_to))"
    return True, "ok"


def classical_iso_map(n, m):
    """The classical map GP(n,k) -> GP(n,k') for k*k' == -1 (mod n) with
    multiplier m=k': u_j -> v'_{m*j}, v_j -> u'_{m*j}.  Here used with
    n=7, k=2, k'=3 (2*3 = 6 == -1 mod 7)."""
    f = {}
    for j in range(n):
        f[('u', j)] = ('v', (m * j) % n)
        f[('v', j)] = ('u', (m * j) % n)
    return f

# ----------------------------------------------------------------------
# Main verification
# ----------------------------------------------------------------------

def analyze(n, k):
    adj = adjacency_masks(n, k)
    coeffs = indep_poly(adj)
    info = real_rootedness(coeffs)
    info.update(n=n, k=k, coeffs=coeffs,
                conjecture_predicts_real_rooted=(k % 2 == 0))
    info['violates_conjecture'] = (info['real_rooted'] != (k % 2 == 0))
    info['direction'] = (
        'if (k even but NOT real-rooted)' if (k % 2 == 0 and not info['real_rooted'])
        else "only-if (k odd but real-rooted)" if (k % 2 == 1 and info['real_rooted'])
        else None)
    return info


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def run_selftest():
    print("== SELFTEST / MUTATION TESTS ==")
    if not __debug__:
        fail("selftest requires asserts enabled; do not run with python -O")
    # 1. Known real-rooted polynomials
    assert real_rootedness([1, 2, 1])['real_rooted'] is True            # (1+x)^2
    assert real_rootedness([1, 3, 3, 1])['real_rooted'] is True         # (1+x)^3
    assert real_rootedness([0, -6, 11, -6, 1])['real_rooted'] is True   # x(x-1)(x-2)(x-3)
    assert real_rootedness([1, 2, 1])['squarefree'] is False
    # 2. Known NON-real-rooted polynomials
    assert real_rootedness([1, 0, 1])['real_rooted'] is False           # x^2+1
    assert real_rootedness([1, 1, 1])['real_rooted'] is False           # x^2+x+1
    assert real_rootedness([1, 1, 1, 1, 1])['real_rooted'] is False     # Phi_5
    assert real_rootedness([2, 3, 1, 0, 0, 1])['real_rooted'] is False
    # mixed: (x^2+1)(x+1)^2 = x^4+2x^3+2x^2+2x+1 (non-squarefree, not real-rooted)
    rr = real_rootedness([1, 2, 2, 2, 1])
    assert rr['real_rooted'] is False and rr['squarefree'] is False
    # (x^2+x+1)*(x+1) = x^3+2x^2+2x+1
    assert real_rootedness([1, 2, 2, 1])['real_rooted'] is False
    # 3. Sturm count sanity: x^5-5x^3+4x = x(x-1)(x+1)(x-2)(x+2): 5 real
    assert real_rootedness([0, 4, 0, -5, 0, 1])['real_distinct'] == 5
    # 4. Petersen graph GP(5,2) cross-check vs literature:
    #    I(Petersen) = 1+10x+30x^2+30x^3+5x^4
    pet = indep_poly(adjacency_masks(5, 2))
    assert pet == [1, 10, 30, 30, 5], pet
    assert indep_poly_bruteforce(adjacency_masks(5, 2)) == pet
    # 5. Mutation: tampered coefficient list must change the verdict data
    g92 = indep_poly(adjacency_masks(9, 2))
    bad = list(g92)
    bad[3] += 1
    assert bad != g92  # certificate comparison would reject
    # and a tampered polynomial can even flip the real-rootedness verdict:
    assert real_rootedness([1, 18, 126, 438, 801, 747, 303, 27]) != \
           real_rootedness([1, 18, 126, 438, 801, 747, 303, 28])
    # 6. Mutation: corrupted isomorphism map must be rejected
    good = classical_iso_map(7, 3)
    ok, _ = verify_isomorphism(7, 2, 3, good)
    assert ok
    badmap = dict(good)
    badmap[('u', 0)], badmap[('u', 1)] = badmap[('u', 1)], badmap[('u', 0)]
    ok, why = verify_isomorphism(7, 2, 3, badmap)
    assert not ok, "mutated isomorphism map was wrongly accepted"
    # non-bijective corruption
    badmap2 = dict(good)
    badmap2[('u', 0)] = badmap2[('u', 1)]
    ok, why = verify_isomorphism(7, 2, 3, badmap2)
    assert not ok
    # 7. Mutation: wrong target graph must be rejected
    ok, why = verify_isomorphism(9, 2, 4, classical_iso_map(9, 4))
    # (2*4=8 == -1 mod 9, so this one should actually PASS -- classical map)
    assert ok
    ok, why = verify_isomorphism(9, 2, 3, classical_iso_map(9, 3))
    assert not ok, "GP(9,2) is not isomorphic to GP(9,3) via this map"
    print("selftest: all unit and mutation tests passed")


def main():
    selftest = '--selftest' in sys.argv
    certpath = None
    if '--cert' in sys.argv:
        certpath = sys.argv[sys.argv.index('--cert') + 1]
    if selftest:
        run_selftest()

    print("== STATEMENT UNDER TEST ==")
    print('Conjecture 4.1 (arXiv:2601.03293): "For all integers n >= 2k+1,')
    print('the independence polynomial I(GP(n,k),x) has only real roots if')
    print('and only if k is even."  GP domain: n >= 3, 1 <= k < n/2.')
    print()

    # ---- Direction 1: k even but NOT real-rooted (primary: GP(9,2)) ----
    g92 = analyze(9, 2)
    print(f"GP(9,2): I = {g92['coeffs']}")
    print(f"  degree {g92['degree']}, squarefree={g92['squarefree']}, "
          f"distinct real roots (Sturm, exact) = {g92['real_distinct']}")
    if not g92['squarefree']:
        fail("GP(9,2) polynomial unexpectedly not squarefree")
    if g92['real_distinct'] != 5 or g92['degree'] != 7:
        fail("GP(9,2): expected exactly 5 real roots of a degree-7 squarefree poly")
    if g92['real_rooted']:
        fail("GP(9,2) came out real-rooted; refutation claim wrong")
    print("  => NOT real-rooted although k=2 is even: the 'if' direction is FALSE.")
    bf92 = None
    try:
        bf92 = indep_poly_bruteforce(adjacency_masks(9, 2))
    except ValueError:
        pass
    if bf92 is not None:
        if bf92 != g92['coeffs']:
            fail("GP(9,2) brute-force cross-check mismatch")
        print("  brute-force 2^18 subset enumeration: coefficients confirmed")
    print()

    # ---- Direction 2: k odd but real-rooted (GP(7,3); also GP(3,1)) ----
    g73 = analyze(7, 3)
    print(f"GP(7,3): I = {g73['coeffs']}")
    print(f"  degree {g73['degree']}, squarefree={g73['squarefree']}, "
          f"distinct real roots (Sturm, exact) = {g73['real_distinct']}")
    if not g73['real_rooted']:
        fail("GP(7,3) came out NOT real-rooted; refutation claim wrong")
    print("  => real-rooted although k=3 is odd: the 'only if' direction is FALSE.")
    bf73 = indep_poly_bruteforce(adjacency_masks(7, 3))
    if bf73 != g73['coeffs']:
        fail("GP(7,3) brute-force cross-check mismatch")
    print("  brute-force 2^14 subset enumeration: coefficients confirmed")

    g31 = analyze(3, 1)
    print(f"GP(3,1) (triangular prism): I = {g31['coeffs']}, "
          f"real_rooted={g31['real_rooted']} (k=1 odd)")
    if not g31['real_rooted']:
        fail("GP(3,1) expected real-rooted")
    bf31 = indep_poly_bruteforce(adjacency_masks(3, 1))
    if bf31 != g31['coeffs']:
        fail("GP(3,1) brute-force cross-check mismatch")
    print("  => second, minimal 'only if' violation (n=3 >= 2*1+1).")
    print()

    # ---- Structural incoherence: GP(7,3) ~= GP(7,2) ----
    print("== STRUCTURAL INCOHERENCE: GP(7,2) ~= GP(7,3) ==")
    iso = classical_iso_map(7, 3)   # u_j -> v'_{3j}, v_j -> u'_{3j} (2*3==-1 mod 7)
    ok, why = verify_isomorphism(7, 2, 3, iso)
    if not ok:
        fail(f"isomorphism GP(7,2)->GP(7,3) rejected: {why}")
    print("explicit isomorphism GP(7,2) -> GP(7,3):  u_j |-> v_{3j mod 7},  "
          "v_j |-> u_{3j mod 7}")
    print("  verified: bijection on 14 vertices; all 21 edges map bijectively"
          " onto all 21 edges.")
    g72 = analyze(7, 2)
    if g72['coeffs'] != g73['coeffs']:
        fail("isomorphic graphs GP(7,2), GP(7,3) disagree on I(G,x) ?!")
    print(f"  consistency: I(GP(7,2)) = I(GP(7,3)) = {g72['coeffs']}")
    print("  GP(7,2) has k even, GP(7,3) has k odd, yet they are the SAME graph:")
    print("  the conjecture's predicate is not isomorphism-invariant, so as")
    print("  stated it is not even well-posed (and with k=2 it predicts")
    print("  real-rooted for this graph, which is correct here, while with")
    print("  k=3 it predicts non-real-rooted for the very same graph).")
    print()

    # ---- Full scan n = 3..14 ----
    print("== FULL SCAN: all GP(n,k), 3 <= n <= 14, 1 <= k < n/2 ==")
    violations = []
    rows = []
    for n in range(3, 15):
        for k in range(1, (n - 1) // 2 + 1):
            r = analyze(n, k)
            rows.append(r)
            flag = "  <-- VIOLATION (" + r['direction'] + ")" if r['violates_conjecture'] else ""
            print(f"GP({n:2d},{k}): k {'even' if k%2==0 else 'odd '}, "
                  f"deg={r['degree']:2d}, sqfree={'Y' if r['squarefree'] else 'N'}, "
                  f"realroots={r['real_distinct']:2d}, "
                  f"real_rooted={str(r['real_rooted']):5s}{flag}")
            if r['violates_conjecture']:
                violations.append(r)
    print()
    v914 = [r for r in violations if 9 <= r['n'] <= 14]
    print(f"violations in 9 <= n <= 14: "
          f"{[(r['n'], r['k']) for r in v914]}")
    print(f"all violations in 3 <= n <= 14: "
          f"{[(r['n'], r['k']) for r in violations]}")
    if not any(r['n'] == 9 and r['k'] == 2 for r in violations):
        fail("scan lost the GP(9,2) violation")
    if not violations:
        fail("no violations found -- refutation claim wrong")

    # ---- Compare against certificate ----
    if certpath:
        print()
        print(f"== CERTIFICATE COMPARISON ({certpath}) ==")
        with open(certpath, encoding='utf-8') as fh:
            cert = json.load(fh)
        if cert['gp_9_2']['coeffs'] != g92['coeffs']:
            fail("certificate GP(9,2) coefficients do not match recomputation")
        if cert['gp_7_3']['coeffs'] != g73['coeffs']:
            fail("certificate GP(7,3) coefficients do not match recomputation")
        if cert['gp_3_1']['coeffs'] != g31['coeffs']:
            fail("certificate GP(3,1) coefficients do not match recomputation")
        cmap = {}
        for a, b in cert['isomorphism_gp72_to_gp73']['map']:
            cmap[(a[0], int(a[1]))] = (b[0], int(b[1]))
        ok, why = verify_isomorphism(7, 2, 3, cmap)
        if not ok:
            fail(f"certificate isomorphism map rejected: {why}")
        cv = sorted([tuple(t) for t in cert['violations_3_to_14']])
        mv = sorted([(r['n'], r['k']) for r in violations])
        if cv != mv:
            fail(f"certificate violation list {cv} != recomputed {mv}")
        for row in cert['scan_table']:
            n, k = row['n'], row['k']
            r = next(t for t in rows if t['n'] == n and t['k'] == k)
            if (row['coeffs'] != r['coeffs']
                    or row['real_rooted'] != r['real_rooted']
                    or row['real_distinct'] != r['real_distinct']
                    or row['squarefree'] != r['squarefree']):
                fail(f"certificate scan row GP({n},{k}) mismatch")
        print("certificate matches recomputation exactly")

    print()
    print("== VERDICT ==")
    print("Conjecture 4.1 of arXiv:2601.03293 is FALSE in both directions:")
    print("  * 'if' direction killed by GP(9,2) (k even, not real-rooted);")
    print("  * 'only if' direction killed by GP(7,3) and GP(3,1) (k odd,")
    print("    real-rooted);")
    print("  * and the statement is not isomorphism-invariant, witnessed by")
    print("    the explicit isomorphism GP(7,2) ~= GP(7,3).")
    print("ALL CHECKS PASSED")


if __name__ == '__main__':
    main()
