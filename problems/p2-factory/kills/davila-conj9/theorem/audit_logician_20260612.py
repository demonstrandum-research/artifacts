"""Adversarial audit of gamma-exact.md (logician lens), 2026-06-12.

Independent of validate_gamma_exact.py: the graph is built from the PROSE
adjacency table of gamma-exact.md section 3 (not from chain_study.chain),
the DP tables are recomputed from the section-5 feasibility conditions with
fresh code, the section-7 forcing cascade is replayed force-by-force with a
legality check at every single step, the fort case analyses of Lemma 6.2 are
checked for COMPLETENESS (every 3-subset must miss at least one *named*
fort, otherwise the hand case analysis has a hole even if the conclusion is
machine-true), and Lemma 6.1 is stress-tested on random graphs.

Exit 0 iff all checks pass.
"""

import os
import random
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)

FAIL = []


def check(name, cond):
    print(("pass " if cond else "FAIL ") + name, flush=True)
    if not cond:
        FAIL.append(name)


# ---------------------------------------------------------------- construction
# Straight from gamma-exact.md section 3 adjacency table (NOT from chain()).
# offsets: block 1 at 0; block i>=2 at 7+8*(i-2).
# a1a2a3 = o,o+1,o+2 ; b1b2b3 = o+3,o+4,o+5 ; s/p = o+6 ; q = o+7 (middle).
def build_from_prose(k):
    assert k >= 2
    def off(i):  # 1-based block index
        return 0 if i == 1 else 7 + 8 * (i - 2)

    E = set()

    def ae(u, v):
        assert u != v
        E.add((min(u, v), max(u, v)))

    for i in range(1, k + 1):
        o = off(i)
        a = {1: o, 2: o + 1, 3: o + 2}
        b = {1: o + 3, 2: o + 4, 3: o + 5}
        if i == 1 or i == k:
            s = o + 6
            # end block table: a1: b2,b3,s ; a2: b1,b2,b3 ; a3: b1,b2,b3 ;
            # b1: a2,a3,s ; (rest implied); s: a1,b1
            for y in (2, 3):
                ae(a[1], b[y])
            for y in (1, 2, 3):
                ae(a[2], b[y])
                ae(a[3], b[y])
            ae(s, a[1])
            ae(s, b[1])
        else:
            p, q = o + 6, o + 7
            # middle table: a1: b2,b3,p ; a2: b1,b3,q ; a3: b1,b2,b3 ;
            # p: a1,b1 ; q: a2,b2
            ae(a[1], b[2]); ae(a[1], b[3]); ae(a[1], p)
            ae(a[2], b[1]); ae(a[2], b[3]); ae(a[2], q)
            ae(a[3], b[1]); ae(a[3], b[2]); ae(a[3], b[3])
            ae(p, b[1])
            ae(q, b[2])
    # bridges q_i -- p_{i+1}; out-port of block 1 is its s; in-port of
    # block k is its s
    for i in range(1, k):
        qi = off(i) + 6 if i == 1 else off(i) + 7
        pi1 = off(i + 1) + 6
        ae(qi, pi1)
    n = 8 * k - 2
    return n, sorted(E)


def blocks_of(k):
    """[(verts, in_port, out_port)] 1-based block i -> 0-based ids."""
    def off(i):
        return 0 if i == 1 else 7 + 8 * (i - 2)
    out = []
    for i in range(1, k + 1):
        o = off(i)
        nb = 7 if i in (1, k) else 8
        verts = list(range(o, o + nb))
        ip = None if i == 1 else o + 6
        op = None if i == k else (o + 6 if i == 1 else o + 7)
        out.append((verts, ip, op))
    return out


def adjsets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        nbr[u] |= 1 << v
        nbr[v] |= 1 << u
    return nbr


# A. prose construction == certified edge files
def audit_A():
    ok = True
    for k in range(2, 9):
        with open(os.path.join(PARENT, f"chain_indep_k{k}.edges")) as f:
            t = f.read().split()
        nf, mf = int(t[0]), int(t[1])
        fe = sorted(tuple(sorted((int(t[2 + 2 * i]), int(t[3 + 2 * i]))))
                    for i in range(mf))
        n, e = build_from_prose(k)
        if (n, e) != (nf, fe):
            ok = False
            print(f"  mismatch at k={k}")
    check("A: prose adjacency table rebuild == certified .edges, k=2..8", ok)
    ok2 = True
    for k in range(2, 13):
        n, e = build_from_prose(k)
        adj = adjsets(n, e)
        if n != 8 * k - 2 or len(e) != 3 * n // 2:
            ok2 = False
        if any(len(adj[v]) != 3 for v in range(n)):
            ok2 = False
        seen = {0}
        fr = {0}
        while fr:
            fr = {w for v in fr for w in adj[v]} - seen
            seen |= fr
        if len(seen) != n:
            ok2 = False
        if any(adj[u] & adj[v] for u, v in e):
            ok2 = False
        # girth check sanity: triangle-free verified above via common nbrs
    check("A: connected/cubic/triangle-free/n=8k-2 from prose, k=2..12", ok2)


# B. DP tables recomputed from section-5 feasibility conditions
def block_table_fresh(adj, verts, ip, op):
    vset = set(verts)
    interior = [v for v in verts if v not in (ip, op)]
    for v in interior:
        assert adj[v] <= vset
    INF = 10 ** 9
    sin = [None] if ip is None else [0, 1, 2]   # 0=A,1=B,2=C
    sout = [None] if op is None else [0, 1, 2]
    T = {(si, so): INF for si in sin for so in sout}
    m = len(verts)
    for bits in range(1 << m):
        S = {verts[j] for j in range(m) if bits >> j & 1}
        # condition 1
        if any(not (({v} | adj[v]) & S) for v in interior):
            continue
        # condition 4 / state at out-port determined by S only
        if op is None:
            so = None
        elif op in S:
            so = 0
        elif (adj[op] & vset) & S:
            so = 1
        else:
            so = 2
        for si in sin:
            if ip is not None:
                dominated = (ip in S) or ((adj[ip] & vset) & S) or si == 0
                if not dominated:          # condition 2
                    continue
                if si == 2 and ip not in S:  # condition 3
                    continue
            T[(si, so)] = min(T[(si, so)], len(S))
    return T


EXP_V1 = (3, 2, 2)
EXP_M = {(0, 0): 3, (0, 1): 2, (0, 2): 2,
         (1, 0): 3, (1, 1): 3, (1, 2): 2,
         (2, 0): 3, (2, 1): 3, (2, 2): 3}
EXP_C = (2, 2, 3)


def audit_B():
    n, e = build_from_prose(8)
    adj = adjsets(n, e)
    blks = blocks_of(8)
    tabs = [block_table_fresh(adj, v, ip, op) for v, ip, op in blks]
    first = tuple(tabs[0][(None, so)] for so in (0, 1, 2))
    last = tuple(tabs[-1][(si, None)] for si in (0, 1, 2))
    mids = tabs[1:-1]
    check("B: v1 = (3,2,2) [fresh enumeration]", first == EXP_V1)
    check("B: c = (2,2,3) [fresh enumeration]", last == EXP_C)
    check("B: all 6 middle blocks of G_8 give identical table",
          all(t == mids[0] for t in mids))
    check("B: M = [[3,2,2],[3,3,2],[3,3,3]] [fresh enumeration]",
          mids[0] == EXP_M)
    # Step-3 claim of Lemma 5.2: the only cost-2 feasible (si,S,so) cells
    # are (A->B),(A->C),(B->C); realized only by the three core pairs.
    verts, ip, op = blks[3]
    cost2_cells = set()
    cost2_sets = set()
    m = len(verts)
    for bits in range(1 << m):
        S = {verts[j] for j in range(m) if bits >> j & 1}
        if len(S) != 2:
            continue
        if any(not (({v} | adj[v]) & S) for v in verts
               if v not in (ip, op)):
            continue
        so = 0 if op in S else (1 if (adj[op] & set(verts)) & S else 2)
        for si in (0, 1, 2):
            dom = (ip in S) or ((adj[ip] & set(verts)) & S) or si == 0
            if not dom or (si == 2 and ip not in S):
                continue
            cost2_cells.add((si, so))
            cost2_sets.add(frozenset(v - verts[0] for v in S))
    check("B: cost-2 cells exactly {(A,B),(A,C),(B,C)}",
          cost2_cells == {(0, 1), (0, 2), (1, 2)})
    check("B: cost-2 feasible sets exactly the three core pairs",
          cost2_sets == {frozenset({0, 3}), frozenset({1, 4}),
                         frozenset({2, 5})})
    return tabs


def dp_gamma(k):
    n, e = build_from_prose(k)
    adj = adjsets(n, e)
    blks = blocks_of(k)
    tabs = [block_table_fresh(adj, v, ip, op) for v, ip, op in blks]
    vec = [tabs[0][(None, so)] for so in (0, 1, 2)]
    hist = [tuple(vec)]
    for t in tabs[1:-1]:
        vec = [min(vec[si] + t[(si, so)] for si in (0, 1, 2))
               for so in (0, 1, 2)]
        hist.append(tuple(vec))
    g = min(vec[si] + tabs[-1][(si, None)] for si in (0, 1, 2))
    return g, hist


def gamma_brute(n, edges, upto):
    """Return min |D| dominating, exhaustively, or None if > upto."""
    closed = []
    adj = adjsets(n, edges)
    for v in range(n):
        mm = 1 << v
        for w in adj[v]:
            mm |= 1 << w
        closed.append(mm)
    full = (1 << n) - 1
    for r in range(upto + 1):
        for D in combinations(range(n), r):
            cov = 0
            for v in D:
                cov |= closed[v]
            if cov == full:
                return r
    return None


def audit_C():
    g2, _ = dp_gamma(2)
    g3, _ = dp_gamma(3)
    b2 = gamma_brute(*build_from_prose(2), upto=5)
    b3 = gamma_brute(*build_from_prose(3), upto=7)
    check("C: brute gamma(G_2) = 4 = DP", b2 == 4 == g2)
    check("C: brute gamma(G_3) = 7 = DP", b3 == 7 == g3)
    ok = all(dp_gamma(k)[0] == 7 * k // 3 for k in range(2, 31))
    check("C: DP gamma = floor(7k/3), k=2..30 [fresh tables every k]", ok)
    _, hist = dp_gamma(40)
    check("C: v_{i+3} = v_i + 7 along k=40 [fresh]",
          all(hist[i + 3] == tuple(x + 7 for x in hist[i])
              for i in range(len(hist) - 3)))
    # CP-SAT independent model
    try:
        from ortools.sat.python import cp_model
    except Exception:
        print("skip CP-SAT (no ortools)")
        return
    ok = True
    for k in range(2, 11):
        n, e = build_from_prose(k)
        adj = adjsets(n, e)
        mo = cp_model.CpModel()
        x = [mo.NewBoolVar(str(v)) for v in range(n)]
        for v in range(n):
            mo.Add(x[v] + sum(x[u] for u in adj[v]) >= 1)
        mo.Minimize(sum(x))
        so = cp_model.CpSolver()
        so.parameters.num_workers = 16
        if so.Solve(mo) != cp_model.OPTIMAL or \
                int(so.ObjectiveValue()) != 7 * k // 3:
            ok = False
    check("C: CP-SAT gamma = floor(7k/3), k=2..10 [own model]", ok)


# D. blocks S1,S2: Z = 4; named forts; case-analysis completeness
def closure(nbr, blue, n):
    full = (1 << n) - 1
    while True:
        add = 0
        for v in range(n):
            if blue >> v & 1:
                w = nbr[v] & ~blue
                if w and w & (w - 1) == 0:
                    add |= w
        if add & ~blue == 0:
            return blue
        blue |= add
    return blue


def block_graph(kind):
    """S1 (end, 7 vts) or S2 (middle, 8 vts), local labels
    a1a2a3=0,1,2 b1b2b3=3,4,5 s/p=6 q=7, built from the prose table."""
    E = []
    if kind == "S1":
        E = [(0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
             (6, 0), (6, 3)]
        n = 7
    else:
        E = [(0, 4), (0, 5), (0, 6), (1, 3), (1, 5), (1, 7),
             (2, 3), (2, 4), (2, 5), (6, 3), (7, 4)]
        n = 8
    return n, E


def is_fort(n, adj, F):
    return bool(F) and all(len(adj[v] & F) != 1
                           for v in range(n) if v not in F)


def audit_D():
    for kind, exp in (("S1", 4), ("S2", 4)):
        n, e = block_graph(kind)
        nbr = masks(n, e)
        full = (1 << n) - 1
        z = None
        for r in range(n + 1):
            if any(closure(nbr, sum(1 << v for v in S), n) == full
                   for S in combinations(range(n), r)):
                z = r
                break
        check(f"D: Z({kind}) = 4 [fresh exhaustive]", z == exp)
    # named forts (doc labels -> local ids)
    n1, e1 = block_graph("S1")
    a1 = adjsets(n1, e1)
    s1_forts = [{1, 2}, {4, 5}, {0, 2, 6}, {3, 5, 6}, {0, 2, 3, 5}]
    check("D: the 5 named S1 forts are forts",
          all(is_fort(n1, a1, F) for F in s1_forts))
    n2, e2 = block_graph("S2")
    a2 = adjsets(n2, e2)
    s2_forts = [{0, 2, 6}, {1, 2, 7}, {3, 5, 6}, {4, 5, 7}, {0, 1, 3, 4},
                {0, 2, 3, 5}, {1, 2, 4, 5}, {0, 1, 6, 7}, {3, 4, 6, 7},
                {0, 2, 3, 7}, {0, 3, 5, 7}]
    check("D: the 11 named S2 forts are forts",
          all(is_fort(n2, a2, F) for F in s2_forts))
    # COMPLETENESS of the hand case analyses.  The written proofs first
    # normalize B by the named automorphisms (WLOG), so the correct
    # criterion is: every 3-subset misses some fort in the ORBIT of the
    # named forts under the group generated by the named automorphisms.
    # (The strict no-WLOG version is false -- e.g. S1's {a3,b3,s} meets
    # all five named forts directly but maps under the swaps to
    # {a2,b2,s}, which misses F5; see audit_wlog_completeness.py.)
    def group_closure(nn, gens):
        ident = tuple(range(nn))
        G = {ident}
        fr = {ident}
        while fr:
            new = set()
            for g in fr:
                for h in gens:
                    gh = tuple(h[g[i]] for i in range(nn))
                    if gh not in G:
                        new.add(gh)
            G |= new
            fr = new
        return G

    grp1 = group_closure(n1, [(0, 2, 1, 3, 4, 5, 6),
                              (0, 1, 2, 3, 5, 4, 6)])
    orb1 = {frozenset(g[v] for v in F) for F in s1_forts for g in grp1}
    hole1 = [S for S in combinations(range(n1), 3)
             if all(set(S) & F for F in orb1)]
    check("D: every 3-subset of S1 misses a named fort modulo the WLOG "
          "automorphisms (case analysis complete)", not hole1)
    grp2 = group_closure(n2, [(3, 4, 5, 0, 1, 2, 6, 7),
                              (1, 0, 2, 4, 3, 5, 7, 6)])
    orb2 = {frozenset(g[v] for v in F) for F in s2_forts for g in grp2}
    hole2 = [S for S in combinations(range(n2), 3)
             if all(set(S) & F for F in orb2)]
    check("D: every 3-subset of S2 misses a named fort modulo the WLOG "
          "automorphisms (case analysis complete)", not hole2)
    # side claim: S2 has 14 inclusion-minimal forts
    all_forts = [frozenset(F) for r in range(1, n2 + 1)
                 for F in combinations(range(n2), r)
                 if is_fort(n2, a2, set(F))]
    minimal = [F for F in all_forts
               if not any(G < F for G in all_forts)]
    check("D: S2 has exactly 14 inclusion-minimal forts (side claim)",
          len(minimal) == 14)
    # automorphisms used in WLOG steps
    def is_auto(n, adj, perm):
        return all((perm[v] in adj[perm[u]]) == (v in adj[u])
                   for u in range(n) for v in range(n) if u != v)
    check("D: S1 swaps a2<->a3, b2<->b3 are automorphisms",
          is_auto(n1, a1, [0, 2, 1, 3, 4, 5, 6]) and
          is_auto(n1, a1, [0, 1, 2, 3, 5, 4, 6]))
    check("D: S2 alpha, beta are automorphisms",
          is_auto(n2, a2, [3, 4, 5, 0, 1, 2, 6, 7]) and
          is_auto(n2, a2, [1, 0, 2, 4, 3, 5, 7, 6]))


# E. replay the section-7 cascade with per-force legality
def audit_E():
    ok = True
    for k in range(2, 13):
        n, e = build_from_prose(k)
        nbr = masks(n, e)
        blks = blocks_of(k)
        blue = 0
        for j, (verts, ip, op) in enumerate(blks):
            o = verts[0]
            init = [o, o + 1, o + 3, o + 4] if j == 0 else [o, o + 1, o + 4]
            for v in init:
                blue |= 1 << v
        full = (1 << n) - 1

        def force(u, v):
            nonlocal blue, ok
            if not (blue >> u & 1):
                ok = False
            if blue >> v & 1:
                ok = False
            if nbr[u] & ~blue != 1 << v:
                ok = False
            blue |= 1 << v

        for j, (verts, ip, op) in enumerate(blks):
            o = verts[0]
            A = {1: o, 2: o + 1, 3: o + 2}
            B = {1: o + 3, 2: o + 4, 3: o + 5}
            if j == 0:
                s = o + 6
                force(A[2], B[3]); force(B[2], A[3]); force(A[1], s)
                force(s, op and (blks[j + 1][0][0] + 6))
            elif j < k - 1:
                p, q = o + 6, o + 7
                force(p, B[1]); force(A[1], B[3]); force(A[2], q)
                force(B[2], A[3])
                force(q, blks[j + 1][0][0] + 6)
            else:
                s = o + 6
                force(s, B[1]); force(A[2], B[3]); force(B[2], A[3])
        if blue != full:
            ok = False
    check("E: section-7 cascade legal force-by-force and exhausts V, "
          "k=2..12", ok)


# F. D_k from the section-4 prose, fresh domination check
def audit_F():
    ok = True
    for k in range(2, 41):
        n, e = build_from_prose(k)
        adj = adjsets(n, e)
        blks = blocks_of(k)
        D = []
        for j, (verts, ip, op) in enumerate(blks):
            o = verts[0]
            i = j + 1
            if i == 1:
                D += [o, o + 3]
            elif i == k:
                if k % 3 == 2:
                    D += [o, o + 3]
                elif k % 3 == 0:
                    D += [o + 6, o + 2, o + 5]
                else:
                    D += [o + 1, o + 4]
            else:
                if i % 3 == 2:
                    D += [o, o + 3]
                elif i % 3 == 0:
                    D += [o + 6, o + 5, o + 7]
                else:
                    D += [o + 1, o + 4]
        if len(D) != 7 * k // 3 or len(set(D)) != len(D):
            ok = False
        dom = set()
        for v in D:
            dom.add(v)
            dom |= adj[v]
        if len(dom) != n:
            ok = False
    check("F: section-4 D_k dominates with |D_k| = floor(7k/3), k=2..40",
          ok)


# G. stress-test Lemma 6.1 on random graphs
def z_exact(n, nbr):
    full = (1 << n) - 1
    if n == 0:
        return 0
    for r in range(n + 1):
        for S in combinations(range(n), r):
            if closure(nbr, sum(1 << v for v in S), n) == full:
                return r
    return n


def audit_G():
    rng = random.Random(20260612)
    bad = 0
    trials = 0
    for _ in range(150):
        n = rng.randint(4, 9)
        pe = rng.choice((0.25, 0.4, 0.55))
        edges = [(u, v) for u in range(n) for v in range(u + 1, n)
                 if rng.random() < pe]
        if not edges:
            continue
        nbr = masks(n, edges)
        zg = z_exact(n, nbr)
        for _ in range(6):
            m = rng.randint(1, min(4, len(edges)))
            Ep = rng.sample(edges, m)
            rem = [ed for ed in edges if ed not in Ep]
            # components of G - E'
            adj = adjsets(n, rem)
            unseen = set(range(n))
            total = 0
            while unseen:
                v0 = next(iter(unseen))
                comp = {v0}
                fr = {v0}
                while fr:
                    fr = {w for v in fr for w in adj[v]} - comp
                    comp |= fr
                unseen -= comp
                cl = sorted(comp)
                idx = {v: i for i, v in enumerate(cl)}
                ce = [(idx[u], idx[v]) for u, v in rem
                      if u in comp and v in comp]
                total += z_exact(len(cl), masks(len(cl), ce))
            trials += 1
            if zg < total - len(Ep):
                bad += 1
                print(f"  VIOLATION n={n} edges={edges} Ep={Ep} "
                      f"Z={zg} sum={total}")
    check(f"G: Lemma 6.1 holds on {trials} random (G,E') instances", bad == 0)
    # the actual application: G_2 minus its bridge
    n, e = build_from_prose(2)
    nbr = masks(n, e)
    z = z_exact(n, nbr)
    check("G: Z(G_2) = 7 = 4 + 4 - 1 exactly [fresh exhaustive]", z == 7)


# H. arithmetic identities
def audit_H():
    ok = all(3 * k + 1 - (7 * k // 3) == -((-(2 * k + 3)) // 3)
             for k in range(2, 10 ** 6))
    ok2 = all(-((-(2 * k + 3)) // 3) == -((-(8 * k - 2 + 14)) // 12)
              for k in range(2, 10 ** 6))
    check("H: 3k+1-floor(7k/3) = ceil((2k+3)/3) = ceil((n+14)/12), "
          "k < 10^6", ok and ok2)
    check("H: gap table row k=2..10 = (3,3,4,5,5,6,7,7,8)",
          tuple(3 * k + 1 - 7 * k // 3 for k in range(2, 11)) ==
          (3, 3, 4, 5, 5, 6, 7, 7, 8))


def main():
    audit_A()
    audit_B()
    audit_C()
    audit_D()
    audit_E()
    audit_F()
    audit_G()
    audit_H()
    print()
    if FAIL:
        print(f"AUDIT FAILURES ({len(FAIL)}):")
        for f in FAIL:
            print("  " + f)
        sys.exit(1)
    print("AUDIT: ALL CHECKS PASSED")
    sys.exit(0)


if __name__ == "__main__":
    main()
