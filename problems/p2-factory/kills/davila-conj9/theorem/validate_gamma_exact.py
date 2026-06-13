"""
validate_gamma_exact.py -- computational validation suite for gamma-exact.md
(exact domination and zero-forcing numbers of the chain family G_k).

Pure stdlib Python.  Exit code 0 iff every check passes.

What is validated (each item is a lemma or finite claim used in the proof):

  V1  The construction here is byte-identical to the certified family
      (edge lists match chain_indep_k{2..8}.edges).
  V2  Structural lemma: G_k is connected, cubic, triangle-free, n = 8k-2
      (checked k = 2..12).
  V3  Block zero-forcing numbers: Z(S1) = 4 and Z(S2) = 4, by exhaustive
      enumeration (all C(7,3)=35 resp. C(8,3)=56 3-subsets fail; explicit
      4-witnesses force).  S1/S2 are taken as induced subgraphs of actual
      chain graphs (bridges removed), not rebuilt by hand.
  V4  The gamma interface-DP transition tables: first-block vector v1,
      middle-block matrix M, last-block vector c, computed by exhaustive
      enumeration of all subsets of each block, equal the tables claimed
      in the writeup; all middle blocks give the SAME table.
  V5  DP reproduces every independently certified gamma value (k = 2..8:
      4,7,9,11,14,16,18) and equals floor(7k/3) for all k = 2..60.
  V6  Min-plus periodicity: v_{i+3} = v_i + 7 entrywise for all i >= 1
      (checked along a long chain), the finite certificate behind the
      gamma recurrence gamma(G_{k+3}) = gamma(G_k) + 7.
  V7  Independent brute force (no DP, no ILP): gamma(G_2) = 4 (no 3-set
      of C(14,3) dominates) and gamma(G_3) = 7 (no 6-set of C(22,6)
      dominates), witnesses dominate.  Also Z(G_2) = 7 re-proved
      exhaustively (no 6-set of C(14,6) forces; witness forces).
  V8  Explicit dominating set D_k: dominates and |D_k| = floor(7k/3),
      k = 2..60.
  V9  Explicit forcing set F_k: closure is all of V and |F_k| = 3k+1,
      k = 2..60.  (Hence Z <= 3k+1; with V3 + superadditivity, Z = 3k+1.)
  V10 Consistency with prior certified exact Z: Z(G_k) = 3k+1 at k = 2..5
      (7, 10, 13, 16).
  V11 Finite case-claims used in the human-readable matrix-entry proofs:
      the 2-subsets of a middle block dominating its 6-vertex core are
      exactly {a1,b1}, {a2,b2}, {a3,b3}; for an end block exactly
      {a1,b1}, {a2,b2}, {a2,b3}, {a3,b2}, {a3,b3}; and no pair {s,x}
      (end block) dominates the core.
  V12 (optional) OR-Tools CP-SAT ILP cross-check of gamma for k = 2..12,
      if ortools is importable; skipped otherwise.
"""

import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)

CERT_GAMMA = {2: 4, 3: 7, 4: 9, 5: 11, 6: 14, 7: 16, 8: 18}
CERT_Z = {2: 7, 3: 10, 4: 13, 5: 16}

RESULTS = []


def check(name, cond):
    RESULTS.append((name, bool(cond)))
    print(("PASS  " if cond else "FAIL  ") + name, flush=True)


# ------------------------------------------------------------------ family
def chain(k):
    """The certified family ('indep' variant), verbatim logic from
    chain_study.chain, additionally returning block structure.

    Returns (n, edges, blocks); blocks is a list of (verts, in_port,
    out_port) with in_port/out_port = None at the chain ends.
    Within a block at offset o:  a1,a2,a3 = o,o+1,o+2;  b1,b2,b3 =
    o+3,o+4,o+5; end blocks: s = o+6 (subdividing a1b1); middle blocks:
    p = o+6 (subdividing a1b1, the in-port), q = o+7 (subdividing a2b2,
    the out-port)."""
    edges = []
    offset = 0
    out_sub_prev = None
    blocks = []
    for i in range(k):
        a = [offset + 0, offset + 1, offset + 2]
        b = [offset + 3, offset + 4, offset + 5]
        if i == 0 or i == k - 1:
            subdiv = [(a[0], b[0])]
        else:
            subdiv = [(a[0], b[0]), (a[1], b[1])]
        nsub = len(subdiv)
        subs = [offset + 6 + j for j in range(nsub)]
        for u in a:
            for v in b:
                if (u, v) not in subdiv:
                    edges.append((u, v))
        for (u, v), s in zip(subdiv, subs):
            edges.append((u, s))
            edges.append((v, s))
        if out_sub_prev is not None:
            edges.append((out_sub_prev, subs[0]))
        in_port = subs[0] if i > 0 else None
        out_port = subs[-1] if i < k - 1 else None
        blocks.append((list(range(offset, offset + 6 + nsub)),
                       in_port, out_port))
        out_sub_prev = subs[-1]
        offset += 6 + nsub
    return offset, edges, blocks


def adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and v not in adj[u], "multi-edge/loop"
        adj[u].add(v)
        adj[v].add(u)
    return adj


def nbr_masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        nbr[u] |= 1 << v
        nbr[v] |= 1 << u
    return nbr


# ------------------------------------------------------------- V1 edge files
def v1_edge_files():
    ok = True
    for k in range(2, 9):
        path = os.path.join(PARENT, f"chain_indep_k{k}.edges")
        with open(path) as f:
            toks = f.read().split()
        nf, mf = int(toks[0]), int(toks[1])
        file_edges = sorted(
            tuple(sorted((int(toks[2 + 2 * i]), int(toks[3 + 2 * i]))))
            for i in range(mf))
        n, edges, _ = chain(k)
        ours = sorted(tuple(sorted(e)) for e in edges)
        if not (n == nf and len(edges) == mf and ours == file_edges):
            ok = False
    check("V1: construction identical to certified edge files k=2..8", ok)


# ------------------------------------------------------------- V2 structure
def v2_structure():
    ok = True
    for k in range(2, 13):
        n, edges, _ = chain(k)
        if n != 8 * k - 2 or len(edges) != 3 * n // 2:
            ok = False
        adj = adj_sets(n, edges)
        if any(len(adj[v]) != 3 for v in range(n)):
            ok = False
        seen, frontier = {0}, {0}
        while frontier:
            frontier = {w for v in frontier for w in adj[v]} - seen
            seen |= frontier
        if len(seen) != n:
            ok = False
        for u, v in edges:
            if adj[u] & adj[v]:
                ok = False  # triangle
    check("V2: G_k connected, cubic, triangle-free, n=8k-2 (k=2..12)", ok)


# -------------------------------------------------------------- zero forcing
def closure_mask(n, nbr, blue):
    while True:
        forced = 0
        for v in range(n):
            if (blue >> v) & 1:
                w = nbr[v] & ~blue
                if w and (w & (w - 1)) == 0:
                    forced |= w
        if forced & ~blue == 0:
            return blue
        blue |= forced


def induced_block_graph(k, block_index):
    """Block graph (component of G_k minus bridges), reindexed to 0..m-1."""
    n, edges, blocks = chain(k)
    verts, ip, op = blocks[block_index]
    idx = {v: i for i, v in enumerate(verts)}
    sub_edges = [(idx[u], idx[v]) for u, v in edges
                 if u in idx and v in idx]
    return len(verts), sub_edges, idx


def v3_block_Z():
    # S1 = end block (7 vertices), from chain(2) block 0.
    # S2 = middle block (8 vertices), from chain(4) block 1.
    results = {}
    for name, (k, bi, zexp) in {"S1": (2, 0, 4), "S2": (4, 1, 4)}.items():
        m, sub_edges, _ = induced_block_graph(k, bi)
        nbr = nbr_masks(m, sub_edges)
        full = (1 << m) - 1
        none_forces = all(
            closure_mask(m, nbr, sum(1 << v for v in S)) != full
            for S in combinations(range(m), zexp - 1))
        some_forces = any(
            closure_mask(m, nbr, sum(1 << v for v in S)) == full
            for S in combinations(range(m), zexp))
        results[name] = none_forces and some_forces
    check("V3: Z(S1)=4 exhaustively (no 3-set of 35 forces; 4-set does)",
          results["S1"])
    check("V3: Z(S2)=4 exhaustively (no 3-set of 56 forces; 4-set does)",
          results["S2"])


# ------------------------------------------------------------------ gamma DP
# States for an out-port q:  0 = "A" (q in D);  1 = "B" (q not in D but
# dominated by D inside its own block);  2 = "C" (q not yet dominated;
# the next block's in-port must be in D).
def block_table(adj, verts, ip, op):
    """Exact transition table by exhaustive enumeration of all subsets S
    of the block: T[(state_in, state_out)] = min |S| feasible."""
    vset = set(verts)
    sin = [None] if ip is None else [0, 1, 2]
    sout = [None] if op is None else [0, 1, 2]
    INF = float("inf")
    T = {(si, so): INF for si in sin for so in sout}
    interior = [v for v in verts if v != ip and v != op]
    for v in interior:
        assert adj[v] <= vset, "interior vertex with outside neighbor"
    if ip is not None:
        assert len(adj[ip] - vset) == 1, "in-port must have 1 bridge nbr"
    if op is not None:
        assert len(adj[op] - vset) == 1, "out-port must have 1 bridge nbr"
    m = len(verts)
    for bits in range(1 << m):
        S = {verts[j] for j in range(m) if (bits >> j) & 1}
        if any(not (({v} | adj[v]) & S) for v in interior):
            continue  # some interior vertex undominated
        if op is None:
            so = None
        elif op in S:
            so = 0
        elif (adj[op] & vset) & S:
            so = 1
        else:
            so = 2
        cost = len(S)
        for si in sin:
            if ip is not None:
                if si == 2 and ip not in S:
                    continue  # previous out-port needs this in-port in D
                if not ((({ip} | (adj[ip] & vset)) & S) or si == 0):
                    continue  # in-port itself undominated
            if cost < T[(si, so)]:
                T[(si, so)] = cost
    return T


def gamma_dp(k, want_internals=False):
    n, edges, blocks = chain(k)
    adj = adj_sets(n, edges)
    tables = [block_table(adj, v, ip, op) for (v, ip, op) in blocks]
    vec = tuple(tables[0][(None, so)] for so in (0, 1, 2))
    vecs = [vec]
    for t in tables[1:-1]:
        vec = tuple(min(vec[si] + t[(si, so)] for si in (0, 1, 2))
                    for so in (0, 1, 2))
        vecs.append(vec)
    g = min(vec[si] + tables[-1][(si, None)] for si in (0, 1, 2))
    if want_internals:
        return g, vecs, tables
    return g


EXPECTED_V1 = (3, 2, 2)                      # first block, states (A,B,C)
EXPECTED_M = {(0, 0): 3, (0, 1): 2, (0, 2): 2,
              (1, 0): 3, (1, 1): 3, (1, 2): 2,
              (2, 0): 3, (2, 1): 3, (2, 2): 3}
EXPECTED_C = (2, 2, 3)                       # last block, states (A,B,C)


def v4_tables():
    g, vecs, tables = gamma_dp(8, want_internals=True)
    first = tuple(tables[0][(None, so)] for so in (0, 1, 2))
    last = tuple(tables[-1][(si, None)] for si in (0, 1, 2))
    mids = tables[1:-1]
    same_mid = all(t == mids[0] for t in mids)
    mid_ok = mids[0] == EXPECTED_M
    check("V4: first-block vector v1 = (3,2,2)", first == EXPECTED_V1)
    check("V4: every middle-block table identical", same_mid)
    check("V4: middle-block matrix M = [[3,2,2],[3,3,2],[3,3,3]]", mid_ok)
    check("V4: last-block vector c = (2,2,3)", last == EXPECTED_C)


def v5_dp_values():
    ok_cert = all(gamma_dp(k) == CERT_GAMMA[k] for k in range(2, 9))
    ok_formula = all(gamma_dp(k) == (7 * k) // 3 for k in range(2, 61))
    check("V5: DP reproduces all certified gamma (k=2..8)", ok_cert)
    check("V5: DP gamma = floor(7k/3) for k=2..60", ok_formula)


def v6_periodicity():
    g, vecs, tables = gamma_dp(40, want_internals=True)
    # vecs[i] is the state vector after block i+1 (i = 0..k-2)
    ok = all(
        vecs[i + 3] == tuple(x + 7 for x in vecs[i])
        for i in range(len(vecs) - 3))
    check("V6: min-plus periodicity v_{i+3} = v_i + 7 (all i, chain k=40)",
          ok)


# -------------------------------------------------- V7 independent brute force
def dominates(n, adj, D):
    Ds = set(D)
    return all(({v} | adj[v]) & Ds for v in range(n))


def v7_brute():
    # gamma(G_2) = 4, exhaustively, without DP or ILP.
    n, edges, _ = chain(2)
    adj = adj_sets(n, edges)
    no3 = not any(dominates(n, adj, D) for D in combinations(range(n), 3))
    check("V7: no 3-set dominates G_2 (all C(14,3)=364)", no3)
    # gamma(G_3) = 7, exhaustively.
    n3, edges3, _ = chain(3)
    adj3 = adj_sets(n3, edges3)
    closed = [frozenset({v} | adj3[v]) for v in range(n3)]
    no6 = True
    for D in combinations(range(n3), 6):
        cov = set()
        for v in D:
            cov |= closed[v]
        if len(cov) == n3:
            no6 = False
            break
    check("V7: no 6-set dominates G_3 (all C(22,6)=74,613)", no6)
    # Z(G_2) = 7 re-proved exhaustively.
    nbr = nbr_masks(n, edges)
    full = (1 << n) - 1
    no6f = all(closure_mask(n, nbr, sum(1 << v for v in S)) != full
               for S in combinations(range(n), 6))
    check("V7: no 6-set forces G_2 (all C(14,6)=3003 closures)", no6f)


# ------------------------------------------------- V8 explicit dominating set
def build_D(k):
    _, _, blocks = chain(k)
    D = []
    for j, (verts, ip, op) in enumerate(blocks):
        o = verts[0]
        i = j + 1  # 1-based block index
        if i == 1:
            D += [o + 0, o + 3]                    # {a1, b1}
        elif i == k:
            if k % 3 == 2:
                D += [o + 0, o + 3]                # {a1, b1}
            elif k % 3 == 0:
                D += [o + 6, o + 2, o + 5]         # {s, a3, b3}
            else:
                D += [o + 1, o + 4]                # {a2, b2}
        else:
            if i % 3 == 2:
                D += [o + 0, o + 3]                # {a1, b1}
            elif i % 3 == 0:
                D += [o + 6, o + 5, o + 7]         # {p, b3, q}
            else:
                D += [o + 1, o + 4]                # {a2, b2}
    return D


def v8_dominating_sets():
    ok = True
    for k in range(2, 61):
        n, edges, _ = chain(k)
        adj = adj_sets(n, edges)
        D = build_D(k)
        if len(D) != len(set(D)) or len(D) != (7 * k) // 3:
            ok = False
        if not dominates(n, adj, D):
            ok = False
    check("V8: explicit D_k dominates with |D_k| = floor(7k/3), k=2..60",
          ok)


# --------------------------------------------------- V9 explicit forcing set
def build_F(k):
    _, _, blocks = chain(k)
    F = []
    for j, (verts, ip, op) in enumerate(blocks):
        o = verts[0]
        if j == 0:
            F += [o + 0, o + 1, o + 3, o + 4]      # {a1, a2, b1, b2}
        else:
            F += [o + 0, o + 1, o + 4]             # {a1, a2, b2}
    return F


def v9_forcing_sets():
    ok = True
    for k in range(2, 61):
        n, edges, _ = chain(k)
        nbr = nbr_masks(n, edges)
        F = build_F(k)
        if len(F) != len(set(F)) or len(F) != 3 * k + 1:
            ok = False
        blue = 0
        for v in F:
            blue |= 1 << v
        if closure_mask(n, nbr, blue) != (1 << n) - 1:
            ok = False
    check("V9: explicit F_k forces with |F_k| = 3k+1, k=2..60", ok)
    # the k=2 explicit set coincides with the certified witness
    check("V9: F_2 equals the certified Z-witness of G14",
          sorted(build_F(2)) == [0, 1, 3, 4, 7, 8, 11])
    check("V8: D_2 equals the certified gamma-witness of G14",
          sorted(build_D(2)) == [0, 3, 7, 10])


def v10_z_consistency():
    ok = all(CERT_Z[k] == 3 * k + 1 for k in (2, 3, 4, 5))
    check("V10: certified exact Z equals 3k+1 at k=2..5", ok)


# ----------------------------------------------------- V11 core-pair claims
def core_dominating_pairs(core_adj, core_verts):
    pairs = []
    for u, v in combinations(core_verts, 2):
        cov = {u, v} | core_adj[u] | core_adj[v]
        if set(core_verts) <= cov:
            pairs.append((u, v))
    return pairs


def v11_core_pairs():
    # middle block: core = {a1,a2,a3,b1,b2,b3} (local idx 0..5),
    # core edges = K33 minus a1b1 minus a2b2
    m, sub_edges, _ = induced_block_graph(4, 1)
    adj = adj_sets(m, sub_edges)
    core = list(range(6))
    core_adj = [adj[v] & set(core) for v in range(6)]
    pairs = core_dominating_pairs(core_adj, core)
    check("V11: middle-core dominating pairs are exactly "
          "{a1,b1},{a2,b2},{a3,b3}",
          sorted(pairs) == [(0, 3), (1, 4), (2, 5)])
    # end block core = K33 minus a1b1
    m1, sub_edges1, _ = induced_block_graph(2, 0)
    adj1 = adj_sets(m1, sub_edges1)
    core_adj1 = [adj1[v] & set(core) for v in range(6)]
    pairs1 = core_dominating_pairs(core_adj1, core)
    check("V11: end-core dominating pairs are exactly "
          "{a1,b1},{a2,b2},{a2,b3},{a3,b2},{a3,b3}",
          sorted(pairs1) == [(0, 3), (1, 4), (1, 5), (2, 4), (2, 5)])
    # no {s, x} dominates the end core (s = local idx 6)
    s_pairs = [x for x in range(6)
               if set(core) <= ({6, x} | adj1[6] | adj1[x])]
    check("V11: no pair {s,x} dominates the end-block core", not s_pairs)


# ------------------------------------- V13 named forts/automorphisms/witnesses
def is_fort(m, adj, F):
    Fs = set(F)
    if not Fs:
        return False
    return all(len(adj[v] & Fs) != 1 for v in range(m) if v not in Fs)


def is_automorphism(m, adj, perm):
    return all((perm[v] in adj[perm[u]]) == (v in adj[u])
               for u in range(m) for v in range(m) if u != v)


def v13_named_objects():
    # local labels: a1,a2,a3 = 0,1,2; b1,b2,b3 = 3,4,5; s/p = 6; q = 7
    m1, e1, _ = induced_block_graph(2, 0)     # S1
    adj1 = adj_sets(m1, e1)
    m2, e2, _ = induced_block_graph(4, 1)     # S2
    adj2 = adj_sets(m2, e2)

    s1_forts = [{1, 2}, {4, 5}, {0, 2, 6}, {3, 5, 6}, {0, 2, 3, 5}]
    check("V13: the 5 named S1 forts (F1..F5) are forts",
          all(is_fort(m1, adj1, F) for F in s1_forts))
    s2_forts = [{0, 2, 6}, {1, 2, 7}, {3, 5, 6}, {4, 5, 7},
                {0, 1, 3, 4}, {0, 2, 3, 5}, {1, 2, 4, 5},
                {0, 1, 6, 7}, {3, 4, 6, 7}, {0, 2, 3, 7}, {0, 3, 5, 7}]
    check("V13: the 11 named S2 forts (G1..G10, G6') are forts",
          all(is_fort(m2, adj2, F) for F in s2_forts))
    # automorphisms used in the WLOG steps
    pi1 = [0, 2, 1, 3, 4, 5, 6]               # S1: a2<->a3
    pi2 = [0, 1, 2, 3, 5, 4, 6]               # S1: b2<->b3
    alpha = [3, 4, 5, 0, 1, 2, 6, 7]          # S2: a_i<->b_i
    beta = [1, 0, 2, 4, 3, 5, 7, 6]           # S2: 1<->2 with p<->q
    check("V13: S1 automorphisms a2<->a3 and b2<->b3",
          is_automorphism(m1, adj1, pi1) and is_automorphism(m1, adj1, pi2))
    check("V13: S2 automorphisms alpha (a<->b) and beta (1<->2, p<->q)",
          is_automorphism(m2, adj2, alpha) and is_automorphism(m2, adj2, beta))
    # Lemma 6.2 upper-bound witnesses
    nbr1 = nbr_masks(m1, e1)
    nbr2 = nbr_masks(m2, e2)
    w1 = sum(1 << v for v in (0, 1, 3, 4))    # {a1,a2,b1,b2}
    w2 = sum(1 << v for v in (6, 0, 1, 4))    # {p,a1,a2,b2}
    check("V13: witness {a1,a2,b1,b2} forces S1",
          closure_mask(m1, nbr1, w1) == (1 << m1) - 1)
    check("V13: witness {p,a1,a2,b2} forces S2",
          closure_mask(m2, nbr2, w2) == (1 << m2) - 1)


# --------------------------------------------------- V12 optional ILP check
def v12_ilp():
    try:
        from ortools.sat.python import cp_model
    except Exception:
        print("SKIP  V12: ortools not importable; ILP cross-check skipped")
        return
    ok = True
    for k in range(2, 13):
        n, edges, _ = chain(k)
        adj = adj_sets(n, edges)
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f"x{v}") for v in range(n)]
        for v in range(n):
            model.AddBoolOr([x[v]] + [x[u] for u in adj[v]])
        model.Minimize(sum(x))
        solver = cp_model.CpSolver()
        solver.parameters.num_workers = 16
        if solver.Solve(model) != cp_model.OPTIMAL:
            ok = False
            break
        if int(solver.ObjectiveValue()) != (7 * k) // 3:
            ok = False
            break
    check("V12: CP-SAT ILP gamma = floor(7k/3) for k=2..12", ok)


def main():
    v1_edge_files()
    v2_structure()
    v3_block_Z()
    v4_tables()
    v5_dp_values()
    v6_periodicity()
    v7_brute()
    v8_dominating_sets()
    v9_forcing_sets()
    v10_z_consistency()
    v11_core_pairs()
    v13_named_objects()
    v12_ilp()
    bad = [name for name, ok in RESULTS if not ok]
    print()
    if bad:
        print(f"FAILED ({len(bad)}): " + "; ".join(bad))
        sys.exit(1)
    print(f"ALL {len(RESULTS)} CHECKS PASSED")
    sys.exit(0)


if __name__ == "__main__":
    main()
