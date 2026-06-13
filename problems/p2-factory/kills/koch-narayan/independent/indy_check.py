#!/usr/bin/env python3
"""
Clean-room independent verification of the claimed refutation of
Conjecture 1 ("the bipartite bound") of arXiv:2511.01719
(Koch & Narayan, "Maximal bipartite graphs with a unique minimum
dominating set").

Written from scratch for verification: no code shared with the attacker's
checker.py / verify2.py / domfilter.c, nor with Codex's verifier.
Pure Python 3, exact integer arithmetic only.

Conjecture 1 (transcribed by hand from src/PaperDraft.tex, lines 145-148):

  Let G be a bipartite graph without isolated vertices with order n and
  dominating number gamma.  Let G have a unique minimum dominating set.
  If gamma >= 2 and n >= 3*gamma, then the size (number of edges) s(G)
  satisfies s(G) <= m(n, gamma), where

    m(n,g) = 2g + 2*ceil(g/2)*floor(g/2)
             + min(n - 3g, 2*ceil(g/2) - floor(g/2) + 1) * (2*ceil(g/2) + 1)
             + sum_{i=1}^{Phi} ( (2*ceil(g/2) + 1) + ceil(i/2) )

    Phi(n,g) = max(0, n - 3g - 2*ceil(g/2) - floor(g/2) + 1)     [literal]

  The attack report alleges the printed Phi has a sign typo and the
  construction-consistent reading is

    Phi'(n,g) = max(0, n - 3g - 2*ceil(g/2) + floor(g/2) - 1)    [corrected]

  We evaluate the bound under BOTH readings.

The claimed smallest counterexample (n=13, gamma=4, 22 edges) is rebuilt
below from the edge list given in the attack report's certificate text,
NOT loaded from the attacker's files.  Its graph6 string is decoded by an
independent decoder and cross-checked.  Supplementary family certificates
(JSON files) are then verified with the same independent machinery.
"""

import json
import os
import sys
from itertools import combinations
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ATTACK_DIR = os.path.dirname(HERE)

LOG_LINES = []


def log(msg=""):
    print(msg)
    LOG_LINES.append(str(msg))


def ceil_div(a, b):
    return -((-a) // b)


# ----------------------------------------------------------------------
# The conjectured bound, exact integer arithmetic, both Phi readings.
# ----------------------------------------------------------------------

def m_bound(n, g, phi_reading):
    """m(n, g) from Conjecture 1. phi_reading in {'literal', 'corrected'}."""
    cg = ceil_div(g, 2)   # ceil(g/2)
    fg = g // 2           # floor(g/2)
    total = 2 * g + 2 * cg * fg
    total += min(n - 3 * g, 2 * cg - fg + 1) * (2 * cg + 1)
    if phi_reading == 'literal':
        phi = max(0, n - 3 * g - 2 * cg - fg + 1)
    elif phi_reading == 'corrected':
        phi = max(0, n - 3 * g - 2 * cg + fg - 1)
    else:
        raise ValueError(phi_reading)
    total += sum((2 * cg + 1) + ceil_div(i, 2) for i in range(1, phi + 1))
    return total


def formula_sanity_checks():
    """Check our transcription against values the PAPER itself derives."""
    ok = True
    # Statement 12 of the paper: m(6,2)=6, m(7,2)=9, and for the general
    # gamma=2 case  m(n,2) = n(n-2)/4 (n even), (n-1)^2/4 (n odd).
    for reading in ('literal', 'corrected'):
        if m_bound(6, 2, reading) != 6:
            log(f"FORMULA SANITY FAIL: m(6,2,{reading}) = "
                f"{m_bound(6, 2, reading)} != 6")
            ok = False
        if m_bound(7, 2, reading) != 9:
            log(f"FORMULA SANITY FAIL: m(7,2,{reading}) = "
                f"{m_bound(7, 2, reading)} != 9")
            ok = False
        for n in range(6, 41):
            closed = n * (n - 2) // 4 if n % 2 == 0 else (n - 1) ** 2 // 4
            if m_bound(n, 2, reading) != closed:
                log(f"FORMULA SANITY FAIL: m({n},2,{reading}) = "
                    f"{m_bound(n, 2, reading)} != closed form {closed}")
                ok = False
    # Note: for gamma = 2 the two Phi readings coincide identically
    # (floor(g/2)=1 so -fg+1 = +fg-1 = 0), so the closed form pins both.
    log(f"[formula] transcription sanity vs paper's own gamma=2 closed form: "
        f"{'PASS' if ok else 'FAIL'}")
    return ok


# ----------------------------------------------------------------------
# Independent graph6 decoder (format per nauty User's Guide, appendix).
# ----------------------------------------------------------------------

def decode_graph6(s):
    """Return (n, set of frozenset edges) for a graph6 string, n < 63."""
    data = [ord(c) - 63 for c in s.strip()]
    if any(d < 0 or d > 63 for d in data):
        raise ValueError("invalid graph6 characters")
    n = data[0]
    if n >= 63:
        raise NotImplementedError("only short-form graph6 supported here")
    bits_needed = n * (n - 1) // 2
    body = data[1:]
    if len(body) != ceil_div(bits_needed, 6):
        raise ValueError(f"graph6 length mismatch: got {len(body)} payload "
                         f"chars, need {ceil_div(bits_needed, 6)}")
    bits = []
    for d in body:
        for k in range(5, -1, -1):
            bits.append((d >> k) & 1)
    edges = set()
    idx = 0
    # Order: x(0,1), x(0,2), x(1,2), x(0,3), x(1,3), x(2,3), ...
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                edges.add(frozenset((i, j)))
            idx += 1
    if any(bits[bits_needed:]):
        raise ValueError("nonzero padding bits in graph6 string")
    return n, edges


# ----------------------------------------------------------------------
# Independent graph property checks (bitmask based, exact).
# ----------------------------------------------------------------------

def build_closed_nbhd(n, edges):
    """closed[v] = bitmask of N[v]. Also validates simplicity."""
    closed = [1 << v for v in range(n)]
    seen = set()
    for e in edges:
        u, v = tuple(e) if isinstance(e, frozenset) else e
        if u == v:
            raise ValueError(f"self-loop at {u}")
        key = frozenset((u, v))
        if key in seen:
            raise ValueError(f"duplicate edge {sorted(key)}")
        seen.add(key)
        if not (0 <= u < n and 0 <= v < n):
            raise ValueError(f"vertex out of range in edge {(u, v)}")
        closed[u] |= 1 << v
        closed[v] |= 1 << u
    return closed


def is_bipartite_2coloring(n, edges):
    """Independent bipartiteness test via BFS 2-coloring.
    Returns (True, (sideA, sideB)) or (False, None). Handles disconnected."""
    adj = [[] for _ in range(n)]
    for e in edges:
        u, v = tuple(e)
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        queue = [s]
        while queue:
            x = queue.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    queue.append(y)
                elif color[y] == color[x]:
                    return False, None
    a = {v for v in range(n) if color[v] == 0}
    b = {v for v in range(n) if color[v] == 1}
    return True, (a, b)


def is_connected(n, edges):
    adj = [[] for _ in range(n)]
    for e in edges:
        u, v = tuple(e)
        adj[u].append(v)
        adj[v].append(u)
    seen = {0}
    stack = [0]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == n


def min_dominating_sets(n, closed, upto_size):
    """Exhaustively find ALL dominating sets of the minimum size, searching
    sizes 1..upto_size.  Returns (gamma, list_of_sets) or (None, []) if no
    dominating set of size <= upto_size exists.

    Correctness note: domination is monotone under adding vertices, so the
    first size k at which any dominating set exists is exactly gamma, and
    enumerating all k-subsets at that size finds every minimum dominating
    set."""
    full = (1 << n) - 1
    verts = list(range(n))
    for k in range(1, upto_size + 1):
        found = []
        for sub in combinations(verts, k):
            mask = 0
            for v in sub:
                mask |= closed[v]
            if mask == full:
                found.append(set(sub))
        if found:
            return k, found
    return None, []


# ----------------------------------------------------------------------
# Verification of one certificate graph.
# ----------------------------------------------------------------------

def verify_counterexample(name, n, edge_list, claimed_gamma,
                          claimed_unique_D=None, expected_edge_count=None):
    """Returns True iff the graph satisfies EVERY hypothesis of Conjecture 1
    and violates its conclusion under BOTH Phi readings."""
    log(f"--- {name} ---")
    edges = {frozenset(e) for e in edge_list}
    if len(edges) != len(edge_list):
        log("  FAIL: duplicate edges in input list")
        return False
    m_edges = len(edges)
    log(f"  n = {n}, |E| = {m_edges}")
    if expected_edge_count is not None and m_edges != expected_edge_count:
        log(f"  FAIL: expected {expected_edge_count} edges")
        return False

    closed = build_closed_nbhd(n, edges)  # also validates simple graph

    # No isolated vertices (closed nbhd bigger than self).
    isolated = [v for v in range(n) if closed[v] == (1 << v)]
    if isolated:
        log(f"  FAIL: isolated vertices {isolated}")
        return False
    log("  no isolated vertices: OK")

    bip, parts = is_bipartite_2coloring(n, edges)
    if not bip:
        log("  FAIL: not bipartite")
        return False
    log(f"  bipartite: OK (parts sizes {sorted(map(len, parts))})")

    conn = is_connected(n, edges)
    log(f"  connected: {conn} (not required by Conjecture 1; "
        f"reported for completeness)")

    # Exhaustive domination number + ALL minimum dominating sets.
    gamma, mds = min_dominating_sets(n, closed, claimed_gamma + 1)
    if gamma is None:
        log(f"  FAIL: no dominating set of size <= {claimed_gamma + 1}??")
        return False
    log(f"  domination number gamma = {gamma} "
        f"(exhaustive over all C({n},k) subsets, k=1..{gamma}); "
        f"searched {sum(comb(n, k) for k in range(1, gamma + 1))} subsets")
    if gamma != claimed_gamma:
        log(f"  FAIL: claimed gamma {claimed_gamma}")
        return False
    log(f"  number of minimum dominating sets = {len(mds)}")
    if len(mds) != 1:
        log("  FAIL: minimum dominating set not unique")
        return False
    D = mds[0]
    log(f"  unique minimum dominating set = {sorted(D)}")
    if claimed_unique_D is not None and D != set(claimed_unique_D):
        log(f"  FAIL: claimed unique MDS {sorted(claimed_unique_D)} "
            f"differs from actual")
        return False

    # Hypotheses of Conjecture 1.
    if gamma < 2:
        log("  FAIL: gamma < 2, conjecture does not apply")
        return False
    if n < 3 * gamma:
        log(f"  FAIL: n = {n} < 3*gamma = {3 * gamma}, "
            f"conjecture does not apply")
        return False
    log(f"  hypotheses: bipartite, no isolated vertices, unique MDS, "
        f"gamma={gamma}>=2, n={n}>=3*gamma={3 * gamma}: ALL SATISFIED")

    # Conclusion under both readings.
    ml = m_bound(n, gamma, 'literal')
    mc = m_bound(n, gamma, 'corrected')
    log(f"  m({n},{gamma}) literal-Phi   = {ml}  "
        f"-> s(G)={m_edges} {'>' if m_edges > ml else '<='} {ml}")
    log(f"  m({n},{gamma}) corrected-Phi = {mc}  "
        f"-> s(G)={m_edges} {'>' if m_edges > mc else '<='} {mc}")
    if m_edges > ml and m_edges > mc:
        log(f"  VERDICT: VIOLATES Conjecture 1 under BOTH Phi readings")
        return True
    log("  VERDICT: does NOT violate under both readings")
    return False


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    all_ok = True

    log("=" * 72)
    log("Independent clean-room verification: Koch-Narayan Conjecture 1")
    log("(arXiv:2511.01719) -- claimed refutation")
    log("=" * 72)
    log()

    # 0. Formula transcription sanity vs the paper's own derived values.
    if not formula_sanity_checks():
        all_ok = False
    # Extra pinned values quoted in prior audits:
    log(f"[formula] m(10,3) literal={m_bound(10, 3, 'literal')} "
        f"corrected={m_bound(10, 3, 'corrected')} (expected 15, 15)")
    if m_bound(10, 3, 'literal') != 15 or m_bound(10, 3, 'corrected') != 15:
        all_ok = False
    log()

    # 1. PRIMARY: smallest counterexample, n=13, rebuilt from the edge list
    #    printed in the attack report's certificate description.
    edges_13 = [
        (0, 6), (1, 7), (2, 8), (3, 8), (4, 9), (5, 9),
        (0, 10), (2, 10), (3, 10), (4, 10), (5, 10),
        (1, 11), (2, 11), (3, 11), (4, 11), (5, 11),
        (0, 12), (1, 12), (2, 12), (3, 12), (4, 12), (5, 12),
    ]
    # Structural cross-check of the claimed bipartition A={0..5}, B={6..12}.
    A, B = set(range(6)), set(range(6, 13))
    assert all((u in A) != (v in A) for (u, v) in edges_13), \
        "claimed bipartition violated"
    log("[13,4] claimed bipartition A={0..5}, B={6..12} consistent "
        "with every listed edge")

    ok13 = verify_counterexample(
        "PRIMARY counterexample (rebuilt from description): n=13, gamma=4",
        13, edges_13, claimed_gamma=4, claimed_unique_D={0, 1, 8, 9},
        expected_edge_count=22)
    all_ok &= ok13
    log()

    # 1b. Independent decode of the claimed graph6 string; must equal the
    #     described edge list as a labeled graph.
    g6 = "L??CA?oBDwN_~?"
    n_g6, edges_g6 = decode_graph6(g6)
    same = (n_g6 == 13) and (edges_g6 == {frozenset(e) for e in edges_13})
    log(f"[13,4] independent graph6 decode of '{g6}': n={n_g6}, "
        f"|E|={len(edges_g6)}, identical to described labeled edge list: "
        f"{same}")
    if not same:
        all_ok = False
    log()

    # 2. SUPPLEMENTARY: family certificates saved by the attacker
    #    (data files only; verified with this script's own machinery).
    supplementary = [
        ("certificate_14_4.json", 4),
        ("certificate_15_4.json", 4),
        ("certificate_15_4_max.json", 4),
        ("certificate_18_5.json", 5),
        ("certificate_20_6.json", 6),
    ]
    for fname, g in supplementary:
        path = os.path.join(ATTACK_DIR, fname)
        if not os.path.exists(path):
            log(f"--- {fname}: MISSING, skipped ---")
            all_ok = False
            continue
        with open(path, "r", encoding="utf-8") as fh:
            cert = json.load(fh)
        n = cert["n"]
        edge_list = [tuple(e) for e in cert["edges"]]
        ok = verify_counterexample(
            f"supplementary {fname}", n, edge_list, claimed_gamma=g)
        all_ok &= ok
        log()

    log("=" * 72)
    if all_ok:
        log("OVERALL: KILL CONFIRMED.")
        log("The n=13 graph (and every supplementary certificate) satisfies")
        log("all hypotheses of Conjecture 1 of arXiv:2511.01719 and exceeds")
        log("m(n,gamma) under both the literal and the typo-corrected Phi")
        log("readings.  In particular s = 22 > 21 = m(13,4).")
    else:
        log("OVERALL: VERIFICATION FAILED -- see FAIL lines above.")
    log("=" * 72)

    with open(os.path.join(HERE, "verify.log"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(LOG_LINES) + "\n")

    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
