"""
Clean-room verification of the claimed refutation of Conjecture 1 of
arXiv:2511.01719 (Koch & Narayan, "Maximal bipartite graphs with a unique
minimum dominating set").

Written from scratch for this verification pass. It deliberately does NOT
import or reuse any attacker code (checker.py, verify2.py, unbalanced.py,
domfilter.c, codex-scratch/*, or the earlier independent/indy_check.py).
Only raw data is consumed: the edge list quoted in the attack report
(hard-coded below, i.e. the counterexample is REBUILT FROM ITS DESCRIPTION),
the graph6 string quoted in the report, and the supplementary certificate
JSON files (data only).

Conjecture 1, transcribed directly from src/PaperDraft.tex lines 145-148:

  Let G be a bipartite graph without isolated vertices with order n and
  dominating number gamma. Let G have a unique minimum dominating set.
  If gamma >= 2 and n >= 3*gamma, then the size of G, s(G), is bounded
  ABOVE by

    m(n,g) = 2g + 2*ceil(g/2)*floor(g/2)
           + min{ n-3g , 2*ceil(g/2) - floor(g/2) + 1 } * (2*ceil(g/2)+1)
           + sum_{i=1}^{Phi} ( (2*ceil(g/2)+1) + ceil(i/2) )

  where (printed/literal)  Phi = max(0, n - 3g - 2*ceil(g/2) - floor(g/2) + 1).

The paper's own tightness construction (Case 3, tex line 388) instead uses
  |R| = n - (3g + 2*ceil(g/2) - floor(g/2) + 1)
      = n - 3g - 2*ceil(g/2) + floor(g/2) - 1,
the "corrected" Phi reading. Both readings are checked everywhere below.

Run:  python cleanroom_check.py   (writes cleanroom_verify.log next to itself)
"""

import json
import os
import sys
from itertools import combinations
from math import ceil, floor

HERE = os.path.dirname(os.path.abspath(__file__))
ATTACK_DIR = os.path.dirname(HERE)
LOG_PATH = os.path.join(HERE, "cleanroom_verify.log")

LOG_LINES = []


def log(msg=""):
    LOG_LINES.append(msg)
    print(msg)


# --------------------------------------------------------------------------
# 1. The conjectured bound m(n, gamma), transcribed from the TeX by hand.
# --------------------------------------------------------------------------

def m_bound(n, g, phi_reading):
    """m(n, gamma) from Conjecture 1. phi_reading in {'literal','corrected'}."""
    assert g >= 2 and n >= 3 * g
    cg = ceil(g / 2)   # exact: g is an int, ceil of g/2
    fg = floor(g / 2)
    # exactness guard (avoid any float doubt): recompute with integer ops
    cg2 = (g + 1) // 2
    fg2 = g // 2
    assert cg == cg2 and fg == fg2
    cg, fg = cg2, fg2

    if phi_reading == "literal":
        phi = max(0, n - 3 * g - 2 * cg - fg + 1)
    elif phi_reading == "corrected":
        phi = max(0, n - 3 * g - 2 * cg + fg - 1)
    else:
        raise ValueError(phi_reading)

    total = 2 * g + 2 * cg * fg
    total += min(n - 3 * g, 2 * cg - fg + 1) * (2 * cg + 1)
    total += sum((2 * cg + 1) + (i + 1) // 2 for i in range(1, phi + 1))
    return total


def formula_sanity():
    """Anchor the transcription against the paper's OWN stated special values."""
    ok = True

    # Paper, proof of Statement (g2simplified), tex line 542:
    #   "notice m(6,2) = 6 and m(7,2) = 9"
    for (n, g, expect) in [(6, 2, 6), (7, 2, 9)]:
        for r in ("literal", "corrected"):
            v = m_bound(n, g, r)
            if v != expect:
                ok = False
            log(f"[anchor] m({n},{g}) [{r}] = {v}  (paper says {expect})"
                f"  {'OK' if v == expect else 'MISMATCH'}")

    # Paper, Statement g2simplified: for gamma = 2,
    #   m(n,2) = n(n-2)/4 (n even),  (n-1)^2/4 (n odd).
    for n in range(6, 41):
        expect = n * (n - 2) // 4 if n % 2 == 0 else (n - 1) ** 2 // 4
        for r in ("literal", "corrected"):
            v = m_bound(n, 2, r)
            if v != expect:
                ok = False
                log(f"[anchor] gamma=2 closed form FAILS at n={n} [{r}]:"
                    f" {v} != {expect}")
    log("[anchor] gamma=2 closed form m(n,2) checked for n=6..40,"
        " both Phi readings: " + ("PASS" if ok else "FAIL"))

    # Paper, Theorem (Constructions) Case 1: at n = 3*gamma the bound
    # simplifies to 2g + 2*ceil(g/2)*floor(g/2)  (tex line 187).
    for g in range(2, 12):
        expect = 2 * g + 2 * ((g + 1) // 2) * (g // 2)
        for r in ("literal", "corrected"):
            v = m_bound(3 * g, g, r)
            if v != expect:
                ok = False
                log(f"[anchor] n=3g simplification FAILS at g={g} [{r}]")
    log("[anchor] n=3*gamma simplification checked for gamma=2..11,"
        " both Phi readings: " + ("PASS" if ok else "FAIL"))
    return ok


# --------------------------------------------------------------------------
# 2. Graph machinery (from scratch).
# --------------------------------------------------------------------------

class Graph:
    def __init__(self, n, edges):
        self.n = n
        es = set()
        for (u, v) in edges:
            assert 0 <= u < n and 0 <= v < n, "vertex out of range"
            assert u != v, "self-loop"
            e = (min(u, v), max(u, v))
            assert e not in es, "duplicate edge"
            es.add(e)
        self.edges = sorted(es)
        self.adj = [set() for _ in range(n)]
        for (u, v) in self.edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        # closed-neighborhood bitmasks for domination work
        self.closed = [(1 << v) | sum(1 << w for w in self.adj[v])
                       for v in range(n)]

    def num_edges(self):
        return len(self.edges)

    def has_isolated(self):
        return any(len(a) == 0 for a in self.adj)

    def bipartition(self):
        """2-color via BFS; return (sideA, sideB) or None if odd cycle."""
        color = [-1] * self.n
        for s in range(self.n):
            if color[s] != -1:
                continue
            color[s] = 0
            queue = [s]
            while queue:
                u = queue.pop()
                for w in self.adj[u]:
                    if color[w] == -1:
                        color[w] = 1 - color[u]
                        queue.append(w)
                    elif color[w] == color[u]:
                        return None
        return ([v for v in range(self.n) if color[v] == 0],
                [v for v in range(self.n) if color[v] == 1])

    def is_connected(self):
        if self.n == 0:
            return True
        seen = {0}
        queue = [0]
        while queue:
            u = queue.pop()
            for w in self.adj[u]:
                if w not in seen:
                    seen.add(w)
                    queue.append(w)
        return len(seen) == self.n

    def min_dominating_sets(self, hard_cap=None):
        """Exhaustively find (gamma, [all dominating sets of size gamma]).

        Checks every subset of size 1, 2, ... until dominating sets are
        found; within the first size that admits one, collects ALL of them.
        Exact and brute-force by design.
        """
        full = (1 << self.n) - 1
        limit = hard_cap if hard_cap is not None else self.n
        tested = 0
        for k in range(1, limit + 1):
            found = []
            for sub in combinations(range(self.n), k):
                tested += 1
                mask = 0
                for v in sub:
                    mask |= self.closed[v]
                if mask == full:
                    found.append(sub)
            if found:
                return k, found, tested
        raise RuntimeError("no dominating set found (impossible)")


def decode_graph6(s):
    """Independent graph6 decoder (format per nauty's formats.txt)."""
    data = [ord(c) - 63 for c in s]
    assert all(0 <= x <= 63 for x in data), "invalid graph6 character"
    if data[0] <= 62:
        n = data[0]
        rest = data[1:]
    else:
        raise NotImplementedError("only n <= 62 supported here")
    bits = []
    for x in rest:
        for j in range(5, -1, -1):
            bits.append((x >> j) & 1)
    need = n * (n - 1) // 2
    assert len(bits) >= need and all(b == 0 for b in bits[need:]), \
        "bad padding"
    edges = []
    idx = 0
    for col in range(1, n):       # upper triangle, column by column
        for row in range(col):
            if bits[idx]:
                edges.append((row, col))
            idx += 1
    return n, edges


# --------------------------------------------------------------------------
# 3. The primary counterexample, REBUILT FROM THE ATTACK-REPORT DESCRIPTION.
#    (n=13; parts A={0..5}, B={6..12}; 22 edges as listed in the report.)
# --------------------------------------------------------------------------

PRIMARY_N = 13
PRIMARY_GAMMA_CLAIMED = 4
PRIMARY_EDGES = [
    (0, 6), (1, 7), (2, 8), (3, 8), (4, 9), (5, 9),
    (0, 10), (2, 10), (3, 10), (4, 10), (5, 10),
    (1, 11), (2, 11), (3, 11), (4, 11), (5, 11),
    (0, 12), (1, 12), (2, 12), (3, 12), (4, 12), (5, 12),
]
PRIMARY_G6 = "L??CA?oBDwN_~?"
PRIMARY_CLAIMED_MDS = (0, 1, 8, 9)


def check_graph(label, n, edges, gamma_claimed, claimed_mds=None):
    """Full hypothesis + violation check. Returns True iff the graph is a
    valid counterexample to Conjecture 1 under BOTH Phi readings."""
    log(f"--- {label} ---")
    G = Graph(n, edges)
    s = G.num_edges()
    log(f"  n = {G.n}, s(G) = |E| = {s} (simple: no loops/dups verified on"
        " construction)")

    ok = True

    iso = G.has_isolated()
    log(f"  no isolated vertices: {'OK' if not iso else 'FAIL'}")
    ok &= not iso

    bip = G.bipartition()
    if bip is None:
        log("  bipartite: FAIL (odd cycle found)")
        ok = False
    else:
        log(f"  bipartite: OK (2-coloring found; part sizes"
            f" {sorted(len(p) for p in bip)})")

    log(f"  connected: {G.is_connected()}  (not a hypothesis of Conjecture 1;"
        " informational)")

    gamma, mds_list, tested = G.min_dominating_sets(hard_cap=gamma_claimed + 1)
    log(f"  domination number gamma = {gamma} (exhaustive over all subsets of"
        f" sizes 1..{gamma}; {tested} subsets examined)")
    if gamma != gamma_claimed:
        log(f"  FAIL: gamma != claimed {gamma_claimed}")
        ok = False
    log(f"  minimum dominating sets of size {gamma}: count = {len(mds_list)}")
    if len(mds_list) != 1:
        log("  FAIL: minimum dominating set is NOT unique")
        ok = False
    else:
        log(f"  unique minimum dominating set = {list(mds_list[0])}")
        if claimed_mds is not None and tuple(sorted(mds_list[0])) != \
                tuple(sorted(claimed_mds)):
            log(f"  NOTE: differs from claimed MDS {list(claimed_mds)}")

    hyp = (not iso) and bip is not None and len(mds_list) == 1 \
        and gamma >= 2 and n >= 3 * gamma
    log(f"  hypotheses of Conjecture 1 (bipartite, no isolated vertices,"
        f" unique MDS, gamma={gamma}>=2, n={n}>=3*gamma={3*gamma}):"
        f" {'ALL SATISFIED' if hyp else 'NOT satisfied'}")
    ok &= hyp

    violates_both = True
    for r in ("literal", "corrected"):
        m = m_bound(n, gamma, r)
        rel = ">" if s > m else "<="
        log(f"  m({n},{gamma}) [{r:9s}] = {m}   s(G) = {s} {rel} {m}")
        if s <= m:
            violates_both = False
    verdict = ok and violates_both
    log(f"  VERDICT: {'COUNTEREXAMPLE CONFIRMED (violates both Phi readings)' if verdict else 'NOT a confirmed counterexample'}")
    log("")
    return verdict


def main():
    log("=" * 74)
    log("CLEAN-ROOM VERIFICATION (second pass, written from scratch)")
    log("Target: Conjecture 1 of arXiv:2511.01719 (Koch & Narayan)")
    log("Checker: independent/cleanroom_check.py  --  no attacker code reused")
    log("=" * 74)
    log("")

    log("[1] Formula transcription anchored against the paper's own values")
    anchors_ok = formula_sanity()
    log("")

    log("[2] Primary counterexample rebuilt from the attack-report"
        " DESCRIPTION (edge list typed in from the report, not loaded from"
        " any attacker file)")
    # bipartition-as-described sanity: every edge goes A={0..5} -> B={6..12}
    desc_ok = all((u in range(6)) and (v in range(6, 13))
                  for (u, v) in PRIMARY_EDGES)
    log(f"  every described edge joins A={{0..5}} to B={{6..12}}: {desc_ok}")
    primary_ok = check_graph(
        f"PRIMARY: n={PRIMARY_N}, claimed gamma={PRIMARY_GAMMA_CLAIMED},"
        f" 22 edges",
        PRIMARY_N, PRIMARY_EDGES, PRIMARY_GAMMA_CLAIMED, PRIMARY_CLAIMED_MDS)

    log("[3] Independent graph6 decode of the report's string"
        f" {PRIMARY_G6!r}")
    g6n, g6edges = decode_graph6(PRIMARY_G6)
    same = (g6n == PRIMARY_N and
            sorted((min(u, v), max(u, v)) for (u, v) in g6edges) ==
            sorted((min(u, v), max(u, v)) for (u, v) in PRIMARY_EDGES))
    log(f"  decoded: n={g6n}, |E|={len(g6edges)};"
        f" labeled edge set identical to described list: {same}")
    log("")

    log("[4] Supplementary certificates (JSON data files; data only)")
    supp_ok = True
    supp = [
        ("certificate_14_4.json", 4),
        ("certificate_15_4.json", 4),
        ("certificate_15_4_max.json", 4),
        ("certificate_18_5.json", 5),
        ("certificate_20_6.json", 6),
    ]
    for fname, g_claim in supp:
        path = os.path.join(ATTACK_DIR, fname)
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        edges = [tuple(e) for e in data["edges"]]
        supp_ok &= check_graph(f"{fname}: n={data['n']},"
                               f" claimed gamma={g_claim}",
                               data["n"], edges, g_claim)

    log("=" * 74)
    overall = anchors_ok and desc_ok and primary_ok and same and supp_ok
    if overall:
        log("OVERALL VERDICT: KILL CONFIRMED.")
        log("The rebuilt n=13 graph satisfies every hypothesis of Conjecture 1")
        log("of arXiv:2511.01719 (bipartite, no isolated vertices, unique")
        log("minimum dominating set {0,1,8,9}, gamma=4>=2, n=13>=12=3*gamma)")
        log("and has s(G)=22 > 21 = m(13,4) under BOTH the literal printed")
        log("Phi and the construction-consistent (typo-corrected) Phi.")
        log("All five supplementary certificates also violate both readings.")
    else:
        log("OVERALL VERDICT: VERIFICATION FAILED -- see FAIL lines above.")
    log("=" * 74)

    with open(LOG_PATH, "w", encoding="utf-8") as fh:
        fh.write("\n".join(LOG_LINES) + "\n")
    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
