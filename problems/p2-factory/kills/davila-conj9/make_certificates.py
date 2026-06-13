"""Generate the certificate JSON files for the davila-conj9 kill.
Everything regenerated from the construction; graph6 encoder written from
the formal definition (McKay's format) -- no library dependencies."""

import json
from chain_study import chain, neighbor_masks, check_hypotheses, zf_closure
from checker_conj9 import build_g14


def graph6(n, edges):
    adj = [[False] * n for _ in range(n)]
    for u, v in edges:
        adj[u][v] = adj[v][u] = True
    assert n <= 62
    bits = []
    for j in range(1, n):           # column-major upper triangle
        for i in range(j):
            bits.append(1 if adj[i][j] else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(n + 63)]
    for i in range(0, len(bits), 6):
        val = 0
        for b in bits[i:i + 6]:
            val = (val << 1) | b
        out.append(chr(val + 63))
    return "".join(out)


ACCESS = "2026-06-11"
STMT = ("Conjecture 9 (TxGraffiti - Open). If G is a connected, cubic, and "
        "diamond-free graph, then Z(G) <= gamma(G) + 2, and this bound is "
        "sharp.")
SRC = ("arXiv:2406.19231v2 (R. Davila, 'Another conjecture of TxGraffiti "
       "concerning zero forcing and domination in graphs', v2 18 Nov 2024), "
       "Section 4 'Conclusion'. Verified verbatim from "
       "https://arxiv.org/html/2406.19231v2 on " + ACCESS + ".")

# ---------------- main counterexample ----------------
n14, e14 = build_g14()
nbr = neighbor_masks(n14, e14)
check_hypotheses(n14, nbr)
cert = {
    "slug": "davila-conj9",
    "refutes": STMT,
    "source": SRC,
    "construction": "Two disjoint copies of K_{3,3}; in each copy subdivide "
                    "one edge (one new degree-2 vertex per copy); join the "
                    "two subdivision vertices by a bridge. n = 14.",
    "labeling": "Block A: parts {0,1,2}|{3,4,5}, edge (0,3) subdivided by 6. "
                "Block B: parts {7,8,9}|{10,11,12}, edge (7,10) subdivided "
                "by 13. Bridge (6,13).",
    "n": n14,
    "edges": e14,
    "graph6": graph6(n14, e14),
    "hypotheses_verified": ["connected", "3-regular",
                            "triangle-free (hence diamond-free under both "
                            "the subgraph and induced-subgraph readings)"],
    "gamma": 4,
    "gamma_witness": [0, 3, 7, 10],
    "gamma_lower_bound_proof": "exhaustive: none of the C(14,3)=364 "
                               "3-subsets dominates",
    "Z": 7,
    "Z_witness": [0, 1, 3, 4, 7, 8, 11],
    "Z_lower_bound_proof": "exhaustive: none of the C(14,6)=3003 6-subsets "
                           "is a zero forcing set",
    "conclusion": "Z(G) = 7 = gamma(G) + 3 > gamma(G) + 2: Conjecture 9 is "
                  "FALSE. (Sharpness claim moot.)",
    "checker": "checker_conj9.py (pure Python stdlib, exact bitmask "
               "arithmetic); independent Rust verifier rust_check/ agrees.",
}
with open("certificate_g14.json", "w", newline="\n") as f:
    json.dump(cert, f, indent=1)
print("certificate_g14.json written; graph6 =", cert["graph6"])

# ---------------- chain family ----------------
rows = []
table = {
    # k: (gamma, gamma_wit, gamma_lb_status, Z, Z_wit, Z_lb_status)
    2: (4, [0, 3, 7, 10], "exhaustive (Python + Rust): no 3-set dominates",
        7, [0, 1, 3, 4, 7, 8, 11],
        "exhaustive (Python + Rust): no 6-set forces"),
    3: (7, [0, 3, 6, 8, 11, 15, 18],
        "exhaustive (Python C(22,6)=74,613 + Rust DFS): no 6-set dominates",
        10, [0, 1, 3, 4, 7, 8, 11, 15, 16, 19],
        "exhaustive (Python C(22,9)=497,420 closures + Rust DFS): "
        "no 9-set forces"),
    4: (9, [1, 4, 9, 13, 14, 16, 19, 23, 26],
        "exhaustive Rust DFS with sound monotone pruning: no 8-set dominates",
        13, [1, 4, 5, 6, 7, 8, 11, 15, 16, 19, 23, 24, 27],
        "exhaustive Rust DFS with sound monotone pruning: no 12-set forces"),
    5: (11, [0, 3, 7, 10, 17, 21, 22, 24, 27, 31, 34],
        "exhaustive Rust DFS with sound monotone pruning: no 10-set "
        "dominates",
        16, [1, 4, 5, 6, 7, 8, 11, 15, 16, 19, 23, 24, 27, 31, 32, 35],
        "exhaustive Rust DFS with sound monotone pruning: no 15-set forces "
        "(109 s, 32 threads)"),
}
upper_only = {6: 19, 7: 22, 8: 25}
# exact gamma for k=6,7,8 from Rust DFS (no (gamma-1)-set dominates; witness
# found at gamma); witnesses re-verified in Python below
gamma_678 = {
    6: (14, [1, 5, 6, 8, 11, 15, 18, 25, 29, 30, 32, 35, 39, 42]),
    7: (16, [2, 5, 9, 13, 14, 16, 19, 23, 26, 33, 37, 38, 40, 43, 47, 50]),
    8: (18, [0, 3, 7, 10, 17, 21, 22, 24, 27, 31, 34, 41, 45, 46, 48, 51,
             55, 58]),
}

for k in range(2, 9):
    n, edges = chain(k, "indep")
    nbr = neighbor_masks(n, edges)
    check_hypotheses(n, nbr)
    row = {"k": k, "n": n, "edges_file": f"chain_indep_k{k}.edges",
           "graph6": graph6(n, edges)}
    if k in table:
        g, gw, gst, z, zw, zst = table[k]
        # re-verify witnesses right here
        full = (1 << n) - 1
        cover = 0
        for v in gw:
            cover |= nbr[v] | (1 << v)
        assert cover == full and len(gw) == g
        assert zf_closure(n, nbr, sum(1 << v for v in zw)) == full
        assert len(zw) == z
        row.update({"gamma": g, "gamma_witness": gw, "gamma_lb": gst,
                    "Z": z, "Z_witness": zw, "Z_lb": zst,
                    "gap_Z_minus_gamma": z - g, "status": "EXACT, certified"})
    else:
        zub = upper_only[k]
        offs = [0] + [7 + 8 * (i - 1) for i in range(1, k)]
        zw = [1, 4, 5, 6]
        for off in offs[1:]:
            zw += [off, off + 1, off + 4]
        assert len(zw) == zub
        full = (1 << n) - 1
        assert zf_closure(n, nbr, sum(1 << v for v in zw)) == full
        g, gw = gamma_678[k]
        cover = 0
        for v in gw:
            cover |= nbr[v] | (1 << v)
        assert cover == full and len(gw) == g
        row.update({"gamma": g, "gamma_witness": gw,
                    "gamma_lb": "exhaustive Rust DFS with sound monotone "
                                f"pruning: no {g-1}-set dominates",
                    "Z_upper_bound": zub, "Z_witness": zw,
                    "status": "gamma EXACT, certified; Z upper bound only "
                              "(witness verified); Z lower bound NOT "
                              "certified for this k"})
    rows.append(row)

fam = {
    "slug": "davila-conj9-chain-family",
    "description": "Linear chains of k K_{3,3} blocks: end blocks have one "
                   "subdivided edge, middle blocks two ('indep' variant: "
                   "subdivide a1b1 and a2b2); bridges join the out-"
                   "subdivision vertex of block i to the in-subdivision "
                   "vertex of block i+1. All graphs connected, cubic, "
                   "triangle-free (girth 4, not bipartite), hence "
                   "diamond-free. n = 8k-2.",
    "headline": "Z - gamma takes values 3,3,4,5 at k=2..5 (all EXACT). "
                "Conjectured: gamma = floor(7k/3) and Z = 3k+1 for all k, "
                "giving Z - gamma ~ 2k/3 -> infinity (UNBOUNDED). Not yet "
                "proven for general k.",
    "rows": rows,
}
with open("certificate_chain_family.json", "w", newline="\n") as f:
    json.dump(fam, f, indent=1)
print("certificate_chain_family.json written")
for r in rows:
    print(" ", {kk: r[kk] for kk in ("k", "n") },
          "gamma" in r and (r.get("gamma"), r.get("Z"), r.get("gap_Z_minus_gamma")) or r.get("status"))
