"""
Clean-room Gate-4 checker for the refutation of Davila's Conjecture 9
(arXiv:2406.19231v2, Section 4 "Conclusion"):

    Conjecture 9 (TxGraffiti - Open). If G is a connected, cubic, and
    diamond-free graph, then Z(G) <= gamma(G) + 2, and this bound is sharp.

Counterexample (rebuilt from the construction DESCRIPTION, no code reuse):
  Take two disjoint copies of K_{3,3}; in each copy subdivide one edge
  (introducing one new degree-2 vertex per copy); join the two subdivision
  vertices by a bridge.  Call the result G14 (n = 14).

This script verifies, with exhaustive exact integer (bitmask) arithmetic:
  (1) G14 is connected, 3-regular, triangle-free (hence diamond-free under
      BOTH readings: no diamond subgraph, no induced diamond);
  (2) gamma(G14) = 4  (no 3-subset of V dominates: all C(14,3) = 364 checked;
      an explicit 4-subset dominates);
  (3) Z(G14) = 7      (no 6-subset of V is a zero forcing set: all
      C(14,6) = 3003 closures computed; an explicit 7-subset forces);
  (4) hence Z(G14) = gamma(G14) + 3 > gamma(G14) + 2:  Conjecture 9 is FALSE.

Zero forcing rule used (verbatim from the paper, Sec. 1.1): "At each discrete
time step, if a blue-colored vertex has a unique white-colored neighbor, then
this blue-colored vertex forces its white-colored neighbor to become colored
blue."  S is a zero forcing set iff the process started from S colors V blue.

Run:  python checker_conj9.py     (pure Python 3, no imports beyond stdlib)
"""

from itertools import combinations


# ----------------------------------------------------------------------
# Construction (from the description, independent labeling)
# ----------------------------------------------------------------------
def build_g14():
    """Two K_{3,3} blocks, one edge subdivided in each, bridge the two
    subdivision vertices.

    Block A: parts {0,1,2} | {3,4,5}, subdivide edge (0,3) -> vertex 6.
    Block B: parts {7,8,9} | {10,11,12}, subdivide edge (7,10) -> vertex 13.
    Bridge: (6,13).
    """
    edges = []
    for off, sub in ((0, 6), (7, 13)):
        a = [off + 0, off + 1, off + 2]
        b = [off + 3, off + 4, off + 5]
        for u in a:
            for v in b:
                if (u, v) != (a[0], b[0]):        # the edge to subdivide
                    edges.append((u, v))
        edges.append((a[0], sub))                 # subdivision vertex
        edges.append((b[0], sub))
    edges.append((6, 13))                         # the bridge
    return 14, edges


def neighbor_masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        assert 0 <= u < n and 0 <= v < n and u != v
        assert not (nbr[u] >> v) & 1, f"duplicate edge {(u, v)}"
        nbr[u] |= 1 << v
        nbr[v] |= 1 << u
    return nbr


# ----------------------------------------------------------------------
# Hypothesis checks: connected, cubic, triangle-free / diamond-free
# ----------------------------------------------------------------------
def check_hypotheses(n, nbr):
    full = (1 << n) - 1
    # 3-regular
    assert all(bin(m).count("1") == 3 for m in nbr), "not cubic"
    # connected (BFS from 0)
    seen = 1
    frontier = 1
    while frontier:
        newly = 0
        for v in range(n):
            if (frontier >> v) & 1:
                newly |= nbr[v]
        frontier = newly & ~seen
        seen |= newly
    assert seen == full, "not connected"
    # triangle-free: adjacent vertices share no common neighbor
    for u in range(n):
        for v in range(u + 1, n):
            if (nbr[u] >> v) & 1:
                common = nbr[u] & nbr[v]
                assert common == 0, f"triangle at edge ({u},{v})"
    # Triangle-free => no diamond subgraph and no induced diamond.
    # (A diamond = K4 minus an edge contains triangles.)  Explicit
    # diamond-subgraph check anyway: an edge in >= 2 triangles.
    for u in range(n):
        for v in range(u + 1, n):
            if (nbr[u] >> v) & 1:
                assert bin(nbr[u] & nbr[v]).count("1") <= 1


# ----------------------------------------------------------------------
# Domination number, exhaustively
# ----------------------------------------------------------------------
def dominates(closed, subset, full):
    cover = 0
    for v in subset:
        cover |= closed[v]
    return cover == full


def gamma_exact(n, nbr):
    full = (1 << n) - 1
    closed = [nbr[v] | (1 << v) for v in range(n)]
    k = 1
    while True:
        witness = None
        count = 0
        for subset in combinations(range(n), k):
            count += 1
            if dominates(closed, subset, full):
                witness = subset
                break
        if witness is not None:
            return k, witness, count
        k += 1


# ----------------------------------------------------------------------
# Zero forcing number, exhaustively
# ----------------------------------------------------------------------
def zf_closure(n, nbr, blue, full):
    """Fixpoint of the color change rule, exact bitmask arithmetic."""
    while True:
        forced = 0
        for v in range(n):
            if (blue >> v) & 1:
                white = nbr[v] & ~blue
                if white and (white & (white - 1)) == 0:   # exactly one
                    forced |= white
        if not forced:
            return blue
        blue |= forced


def z_exact(n, nbr):
    full = (1 << n) - 1
    k = 1
    while True:
        witness = None
        tested = 0
        for subset in combinations(range(n), k):
            tested += 1
            blue = 0
            for v in subset:
                blue |= 1 << v
            if zf_closure(n, nbr, blue, full) == full:
                witness = subset
                break
        if witness is not None:
            return k, witness, tested
        k += 1


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------
def verify_graph(name, n, edges, expect_gamma, expect_z):
    nbr = neighbor_masks(n, edges)
    assert len(edges) == 3 * n // 2, "edge count wrong for a cubic graph"
    check_hypotheses(n, nbr)
    print(f"[{name}] n={n}, m={len(edges)}: connected, cubic, triangle-free "
          f"(hence diamond-free, both readings)  -- OK")

    g, gwit, _ = gamma_exact(n, nbr)
    # exhaustiveness of the lower bound: every (g-1)-subset was tried
    from math import comb
    print(f"[{name}] gamma = {g}  (all {comb(n, g - 1)} subsets of size "
          f"{g - 1} fail to dominate; witness {gwit})")
    assert g == expect_gamma

    z, zwit, _ = z_exact(n, nbr)
    print(f"[{name}] Z = {z}  (all {comb(n, z - 1)} subsets of size {z - 1} "
          f"fail to force; witness {zwit})")
    assert z == expect_z

    gap = z - g
    verdict = "REFUTES Conjecture 9" if gap >= 3 else "consistent with Conj 9"
    print(f"[{name}] Z - gamma = {gap}  => Z = gamma + {gap}  [{verdict}]")
    return g, z


def main():
    # --- sanity anchors: reproduce known values first (Gate-2 style) ---
    # K_{3,3}: gamma = 2, Z = 4 (known; equality case cited in the record)
    k33 = [(u, v) for u in range(3) for v in range(3, 6)]
    nbr = neighbor_masks(6, k33)
    g, _, _ = gamma_exact(6, nbr)
    z, _, _ = z_exact(6, nbr)
    assert (g, z) == (2, 4), f"K3,3 sanity failed: gamma={g}, Z={z}"
    print(f"[sanity] K3,3: gamma={g}, Z={z}  (matches literature: Z=gamma+2)")

    # Petersen: gamma = 3, Z = 5 (known)
    pet = [(i, (i + 1) % 5) for i in range(5)] + \
          [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + \
          [(i, i + 5) for i in range(5)]
    nbr = neighbor_masks(10, pet)
    g, _, _ = gamma_exact(10, nbr)
    z, _, _ = z_exact(10, nbr)
    assert (g, z) == (3, 5), f"Petersen sanity failed: gamma={g}, Z={z}"
    print(f"[sanity] Petersen: gamma={g}, Z={z}  (matches literature)")

    # --- the counterexample, rebuilt from the description ---
    n, edges = build_g14()
    g, z = verify_graph("G14 = K3,3 # K3,3", n, edges, expect_gamma=4,
                        expect_z=7)
    assert z == g + 3
    print()
    print("CONCLUSION: G14 is connected, cubic, diamond-free with "
          f"Z = {z} = gamma + 3 > gamma + 2.")
    print("Conjecture 9 of arXiv:2406.19231v2 is FALSE.  VERIFIED.")

    # --- cross-check the claim record's own edge list (independent object) ---
    rec_edges = [(0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
                 (2, 5), (0, 12), (3, 12), (6, 10), (6, 11), (7, 9), (7, 10),
                 (7, 11), (8, 9), (8, 10), (8, 11), (6, 13), (9, 13),
                 (12, 13)]
    print()
    verify_graph("record edge list", 14, rec_edges, expect_gamma=4,
                 expect_z=7)
    print("Record's stated witnesses re-checked:")
    nbr = neighbor_masks(14, rec_edges)
    full = (1 << 14) - 1
    closed = [nbr[v] | (1 << v) for v in range(14)]
    assert dominates(closed, (0, 3, 6, 9), full), "record gamma-witness fails"
    blue = sum(1 << v for v in (0, 1, 3, 4, 6, 7, 10))
    assert zf_closure(14, nbr, blue, full) == full, "record Z-witness fails"
    print("  {0,3,6,9} dominates: OK;  {0,1,3,4,6,7,10} forces: OK")

    # isomorphism of my rebuild to the record's graph (backtracking)
    n1, e1 = build_g14()
    nbr1 = neighbor_masks(n1, e1)
    iso = find_isomorphism(14, nbr1, nbr)
    assert iso is not None, "rebuild NOT isomorphic to record graph"
    print(f"  rebuild is isomorphic to record graph; mapping {iso}")


def find_isomorphism(n, nbr1, nbr2):
    """Simple backtracking graph isomorphism (both graphs cubic, n small)."""
    deg2 = [bin(m).count("1") for m in nbr2]
    mapping = [-1] * n
    used = [False] * n

    def ok(v, w):
        for u in range(n):
            if mapping[u] != -1:
                a = (nbr1[v] >> u) & 1
                b = (nbr2[w] >> mapping[u]) & 1
                if a != b:
                    return False
        return True

    def rec(v):
        if v == n:
            return True
        for w in range(n):
            if not used[w] and deg2[w] == bin(nbr1[v]).count("1") and ok(v, w):
                mapping[v] = w
                used[w] = True
                if rec(v + 1):
                    return True
                mapping[v] = -1
                used[w] = False
        return False

    return list(mapping) if rec(0) else None


if __name__ == "__main__":
    main()
