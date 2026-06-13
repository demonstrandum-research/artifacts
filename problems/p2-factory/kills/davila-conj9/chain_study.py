"""
Upgrade study: does Z - gamma GROW on chains of K3,3 blocks?

Chain construction (k blocks, linear):
  Each block is a copy of K3,3 with parts {a1,a2,a3} | {b1,b2,b3}.
  End blocks (first, last): one subdivided edge.
  Middle blocks: two subdivided edges (variant 'indep': a1b1 and a2b2;
  variant 'shared': a1b1 and a1b2 sharing vertex a1).
  Bridges join the 'out' subdivision vertex of block i to the 'in'
  subdivision vertex of block i+1.
  n = 7*2 + 8*(k-2) = 8k - 2.  Connected, cubic, triangle-free
  (K3,3 is bipartite; girth stays >= 4; bridges create no short cycles),
  hence diamond-free.

Exact gamma: CP-SAT ILP (minimize sum x_v s.t. closed neighborhoods covered),
  cross-checked by exhaustive enumeration for small n.
Exact Z: fort-cover loop with CP-SAT hitting-set ILP:
  - Every zero forcing set intersects every fort (F nonempty, no vertex
    outside F has exactly one neighbor in F): if B avoids F, the first force
    into all-white F would need a blue vertex with its unique white neighbor
    in F, i.e. exactly one neighbor in F - contradiction.
  - The complement of a stalled closure is a fort: if v in closure(B) had
    exactly one neighbor outside, that neighbor would be its unique white
    neighbor and would be forced - contradiction with fixpoint.
  Loop: solve min-hitting-set over discovered forts -> candidate B;
  if closure(B) = V then |B| = Z exactly (ILP optimum <= Z is a relaxation
  lower bound and B is a forcing set, an upper bound); else add the fort
  V \\ closure(B) and repeat.  Exhaustive enumeration cross-check for small n.
"""

import sys
from itertools import combinations
from math import comb
from ortools.sat.python import cp_model


# ---------------------------------------------------------------- chains
def chain(k, variant="indep"):
    """Return (n, edges, blocks) for a linear chain of k K3,3 blocks."""
    edges = []
    offset = 0
    out_sub_prev = None
    for i in range(k):
        a = [offset + 0, offset + 1, offset + 2]
        b = [offset + 3, offset + 4, offset + 5]
        if i == 0 or i == k - 1:
            subdiv = [(a[0], b[0])]          # one subdivided edge
        elif variant == "indep":
            subdiv = [(a[0], b[0]), (a[1], b[1])]
        else:                                 # 'shared'
            subdiv = [(a[0], b[0]), (a[0], b[1])]
        nsub = len(subdiv)
        subs = [offset + 6 + j for j in range(nsub)]
        for u in a:
            for v in b:
                if (u, v) not in subdiv:
                    edges.append((u, v))
        for (u, v), s in zip(subdiv, subs):
            edges.append((u, s))
            edges.append((v, s))
        # bridge wiring: first sub vertex = 'in' (to previous), last = 'out'
        if out_sub_prev is not None:
            edges.append((out_sub_prev, subs[0]))
        out_sub_prev = subs[-1]
        offset += 6 + nsub
    return offset, edges


def neighbor_masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        assert u != v and not (nbr[u] >> v) & 1
        nbr[u] |= 1 << v
        nbr[v] |= 1 << u
    return nbr


def check_hypotheses(n, nbr):
    full = (1 << n) - 1
    assert all(bin(m).count("1") == 3 for m in nbr), "not cubic"
    seen, frontier = 1, 1
    while frontier:
        newly = 0
        for v in range(n):
            if (frontier >> v) & 1:
                newly |= nbr[v]
        frontier = newly & ~seen
        seen |= newly
    assert seen == full, "not connected"
    for u in range(n):
        for v in range(u + 1, n):
            if (nbr[u] >> v) & 1:
                assert nbr[u] & nbr[v] == 0, "triangle!"


# ---------------------------------------------------------------- gamma
def gamma_ilp(n, nbr):
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f"x{v}") for v in range(n)]
    for v in range(n):
        dominators = [x[v]] + [x[u] for u in range(n) if (nbr[v] >> u) & 1]
        model.AddBoolOr(dominators)
    model.Minimize(sum(x))
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 16
    status = solver.Solve(model)
    assert status == cp_model.OPTIMAL
    wit = [v for v in range(n) if solver.Value(x[v])]
    return len(wit), wit


def gamma_brute(n, nbr, upper):
    """Exhaustive: confirm no (upper-1)-set dominates; return witness check."""
    full = (1 << n) - 1
    closed = [nbr[v] | (1 << v) for v in range(n)]
    for subset in combinations(range(n), upper - 1):
        cover = 0
        for v in subset:
            cover |= closed[v]
        if cover == full:
            return False
    return True


# ---------------------------------------------------------------- zero forcing
def zf_closure(n, nbr, blue):
    while True:
        forced = 0
        for v in range(n):
            if (blue >> v) & 1:
                white = nbr[v] & ~blue
                if white and (white & (white - 1)) == 0:
                    forced |= white
        if not forced:
            return blue
        blue |= forced


def z_fort_cover(n, nbr, verbose=False):
    full = (1 << n) - 1
    forts = []
    while True:
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f"b{v}") for v in range(n)]
        for F in forts:
            model.AddBoolOr([x[v] for v in range(n) if (F >> v) & 1])
        model.Minimize(sum(x))
        solver = cp_model.CpSolver()
        solver.parameters.num_workers = 16
        status = solver.Solve(model)
        assert status == cp_model.OPTIMAL
        B = 0
        wit = []
        for v in range(n):
            if solver.Value(x[v]):
                B |= 1 << v
                wit.append(v)
        cl = zf_closure(n, nbr, B)
        if cl == full:
            return len(wit), wit, forts
        F = full & ~cl
        assert F and (F & B) == 0
        # sanity: F is a fort
        for v in range(n):
            if not (F >> v) & 1:
                inF = nbr[v] & F
                assert not (inF and (inF & (inF - 1)) == 0), "not a fort!"
        forts.append(F)
        if verbose and len(forts) % 25 == 0:
            print(f"    ... {len(forts)} forts, current LB {len(wit)}",
                  flush=True)


def z_brute_lb(n, nbr, size):
    """Exhaustive: True iff NO subset of given size forces."""
    full = (1 << n) - 1
    for subset in combinations(range(n), size):
        blue = 0
        for v in subset:
            blue |= 1 << v
        if zf_closure(n, nbr, blue) == full:
            return False
    return True


# ---------------------------------------------------------------- main
def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    brute_n_limit_gamma = 30   # exhaustive gamma confirmation up to this n
    brute_n_limit_z = 22       # exhaustive Z confirmation up to this n
    for variant in ("indep", "shared"):
        print(f"=== variant '{variant}' ===")
        rows = []
        for k in range(2, kmax + 1):
            n, edges = chain(k, variant)
            nbr = neighbor_masks(n, edges)
            check_hypotheses(n, nbr)
            g, gwit = gamma_ilp(n, nbr)
            z, zwit, forts = z_fort_cover(n, nbr)
            note = []
            if n <= brute_n_limit_gamma:
                assert gamma_brute(n, nbr, g), "brute force contradicts ILP!"
                note.append("gamma brute-confirmed")
            if n <= brute_n_limit_z:
                assert z_brute_lb(n, nbr, z - 1), \
                    "brute force found smaller forcing set!"
                note.append("Z brute-confirmed")
            rows.append((k, n, g, z, z - g))
            print(f"k={k}  n={n}  gamma={g} {gwit}")
            print(f"      Z={z} {zwit}  (#forts used: {len(forts)})")
            print(f"      Z-gamma = {z-g}   {'; '.join(note)}", flush=True)
        print(f"--- summary ({variant}): k, n, gamma, Z, gap ---")
        for r in rows:
            print("   ", r)
        print()


if __name__ == "__main__":
    main()
