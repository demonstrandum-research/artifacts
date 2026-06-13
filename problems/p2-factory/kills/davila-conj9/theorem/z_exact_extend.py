"""
z_exact_extend.py -- exact Z(G_k) for k = 6,7,8 by the fort-cover loop
(iterative fort generation + CP-SAT min hitting set).  Soundness:
  * every zero forcing set hits every fort  => ILP optimum <= Z (lower bound);
  * if the optimal hitting set B forces (closure = V), then |B| = Z exactly.
Each discovered fort is asserted to be a genuine fort before use.
This extends the certified table (Z exact at k<=5) to k = 6,7,8 as extra
validation of the proven formula Z = 3k+1.  NOT part of the proof.
"""
from ortools.sat.python import cp_model

def chain(k):
    edges, blocks = [], []
    offset, out_sub_prev = 0, None
    for i in range(k):
        a = [offset + 0, offset + 1, offset + 2]
        b = [offset + 3, offset + 4, offset + 5]
        subdiv = [(a[0], b[0])] if i in (0, k - 1) else [(a[0], b[0]), (a[1], b[1])]
        subs = [offset + 6 + j for j in range(len(subdiv))]
        for u in a:
            for v in b:
                if (u, v) not in subdiv:
                    edges.append((u, v))
        for (u, v), s in zip(subdiv, subs):
            edges.append((u, s)); edges.append((v, s))
        if out_sub_prev is not None:
            edges.append((out_sub_prev, subs[0]))
        out_sub_prev = subs[-1]
        blocks.append(dict(a=a, b=b, subs=subs))
        offset += 6 + len(subs)
    return offset, edges, blocks

def neighbor_masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        nbr[u] |= 1 << v; nbr[v] |= 1 << u
    return nbr

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

def is_fort(n, nbr, F):
    if F == 0:
        return False
    for v in range(n):
        if not (F >> v) & 1:
            inF = nbr[v] & F
            if inF and (inF & (inF - 1)) == 0:
                return False
    return True

def bits(m):
    out, v = [], 0
    while m:
        if m & 1: out.append(v)
        m >>= 1; v += 1
    return out

def min_fort_avoiding(n, nbr, B):
    """Minimum-size fort disjoint from blue set B (bitmask), or None.
    Fort: F nonempty, and every v not in F has != 1 neighbours in F."""
    model = cp_model.CpModel()
    f = [model.NewBoolVar(f"f{v}") for v in range(n)]
    model.AddBoolOr(f)                      # nonempty
    for v in range(n):
        if (B >> v) & 1:
            model.Add(f[v] == 0)            # disjoint from B
    for v in range(n):
        nb = [f[u] for u in bits(nbr[v])]
        e = model.NewBoolVar(f"e{v}")       # e_v <=> exactly one nbr in F
        model.Add(sum(nb) == 1).OnlyEnforceIf(e)
        model.Add(sum(nb) != 1).OnlyEnforceIf(e.Not())
        model.AddImplication(e, f[v])       # outside F => not exactly one
    model.Minimize(sum(f))
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 28
    status = solver.Solve(model)
    if status == cp_model.INFEASIBLE:
        return None
    assert status == cp_model.OPTIMAL
    F = 0
    for v in range(n):
        if solver.Value(f[v]):
            F |= 1 << v
    return F

def z_fort_cover(n, nbr):
    """Exact Z by fort-cover: hitting-set LB + closure check, min-fort cuts."""
    full = (1 << n) - 1
    forts = []
    while True:
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f"b{v}") for v in range(n)]
        for F in forts:
            model.AddBoolOr([x[v] for v in range(n) if (F >> v) & 1])
        model.Minimize(sum(x))
        solver = cp_model.CpSolver()
        solver.parameters.num_workers = 28
        status = solver.Solve(model)
        assert status == cp_model.OPTIMAL
        B = 0
        for v in range(n):
            if solver.Value(x[v]):
                B |= 1 << v
        cl = zf_closure(n, nbr, B)
        if cl == full:
            return bin(B).count("1"), sorted(bits(B)), len(forts)
        F = min_fort_avoiding(n, nbr, B)    # strongest cut: minimum fort
        assert F is not None and (F & B) == 0 and is_fort(n, nbr, F)
        forts.append(F)
        if len(forts) % 25 == 0:
            print(f"   ... {len(forts)} forts, current LB {bin(B).count('1')}", flush=True)

if __name__ == "__main__":
    import io
    for k in (6, 7, 8):
        n, edges, blocks = chain(k)
        nbr = neighbor_masks(n, edges)
        z, wit, nf = z_fort_cover(n, nbr)
        pred = 3 * k + 1
        verdict = "MATCHES 3k+1" if z == pred else f"*** MISMATCH (predicted {pred}) ***"
        print(f"k={k} n={n}: Z = {z}  ({verdict}); witness {wit}; {nf} forts", flush=True)
