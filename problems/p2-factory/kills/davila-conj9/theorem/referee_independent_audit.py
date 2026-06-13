#!/usr/bin/env python3
"""Independent hostile audit for induction-transfer.md.

This deliberately does not import validate_induction.py.  It rebuilds the chain
family, recomputes the finite gadget facts, solves gamma/Z for k=2,3,4, and
stress-tests the cut inequality on small graphs.
"""

from itertools import combinations, product
from math import ceil, floor
import random
import sys


def add_edge(edges, u, v):
    if u == v:
        raise ValueError("loop")
    edges.add(tuple(sorted((u, v))))


def build_chain(k):
    labels = []
    edges_named = set()
    for i in range(k):
        labs = ["a0", "a1", "a2", "b0", "b1", "b2", "s"]
        if 0 < i < k - 1:
            labs.append("t")
        for lab in labs:
            labels.append((i, lab))
        subdivided = {("a0", "b0")}
        if 0 < i < k - 1:
            subdivided.add(("a1", "b1"))
        for a in ("a0", "a1", "a2"):
            for b in ("b0", "b1", "b2"):
                if (a, b) not in subdivided:
                    edges_named.add(tuple(sorted(((i, a), (i, b)))))
        for a, b, s in [("a0", "b0", "s")]:
            edges_named.add(tuple(sorted(((i, a), (i, s)))))
            edges_named.add(tuple(sorted(((i, b), (i, s)))))
        if 0 < i < k - 1:
            edges_named.add(tuple(sorted(((i, "a1"), (i, "t")))))
            edges_named.add(tuple(sorted(((i, "b1"), (i, "t")))))
    for i in range(k - 1):
        out_port = "s" if i == 0 else "t"
        edges_named.add(tuple(sorted(((i, out_port), (i + 1, "s")))))

    index = {v: j for j, v in enumerate(labels)}
    edges = [(index[u], index[v]) for u, v in edges_named]
    return labels, edges


def piece(double_subdivision):
    labels = ["a0", "a1", "a2", "b0", "b1", "b2", "s"]
    if double_subdivision:
        labels.append("t")
    edges = set()
    subdivided = {("a0", "b0")}
    if double_subdivision:
        subdivided.add(("a1", "b1"))
    for a in ("a0", "a1", "a2"):
        for b in ("b0", "b1", "b2"):
            if (a, b) not in subdivided:
                add_edge(edges, labels.index(a), labels.index(b))
    add_edge(edges, labels.index("a0"), labels.index("s"))
    add_edge(edges, labels.index("b0"), labels.index("s"))
    if double_subdivision:
        add_edge(edges, labels.index("a1"), labels.index("t"))
        add_edge(edges, labels.index("b1"), labels.index("t"))
    return labels, sorted(edges)


def adjacency(n, edges):
    adj = [0] * n
    for u, v in edges:
        if (adj[u] >> v) & 1:
            raise ValueError("duplicate edge")
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def z_closure(n, adj, blue):
    while True:
        forced = 0
        for u in range(n):
            if (blue >> u) & 1:
                white = adj[u] & ~blue
                if white and white & (white - 1) == 0:
                    forced |= white
        forced &= ~blue
        if not forced:
            return blue
        blue |= forced


def exact_z_by_subsets(n, edges, stop_at=None):
    adj = adjacency(n, edges)
    full = (1 << n) - 1
    max_r = n if stop_at is None else stop_at
    for r in range(max_r + 1):
        for sub in combinations(range(n), r):
            blue = 0
            for v in sub:
                blue |= 1 << v
            if z_closure(n, adj, blue) == full:
                return r, sub
    return None, None


def dominates_with_set(n, closed, sub, target):
    cover = 0
    for v in sub:
        cover |= closed[v]
    return (cover & target) == target


def exact_domination(n, edges, target=None, stop_at=None):
    adj = adjacency(n, edges)
    closed = [adj[v] | (1 << v) for v in range(n)]
    if target is None:
        target = (1 << n) - 1
    max_r = n if stop_at is None else stop_at
    for r in range(max_r + 1):
        for sub in combinations(range(n), r):
            if dominates_with_set(n, closed, sub, target):
                return r, sub
    return None, None


def induced(vertices, edges):
    vertices = list(vertices)
    pos = {v: i for i, v in enumerate(vertices)}
    keep = set(vertices)
    new_edges = []
    for u, v in edges:
        if u in keep and v in keep:
            new_edges.append((pos[u], pos[v]))
    return len(vertices), new_edges, pos


def window_case(k, first_block):
    labels, edges = build_chain(k)
    inv = {name: i for i, name in enumerate(labels)}
    window_names = [
        name for name in labels
        if first_block <= name[0] <= first_block + 2
    ]
    free = set()
    if first_block > 0:
        free.add((first_block, "s"))
    if first_block + 2 < k - 1:
        free.add((first_block + 2, "t"))
    window_vertices = [inv[name] for name in window_names]
    n_win, e_win, pos = induced(window_vertices, edges)
    target = 0
    for name in window_names:
        if name not in free:
            target |= 1 << pos[inv[name]]

    full_adj = adjacency(len(labels), edges)
    wset = set(window_vertices)
    for name in window_names:
        v = inv[name]
        outside = [u for u in range(len(labels)) if ((full_adj[v] >> u) & 1) and u not in wset]
        if name in free:
            assert len(outside) == 1, (name, outside)
        else:
            assert not outside, (name, outside)
    return n_win, e_win, target


def gamma_chain_bruteforce(k):
    labels, edges = build_chain(k)
    return exact_domination(len(labels), edges)


def theorem_forcing_schedule_check(k):
    labels, edges = build_chain(k)
    n = len(labels)
    inv = {name: i for i, name in enumerate(labels)}
    adj = adjacency(n, edges)
    blue = 0
    initial = [(0, "a0"), (0, "a1"), (0, "b0"), (0, "b1")]
    for i in range(1, k):
        initial.extend([(i, "a1"), (i, "b0"), (i, "b1")])
    for name in initial:
        blue |= 1 << inv[name]

    forces = [
        ((0, "a1"), (0, "b2")),
        ((0, "b1"), (0, "a2")),
        ((0, "a0"), (0, "s")),
        ((0, "s"), (1, "s")),
    ]
    for i in range(1, k - 1):
        forces.extend([
            ((i, "s"), (i, "a0")),
            ((i, "a0"), (i, "b2")),
            ((i, "b0"), (i, "a2")),
            ((i, "a1"), (i, "t")),
            ((i, "t"), (i + 1, "s")),
        ])
    last = k - 1
    forces.extend([
        ((last, "s"), (last, "a0")),
        ((last, "a0"), (last, "b2")),
        ((last, "b0"), (last, "a2")),
    ])

    for u_name, v_name in forces:
        u = inv[u_name]
        v = inv[v_name]
        white = adj[u] & ~blue
        if not ((blue >> u) & 1):
            return False, f"{u_name} is not blue before forcing"
        if (blue >> v) & 1:
            return False, f"{v_name} is already blue before forcing"
        if not ((adj[u] >> v) & 1):
            return False, f"{u_name}->{v_name} is not an edge"
        if white != (1 << v):
            bad = [labels[x] for x in range(n) if (white >> x) & 1]
            return False, f"{u_name} white neighbors are {bad}, not only {v_name}"
        blue |= 1 << v
    if blue != (1 << n) - 1:
        missing = [labels[x] for x in range(n) if not ((blue >> x) & 1)]
        return False, f"schedule ended with white vertices {missing}"
    return len(set(initial)) == 3 * k + 1, f"initial size {len(set(initial))}"


def theorem_domination_pattern_check(k):
    labels, edges = build_chain(k)
    inv = {name: i for i, name in enumerate(labels)}
    configs = []
    if k == 2:
        configs = ["2A", "2A"]
    elif k % 3 == 1:
        configs = ["2A"] + ["2A", "T3", "2B"] * ((k - 1) // 3)
    elif k % 3 == 2:
        configs = ["2A"] + ["2A", "T3", "2B"] * ((k - 2) // 3) + ["2A"]
    else:
        configs = ["2A"] + ["2A", "T3", "2B"] * ((k - 3) // 3) + ["T3p", "2B"]
    chosen = set()
    for i, cfg in enumerate(configs):
        if cfg == "2A":
            names = [(i, "a0"), (i, "b0")]
        elif cfg == "2B":
            names = [(i, "a1"), (i, "b1")]
        elif cfg == "T3":
            names = [(i, "s"), (i, "t"), (i, "a2")]
        elif cfg == "T3p":
            names = [(i, "a0"), (i, "b0"), (i, "t")]
        else:
            raise ValueError(cfg)
        for name in names:
            if name not in inv:
                return False, f"config {cfg} uses absent vertex {name}"
            chosen.add(inv[name])
    adj = adjacency(len(labels), edges)
    closed = [adj[v] | (1 << v) for v in range(len(labels))]
    ok_dom = dominates_with_set(len(labels), closed, chosen, (1 << len(labels)) - 1)
    ok_size = len(chosen) == 7 * k // 3
    return ok_dom and ok_size, f"size {len(chosen)}, configs {configs}"


def z_chain_chrono(k, time_limit=120.0):
    try:
        from ortools.sat.python import cp_model
    except Exception as exc:
        raise RuntimeError("ortools is required for the chronological Z check") from exc

    labels, edges = build_chain(k)
    n = len(labels)
    adj = adjacency(n, edges)
    neigh = [[u for u in range(n) if (adj[v] >> u) & 1] for v in range(n)]

    model = cp_model.CpModel()
    initial = [model.NewBoolVar(f"initial_{v}") for v in range(n)]
    time = [model.NewIntVar(0, n, f"time_{v}") for v in range(n)]
    force = {}
    for u, v in edges:
        force[(u, v)] = model.NewBoolVar(f"force_{u}_{v}")
        force[(v, u)] = model.NewBoolVar(f"force_{v}_{u}")

    for v in range(n):
        incoming = [force[(u, v)] for u in neigh[v]]
        model.Add(time[v] == 0).OnlyEnforceIf(initial[v])
        model.Add(sum(incoming) == 0).OnlyEnforceIf(initial[v])
        model.Add(time[v] >= 1).OnlyEnforceIf(initial[v].Not())
        model.Add(sum(incoming) == 1).OnlyEnforceIf(initial[v].Not())

    for (u, v), fvar in force.items():
        model.Add(time[u] <= time[v] - 1).OnlyEnforceIf(fvar)
        for w in neigh[u]:
            if w != v:
                model.Add(time[w] <= time[v] - 1).OnlyEnforceIf(fvar)

    model.Minimize(sum(initial))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_workers = 8
    status = solver.Solve(model)
    if status != cp_model.OPTIMAL:
        raise RuntimeError(f"CP-SAT did not prove optimality for k={k}; status={status}")
    witness = [v for v in range(n) if solver.Value(initial[v])]
    blue = 0
    for v in witness:
        blue |= 1 << v
    assert z_closure(n, adj, blue) == (1 << n) - 1
    return int(solver.ObjectiveValue()), tuple(witness)


def graph_from_mask(n, mask):
    edges = []
    bit = 0
    for u in range(n):
        for v in range(u + 1, n):
            if (mask >> bit) & 1:
                edges.append((u, v))
            bit += 1
    return edges


Z_CACHE = {}


def cached_z(n, edges):
    key_edges = tuple(sorted(tuple(sorted(e)) for e in edges))
    key = (n, key_edges)
    if key not in Z_CACHE:
        Z_CACHE[key] = exact_z_by_subsets(n, list(key_edges))[0]
    return Z_CACHE[key]


def cut_bound_value(n, edges, parts):
    crossing = 0
    for u, v in edges:
        iu = next(i for i, p in enumerate(parts) if u in p)
        iv = next(i for i, p in enumerate(parts) if v in p)
        if iu != iv:
            crossing += 1
    zsum = 0
    for part in parts:
        m, e_ind, _ = induced(sorted(part), edges)
        zsum += cached_z(m, e_ind)
    return cached_z(n, edges), zsum - crossing


def canonical_partitions(n, r):
    for assignment in product(range(r), repeat=n):
        if set(assignment) != set(range(r)):
            continue
        if assignment[0] != 0:
            continue
        parts = [set() for _ in range(r)]
        for v, cls in enumerate(assignment):
            parts[cls].add(v)
        yield parts


def test_cut_lemma():
    checked = 0
    for n in range(2, 6):
        edge_count = n * (n - 1) // 2
        for mask in range(1 << edge_count):
            edges = graph_from_mask(n, mask)
            for r in (2, 3):
                if r > n:
                    continue
                for parts in canonical_partitions(n, r):
                    lhs, rhs = cut_bound_value(n, edges, parts)
                    checked += 1
                    if lhs < rhs:
                        return False, checked, (n, edges, parts, lhs, rhs)

    rng = random.Random(20260612)
    for _ in range(200):
        n = rng.randint(6, 8)
        edges = []
        for u in range(n):
            for v in range(u + 1, n):
                if rng.random() < 0.35:
                    edges.append((u, v))
        r = rng.choice((2, 3, 4))
        while True:
            assignment = [rng.randrange(r) for _ in range(n)]
            if set(assignment) == set(range(r)):
                break
        parts = [set() for _ in range(r)]
        for v, cls in enumerate(assignment):
            parts[cls].add(v)
        lhs, rhs = cut_bound_value(n, edges, parts)
        checked += 1
        if lhs < rhs:
            return False, checked, (n, edges, parts, lhs, rhs)
    return True, checked, None


def arithmetic_checks():
    bad = []
    for k in range(2, 200):
        if 3 * k + 1 - floor(7 * k / 3) != ceil((2 * k + 3) / 3):
            bad.append(k)
        r = k % 3
        if r == 0 and floor(7 * k / 3) != 7 * (k // 3):
            bad.append(k)
        if r == 1 and floor(7 * k / 3) != 7 * ((k - 1) // 3) + 2:
            bad.append(k)
        if r == 2 and floor(7 * k / 3) != 7 * ((k - 2) // 3) + 4:
            bad.append(k)
    return bad


def main():
    print("Independent audit: no imports from validate_induction.py")

    for name, double, expected in [("B1", False, 4), ("B2", True, 4)]:
        labels, edges = piece(double)
        z, witness = exact_z_by_subsets(len(labels), edges)
        print(f"{name}: exact Z={z}, witness labels={[labels[v] for v in witness]}")
        assert z == expected

    for name, k, first in [
        ("EMM", 5, 0),
        ("MMM", 5, 1),
        ("MME", 5, 2),
        ("EME", 3, 0),
    ]:
        n_win, e_win, target = window_case(k, first)
        q, witness = exact_domination(n_win, e_win, target=target)
        print(f"{name}: quasi-domination minimum={q}, witness={witness}")
        assert q == 7

    for k in range(2, 13):
        ok_force, force_detail = theorem_forcing_schedule_check(k)
        ok_dom, dom_detail = theorem_domination_pattern_check(k)
        print(
            f"Explicit constructions k={k}: "
            f"forcing_schedule={ok_force} ({force_detail}); "
            f"domination_pattern={ok_dom} ({dom_detail})"
        )
        assert ok_force and ok_dom

    for k in (2, 3, 4):
        gamma, gw = gamma_chain_bruteforce(k)
        z, zw = z_chain_chrono(k)
        print(
            f"G_{k}: gamma={gamma} (target {7*k//3}), "
            f"Z={z} (target {3*k+1})"
        )
        assert gamma == 7 * k // 3
        assert z == 3 * k + 1

    ok, count, counterexample = test_cut_lemma()
    print(f"Cut lemma stress test: checked {count} cases; violation={counterexample}")
    assert ok

    bad_arithmetic = arithmetic_checks()
    print(f"Arithmetic checks: bad k values={bad_arithmetic}")
    assert not bad_arithmetic

    print("ALL INDEPENDENT AUDIT CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
