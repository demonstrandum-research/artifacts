from itertools import combinations, product
from math import comb
import random


def bits(mask):
    while mask:
        lsb = mask & -mask
        yield lsb.bit_length() - 1
        mask ^= lsb


def bitcount(mask):
    return mask.bit_count()


def ceil_div(a, b):
    return -(-a // b)


def make_graph(n, edges):
    adj = [0] * n
    for u, v in edges:
        assert u != v
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return tuple(adj)


def closure(adj, start):
    n = len(adj)
    full = (1 << n) - 1
    blue = start
    changed = True
    while changed:
        changed = False
        white = full ^ blue
        for u in range(n):
            if blue >> u & 1:
                wn = adj[u] & white
                if wn and (wn & (wn - 1)) == 0:
                    blue |= wn
                    changed = True
    return blue


def is_zfs(adj, start):
    return closure(adj, start) == (1 << len(adj)) - 1


def z_number(adj):
    n = len(adj)
    full = (1 << n) - 1
    for r in range(n + 1):
        for combo in combinations(range(n), r):
            mask = 0
            for v in combo:
                mask |= 1 << v
            if closure(adj, mask) == full:
                return r
    raise AssertionError("unreachable")


def is_fort(adj, F):
    if F == 0:
        return False
    n = len(adj)
    full = (1 << n) - 1
    outside = full ^ F
    for v in bits(outside):
        if bitcount(adj[v] & F) == 1:
            return False
    return True


def forts(adj):
    n = len(adj)
    return [F for F in range(1, 1 << n) if is_fort(adj, F)]


def is_minimal_fort(adj, F):
    if not is_fort(adj, F):
        return False
    sub = (F - 1) & F
    while sub:
        if is_fort(adj, sub):
            return False
        sub = (sub - 1) & F
    return True


def dominates(adj, D):
    covered = D
    for v in bits(D):
        covered |= adj[v]
    return covered == (1 << len(adj)) - 1


def subset_mask(names, labels):
    inv = {name: i for i, name in enumerate(labels)}
    mask = 0
    for name in names:
        mask |= 1 << inv[name]
    return mask


def mask_names(mask, labels):
    return "{" + ",".join(labels[i] for i in bits(mask)) + "}"


def R_end():
    labels = ["a1", "a2", "a3", "b1", "b2", "b3", "s"]
    edges = []
    for a in range(3):
        for b in range(3, 6):
            if (a, b) != (0, 3):
                edges.append((a, b))
    edges += [(0, 6), (3, 6)]
    return labels, make_graph(7, edges)


def R_mid():
    labels = ["a1", "a2", "a3", "b1", "b2", "b3", "s1", "s2"]
    edges = []
    for a in range(3):
        for b in range(3, 6):
            if (a, b) not in [(0, 3), (1, 4)]:
                edges.append((a, b))
    edges += [(0, 6), (3, 6), (1, 7), (4, 7)]
    return labels, make_graph(8, edges)


def verify_per_block_and_tables():
    rows_end = [
        (["a1", "a2", "a3"], 2, ["b2", "b3"]),
        (["a1", "a2", "b1"], 4, ["b2", "b3"]),
        (["a2", "a3", "b1"], 2, ["b2", "b3"]),
        (["a1", "a2", "b2"], 8, ["b1", "b3", "s"]),
        (["a2", "a3", "b2"], 4, ["b1", "b3", "s"]),
        (["a1", "a2", "s"], 4, ["b2", "b3"]),
        (["a2", "a3", "s"], 2, ["b2", "b3"]),
        (["a1", "b1", "s"], 1, ["a2", "a3"]),
        (["a2", "b1", "s"], 4, ["b2", "b3"]),
        (["a2", "b2", "s"], 4, ["a1", "a3", "b1", "b3"]),
    ]
    rows_mid = [
        (["a1", "a2", "a3"], 2, ["b1", "b3", "s1"]),
        (["a1", "a2", "b1"], 4, ["b2", "b3", "s2"]),
        (["a1", "a3", "b1"], 4, ["b2", "b3", "s2"]),
        (["a2", "a3", "b1"], 4, ["b2", "b3", "s2"]),
        (["a3", "b1", "b2"], 2, ["a1", "a2", "s1", "s2"]),
        (["a1", "a3", "b3"], 4, ["b1", "b2", "s1", "s2"]),
        (["a1", "a2", "s1"], 4, ["b2", "b3", "s2"]),
        (["a1", "a3", "s1"], 4, ["b2", "b3", "s2"]),
        (["a2", "a3", "s1"], 4, ["b2", "b3", "s2"]),
        (["a1", "b1", "s1"], 2, ["a2", "a3", "s2"]),
        (["a2", "b1", "s1"], 4, ["b2", "b3", "s2"]),
        (["a3", "b1", "s1"], 4, ["b2", "b3", "s2"]),
        (["a2", "b2", "s1"], 2, ["a1", "a3", "b1", "b3"]),
        (["a3", "b2", "s1"], 4, ["a1", "b1", "b3", "s2"]),
        (["a3", "b3", "s1"], 2, ["a1", "a2", "b1", "b2"]),
        (["a1", "s1", "s2"], 4, ["a2", "a3", "b2", "b3"]),
        (["a3", "s1", "s2"], 2, ["a1", "a2", "b1", "b2"]),
    ]

    def perm_from_cycles(n, cycles):
        p = list(range(n))
        for cyc in cycles:
            vals = list(cyc)
            for a, b in zip(vals, vals[1:] + vals[:1]):
                p[a] = b
        return tuple(p)

    def compose(p, q):
        return tuple(p[q[i]] for i in range(len(p)))

    def generated_group(n, gens):
        ident = tuple(range(n))
        group = {ident}
        frontier = [ident]
        while frontier:
            g = frontier.pop()
            for h in gens:
                for new in (compose(g, h), compose(h, g)):
                    if new not in group:
                        group.add(new)
                        frontier.append(new)
        return sorted(group)

    def apply_perm(mask, p):
        out = 0
        for i in bits(mask):
            out |= 1 << p[i]
        return out

    def check_table(kind, labels, adj, rows, gens, expected_group_order):
        z = z_number(adj)
        fs = forts(adj)
        minimal = [F for F in fs if is_minimal_fort(adj, F)]
        all3 = [sum(1 << i for i in c) for c in combinations(range(len(labels)), 3)]
        misses = {B: [F for F in minimal if not (B & F)] for B in all3}
        assert all(misses[B] for B in all3), kind
        group = generated_group(len(labels), gens)
        assert len(group) == expected_group_order, (kind, len(group))
        seen = set()
        size_sum = 0
        checked_rows = 0
        for rep_names, size, fort_names in rows:
            B = subset_mask(rep_names, labels)
            F = subset_mask(fort_names, labels)
            assert B & F == 0, (kind, rep_names, fort_names)
            assert is_fort(adj, F), (kind, fort_names)
            assert is_minimal_fort(adj, F), (kind, fort_names)
            orbit = {apply_perm(B, p) for p in group}
            assert len(orbit) == size, (kind, rep_names, len(orbit), size)
            assert not (seen & orbit), (kind, rep_names)
            seen |= orbit
            size_sum += size
            checked_rows += 1
        assert seen == set(all3), (kind, len(seen), len(all3))
        return {
            "Z": z,
            "forts": len(fs),
            "minimal_forts": len(minimal),
            "group_order": len(group),
            "rows_checked": checked_rows,
            "orbit_size_sum": size_sum,
            "three_subsets": len(all3),
        }

    labels_e, adj_e = R_end()
    labels_m, adj_m = R_mid()
    rho_e = perm_from_cycles(7, [(0, 3), (1, 4), (2, 5)])
    sigma_e = perm_from_cycles(7, [(1, 2)])
    tau_e = perm_from_cycles(7, [(4, 5)])
    rho_m = perm_from_cycles(8, [(0, 3), (1, 4), (2, 5)])
    pi_m = perm_from_cycles(8, [(0, 1), (3, 4), (6, 7)])
    return {
        "R_end": check_table("R_end", labels_e, adj_e, rows_end, [rho_e, sigma_e, tau_e], 8),
        "R_mid": check_table("R_mid", labels_m, adj_m, rows_mid, [rho_m, pi_m], 4),
    }


def verify_fort_theorems_degenerate():
    checked_graphs = 0
    checked_pairs = 0
    for n in range(0, 6):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for gmask in range(1 << len(pairs)):
            edges = [pairs[e] for e in range(len(pairs)) if gmask >> e & 1]
            adj = make_graph(n, edges)
            full = (1 << n) - 1
            fs = forts(adj)
            checked_graphs += 1
            for B in range(1 << n):
                cl = closure(adj, B)
                forcing = cl == full
                hits_all = all(B & F for F in fs)
                assert forcing == hits_all, (n, gmask, B, forcing, hits_all)
                if forcing:
                    for F in fs:
                        assert B & F, ("Lemma 2.2", n, gmask, B, F)
                else:
                    F = full ^ cl
                    assert F != 0
                    assert (B & F) == 0
                    assert is_fort(adj, F), ("Lemma 2.3", n, gmask, B, F)
                checked_pairs += 1
    return {"graphs_n_le_5": checked_graphs, "graph_start_pairs": checked_pairs}


def verify_cut_lemma_counterexample_search():
    max_exhaustive_n = 6
    exhaustive_states = 0
    for n in range(0, max_exhaustive_n + 1):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        edge_count = len(pairs)
        adj_cache = []
        z_cache = []
        for gmask in range(1 << edge_count):
            adj = make_graph(n, [pairs[e] for e in range(edge_count) if gmask >> e & 1])
            adj_cache.append(adj)
            z_cache.append(z_number(adj))

        def rec(pos, kept, deleted):
            nonlocal exhaustive_states
            if pos == edge_count:
                exhaustive_states += 1
                G = kept | deleted
                H = kept
                lhs = z_cache[G]
                rhs = z_cache[H] - bitcount(deleted)
                assert lhs >= rhs, (n, G, deleted, lhs, z_cache[H], bitcount(deleted))
                return
            rec(pos + 1, kept, deleted)
            rec(pos + 1, kept | (1 << pos), deleted)
            rec(pos + 1, kept, deleted | (1 << pos))

        rec(0, 0, 0)

    rng = random.Random(20260612)
    random_trials = 0
    for n in (7, 8):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for _ in range(2000):
            G = 0
            deleted = 0
            for e in range(len(pairs)):
                if rng.random() < 0.45:
                    G |= 1 << e
                    if rng.random() < 0.35:
                        deleted |= 1 << e
            H = G & ~deleted
            adjG = make_graph(n, [pairs[e] for e in range(len(pairs)) if G >> e & 1])
            adjH = make_graph(n, [pairs[e] for e in range(len(pairs)) if H >> e & 1])
            lhs = z_number(adjG)
            rhs = z_number(adjH) - bitcount(deleted)
            assert lhs >= rhs, (n, G, deleted, lhs, z_number(adjH), bitcount(deleted))
            random_trials += 1
    return {"exhaustive_ternary_states_n_le_6": exhaustive_states, "random_trials_n_7_8": random_trials}


def build_chain(k):
    labels = []
    block = [{} for _ in range(k + 1)]

    def add(i, name):
        idx = len(labels)
        labels.append(f"{name}^{i}")
        block[i][name] = idx
        return idx

    for i in range(1, k + 1):
        for name in ["a1", "a2", "a3", "b1", "b2", "b3"]:
            add(i, name)
        if i == 1:
            add(i, "s_out")
        elif i == k:
            add(i, "s_in")
        else:
            add(i, "s_in")
            add(i, "s_out")

    edges = []
    for i in range(1, k + 1):
        b = block[i]
        missing = {("a1", "b1")}
        if 1 < i < k:
            missing.add(("a2", "b2"))
        for a in ["a1", "a2", "a3"]:
            for bb in ["b1", "b2", "b3"]:
                if (a, bb) not in missing:
                    edges.append((b[a], b[bb]))
        if i == 1:
            edges += [(b["a1"], b["s_out"]), (b["b1"], b["s_out"])]
        elif i == k:
            edges += [(b["a1"], b["s_in"]), (b["b1"], b["s_in"])]
        else:
            edges += [(b["a1"], b["s_in"]), (b["b1"], b["s_in"])]
            edges += [(b["a2"], b["s_out"]), (b["b2"], b["s_out"])]
    for i in range(1, k):
        edges.append((block[i]["s_out"], block[i + 1]["s_in"]))
    return labels, block, make_graph(len(labels), edges), edges


def read_edge_file(path):
    with open(path, "r", encoding="utf-8") as f:
        first = f.readline().split()
        n, m = int(first[0]), int(first[1])
        edges = []
        for line in f:
            if not line.strip():
                continue
            u, v = map(int, line.split())
            edges.append((u, v))
    assert len(edges) == m
    return n, sorted(tuple(sorted(e)) for e in edges)


def verify_edge_files():
    mismatches = []
    for k in range(2, 9):
        _, _, _, edges = build_chain(k)
        n = 8 * k - 2
        generated = sorted(tuple(sorted(e)) for e in edges)
        file_n, file_edges = read_edge_file(f"..\\chain_indep_k{k}.edges")
        if file_n != n or file_edges != generated:
            mismatches.append(k)
    assert not mismatches, mismatches
    return {"edge_files_matched_k": "2..8"}


def simulate_exact_W_schedule():
    results = {}
    for k in range(2, 7):
        labels, block, adj, _ = build_chain(k)
        W = 0
        for name in ["a1", "a2", "b1", "b2"]:
            W |= 1 << block[1][name]
        for i in range(2, k + 1):
            for name in ["a1", "a2", "b2"]:
                W |= 1 << block[i][name]
        seq = [
            (block[1]["a2"], block[1]["b3"]),
            (block[1]["b2"], block[1]["a3"]),
            (block[1]["a1"], block[1]["s_out"]),
            (block[1]["s_out"], block[2]["s_in"]),
        ]
        for i in range(2, k):
            seq += [
                (block[i]["a1"], block[i]["b3"]),
                (block[i]["s_in"], block[i]["b1"]),
                (block[i]["b1"], block[i]["a3"]),
                (block[i]["a2"], block[i]["s_out"]),
                (block[i]["s_out"], block[i + 1]["s_in"]),
            ]
        seq += [
            (block[k]["a1"], block[k]["b3"]),
            (block[k]["s_in"], block[k]["b1"]),
            (block[k]["b2"], block[k]["a3"]),
        ]
        blue = W
        full = (1 << len(labels)) - 1
        for step, (u, v) in enumerate(seq, start=1):
            white_neighbors = adj[u] & (full ^ blue)
            assert blue >> u & 1, (k, step, labels[u], "forcer not blue")
            assert not (blue >> v & 1), (k, step, labels[v], "target already blue")
            assert white_neighbors == (1 << v), (
                k,
                step,
                labels[u],
                labels[v],
                [labels[x] for x in bits(white_neighbors)],
            )
            blue |= 1 << v
        assert blue == full, (k, [labels[x] for x in bits(full ^ blue)])
        assert bitcount(W) == 3 * k + 1
        results[k] = {"start_size": bitcount(W), "forces": len(seq)}
    return results


def verify_pair_classifications():
    out = {}
    for kind, (labels, adj), expected in [
        (
            "end",
            R_end(),
            [
                ("a1", "b1"),
                ("a2", "b2"),
                ("a2", "b3"),
                ("a3", "b2"),
                ("a3", "b3"),
            ],
        ),
        (
            "middle",
            R_mid(),
            [
                ("a1", "b1"),
                ("a2", "b2"),
                ("a3", "b3"),
            ],
        ),
    ]:
        core = subset_mask(["a1", "a2", "a3", "b1", "b2", "b3"], labels)
        good = []
        for i, j in combinations(range(len(labels)), 2):
            cover = (1 << i) | (1 << j) | adj[i] | adj[j]
            if (cover & core) == core:
                good.append(tuple(sorted([labels[i], labels[j]])))
        exp = sorted(tuple(sorted(x)) for x in expected)
        assert sorted(good) == exp, (kind, good, exp)
        assert all(not any(name.startswith("s") for name in pair) for pair in good)
        out[kind] = good
    return out


def verify_window_lemma_search():
    results = {}
    for k in range(3, 7):
        labels, block, adj, _ = build_chain(k)
        full = (1 << len(labels)) - 1
        block_masks = {}
        for i in range(1, k + 1):
            mask = 0
            for v in block[i].values():
                mask |= 1 << v
            block_masks[i] = mask
        checked = 0
        for start in range(1, k - 1):
            triple_mask = block_masks[start] | block_masks[start + 1] | block_masks[start + 2]
            outside = full ^ triple_mask
            choices = []
            for i in [start, start + 1, start + 2]:
                verts = list(bits(block_masks[i]))
                choices.append([(1 << a) | (1 << b) for a, b in combinations(verts, 2)])
            for p1 in choices[0]:
                for p2 in choices[1]:
                    for p3 in choices[2]:
                        checked += 1
                        D = outside | p1 | p2 | p3
                        if dominates(adj, D):
                            names = [labels[v] for v in bits(p1 | p2 | p3)]
                            raise AssertionError(("window violation", k, start, names))
        results[k] = {"triple_pair_assignments_checked": checked}
    return results


def domination_pattern(k, block):
    q, r = divmod(k, 3)
    if r == 2:
        motifs = ["E"] + ["A", "T", "B"] * q + ["E"]
    elif r == 0:
        motifs = ["E"] + ["A", "T", "B"] * (q - 1) + ["A", "P"]
    else:
        assert k >= 4
        motifs = ["E"] + ["A", "T", "B"] * (q - 1) + ["A", "W", "E"]
    assert len(motifs) == k
    D = 0
    for i, motif in enumerate(motifs, start=1):
        b = block[i]
        if motif == "E":
            take = ["a1", "b1"]
        elif motif == "A":
            take = ["a1", "b1"]
        elif motif == "B":
            take = ["a2", "b2"]
        elif motif == "T":
            take = ["s_in", "s_out", "a3"]
        elif motif == "W":
            take = ["s_in", "a2", "b2"]
        elif motif == "P":
            take = ["s_in", "a2", "b2"]
        else:
            raise AssertionError(motif)
        for name in take:
            D |= 1 << b[name]
    return motifs, D


def verify_gamma_patterns_and_arithmetic():
    results = {}
    certified_gamma = {2: 4, 3: 7, 4: 9, 5: 11, 6: 14, 7: 16, 8: 18}
    certified_Z_exact = {2: 7, 3: 10, 4: 13, 5: 16}
    for k in range(2, 13):
        labels, block, adj, _ = build_chain(k)
        motifs, D = domination_pattern(k, block)
        gamma_formula = (7 * k) // 3
        z_formula = 3 * k + 1
        n = 8 * k - 2
        gap = z_formula - gamma_formula
        assert dominates(adj, D), (k, motifs)
        assert bitcount(D) == gamma_formula, (k, bitcount(D), gamma_formula)
        assert gap == ceil_div(2 * k, 3) + 1, (k, gap)
        assert gap == ceil_div(n + 14, 12), (k, gap, n)
        if k in certified_gamma:
            assert gamma_formula == certified_gamma[k], (k, gamma_formula, certified_gamma[k])
        if k in certified_Z_exact:
            assert z_formula == certified_Z_exact[k], (k, z_formula, certified_Z_exact[k])
        results[k] = {"motifs": "".join(motifs), "size": bitcount(D), "gap": gap}
    return results


def main():
    report = {}
    report["edge_files"] = verify_edge_files()
    report["per_block_and_tables"] = verify_per_block_and_tables()
    report["fort_theorems_degenerate"] = verify_fort_theorems_degenerate()
    report["cut_lemma_counterexample_search"] = verify_cut_lemma_counterexample_search()
    report["W_schedule"] = simulate_exact_W_schedule()
    report["pair_classifications"] = verify_pair_classifications()
    report["window_search"] = verify_window_lemma_search()
    report["gamma_patterns_arithmetic"] = verify_gamma_patterns_and_arithmetic()
    for key, value in report.items():
        print(f"{key}: {value}")
    print("FRESH HOSTILE CHECKS PASSED")


if __name__ == "__main__":
    main()
