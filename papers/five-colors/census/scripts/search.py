#!/usr/bin/env python3
"""Exact strong-majority edge-colouring search matching AristotleMaj5.lean.

Input graphs are graph6 records (normally emitted by nauty geng).  For each
edge uv, its row is every edge incident with u or v except uv itself.  Every
colour occurs in that row at most (deg(u)+deg(v)-2)//2 times.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195, Glucose42


def edges_and_rows(g: nx.Graph):
    edges = sorted(tuple(sorted(e)) for e in g.edges())
    where = {e: i for i, e in enumerate(edges)}
    inc = {v: set() for v in g.nodes()}
    for i, (u, v) in enumerate(edges):
        inc[u].add(i)
        inc[v].add(i)
    rows = []
    caps = []
    for i, (u, v) in enumerate(edges):
        rows.append(sorted((inc[u] | inc[v]) - {i}))
        # Python integers are nonnegative here: endpoints of an edge have
        # degree >= 1. This is exactly Lean Nat subtraction and division.
        caps.append((g.degree(u) + g.degree(v) - 2) // 2)
    return edges, rows, caps


def admissible(g: nx.Graph) -> bool:
    return all(g.degree(u) + g.degree(v) != 3 for u, v in g.edges())


def verify_coloring(g: nx.Graph, colors: list[int], q: int) -> bool:
    edges, rows, caps = edges_and_rows(g)
    if len(colors) != len(edges) or any(not 0 <= c < q for c in colors):
        return False
    return all(sum(colors[j] == a for j in row) <= cap
               for row, cap in zip(rows, caps) for a in range(q))


def make_cnf(g: nx.Graph, q: int) -> tuple[CNF, list[list[int]]]:
    edges, rows, caps = edges_and_rows(g)
    pool = IDPool()
    x = [[pool.id((e, a)) for a in range(q)] for e in range(len(edges))]
    cnf = CNF()
    for variables in x:
        cnf.extend(CardEnc.equals(variables, 1, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    # Colour permutation symmetry: if an edge exists, call its colour 0.
    if edges:
        cnf.append([x[0][0]])
    for row, cap in zip(rows, caps):
        if cap < len(row):
            for a in range(q):
                cnf.extend(CardEnc.atmost([x[j][a] for j in row], cap,
                                          vpool=pool,
                                          encoding=EncType.seqcounter).clauses)
    return cnf, x


def backtrack_coloring(g: nx.Graph, q: int):
    """Constructive exact DFS; a returned assignment is a SAT certificate.

    It is optimized for the overwhelmingly SAT enumeration cases. If its
    complete search fails, solve_exact still asks two CDCL solvers to certify
    UNSAT independently.
    """
    edges, rows, caps = edges_and_rows(g)
    m = len(edges)
    if not m:
        return [], 1
    containing = [[] for _ in range(m)]
    for target, row in enumerate(rows):
        for e in row: containing[e].append(target)
    order = sorted(range(m), key=lambda e: (
        -sum(1.0/(caps[t]+1) for t in containing[e]),
        -len(containing[e]), e))
    counts = [[0]*q for _ in range(m)]
    colors = [-1]*m
    nodes = 0
    def dfs(pos, used):
        nonlocal nodes
        nodes += 1
        if pos == m: return True
        e = order[pos]
        # Existing colours first, least-loaded in affected rows. Then at most
        # one new colour: all unused colours are permutation-equivalent.
        choices = list(range(used))
        choices.sort(key=lambda a: sum(counts[t][a] for t in containing[e]))
        if used < q: choices.append(used)
        for a in choices:
            if any(counts[t][a] >= caps[t] for t in containing[e]):
                continue
            colors[e] = a
            for t in containing[e]: counts[t][a] += 1
            if dfs(pos+1, max(used, a+1)): return True
            for t in containing[e]: counts[t][a] -= 1
            colors[e] = -1
        return False
    return (colors if dfs(0, 0) else None), nodes


def solve_exact(g: nx.Graph, q: int, crosscheck_unsat: bool = False,
                use_dfs: bool = True):
    nodes = 0
    if use_dfs:
        quick, nodes = backtrack_coloring(g, q)
        if quick is not None:
            assert verify_coloring(g, quick, q)
            return True, quick, 0.0, {"engine":"dfs", "nodes":nodes,
                                      "conflicts":max(0, nodes-len(quick)-1)}, None
    cnf, x = make_cnf(g, q)
    start = time.perf_counter()
    with Cadical195(bootstrap_with=cnf.clauses) as solver:
        sat = solver.solve()
        elapsed = time.perf_counter() - start
        stats = solver.accum_stats()
        model = solver.get_model() if sat else None
    colors = None
    if sat:
        positive = set(v for v in model if v > 0)
        colors = [next(a for a, var in enumerate(vs) if var in positive)
                  for vs in x]
        assert verify_coloring(g, colors, q)
    elif crosscheck_unsat:
        with Glucose42(bootstrap_with=cnf.clauses) as solver2:
            assert not solver2.solve(), "independent solver disagreement"
    stats["engine"] = "cadical195"
    stats["dfs_nodes"] = nodes
    return sat, colors, elapsed, stats, cnf


def graph_record(g: nx.Graph, **extra):
    h = nx.convert_node_labels_to_integers(g, ordering="sorted")
    rec = {
        "n": h.number_of_nodes(), "m": h.number_of_edges(),
        "degree_sequence": sorted((d for _, d in h.degree()), reverse=True),
        "edges": sorted([list(sorted(e)) for e in h.edges()]),
        "graph6": nx.to_graph6_bytes(h, header=False).decode().strip(),
    }
    rec.update(extra)
    return rec


def read_g6(path: Path):
    with path.open("rb") as f:
        for raw in f:
            raw = raw.strip()
            if raw and not raw.startswith(b">"):
                yield nx.from_graph6_bytes(raw)


def exhaustive(args):
    out = Path(args.output)
    summary = {"mode": "exhaustive", "inputs": [], "totals": {}}
    top_hard = []
    failures4 = []
    failures5 = []
    totals = {"graphs": 0, "admissible": 0, "sat5": 0, "unsat5": 0,
              "sat4": 0, "unsat4": 0}
    for name in args.graph6:
        p = Path(name)
        item = {"file": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                "graphs": 0, "admissible": 0, "sat5": 0, "unsat5": 0,
                "sat4": 0, "unsat4": 0}
        for g in read_g6(p):
            item["graphs"] += 1
            totals["graphs"] += 1
            if not admissible(g):
                continue
            item["admissible"] += 1
            totals["admissible"] += 1
            sat5, c5, t5, s5, _ = solve_exact(g, 5, crosscheck_unsat=True)
            key5 = "sat5" if sat5 else "unsat5"
            item[key5] += 1; totals[key5] += 1
            if not sat5:
                failures5.append(graph_record(g, seconds=t5, stats=s5))
            sat4, c4, t4, s4, _ = solve_exact(g, 4, crosscheck_unsat=True)
            key4 = "sat4" if sat4 else "unsat4"
            item[key4] += 1; totals[key4] += 1
            if not sat4:
                failures4.append(graph_record(g, seconds=t4, stats=s4))
            score = (s5.get("conflicts", 0), t5)
            top_hard.append((score, graph_record(g, sat4=sat4,
                            seconds5=t5, stats5=s5, coloring5=c5)))
            if len(top_hard) > args.keep_hard * 3:
                top_hard.sort(key=lambda z: z[0], reverse=True)
                del top_hard[args.keep_hard:]
        summary["inputs"].append(item)
        print(json.dumps(item), flush=True)
    top_hard.sort(key=lambda z: z[0], reverse=True)
    summary["totals"] = totals
    summary["failures5"] = failures5
    summary["failures4"] = failures4
    summary["hardest5"] = [r for _, r in top_hard[:args.keep_hard]]
    out.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(totals), flush=True)


def family_graphs(seed: int):
    def emit(label, g):
        g = nx.convert_node_labels_to_integers(nx.Graph(g))
        if nx.is_connected(g): return label, g
        return None
    for n in range(5, 31):
        for k in range(2, min(n, 9)):
            if n * k % 2 == 0:
                for j in range(3):
                    try:
                        z = emit(f"random_{k}regular_n{n}_{j}",
                                 nx.random_regular_graph(k, n, seed=seed+1000*n+10*k+j))
                        if z: yield z
                    except nx.NetworkXError: pass
    for a in range(1, 16):
        for b in range(a, 16):
            z = emit(f"K_{a}_{b}", nx.complete_bipartite_graph(a, b))
            if z: yield z
    for n in range(4, 21):
        for k in range(2, min(8, n)):
            z = emit(f"cycle_blown_K{k}_n{n}",
                     nx.lexicographic_product(nx.cycle_graph(n), nx.complete_graph(k)))
            if z: yield z
    # Subdivided high-degree cores: 1 and 2 subdivisions per core edge.
    for core_name, core in [("K5", nx.complete_graph(5)), ("K6", nx.complete_graph(6)),
                            ("Petersen", nx.petersen_graph()),
                            ("octahedral", nx.octahedral_graph())]:
        for count in (1, 2):
            g = nx.Graph(); g.add_nodes_from(core.nodes()); nxt = len(core)
            for u, v in core.edges():
                path = [u] + list(range(nxt, nxt+count)) + [v]; nxt += count
                g.add_edges_from(zip(path, path[1:]))
            z = emit(f"{core_name}_subdiv{count}", g)
            if z: yield z


def targeted(args):
    records = []
    out = Path(args.output)
    for label, g in family_graphs(args.seed):
        if not admissible(g):
            records.append(graph_record(g, label=label, admissible=False))
            out.write_text(json.dumps({"mode":"targeted", "seed":args.seed,
                                       "complete":False, "records":records}, indent=2)+"\n")
            continue
        sat5, c5, t5, s5, _ = solve_exact(g, 5, crosscheck_unsat=True, use_dfs=False)
        sat4, c4, t4, s4, _ = solve_exact(g, 4, crosscheck_unsat=True, use_dfs=False)
        records.append(graph_record(g, label=label, admissible=True, sat5=sat5,
                       sat4=sat4, seconds5=t5, seconds4=t4, stats5=s5, stats4=s4,
                       coloring5=c5, coloring4=c4))
        out.write_text(json.dumps({"mode":"targeted", "seed":args.seed,
                                   "complete":False, "records":records}, indent=2)+"\n")
        print(label, g.number_of_nodes(), g.number_of_edges(), sat5, sat4, flush=True)
    out.write_text(json.dumps({"mode":"targeted", "seed":args.seed,
                               "complete":True, "records":records}, indent=2)+"\n")


def certificate(args):
    g = nx.from_graph6_bytes(args.graph6.encode())
    sat, colors, elapsed, stats, cnf = solve_exact(g, args.colors, True)
    if sat: raise SystemExit("graph is SAT, not a failure certificate")
    if cnf is None:
        cnf, _ = make_cnf(g, args.colors)
    cnf.to_file(args.output)
    print(json.dumps(graph_record(g, colors=args.colors, sat=False,
                                  seconds=elapsed, stats=stats,
                                  cnf_sha256=hashlib.sha256(Path(args.output).read_bytes()).hexdigest()),
                     indent=2))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(required=True)
    p = sub.add_parser("exhaustive")
    p.add_argument("graph6", nargs="+"); p.add_argument("--output", required=True)
    p.add_argument("--keep-hard", type=int, default=30); p.set_defaults(func=exhaustive)
    p = sub.add_parser("targeted")
    p.add_argument("--output", required=True); p.add_argument("--seed", type=int, default=20260711)
    p.set_defaults(func=targeted)
    p = sub.add_parser("certificate")
    p.add_argument("graph6"); p.add_argument("--colors", type=int, required=True)
    p.add_argument("--output", required=True); p.set_defaults(func=certificate)
    args = ap.parse_args(); args.func(args)


if __name__ == "__main__": main()
