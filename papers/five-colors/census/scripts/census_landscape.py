#!/usr/bin/env python3
"""Exact Maj' census using the frozen AristotleMaj5 row inequalities.

For every reported k>1, CaDiCaL proves SAT at k and UNSAT at k-1, the SAT
model is checked directly, and Glucose independently confirms UNSAT at k-1.
"""
from __future__ import annotations
import argparse, json, time
from collections import Counter, defaultdict
from pathlib import Path

import networkx as nx
from pysat.solvers import Glucose42
from search import (admissible, edges_and_rows, graph_record, make_cnf,
                    read_g6, solve_exact)


def palette_lower_bound(g: nx.Graph) -> int:
    """Pigeonhole lower bound from each row; at least one color always."""
    _, rows, caps = edges_and_rows(g)
    lb = 1
    for row, cap in zip(rows, caps):
        if row:
            if cap == 0:
                return 10**9  # cannot occur in an admissible graph
            lb = max(lb, (len(row) + cap - 1) // cap)
    return lb


def exact_maj(g: nx.Graph, max_k: int = 6):
    lb = palette_lower_bound(g)
    last_unsat = None
    trials = []
    for k in range(lb, max_k + 1):
        sat, colors, seconds, stats, cnf = solve_exact(
            g, k, crosscheck_unsat=False, use_dfs=False)
        trials.append({"k": k, "sat": sat, "seconds": seconds,
                       "conflicts": stats.get("conflicts", 0)})
        if sat:
            if k > 1:
                if last_unsat is not None and last_unsat[0] == k-1:
                    _, sec_prev, stats_prev, previous_cnf = last_unsat
                else:
                    sat_prev, _, sec_prev, stats_prev, previous_cnf = solve_exact(
                        g, k-1, crosscheck_unsat=False, use_dfs=False)
                    assert not sat_prev
                if previous_cnf is None:
                    previous_cnf, _ = make_cnf(g, k-1)
                with Glucose42(bootstrap_with=previous_cnf.clauses) as s2:
                    assert not s2.solve(), "Glucose disagrees at k-1"
                boundary = {"k_minus_1": k-1, "cadical_unsat": True,
                            "glucose_unsat": True,
                            "cadical_seconds": sec_prev,
                            "cadical_conflicts": stats_prev.get("conflicts", 0)}
            else:
                boundary = {"k_minus_1": 0, "not_applicable": True}
            return k, colors, trials, boundary
        last_unsat = (k, seconds, stats, cnf)
    raise RuntimeError(f"no coloring through {max_k} colors")


def features(g: nx.Graph):
    return {
        "degree_sequence": sorted((d for _, d in g.degree()), reverse=True),
        "degree2_vertices": sum(d == 2 for _, d in g.degree()),
        "triangles": sum(nx.triangles(g).values()) // 3,
    }


def exhaustive(args):
    root = Path(args.output_dir); root.mkdir(parents=True, exist_ok=True)
    for name in args.graph6:
        p = Path(name); n = None; dist = Counter(); tested = 0
        out_path = root / (p.stem + "_maj.jsonl")
        with out_path.open("w", encoding="utf-8") as out:
            for g in read_g6(p):
                if not admissible(g): continue
                n = g.number_of_nodes(); tested += 1
                k, colors, trials, boundary = exact_maj(g, args.max_k)
                dist[k] += 1
                rec = {"graph6": nx.to_graph6_bytes(g, header=False).decode().strip(),
                       "n": n, "m": g.number_of_edges(), "maj": k}
                out.write(json.dumps(rec, separators=(",", ":")) + "\n")
        print(n, tested, dict(sorted(dist.items())), flush=True)


def finalize(args):
    files=[Path(x) for x in args.jsonl]
    counts=defaultdict(Counter); candidates=defaultdict(list); min_n={}
    for p in files:
        for line in p.open(encoding="utf-8"):
            r=json.loads(line); n=r["n"]; k=r["maj"]; counts[n][k]+=1
            if k not in min_n or n < min_n[k]: min_n[k]=n; candidates[k]=[r]
            elif n == min_n[k]: candidates[k].append(r)
    extremal={}
    for k, rs in sorted(candidates.items()):
        extremal[str(k)]=[]
        for r in rs:
            g=nx.from_graph6_bytes(r["graph6"].encode())
            k2, colors, trials, boundary=exact_maj(g,args.max_k); assert k2==k
            extremal[str(k)].append(graph_record(g,maj=k,boundary=boundary,
                coloring=colors,**features(g)))
    dist={str(n):{**{str(k):counts[n][k] for k in range(1,args.max_k+1)},
                  "total":sum(counts[n].values())} for n in sorted(counts)}
    summary={"scope":"all admissible connected unlabeled graphs through n=9",
      "definition":"frozen AristotleMaj5.lean",
      "boundary_verification":"CaDiCaL SAT at k; direct model check; CaDiCaL and Glucose UNSAT at k-1",
      "distribution":dist,"maximum_maj":max(min_n),"value5_occurs":5 in min_n,
      "per_graph_files":[str(p) for p in files]}
    Path(args.output).write_text(json.dumps(summary,indent=2)+"\n")
    Path(args.extremal).write_text(json.dumps(extremal,indent=2)+"\n")
    print(json.dumps(dist,indent=2))


def nonexhaustive(args):
    records=[]
    for spec in args.graph6:
        p=Path(spec)
        for g in read_g6(p):
            if not admissible(g): continue
            k, colors, trials, boundary=exact_maj(g,args.max_k)
            records.append({"source":p.name,
                "graph6":nx.to_graph6_bytes(g,header=False).decode().strip(),
                "n":g.number_of_nodes(),"m":g.number_of_edges(),"maj":k})
    if args.targeted:
        data=json.loads(Path(args.targeted).read_text())
        for r in data["records"]:
            if not r.get("admissible",True): continue
            g=nx.from_graph6_bytes(r["graph6"].encode())
            k, colors, trials, boundary=exact_maj(g,args.max_k)
            records.append({"source":"targeted","label":r.get("label"),
                "graph6":r["graph6"],"n":r["n"],"m":r["m"],"maj":k})
    dist=Counter(r["maj"] for r in records)
    Path(args.output).write_text(json.dumps({"coverage":"non-exhaustive beyond n=9",
        "records":records,"distribution":{str(k):v for k,v in sorted(dist.items())}},
        indent=2)+"\n")
    print(len(records),dict(sorted(dist.items())))


def main():
    ap=argparse.ArgumentParser(); sub=ap.add_subparsers(required=True)
    p=sub.add_parser("exhaustive");p.add_argument("graph6",nargs="+")
    p.add_argument("--output-dir",required=True);p.add_argument("--max-k",type=int,default=6)
    p.set_defaults(func=exhaustive)
    p=sub.add_parser("nonexhaustive");p.add_argument("graph6",nargs="*")
    p.add_argument("--targeted");p.add_argument("--output",required=True)
    p.add_argument("--max-k",type=int,default=6);p.set_defaults(func=nonexhaustive)
    p=sub.add_parser("finalize");p.add_argument("jsonl",nargs="+")
    p.add_argument("--output",required=True);p.add_argument("--extremal",required=True)
    p.add_argument("--max-k",type=int,default=6);p.set_defaults(func=finalize)
    a=ap.parse_args();a.func(a)
if __name__=="__main__":main()
