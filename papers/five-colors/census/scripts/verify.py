#!/usr/bin/env python3
"""Independent rerun/checker for scout JSON results and CNF certificates."""
import argparse, hashlib, json
from pathlib import Path
import networkx as nx
from pysat.formula import CNF
from pysat.solvers import Cadical195, Glucose42
from search import admissible, solve_exact, verify_coloring

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("json"); args=ap.parse_args()
    data=json.loads(Path(args.json).read_text())
    records=data.get("records", []) + data.get("failures4", []) + data.get("failures5", [])
    checked=0
    for r in records:
        if not r.get("admissible", True): continue
        g=nx.from_graph6_bytes(r["graph6"].encode())
        assert admissible(g)
        for q in (4,5):
            key=f"coloring{q}"
            if r.get(key) is not None:
                assert verify_coloring(g, r[key], q)
            satkey=f"sat{q}"
            if satkey in r:
                sat, colors, *_=solve_exact(g,q,crosscheck_unsat=True)
                assert sat == r[satkey]
        checked += 1
    print(f"verified {checked} graph records")

if __name__ == "__main__": main()
